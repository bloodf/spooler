"""Slot links shared with U1 Control and Kobra Control. Spoolman's location is the one link store; this file checks
that Spooler writes the form each peer reads and reads the form each peer writes (a renamed Kobra printer included,
by the name Kobra Control's presence gives), that a link change on either side is signalled through the presence
files, and the refresh setting. No printer and no Spoolman is contacted: spoolman_call is a fake."""

import os
import tempfile
import time
import unittest
from pathlib import Path
from unittest import mock

from test_slot_bind import KOBRA, Base, sp, spool  # the same loaded plugin module as Base patches


def kobra_presence(name="Workshop", host="http://kx.example", links=0, **extra):
    return {"schema": sp.PEER_SCHEMA, "version": 1, "plugin": "kobracontrol", "session": "k1", "pid": os.getpid(),
            "ts": time.time(), "state": "active", "links": links, "printer": {"host": host, "name": name}, **extra}


class PeerFiles(unittest.TestCase):
    """Presence files in a temporary OrcaSlicer data folder."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        patch = mock.patch.object(sp, "_orca_data_dir", return_value=self.root)
        patch.start()
        self.addCleanup(patch.stop)
        saved = dict(sp._peer)
        self.addCleanup(lambda: (sp._peer.clear(), sp._peer.update(saved)))
        sp._peer.update(seen={}, kobra=None, links=0)

    def write(self, plugin, doc):
        (self.root / plugin).mkdir(exist_ok=True)
        (self.root / plugin / "presence.json").write_text(sp.json.dumps(doc), encoding="utf-8")


class KobraNameTest(PeerFiles, Base):
    def setUp(self):
        Base.setUp(self)
        PeerFiles.setUp(self)

    def test_renamed_kobra_printer_is_linked_and_read_by_its_name(self):
        self.write("kobracontrol", kobra_presence("Workshop"))
        sp.watch_peer_links()
        self.assertEqual(sp.location_names(KOBRA), ("Anycubic Kobra X", "Workshop"))
        self.spools.append(spool(5, "Workshop S1"))   # linked in Kobra Control under its own name
        self.assertEqual(sp.spool_at_kx_slot(self.spools, sp.location_names(KOBRA), 1)["id"], 5)
        self.assertTrue(sp.slot_bind(1, "auto-kx", 0, True)["ok"])
        self.assertEqual(self.calls, [("PATCH", "spool/1", {"location": "Workshop S1"}),
                                      ("PATCH", "spool/5", {"location": None})])

    def test_kobra_name_for_another_printer_is_not_used(self):
        self.write("kobracontrol", kobra_presence("Garage", host="http://other.example"))
        sp.watch_peer_links()
        self.assertEqual(sp.location_names(KOBRA), ("Anycubic Kobra X",))

    def test_without_kobra_control_the_model_name_is_written(self):
        sp.watch_peer_links()
        self.assertTrue(sp.slot_bind(1, "auto-kx", 2, True)["ok"])
        self.assertEqual(self.calls[0], ("PATCH", "spool/1", {"location": "Anycubic Kobra X S3"}))

    def test_u1_controls_renamed_printer_is_read(self):
        # u1control keeps a name ending in "U1"; Spooler reads any such name.
        self.assertEqual(sp.spool_at_location([spool(6, "Workshop U1 T2")], ("Snapmaker U1",), 2)["id"], 6)


class LinksSignalTest(PeerFiles):
    def test_peer_links_moving_refreshes_the_page_once(self):
        with mock.patch.object(sp, "_ws_notify") as notify:
            self.write("u1control", {**kobra_presence(), "plugin": "u1control", "links": 1})
            sp.watch_peer_links()
            notify.assert_not_called()          # the first value seen is only remembered
            sp.watch_peer_links()
            notify.assert_not_called()
            self.write("u1control", {**kobra_presence(), "plugin": "u1control", "links": 2})
            sp.watch_peer_links()
            notify.assert_called_once()

    def test_a_stopped_peer_moves_nothing(self):
        with mock.patch.object(sp, "_ws_notify") as notify:
            self.write("kobracontrol", kobra_presence(links=1))
            sp.watch_peer_links()
            self.write("kobracontrol", kobra_presence(links=2, state="stopped"))
            sp.watch_peer_links()
            notify.assert_not_called()

    def test_spoolers_own_links_are_published(self):
        sp._peer["session"] = "s1"
        self.addCleanup(lambda: sp._peer.update(session=""))
        self.assertEqual(sp.presence_doc()["links"], 0)
        sp.links_changed()
        self.assertGreater(sp._peer["links"], 0)
        written = sp.json.loads((self.root / "spooler" / "presence.json").read_text(encoding="utf-8"))
        self.assertEqual(written["links"], sp._peer["links"])


class RefreshSettingTest(unittest.TestCase):
    def test_values(self):
        self.assertEqual([sp.parse_refresh(v) for v in (0, 10, 300, 45, 9, 301, True, "30", None, 2.5)],
                         [0, 10, 300, 45, 30, 30, 30, 30, 30, 30])

    def test_saved_on_its_own(self):
        with mock.patch.object(sp, "update_settings") as update:
            sp.save_refresh(60)
            sp.save_refresh(5)
            sp.save_refresh(None)
        update.assert_called_once_with({"spoolman_refresh_s": 60})


if __name__ == "__main__":
    unittest.main()
