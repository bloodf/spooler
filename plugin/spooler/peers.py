# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Files shared with u1control and Kobra Control: links, presence and stock."""

import json
import os
import threading
import time
import urllib.parse
from pathlib import Path

# --- Files shared with u1control --------------------------------------------------------
# u1control (github.com/bloodf/u1control) runs the Snapmaker U1 from OrcaSlicer and reads these
# from <OrcaSlicer data folder>/spooler/, so both plugins pick the same preset for a spool and
# only one of them changes the plate's slots:
#   profiles.json:   {"version": 1, "updated": <unix s>,
#                     "filaments": {"<filament id>": {"<printer label>": "_local/spooler/<preset>"}},
#                     "spools": {"<spool id>": {"<printer label>": "_local/spooler/<preset>"}}}
#                    "spools" is there only with presets per spool: each spool's own preset, which readers
#                    use before the filament's. "ids": {"_local/spooler/<preset>": "<filament_id>"}, the
#                    filament_id of each standalone preset, which OrcaSlicer's plugin API doesn't show:
#                    printer agents report it so OrcaSlicer's sync from AMS loads that preset.
#   keep_slots.json: {"active": true, "printer": "<label>", "ts": <unix s>} while Keep Slots Synced
#                    runs, refreshed every pass; {"active": false, "ts": ...} once it stops.
BRIDGE_PROFILES = "profiles.json"
BRIDGE_KEEP = "keep_slots.json"
_bridge: dict = {"profiles": None}


def bridge_dir() -> Path:
    """<OrcaSlicer data folder>/spooler, where u1control looks for these files."""
    root = _filament_profiles._orca_data_dir()
    return root / _filament_profiles.PROFILE_BUNDLE if root else _core.DATA_DIR


def profile_map(by_key: dict, printers: list[dict]) -> dict:
    """{"<filament id>": {"<printer label>": "_local/spooler/<preset>"}} for every generated preset;
    with presets per spool, the preset of the filament's lowest-numbered spool on that printer."""
    labels = {p["target"]: p["label"] for p in printers}
    out: dict = {}
    # Per filament as before (filament id as text, then printer), so profiles.json doesn't change.
    for key, name in sorted(by_key.items(), key=lambda item: (str(item[0][0]), item[0][1], str(item[0][2] if len(item[0]) > 2 else "").zfill(12))):
        if key[1] in labels:
            out.setdefault(str(key[0]), {}).setdefault(labels[key[1]], _filament_profiles.PROFILE_PREFIX + name)
    return out


def spool_map(by_key: dict, printers: list[dict]) -> dict:
    """{"<spool id>": {"<printer label>": "_local/spooler/<preset>"}} for presets made per spool; {} otherwise."""
    labels = {p["target"]: p["label"] for p in printers}
    out: dict = {}
    for key, name in sorted(by_key.items(), key=lambda item: str(item[0][2] if len(item[0]) > 2 else "").zfill(12)):
        if len(key) > 2 and key[1] in labels:
            out.setdefault(str(key[2]), {}).setdefault(labels[key[1]], _filament_profiles.PROFILE_PREFIX + name)
    return out


def publish_profiles(by_key: dict, printers: list[dict], files: dict | None = None) -> None:
    """Write profiles.json when the presets changed (or it is missing). Never raises."""
    doc = {"filaments": profile_map(by_key, printers)}
    spools = spool_map(by_key, printers)
    if spools:
        doc["spools"] = spools
    ids = {_filament_profiles.PROFILE_PREFIX + name: (files or {}).get(f"{name}.json", {}).get("filament_id")
           for name in sorted(by_key.values())}
    ids = {name: fid for name, fid in ids.items() if fid}
    if ids:
        doc["ids"] = ids
    path = bridge_dir() / BRIDGE_PROFILES
    if doc == _bridge["profiles"] and path.exists():
        return
    try:
        _filament_profiles._write_json(path, {"version": 1, "updated": int(time.time()), **doc})
        _bridge["profiles"] = doc
    except OSError as exc:
        _core.log.warning("Could not write %s: %s", path, exc)


def mark_keep_slots(active: bool, printer: str = "") -> None:
    """Tell u1control whether Keep Slots Synced owns the plate's slots. Never raises."""
    marker = {"active": True, "printer": printer, "ts": int(time.time())} if active else \
        {"active": False, "ts": int(time.time())}
    try:
        _filament_profiles._write_json(bridge_dir() / BRIDGE_KEEP, marker)
    except OSError as exc:
        _core.log.warning("Could not write %s: %s", BRIDGE_KEEP, exc)


def label_for_target(target: str) -> str:
    """Spooler's label for a printer ("Snapmaker U1"), from the last snapshot; "" when unknown."""
    return next((p["label"] for p in _filament_profiles._ui_snap.get("printers") or [] if p["target"] == target), "")


# --- Presence and stock for u1control -------------------------------------------------------
# OrcaSlicer's plugin API can't list the loaded plugins, pass messages between them or hide a tab;
# its data folder is shared and writable by every plugin. So each plugin writes
# <data folder>/<plugin>/presence.json every PEER_BEAT seconds while it is loaded:
#   {"schema": "orca-plugin-presence", "version": 1, "plugin": "spooler", "plugin_version": ...,
#    "session": <random per load>, "pid": <process>, "started", "ts": <unix s>, "state": "active"|"stopped", ...}
# A peer counts as running only when its file is "active", fresh (PEER_FRESH s) and of this process.
# While u1control runs and its tab shows the stock (its presence "wants" it), Spooler writes
# <data folder>/spooler/stock.json from its Spoolman reads; nothing is written to Spoolman or a
# printer for it. u1control links spools with its own commands; filament use stays with u1control.
PEER_SCHEMA = "orca-plugin-presence"
PEER_VERSION = 1
STOCK_SCHEMA = "spooler-stock"
STOCK_VERSION = 1
PEER_BEAT = 5.0
PEER_FRESH = 20.0
STOCK_EVERY = 30.0      # seconds between stock re-reads while u1control shows the stock
STOCK_ROWS = 2000
PEER_FILE = "presence.json"
STOCK_FILE = "stock.json"
U1CONTROL = "u1control"
KOBRACONTROL = "kobracontrol"
# Each plugin's presence carries "links": the time (unix ms) it last linked or unlinked a spool. Seeing a peer's
# move, the open page re-reads Spoolman at once; Spooler's own moves when its Printer tab assigns. Kobra Control's
# presence also names its printer ({"host", "name"}): its slot links use that name, which the user may have changed.
_peer: dict = {"session": "", "started": 0.0, "users": 0, "stop": None, "thread": None,
               "seq": 0, "stock_at": 0.0, "served": None, "links": 0, "seen": {}, "kobra": None}
_peer_lock = threading.Lock()


def public_url(url: str) -> str:
    """A Spoolman address without user name or password, for files other plugins read."""
    try:
        parts = urllib.parse.urlsplit(_sources.clean_url(url))
    except ValueError:
        return ""
    if not parts.hostname:
        return _sources.clean_url(url)
    host = f"[{parts.hostname}]" if ":" in parts.hostname else parts.hostname
    try:
        port = f":{parts.port}" if parts.port else ""
    except ValueError:
        return ""
    return urllib.parse.urlunsplit((parts.scheme, host + port, parts.path, "", ""))


def peer_alive(doc: object, plugin: str, now: float | None = None) -> bool:
    """Whether a presence file is of `plugin`, running now in this OrcaSlicer process."""
    now = time.time() if now is None else now
    if not isinstance(doc, dict) or doc.get("schema") != PEER_SCHEMA or doc.get("version") != PEER_VERSION:
        return False
    ts = doc.get("ts")
    return (doc.get("plugin") == plugin and doc.get("state") == "active" and doc.get("pid") == os.getpid()
            and isinstance(doc.get("session"), str) and bool(doc["session"])
            and isinstance(ts, (int, float)) and not isinstance(ts, bool) and -5 <= now - ts <= PEER_FRESH)


def _read_peer(plugin: str) -> dict | None:
    root = _filament_profiles._orca_data_dir()
    if root is None:
        return None
    try:
        data = json.loads((root / plugin / PEER_FILE).read_text(encoding="utf-8"))
    except (OSError, ValueError):
        return None
    return data if isinstance(data, dict) else None


def presence_doc(state: str = "active") -> dict:
    settings = _core.get_settings()
    src = _sources.parse_source(settings.get("spool_source"))
    return {"schema": PEER_SCHEMA, "version": PEER_VERSION, "plugin": _filament_profiles.PROFILE_BUNDLE, "plugin_version": _core.PLUGIN_VERSION,
            "session": _peer["session"], "pid": os.getpid(), "started": int(_peer["started"]), "ts": time.time(),
            "state": state, "provides": {"stock": STOCK_VERSION}, "links": _peer["links"],
            "spoolman": {"source": src, "origin": public_url(settings.get("spoolman_url")) if src == "spoolman" else ""}}


def publish_presence(state: str = "active") -> bool:
    if _filament_profiles._orca_data_dir() is None or not _peer["session"]:
        return False
    try:
        _filament_profiles._write_json(bridge_dir() / PEER_FILE, presence_doc(state))
        return True
    except OSError as exc:
        _core.log.warning("Could not write %s: %s", PEER_FILE, exc)
        return False


def u1control_wants() -> dict | None:
    """u1control's stock request while it runs and its tab shows the stock; else None."""
    doc = _read_peer(U1CONTROL)
    if not peer_alive(doc, U1CONTROL):
        return None
    wants = doc.get("wants") if isinstance(doc.get("wants"), dict) else {}
    until = wants.get("stock_until")
    if not isinstance(until, (int, float)) or isinstance(until, bool) or until < time.time():
        return None
    request = wants.get("stock_request")
    return {"request": request if isinstance(request, int) and not isinstance(request, bool) else 0}


def peer_context() -> dict:
    """For the page: whether U1 Control runs in this OrcaSlicer now (its tab holds the printer and spool links).
    Read-only; never sends anything to a printer. Never raises."""
    try:
        return {"peers": {"u1control": peer_alive(_read_peer(U1CONTROL), U1CONTROL)}}
    except Exception:  # noqa: BLE001 - a hint for the page, never worth failing the spool list
        return {"peers": {"u1control": False}}


def spools_message_extras(result: dict) -> dict:
    """Fields every "spools" message carries besides the list: the peer hint and, on a failed read, a stable
    error code ("read_failed") the page can word in its own language; the English "error" text stays."""
    extras = {**peer_context(), "refresh_s": _capabilities.refresh_secs()}
    if not result.get("ok", True) and "error_code" not in result:
        extras["error_code"] = "read_failed"
    return extras


def stock_row(spool: dict, limit: float, first: dict) -> dict:
    filament = spool.get("filament") if isinstance(spool.get("filament"), dict) else {}
    vendor = filament.get("vendor") if isinstance(filament.get("vendor"), dict) else {}
    remaining = spool.get("remaining_weight")
    multi = filament.get("multi_color_hexes")
    return {"id": spool.get("id"), "filament_id": filament.get("id"), "name": filament.get("name") or "",
            "vendor": vendor.get("name") or "", "material": filament.get("material") or "",
            "colour": filament.get("color_hex") or "", "colours": multi.split(",") if isinstance(multi, str) else [],
            "remaining": remaining, "initial": _filament_profiles._num(spool.get("initial_weight")) or _filament_profiles._num(filament.get("weight")), "location": spool.get("location") or "",
            "low": limit > 0 and isinstance(remaining, (int, float)) and remaining < limit,
            "use_first": first.get(filament.get("id")) == spool.get("id"), "u1_bound": _rfid.u1_bound(spool.get("location"))}


def publish_stock(url: str, spools: list | None, error: str = "", request: int | None = None) -> bool:
    """Write stock.json for u1control, only while it runs and asks for it. Never raises."""
    origin = _spoolman_sync.current_origin()
    wants = u1control_wants()
    if wants is None or _filament_profiles._orca_data_dir() is None or not _peer["session"] or origin[0] != _sources.clean_url(url):
        return False
    live = _core.active_spools(spools or [])
    limit = _core.parse_low(_core.get_settings().get("low_stock_grams"))
    first = _core.use_first_id(live)
    with _peer_lock:
        _peer["seq"] += 1
        seq = _peer["seq"]
    doc = {"schema": STOCK_SCHEMA, "version": STOCK_VERSION, "session": _peer["session"], "seq": seq, "ts": time.time(),
           "origin": {"url": public_url(url), "gen": origin[1], "source": _sources.source()},
           "request": wants["request"] if request is None else request,
           "low_stock_grams": limit, "spools": [stock_row(s, limit, first) for s in live[:STOCK_ROWS]]}
    if error:
        doc["error"] = error[:200]
    try:
        _filament_profiles._write_json(bridge_dir() / STOCK_FILE, doc)
    except OSError as exc:
        _core.log.warning("Could not write %s: %s", STOCK_FILE, exc)
        return False
    _peer["stock_at"] = time.monotonic()
    return True


def refresh_stock(wants: dict) -> None:
    """Read Spoolman (read only: no fields are created) and publish the list for u1control."""
    _peer["served"] = wants["request"]
    with _spoolman_sync.pinned_origin() as origin:
        if origin[0] in ("", _sources.BAMBU_KEY):
            # Not Spoolman: say so, so u1control can explain why there is no stock to show.
            if _filament_profiles._orca_data_dir() is not None and _peer["session"]:
                try:
                    _filament_profiles._write_json(bridge_dir() / STOCK_FILE, {
                        "schema": STOCK_SCHEMA, "version": STOCK_VERSION, "session": _peer["session"], "seq": 0,
                        "ts": time.time(), "origin": {"url": "", "gen": origin[1], "source": _sources.source() if origin[0] else ""},
                        "request": wants["request"], "spools": []})
                except OSError as exc:
                    _core.log.warning("Could not write %s: %s", STOCK_FILE, exc)
            _peer["stock_at"] = time.monotonic()
            return
        result = _core.get_spools(origin[0])   # publishes through its hook when the read succeeds
        if not result.get("ok"):
            publish_stock(origin[0], [], result.get("error") or _i18n.tr("Spoolman could not be read"), wants["request"])


def links_changed() -> None:
    """Spooler wrote a slot link: say so in its presence now, so U1 Control and Kobra Control re-read Spoolman."""
    _peer["links"] = int(time.time() * 1000)
    publish_presence()


def kobra_printer(doc: object) -> dict | None:
    """{"host", "name"} of the printer a running Kobra Control shows, from its presence; else None."""
    printer = doc.get("printer") if peer_alive(doc, KOBRACONTROL) else None
    if not isinstance(printer, dict):
        return None
    host, name = printer.get("host"), " ".join(str(printer.get("name") or "").split())[:56]
    return {"host": host.strip(), "name": name} if isinstance(host, str) and host.strip() and name else None


def watch_peer_links() -> None:
    """Re-read Spoolman when a peer says it changed a link (its presence "links" moved since the last beat)."""
    moved = False
    for plugin in (U1CONTROL, KOBRACONTROL):
        doc = _read_peer(plugin)
        if plugin == KOBRACONTROL:
            _peer["kobra"] = kobra_printer(doc)
        links = doc.get("links") if peer_alive(doc, plugin) else None
        if isinstance(links, (int, float)) and not isinstance(links, bool):
            moved = moved or (plugin in _peer["seen"] and _peer["seen"][plugin] != links)
            _peer["seen"][plugin] = links
    if moved:
        _core._spool_cache["time"] = 0.0
        _live_updates._ws_notify()


def peer_tick() -> None:
    """One heartbeat: say Spooler runs, follow the peers' link changes, and refresh the stock when u1control shows
    it. Never raises."""
    try:
        publish_presence()
        watch_peer_links()
        wants = u1control_wants()
        if wants is None:
            return
        due = time.monotonic() - _peer["stock_at"] >= STOCK_EVERY
        if due or wants["request"] != _peer["served"]:
            refresh_stock(wants)
    except Exception:
        _core.log.exception("Presence for u1control failed")


def start_presence() -> None:
    """Called from each Spooler capability's on_load (OrcaSlicer calls it whether or not the tab is
    enabled); the heartbeat runs until the last of them unloads."""
    with _peer_lock:
        _peer["users"] += 1
        if _peer["thread"] is not None:
            return
        _peer.update(session=os.urandom(8).hex(), started=time.time(), stop=threading.Event(), seq=0,
                     stock_at=0.0, served=None)
        stop = _peer["stop"]

        def beat():
            while not stop.wait(PEER_BEAT):
                peer_tick()
        publish_presence()   # visible from load on, not only after the first beat
        _peer["thread"] = threading.Thread(target=beat, name="spooler-presence", daemon=True)
        _peer["thread"].start()


def stop_presence() -> None:
    with _peer_lock:
        _peer["users"] = max(0, _peer["users"] - 1)
        if _peer["users"] or _peer["thread"] is None:
            return
        thread, stop = _peer["thread"], _peer["stop"]
        _peer.update(thread=None, stop=None)
    stop.set()
    if thread is not threading.current_thread():
        thread.join(2.0)
    publish_presence("stopped")
    _peer["session"] = ""


def location_names(target: str) -> tuple:
    """The printer names a u1control location may start with for this printer: Spooler's label,
    the printer model (the label without the nozzle Spooler adds when two presets share a model)."""
    printer = next((p for p in _filament_profiles._ui_snap.get("printers") or [] if p["target"] == target), {})
    kobra = _peer["kobra"]
    own = kobra["name"] if kobra and target and target_for_host(kobra["host"]) == target else None
    # Last: the name Kobra Control uses for this printer, which Spooler then also writes (slot_bind).
    return tuple(name for name in dict.fromkeys((printer.get("label"), printer.get("model"), own)) if name)


def profile_sync(spools: list[dict], snapshot: dict | None, force: bool = False) -> dict:
    """Write and hot-reload the Spoolman filament presets. Never raises. force (Sync Presets)
    rewrites and reloads them even when nothing changed or a refused set is backing off."""
    if not snapshot:
        return dict(_filament_profiles._profiles)
    with _filament_profiles._profile_lock:
        root = _filament_profiles._orca_data_dir()
        files, by_key = _filament_profiles.profile_files(spools, snapshot)
        digest = _filament_profiles.profile_digest(files)
        failed, when = _filament_profiles._profiles["failed"]
        if not force and digest == failed and time.monotonic() - when < _filament_profiles.PROFILE_RETRY:
            return dict(_filament_profiles._profiles)
        try:
            if root is None:
                raise RuntimeError(_i18n.tr("OrcaSlicer's data folder was not found"))
            _filament_profiles._install_profiles(root, snapshot, files, digest, force)
            pinned = getattr(_spoolman_sync._op, "origin", None)
            if pinned is not None and not _spoolman_sync.origin_live(pinned):
                # Built from a source the settings left: its names must not map ids of the new one,
                # nor reach profiles.json. The next refresh builds them from the new source.
                raise _spoolman_sync.OriginChanged()
            _filament_profiles._profiles.update(names=by_key, count=len(files), error="", failed=("", 0.0),
                             gen=pinned[1] if pinned else None)
            publish_profiles(by_key, snapshot.get("printers") or [], files)
            _core._report("Profile sync", None)
        except Exception as exc:
            _filament_profiles._profiles.update(error=str(exc), failed=(digest, time.monotonic()))
            _core._report("Profile sync", str(exc), exc_info=True)
        return dict(_filament_profiles._profiles)


def load_spools_synced(snapshot: dict | None, force: bool = False) -> dict:
    """The spool list, after syncing the filament profiles from it. For worker threads."""
    with _spoolman_sync.pinned_origin():
        result = _sources.load_spools()
        if result.get("ok") and snapshot:
            state = profile_sync(_core.active_spools(result["spools"]), snapshot, force)
            result["profiles"] = {"count": state["count"], "error": state["error"]}
    return result


def fresh_spools(snapshot: dict | None, force: bool = False) -> dict:
    """load_spools_synced for a page: read again when the source changed while it ran, so a list
    from the old source never reaches a page that now shows the new one."""
    for _ in range(3):
        with _spoolman_sync.pinned_origin() as origin:
            result = load_spools_synced(snapshot, force)
        if _spoolman_sync.origin_live(origin):
            # The page sends it back with card actions and bookings: ids picked from this list
            # are only written while this source is still the one in Settings.
            return {**result, "origin": origin[1]}
    return {"ok": False, "error": _i18n.tr("The spool source kept changing while loading; refresh to try again.")}


def start_preset_sync(post) -> None:
    """Sync Presets: read Spoolman now and rebuild every Spooler filament preset, even when nothing
    changed. Call it on the UI thread; post() gets {"type": "sent", "ok": ..., "text": ...}."""
    if _sources.source() != "spoolman":
        post({"type": "sent", "ok": False, "text": _i18n.tr("Syncing presets needs Spoolman as the source.")})
        return
    _filament_profiles._parent_cache["configs"] = {}  # read every parent's settings again: an updated one is copied anew
    snapshot = _moonraker.refresh_snapshot()
    if snapshot is None:
        post({"type": "sent", "ok": False, "text": _i18n.tr("Could not read OrcaSlicer's presets.")})
        return

    def worker():
        result = fresh_spools(snapshot, force=True)
        state = result.get("profiles") or {}
        if not result.get("ok"):
            ok, text = False, result.get("error") or _i18n.tr("Could not read Spoolman.")
        elif state.get("error"):
            ok, text = False, _i18n.tr("The filament presets were not rebuilt: {error}", error=state["error"])
        else:
            ok, text = True, _i18n.tr("Synced {count} filament presets from Spoolman.", count=state.get("count", 0))
        post({"type": "sent", "ok": ok, "text": text})

    _filament_profiles.spawn(worker)


def target_for_host(host: str) -> str:
    """The system printer preset a printer address belongs to, from the last snapshot."""
    for printer in _filament_profiles._ui_snap.get("printers") or []:
        if host in printer["hosts"]:
            return printer["target"]
    return ""


def profile_for_spool(spool: dict | None, target: str) -> str:
    """The preset name OrcaSlicer knows a spool by on one printer, or ''. With presets per spool,
    only the spool's own: one its Use with leaves out has none there. A spool linked to your own
    preset (orca_filament_preset) has that one on each printer it fits (link_fits)."""
    linked = _filament_profiles.spool_link(spool, target, _filament_profiles._ui_snap)
    if linked:
        return linked
    fid = ((spool or {}).get("filament") or {}).get("id")
    names = _filament_profiles._profiles["names"]
    name = names.get((fid, target, (spool or {}).get("id"))) or names.get((fid, target))
    return _filament_profiles.PROFILE_PREFIX + name if name else ""


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import capabilities as _capabilities  # noqa: E402
from . import core as _core  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
