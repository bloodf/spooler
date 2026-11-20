# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""New RFID spools: Bambu tags no Spoolman spool carries yet, and sending to the printer."""

import ftplib
import math
import re
import socket
import ssl
import tempfile
import time
import urllib.error
import xml.etree.ElementTree as ET
import zipfile

# --- New RFID spools -------------------------------------------------------------------------------
# A Bambu RFID spool in an AMS slot or the external holder whose tag no Spoolman spool carries is
# offered on the Printer tab, built from the printer's own report (nothing is sent to the printer).
# Adding it stores the tag in the spool's "tag" field, the first place match_spool looks.
TAG_FIELD = "tag"
RFID_SKIP = "rfid_skip"  # settings: {printer id: [tag, ...]}, the RFID spools the user chose not to add
RFID_SKIP_MAX = 200


def tray_tag(tray: dict) -> str:
    """The tag Spooler stores for a printer tray: tray_uuid (one per spool, which both its chips
    share), else the chip's tag_uid; "" when the tray reports no RFID spool."""
    for key in ("tray_uuid", "tag_uid"):
        found = _netprinters._tag_ids(tray.get(key))
        if found:
            return min(found)
    return ""


def _report_num(value: object, low: float, high: float) -> float | None:
    """A number from a printer report (Bambu sends most as text), inside (low, high]; else None."""
    if isinstance(value, bool):
        return None
    try:
        number = float(value) if isinstance(value, (int, float, str)) else None
    except ValueError:
        return None
    return number if number is not None and math.isfinite(number) and low < number <= high else None


def rfid_offer(tray: object, known: set) -> dict | None:
    """What the page offers to add for one Bambu tray, or None: an empty or non-RFID tray, a tray
    that names its spool itself, or a tag a Spoolman spool already carries."""
    # tray_uuid and tray_info_idx come only from Bambu reports; other printers' trays carry neither.
    if not isinstance(tray, dict) or not ("tray_uuid" in tray or "tray_info_idx" in tray):
        return None
    kind, tag = str(tray.get("tray_type") or "").strip(), tray_tag(tray)
    if not kind or not tag or tray.get("spool_id") not in (None, ""):
        return None
    if _netprinters._tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")]) & known:
        return None
    cols = [c for c in (_sources._hex6(x) for x in tray.get("cols") or [] if isinstance(x, str)) if c] if isinstance(tray.get("cols"), list) else []
    colour = _sources._hex6(tray.get("tray_color"))
    remain = _report_num(tray.get("remain"), -1, 100)
    low, high = _report_num(tray.get("nozzle_temp_min"), 0, 600), _report_num(tray.get("nozzle_temp_max"), 0, 600)
    return {"tag": tag, "type": kind, "name": str(tray.get("tray_sub_brands") or kind).strip()[:64],
            "colours": cols if len(cols) > 1 else [colour] if colour else [],
            "remain": remain, "weight": _report_num(tray.get("tray_weight"), 0, _editor.MAX_GRAMS),
            "diameter": _report_num(tray.get("tray_diameter"), 0, 10),
            "nozzle": [int(low), int(high)] if low and high and low <= high else None}


def _rfid_skipped(settings: dict | None = None) -> dict:
    raw = (settings or _core.get_settings()).get(RFID_SKIP)
    if not isinstance(raw, dict):
        return {}
    return {str(pid): [t for t in tags if isinstance(t, str)] for pid, tags in raw.items() if isinstance(tags, list)}


def rfid_skipped_count() -> int:
    return sum(len(tags) for tags in _rfid_skipped().values())


def rfid_skip(pid: object, tag: object) -> bool:
    """Stop offering this RFID spool in this printer. The newest RFID_SKIP_MAX tags per printer are kept."""
    tags = _netprinters._tag_ids(tag) if isinstance(tag, str) else set()
    if not isinstance(pid, str) or not pid or len(pid) > 64 or len(tags) != 1:
        return False
    def add(settings: dict) -> dict:
        skipped = _rfid_skipped(settings)
        kept = [t for t in skipped.get(pid, []) if t not in tags] + sorted(tags)
        return {RFID_SKIP: {**skipped, pid: kept[-RFID_SKIP_MAX:]}}
    _core.log.info("RFID spool %s in printer %s skipped", min(tags), pid)
    return _core.update_settings(add)


def rfid_unskip() -> bool:
    """Offer every skipped RFID spool again (Settings)."""
    return _core.update_settings({RFID_SKIP: {}})


def _live_trays(state: dict) -> list[tuple]:
    """(unit, slot, tray) for every slot a printer reports: AMS and toolhead slots, then the
    external holder. Holds _live_lock."""
    trays = [(unit, slot, tray) for unit, slots in sorted(state["units"].items()) for slot, tray in sorted(slots.items())]
    return trays + ([("ext", 0, state["ext"])] if state["ext"] else [])


def _all_tags(spools: list) -> set:
    return set().union(*(_netprinters.spool_tags(s) for s in spools if isinstance(s, dict)))


ARCHIVED_SECS = 300
_archived_tags: dict = {"url": "", "time": 0.0, "tags": set()}  # archived spools' tags, per Spoolman address


def _archived(url: str) -> set:
    """The tags of a Spoolman's archived spools, read again after ARCHIVED_SECS or a card action.
    Raises when Spoolman can't be read."""
    if _archived_tags["url"] != url or time.monotonic() - _archived_tags["time"] >= ARCHIVED_SECS:
        spools = _sources._spoolman_open(url, "spool?allow_archived=true") or []
        tags = _all_tags([s for s in spools if isinstance(s, dict) and s.get("archived")])
        _archived_tags.update(url=url, time=time.monotonic(), tags=tags)
    return _archived_tags["tags"]


def rfid_known(url: str, data: list, with_archived: bool) -> dict:
    """For the spool cache, read with each spool list: every tag Spoolman holds, archived spools
    included (an archived spool still in the AMS is no new spool), and the tray tags checked against
    them. Archived spools are read (and kept ARCHIVED_SECS) only when the list left them out and a
    tray carries a tag no active spool has and that wasn't skipped. Called off the UI thread."""
    known = _all_tags(data if with_archived else _core.active_spools(data))
    skipped = _rfid_skipped()
    with _live_updates._live_lock:
        trays = [(pid, tray) for pid, state in _live_updates._live["printers"].items() for _u, _s, tray in _live_trays(state)]
    wanted = set()
    for pid, tray in trays:
        offer = rfid_offer(tray, known)
        if offer and not _netprinters._tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")]) & set(skipped.get(pid, [])):
            wanted.add(offer["tag"])
    if wanted and not with_archived:
        try:
            known |= _archived(url)
        except Exception as exc:
            _core._report("Archived spool tags", str(exc))
            return {"rfid_known": known, "rfid_checked": set()}  # unsure: offer nothing until the next read
        _core._report("Archived spool tags", None)
    return {"rfid_known": known, "rfid_checked": wanted}


def rfid_offers() -> list[dict]:
    """The new RFID spools in the printers Spooler reads, for the Printer tab. Only tags checked
    against the spool list of the Spoolman in Settings (archived spools included), read after the
    last write, so a spool just added, or archived, is never offered. A spool put in the AMS shows
    with the next list read (every REFRESH_SECS while the page is open)."""
    url = _spoolman_sync.current_origin()[0]
    if _sources.source() != "spoolman" or not url or _core._spool_cache["url"] != url or not _core._spool_cache["time"]:
        return []
    known, checked = _core._spool_cache.get("rfid_known") or set(), _core._spool_cache.get("rfid_checked") or set()
    skipped, out, seen = _rfid_skipped(), [], set()
    with _live_updates._live_lock:
        for pid, state in _live_updates._live["printers"].items():
            for unit, slot, tray in _live_trays(state):
                offer = rfid_offer(tray, known)
                # Skipped by either id: a report may carry only tag_uid at first, then tray_uuid too.
                ids = _netprinters._tag_ids([tray.get("tag_uid"), tray.get("tray_uuid")])
                if offer and offer["tag"] in checked and offer["tag"] not in seen and not ids & set(skipped.get(pid, [])):
                    seen.add(offer["tag"])
                    out.append({**offer, "printer": pid, "unit": unit, "slot": slot})
    return out


def _loaded(state: dict) -> list[dict]:
    """Trays in slicer slot order, each with its printer tray number as key."""
    trays = []
    for unit_id in sorted(state["units"], key=lambda u: (u >= 128, u)):
        slots = state["units"][unit_id]
        trays += [dict(slots.get(i, {}), key=unit_id if unit_id >= 128 else unit_id * 4 + i)
                  for i in range(1 if unit_id >= 128 else 4)]
    if state["ext"]:
        trays.append(dict(state["ext"], key=254, spare=bool(trays)))
    return trays


def _note_tray(dev_id: str, state: dict) -> list[tuple]:
    """Remember each tray that feeds the running print. Holds _live_lock."""
    run, p = state.get("run"), state.get("prog") or {}
    t = _live_updates.tray_key(p)
    if not run or not 0 <= t <= 254 or str(p.get("gcode_state") or "").upper() != "RUNNING":
        return []
    if _live_updates._int(p.get("layer_num"), 0) < 1 or t in run.setdefault("used", []):
        return []
    run["used"].append(t)
    if t not in [tr.get("key") for tr in run["trays"]]:
        run["trays"] = _loaded(state)
    _core.log.info("Print is using printer tray %d", t)
    return [("save", dev_id, dict(run))]


def _fits(item: dict, tray: dict) -> bool:
    if not _plate_check._same_mat(item.get("material"), tray.get("tray_type")):
        return False
    gap = _plate_check.colour_diff(item.get("colour") or "", _sources._hex6(tray.get("tray_color")))
    return gap is None or gap <= _core.COLOUR_TOLERANCE


def run_tray(run: dict, item: dict, count: int) -> dict | None:
    """The tray a filament slot printed from: the trays seen feeding the print come first."""
    trays = run.get("trays") or []
    keyed = {tr["key"]: tr for tr in trays if "key" in tr}
    used = [keyed[k] for k in run.get("used") or [] if k in keyed]
    if count == 1 and len(used) == 1:
        return used[0]
    slots = [tr for tr in trays if not tr.get("spare")]
    pos = slots[item["n"] - 1] if 0 < item["n"] <= len(slots) else None
    pool = used or trays
    fit = [tr for tr in pool if _fits(item, tr)]
    if len(fit) == 1:
        return fit[0]
    if pos is not None and (not used or pos in used) and (not fit or pos in fit):
        return pos
    return None


JOB_KEYS = ("task_id", "subtask_id", "gcode_start_time")
USAGE_DONE = 40
LIVE_STATES = ("PREPARE", "RUNNING", "PAUSE")


def job_ident(job: dict) -> dict:
    out = {k: str(job.get(k) or "") for k in JOB_KEYS}
    out.update(name=str(job.get("subtask_name") or ""), file=str(job.get("gcode_file") or ""))
    return out


def same_job(a: dict | None, b: dict | None) -> bool:
    """Same print, judged by name and file plus whichever ids both sides know."""
    if not a or not b or (a.get("name"), a.get("file")) != (b.get("name"), b.get("file")):
        return False
    known = [k for k in JOB_KEYS if a.get(k) not in ("", "0") and b.get(k) not in ("", "0")]
    return all(a[k] == b[k] for k in known)


def _ended(run: dict, printer: str, result: str, pct: int) -> dict:
    return {**run, "printer": printer, "result": result, "pct": 100 if result == "finished" else pct}


def usage_track(dev_id: str, state: dict, has_state: bool) -> list[tuple]:
    """Track a printer through a print; returns events to handle outside the lock. Holds _live_lock.

    The run is saved to disk while it lasts, so a dropped link or a restart picks it up again.
    """
    # Printers found from a preset's host address ("auto-..." ids) are booked only when nothing else
    # does it: the Snapmaker U1's toolheads are booked by u1control, a Moonraker with its Spoolman
    # integration connected books its own use, and Anycubic printers have no job file to read. _moon_run
    # sets book_ok for a Klipper printer that is none of these; anything else would count twice.
    if str(dev_id).startswith("auto-") and not state.get("book_ok"):
        return []
    job = state.get("job") or {}
    gcode = job.get("gcode_state")
    if not gcode or _sources.source() != "spoolman" or not state.get("link") or _netprinters.usage_mode() == "off":
        return []
    events: list[tuple] = []
    if not state.get("loaded"):
        state["loaded"] = True
        state["fresh"] = True
        with _netprinters._usage_lock:
            store = _netprinters.usage_load()
        state["run"] = store["active"].get(dev_id)
        state["last"] = store["last"].get(dev_id)
        if state["run"] and not state["run"].get("file"):
            events.append(("fetch", dev_id, state["run"]))
    fresh = has_state and state.pop("fresh", False)
    pct = max(0, min(100, _live_updates._int(job.get("mc_percent"), 0)))
    ident = job_ident(job)
    run = state.get("run")
    if fresh and run and not same_job(run["job"], ident):
        # The tracked print ended while the link was down and another one has run since.
        events.append(("end", dev_id, _ended(run, state["name"], "unknown", run["pct"])))
        state["run"] = run = None
    if run is None:
        if fresh and gcode in ("FINISH", "FAILED") and state.get("last") and not same_job(state["last"], ident):
            events.append(("missed", dev_id, {"job": ident, "printer": state["name"],
                                              "result": "finished" if gcode == "FINISH" else "cancelled",
                                              "pct": pct, "link": state["link"]}))
        if gcode in ("IDLE", "FINISH", "FAILED"):
            state["idle_seen"] = True
        elif gcode in ("PREPARE", "RUNNING") and (state.get("idle_seen") or pct <= 2 or fresh):
            new = state.get("idle_seen") or pct <= 2
            plan = _netprinters._usage["plan"]["slots"] if new and _netprinters._usage["plan"] else None
            state["run"] = {"id": f"{dev_id}-{int(time.time())}", "plan": plan, "file": None, "job": ident,
                            "name": str(job.get("subtask_name") or job.get("gcode_file") or "Print")[:80],
                            "trays": _loaded(state), "pct": pct, "late": not new,
                            "ask": _link_kind(dev_id) in _printers.ASK_ONLY}
            state["idle_seen"] = False
            events.append(("start", dev_id, dict(state["run"])))
        if not same_job(state.get("last"), ident) and (ident["name"] or ident["file"]):
            state["last"] = ident
            events.append(("last", dev_id, ident))
        return events
    if gcode in LIVE_STATES:
        step = pct // 5 != run["pct"] // 5 or run["job"] != ident
        run["pct"] = max(run["pct"], pct)
        run["job"] = ident
        if step:
            events.append(("save", dev_id, dict(run)))
        return events
    if gcode not in ("FINISH", "FAILED", "IDLE"):
        return events
    state["run"] = None
    state["idle_seen"] = True
    state["last"] = ident if ident["name"] or ident["file"] else state.get("last")
    result = "finished" if gcode == "FINISH" else "cancelled"
    events.append(("end", dev_id, _ended(run, state["name"], result, max(run["pct"], pct))))
    return events


FTP_PORT = 990
JOB_DIRS = ("/", "/cache", "/model", "/sdcard", "/sdcard/cache", "/sdcard/model")
JOB_MAX = 1024 * 1024 * 1024
JOB_TRIES = 6
JOB_RETRY = 30.0


class _Ftps(ftplib.FTP_TLS):
    """Implicit FTPS; data connections reuse the control TLS session, which Bambu printers require."""

    def connect(self, host="", port=0, timeout=-999, source_address=None):
        self.host, self.port, self.timeout = host, port, timeout
        raw = socket.create_connection((host, port), timeout=timeout)
        self.af = raw.family
        self.sock = self.context.wrap_socket(raw, server_hostname=host)
        self.file = self.sock.makefile("r", encoding=self.encoding)
        self.welcome = self.getresp()
        return self.welcome

    def ntransfercmd(self, cmd, rest=None):
        conn, size = ftplib.FTP.ntransfercmd(self, cmd, rest)
        if self._prot_p:
            conn = self.context.wrap_socket(conn, server_hostname=self.host, session=self.sock.session)
        return conn, size

    def pull(self, cmd: str, out, limit: int) -> None:
        # No TLS unwrap after the transfer: some printers never answer it.
        self.voidcmd("TYPE I")
        got = 0
        with self.transfercmd(cmd) as conn:
            while chunk := conn.recv(65536):
                got += len(chunk)
                if got > limit:
                    raise ValueError("The job file is too large")
                out.write(chunk)
        self.voidresp()


def _ftp_open(link: dict) -> _Ftps:
    context = ssl.create_default_context()
    context.check_hostname = False
    context.verify_mode = ssl.CERT_NONE
    ftp = _Ftps(context=context, timeout=15)
    ftp.connect(link["ip"], FTP_PORT, 15)
    ftp.login("bblp", link["code"])
    ftp.prot_p()
    return ftp


def job_names(job: dict) -> list[str]:
    file, name = job.get("file") or "", job.get("name") or ""
    names = [file.rsplit("/", 1)[-1]] if file.lower().endswith(".3mf") else []
    names += [f"{name}.gcode.3mf", f"{name}.3mf"] if name else []
    return [n.lower() for n in names if n.strip(".")]


def _find_job(ftp: _Ftps, job: dict) -> str | None:
    wanted = job_names(job)
    if not wanted:
        return None
    for folder in JOB_DIRS:
        out = tempfile.SpooledTemporaryFile()
        try:
            ftp.pull(f"NLST {folder}", out, 4 * 1024 * 1024)
        except (ftplib.Error, OSError, ValueError):
            continue
        out.seek(0)
        found = {line.rsplit("/", 1)[-1].lower(): line.rsplit("/", 1)[-1]
                 for line in out.read().decode("utf-8", "replace").splitlines() if line.strip()}
        for name in wanted:
            if name in found:
                return folder.rstrip("/") + "/" + found[name]
        jobs = sorted(n for n in found.values() if n.lower().endswith(".3mf"))
        if jobs:
            _core.log.info("Job files in %s: %s", folder, ", ".join(jobs[:20]))
    return None


def parse_slice(data: bytes, file: str = "") -> list[dict] | None:
    """Grams per filament slot for the printed plate, from Metadata/slice_info.config."""
    plates = []
    for plate in ET.fromstring(data).iter("plate"):
        meta = {m.get("key"): m.get("value") for m in plate.findall("metadata")}
        rows = []
        for item in plate.findall("filament"):
            try:
                grams = float(item.get("used_g") or 0)
            except ValueError:
                grams = 0.0
            n = _live_updates._int(item.get("id"), 0)
            if n > 0 and grams > 0:
                rows.append({"n": n, "grams": round(grams, 2), "preset": str(item.get("tray_info_idx") or ""),
                             "colour": _sources._hex6(item.get("color")), "material": str(item.get("type") or "")})
        if rows:
            plates.append((_live_updates._int(meta.get("index"), 0), rows))
    hint = re.search(r"plate_(\d+)", file)
    if hint:
        match = [rows for index, rows in plates if index == int(hint.group(1))]
        if match:
            return match[0]
    return plates[0][1] if len(plates) == 1 else None


WASTE_SUPPORT = ("support",)
WASTE_PURGE = ("prime tower", "wipe tower", "flush", "purge")


def parse_waste(lines) -> dict[int, tuple[float, float]]:
    """Support and purge share of each filament (1-based), from the plate G-code.

    A flush is only the bare "; FLUSH_START" / "; FLUSH_END" comment line. The same words also appear
    inside the printer's custom G-code templates that OrcaSlicer copies into the settings block
    (CONFIG_BLOCK, at the top or the end of the file); read as markers, they left the flush open and
    counted a whole single-colour print as purge. The settings block is skipped entirely."""
    tool, kind, flush, rel, last, config = 0, "model", False, False, 0.0, False
    sums: dict[int, list[float]] = {}
    for raw in lines:
        line = raw.decode("utf-8", "replace") if isinstance(raw, bytes) else raw
        if line.startswith(";"):
            low = line.lower()
            marker = low[1:].strip()
            if marker == "config_block_start":
                config = True
            elif marker == "config_block_end":
                config = False
            elif config:
                pass
            elif low.startswith((";type:", "; feature:")):
                name = low.split(":", 1)[1].strip()
                kind = ("support" if any(w in name for w in WASTE_SUPPORT)
                        else "purge" if any(w in name for w in WASTE_PURGE) else "model")
            elif marker == "flush_start":
                flush = True
            elif marker == "flush_end":
                flush = False
            continue
        if config:
            continue
        cmd = line.split(";", 1)[0].strip()
        if not cmd:
            continue
        head = cmd.split(None, 1)[0].upper()
        if head == "M83":
            rel = True
        elif head == "M82":
            rel = False
        elif re.fullmatch(r"T\d+", head) and int(head[1:]) < 255:
            tool = int(head[1:])
        elif head in ("G1", "G0", "G2", "G3", "G92"):
            m = re.search(r"\bE(-?\d*\.?\d+)", cmd, re.I)
            if not m:
                continue
            e = float(m.group(1))
            if head == "G92":
                last = e
                continue
            d = e if rel else e - last
            last = last if rel else e
            if d > 0:
                k = "purge" if flush else kind
                acc = sums.setdefault(tool + 1, [0.0, 0.0, 0.0])
                acc[(k == "support") + 2 * (k == "purge")] += d
    out = {}
    for n, (model, sup, pur) in sums.items():
        total = model + sup + pur
        if total > 0:
            out[n] = (round(sup / total, 4), round(pur / total, 4))
    return out


def _plate_gcode(box: zipfile.ZipFile, file: str) -> str | None:
    names = [n for n in box.namelist() if re.fullmatch(r"Metadata/plate_\d+\.gcode", n)]
    hint = re.search(r"plate_(\d+)", file)
    if hint and f"Metadata/plate_{hint.group(1)}.gcode" in names:
        return f"Metadata/plate_{hint.group(1)}.gcode"
    return names[0] if len(names) == 1 else None


def add_waste(items: list[dict], box: zipfile.ZipFile, file: str) -> None:
    name = _plate_gcode(box, file)
    if not name:
        return
    try:
        with box.open(name) as fh:
            waste = parse_waste(fh)
    except (OSError, ValueError, zipfile.BadZipFile) as exc:
        _core.log.info("Could not read waste from the job G-code: %s", exc)
        return
    for item in items:
        if item["n"] in waste:
            item["ws"], item["wp"] = waste[item["n"]]
    _core.log.info("Waste from %s: %s", name, {n: waste[n] for n in sorted(waste)})


def fetch_job(link: dict, job: dict) -> list[dict] | None:
    """Download the printing job's file over FTPS and read its filament use."""
    ftp = _ftp_open(link)
    try:
        path = _find_job(ftp, job)
        if not path:
            _core.log.info("The job file wasn't found on the printer (looked for %s in %s)",
                     ", ".join(job_names(job)) or "nothing", ", ".join(JOB_DIRS))
            return None
        _core.log.info("Found the job file at %s", path)
        with tempfile.TemporaryFile() as out:
            ftp.pull(f"RETR {path}", out, JOB_MAX)
            out.seek(0)
            with zipfile.ZipFile(out) as box:
                info = box.getinfo("Metadata/slice_info.config")
                if info.file_size > 4 * 1024 * 1024:
                    return None
                items = parse_slice(box.read(info), job.get("file") or "")
                if items:
                    add_waste(items, box, job.get("file") or "")
    finally:
        try:
            ftp.quit()
        except (ftplib.Error, OSError):
            ftp.close()
    return items


def _link_kind(dev_id: str) -> str:
    """'bambu', 'moonraker', 'prusalink' or 'octoprint' for a live printer id."""
    link = (_live_updates._local.get(dev_id) or {}).get("link") or {}
    return link.get("kind") or ("moonraker" if str(dev_id).startswith("auto-") else "bambu")


def _try_fetch(dev_id: str, job: dict) -> list[dict] | None:
    link = (_live_updates._local.get(dev_id) or {}).get("link")
    if not link:
        return None
    try:
        if link.get("kind") in _printers.NET_KINDS:
            return _netprinters.net_fetch_job(link, job, dev_id)
        if link.get("kind") == "moonraker":
            return _netprinters.moon_fetch_job(link, job)
        return fetch_job(link, job)
    except (ftplib.Error, OSError, ValueError, KeyError, zipfile.BadZipFile, ET.ParseError) as exc:
        _core.log.warning("Could not read the job file from a printer: %s", exc)
        return None


def _store(change) -> None:
    with _netprinters._usage_lock:
        data = _netprinters.usage_load()
        change(data)
        try:
            _netprinters.usage_save(data)
        except OSError:
            _core.log.exception("Could not write %s", _netprinters.USAGE_FILE)


def _job_fetch(dev_id: str, run_id: str) -> None:
    """Fetch the job file while the print runs, retrying through link drops."""
    for _ in range(JOB_TRIES):
        with _live_updates._live_lock:
            run = (_live_updates._live["printers"].get(dev_id) or {}).get("run")
            job = dict(run["job"]) if run and run["id"] == run_id else None
        if job is None:
            return
        items = _try_fetch(dev_id, job)
        if items:
            with _live_updates._live_lock:
                run = (_live_updates._live["printers"].get(dev_id) or {}).get("run")
                if run and run["id"] == run_id:
                    run["file"] = items
                    saved = dict(run)
                else:
                    saved = None
            if saved:
                _store(lambda d: d["active"].__setitem__(dev_id, saved))
            _core.log.info("Read the job file: %d slots", len(items))
            return
        time.sleep(JOB_RETRY)


def _missed(dev_id: str, info: dict) -> None:
    ident = info["job"]
    run_id = f"{dev_id}-" + re.sub(r"[^A-Za-z0-9]", "", "-".join(ident.values()))[:60]
    with _netprinters._usage_lock:
        if run_id in _netprinters.usage_load()["done"]:
            return
    items = _try_fetch(dev_id, ident)
    if not items:
        _core.log.info("A print ended while Spooler was away and its job file couldn't be read")
        return
    with _live_updates._live_lock:
        state = _live_updates._live["printers"].get(dev_id)
        trays = _loaded(state) if state else []
    run = {"id": run_id, "plan": None, "file": items, "job": ident, "trays": trays, "late": True,
           "name": (ident["name"] or ident["file"] or "Print")[:80], "pct": info["pct"]}
    usage_finish(_ended(run, info["printer"], info["result"], info["pct"]), dev_id)


def _end(dev_id: str, run: dict) -> None:
    # Finish first: if Orca closes in between, the saved run is picked up and finished again.
    usage_finish(run, dev_id)

    def drop(d):
        if (d["active"].get(dev_id) or {}).get("id") == run["id"]:
            d["active"].pop(dev_id)
        if run["result"] != "unknown":
            d["last"][dev_id] = run["job"]
    _store(drop)


def usage_event(kind: str, dev_id: str, data: dict) -> None:
    if kind in ("start", "save"):
        _store(lambda d: d["active"].__setitem__(dev_id, data))
    if kind in ("start", "fetch"):
        _filament_profiles.spawn(_job_fetch, dev_id, data["id"])
    elif kind == "last":
        _store(lambda d: d["last"].__setitem__(dev_id, data))
    elif kind == "end":
        _filament_profiles.spawn(_end, dev_id, data)
    elif kind == "missed":
        _filament_profiles.spawn(_missed, dev_id, data)


def _spool_label(spool: dict) -> str:
    filament = spool.get("filament") or {}
    vendor = (filament.get("vendor") or {}).get("name") or ""
    return " ".join(part for part in (vendor, filament.get("name") or _i18n.tr("Spool {id}", id=spool.get("id"))) if part)


def usage_finish(run: dict, dev_id: str = "") -> None:
    """Work out each slot's spool and grams, then ask or book. Each run is booked once."""
    with _netprinters._usage_lock:
        if run["id"] in _netprinters.usage_load()["done"]:
            return
    items = run.get("file") or (_try_fetch(dev_id, run["job"]) if dev_id and run.get("job") else None)
    src = "file" if items else "slice"
    items = items or run.get("plan")
    if not items:
        _core.log.info("A print ended but its filament use is unknown")
        return
    url = _spoolman_sync.current_origin()[0]
    spools = (_plate_check.plate_spools(url) if url and url != _sources.BAMBU_KEY else None) or []
    by_id = {sp.get("id"): sp for sp in spools}
    share = run["pct"] / 100 if run["result"] == "cancelled" else 1.0
    rows = []
    for item in items:
        tray = run_tray(run, item, len(items))
        spool = _netprinters.match_spool(tray, spools)
        grams = round(item["grams"] * share, 1)
        if grams <= 0:
            continue
        rows.append({"slot": item["n"], "grams": grams, "preset": item["preset"], "material": item["material"],
                     "colour": item["colour"], "spool": spool["id"] if spool else None,
                     "how": "rfid" if spool else "", "label": _spool_label(by_id[spool["id"]]) if spool else "",
                     "state": "open", "error": "", **{k: item[k] for k in ("ws", "wp") if k in item}})
    late = bool(run.get("late")) or run["result"] == "unknown"
    entry = {"id": run["id"], "printer": run["printer"], "name": run["name"], "result": run["result"],
             "pct": run["pct"], "time": time.time(), "rows": rows, "late": late, "src": src, "state": "pending",
             "origin": url}  # the Spoolman these spool ids belong to; it is only booked there
    with _netprinters._usage_lock:
        data = _netprinters.usage_load()
        if run["id"] in data["done"]:
            return
        data["done"] = [run["id"]] + data["done"][:USAGE_DONE - 1]
        if rows:
            data["prints"] = ([entry] + [e for e in data["prints"] if e.get("id") != entry["id"]])[:_netprinters.USAGE_PRINTS]
        try:
            _netprinters.usage_save(data)
        except OSError:
            _core.log.exception("Could not write %s; the print is not booked", _netprinters.USAGE_FILE)
            return
    if not rows:
        return
    _core.log.info("A print ended (%s, %d%%, grams from the %s): %d slots to book", run["result"], run["pct"],
             "job file" if src == "file" else "last slice", len(rows))
    ask_only = bool(run.get("ask")) or (bool(dev_id) and _link_kind(dev_id) in _printers.ASK_ONLY)
    if _netprinters.usage_mode() == "auto" and run["result"] == "finished" and not late and not ask_only:
        notice = _editor.usage_book(entry["id"], None)
        if notice:
            _core.log.warning("Booking %s: %s", entry["id"], notice)


def spoolman_use(spool_id: int, grams: float) -> None:
    _spoolman_sync.spoolman_call("PUT", f"spool/{int(spool_id)}/use", {"use_weight": round(grams, 1)})
    _core._spool_cache["time"] = 0.0


def spoolman_unuse(spool_id: int, grams: float) -> None:
    """Add grams back in one step on Spoolman's side (used_weight + -grams, clamped at 0), so use
    booked meanwhile by anything else isn't lost. Only for SPOOLMAN_ATOMIC_USE and newer."""
    _spoolman_sync.spoolman_call("PUT", f"spool/{int(spool_id)}/use", {"use_weight": -round(grams, 1)})
    _core._spool_cache["time"] = 0.0


def maybe_applied(exc: Exception) -> bool:
    """Whether a failed Spoolman write may still have been applied: a timeout or dropped
    connection after sending, or a server error. A refusal (4xx), a refused connection, an
    unknown host or a check before sending means it certainly wasn't."""
    if isinstance(exc, _spoolman_sync.NotSent):
        return False
    if isinstance(exc, urllib.error.HTTPError):
        return exc.code >= 500
    if isinstance(exc, urllib.error.URLError):
        return not isinstance(exc.reason, (ConnectionRefusedError, socket.gaierror))
    return True


def _spoolman_error(exc: Exception) -> str:
    if isinstance(exc, urllib.error.HTTPError):
        return _i18n.tr("Spoolman refused it (HTTP {code})", code=exc.code)
    if isinstance(exc, urllib.error.URLError):
        return _i18n.tr("Could not reach Spoolman ({reason})", reason=exc.reason)
    return str(exc)


def u1_bound(location: object) -> bool:
    """Whether a Spoolman location is a u1control toolhead binding ("<printer name> T<n>")."""
    found = re.search(r"\st(\d+)\s*$", str(location or ""), re.I)
    if not found:
        return False
    names = tuple(n for p in _filament_profiles._ui_snap.get("printers") or [] for n in _peers.location_names(p["target"]))
    return _moonraker._bound_here(location, names, int(found.group(1))) > 0


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import core as _core  # noqa: E402
from . import editor as _editor  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import printers as _printers  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
