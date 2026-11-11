# Booking Anycubic Kobra prints

Spooler reads an Anycubic printer's multi-colour box (ACE) and external spool, but it does not yet
book the filament a Kobra print uses to Spoolman. Anycubic hasn't documented how the printer
reports a print in progress over LAN mode, so the messages have to be captured from one real print
first. This page says how to make that capture, and what will be built from it.

## Phase 1: capture (available now)

1. Close OrcaSlicer.
2. Open Spooler's settings file, `spooler_settings.json` in Spooler's data folder:
   - Windows: `%APPDATA%\OrcaSlicer\spooler\`
   - macOS: `~/Library/Application Support/OrcaSlicer/spooler/`
   - Linux: `~/.config/OrcaSlicer/spooler/`
3. Add `"kx_capture": true` next to the other keys, for example:

   ```json
   {
     "spoolman_url": "http://spoolman.local:7912",
     "kx_capture": true
   }
   ```

4. Start OrcaSlicer, open the Spooler tab and its ***Printer*** tab, and leave it open.
5. Run one print on the Kobra from start to finish (a small one is fine). Leave the Printer tab
   open while it runs.
6. Open `spooler.log` in the same folder and copy every line containing `Kobra capture:`. Send
   them in a GitHub issue.
7. Remove `"kx_capture": true` again.

What the capture does: each time the Printer tab connects to the Kobra, Spooler logs every kind of
message the printer sends **once**: its type, its keys and one sample. In the sample, anything that
looks like a serial number, device id, token, password, key, URL, host or IP address is replaced
with `<redacted>`, `<ip>` or `<id>`, so the lines are safe to share. Spooler also asks the printer
for its `info` report every 20 seconds while capturing. That is a read-only status query, as used
by other LAN-mode tools ([runsodin](https://github.com/HughKantsime/runsodin)); it changes nothing
on the printer. With the flag off, Spooler logs nothing extra and sends no extra requests.

## Phase 2: booking (after a capture)

Usage booking (`usage_track`) already works for Bambu printers from their `gcode_state` and
`mc_percent` fields. The plan for Anycubic printers:

1. From the capture, find the message that carries the print state (printing, paused, finished,
   cancelled) and the progress, and map it to the same `gcode_state` / `mc_percent` report the
   Bambu path uses, so `usage_track` works unchanged.
2. Lift the `auto-` gate in `usage_track` for Anycubic printers only. Moonraker printers and the
   Snapmaker U1 keep the gate, because Moonraker's Spoolman integration and u1control already book
   their filament; lifting it there would count every print twice.
3. Grams come from the slice plan (`usage_plan`) times progress. There is no job file to read
   from the printer, so a print sliced on another computer can't be booked.

If the printer turns out not to publish print progress at all, booking for Anycubic printers is
dropped and this page will say so.
