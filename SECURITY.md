# Security

## Reporting a problem

Please report security problems privately, through
[GitHub's private vulnerability reporting](../../security/advisories/new), not in a public issue.
Say what can happen, how to reproduce it, and which Spooler version you used. You'll get an answer
within a week, and a fix is released as soon as it is ready.

## What Spooler can reach

Knowing this helps judge a report:

- **Your Spoolman server**, at the address you enter. Spooler reads spools, filaments, locations
  and the server version. It writes:
  - by itself, each time it reads the spool list: the extra fields it needs, if missing (the
    calibration fields on the filament form, `orca_settings` when a setting is first sent, and
    `dried` on the spool form). It never deletes a field.
  - when a Spooler preset is sent (Send to Spoolman, the automatic send of preset edits, or Save
    on a Spooler preset; the last two can be turned off): the filament's `orca_settings` field and
    its density, diameter and price. On Spoolman 0.26 or newer only `orca_settings` is sent in the
    extra map; on older versions the whole map goes back as just read.
  - when you act on a spool card: the scale weight, used grams, archive state, location (Move),
    the `dried` date, and a new spool of the same filament (Add). On Spoolman 0.26 or newer the
    `dried` date is sent alone; on older versions, which replace the whole extra map, the spool's
    extra fields are read again and sent back with only `dried` changed, and when Spooler can't read
    the version or those fields it writes nothing.
  - when a Bambu Live Link print is booked: the used grams, and the same grams back on Undo
    (Spoolman 0.18 or newer only). Prints on the Snapmaker U1 and other Klipper printers are never
    booked by Spooler.
  Each write goes to the Spoolman the operation started with; if the address or source changes
  meanwhile, Spooler stops before writing more.
- **Your printers on the local network**, found from the host address on your OrcaSlicer printer
  presets: Moonraker over HTTP, Anycubic LAN mode over MQTT/TLS, and Bambu Live Link over MQTT/TLS
  and FTPS with the access code you enter. Spooler reads them and asks them for status reports.
  The one setting it changes is Moonraker's active spool, when you use Change Spool or Clear on a
  single-extruder Klipper printer. The TLS links to Bambu and Anycubic printers don't verify the
  printer's certificate (the printers use self-signed ones), so they trust your local network.
- **Bambu Cloud**, only when you pick it as the spool source and sign in. The token is kept in
  `bambu_auth.json` in Spooler's data folder.
- **GitHub**, to check for a newer release.
- **Files**: its presets in OrcaSlicer's user folder, its settings, log and history in
  `<OrcaSlicer data folder>/spooler/`. There it also keeps `presence.json` (that Spooler runs, its
  version and Spoolman address without credentials) and, only while u1control's tab asks for it,
  `stock.json` (the live spool list); it reads `<OrcaSlicer data folder>/u1control/presence.json`.
  Every plugin can read that folder. Printer access codes are kept there, never sent anywhere
  but the printer. The log never holds what the pages send (passwords, codes); addresses have
  any `user:password@` removed and secret-looking values masked, so it can be attached to a
  bug report.

Spooler downloads no code and starts no programs, except your web browser when you open a link. It declares its folder, threads and fixed addresses
to OrcaSlicer when it loads, and OrcaSlicer asks before it reaches anything else.

## Supported versions

Only the latest release gets fixes.
