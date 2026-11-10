# Security

## Reporting a problem

Please report security problems privately, through
[GitHub's private vulnerability reporting](../../security/advisories/new), not in a public issue.
Say what can happen, how to reproduce it, and which Spooler version you used. You'll get an answer
within a week, and a fix is released as soon as it is ready.

## What Spooler can reach

Knowing this helps judge a report:

- **Your Spoolman server**, at the address you enter. Spooler reads spools and filaments, creates
  the extra fields it needs, writes calibrated settings to a filament's `orca_settings` and fields,
  and books filament use. It never changes a spool's location.
- **Your printers on the local network**, found from the host address on your OrcaSlicer printer
  presets: Moonraker over HTTP, Anycubic LAN mode over MQTT/TLS, and Bambu Live Link over MQTT/TLS
  and FTPS with the access code you enter.
- **Bambu Cloud**, only when you pick it as the spool source and sign in. The token is kept in
  `bambu_auth.json` in Spooler's data folder.
- **GitHub**, to check for a newer release.
- **Files**: its presets in OrcaSlicer's user folder, its settings, log and history in
  `<OrcaSlicer data folder>/spooler/`. Printer access codes are kept there, never sent anywhere
  but the printer.

Spooler downloads no code and starts no programs, except your web browser when you open a link. It declares its folder, threads and fixed addresses
to OrcaSlicer when it loads, and OrcaSlicer asks before it reaches anything else.

## Supported versions

Only the latest release gets fixes.
