# Changelog

Spooler is a fork of [Spoolio](https://github.com/danm1989/spoolio-orcaslicer); entries before
0.9.0 are Spoolio's.

## [0.9.2] - Unreleased

### Added
- Calibrated settings per filament: a Spoolman extra field `orca_settings` on the filament holds
  OrcaSlicer filament keys (flow ratio, max volumetric speed, pressure advance, retraction,
  ironing, temperatures and others) as a JSON object, for every printer or per printer, and the
  generated presets carry them.
- Anycubic Kobra X (and other Anycubic printers in LAN mode): the multi-colour box slots and the
  external spool show in the Printer tab, matched to Spoolman spools by material and colour. The
  printer is found from its preset's host address, like Moonraker printers.
- Send to Spoolman on the Spools tab: the unsaved changes of a Spooler preset open in OrcaSlicer's
  filament settings go into the filament's `orca_settings` field, in the section for that preset's
  printer, and the presets are rebuilt. A setting changed in Spoolman meanwhile keeps Spoolman's
  value.
- `orca_settings` also takes density, diameter, cost, Z shrinkage and notes.
- Klipper filament changers run by AFC, Happy Hare or anything else that writes Moonraker's
  `lane_data`: every lane shows in the Printer tab, matched to its Spoolman spool, and Load Printer
  Filaments fills the plate's slots lane by lane.
- Plugins > Run > "Spooler: Keep Slots Synced" keeps the plate's slots on the lanes' presets while
  it runs; run it again to stop it.

### Changed
- Publishing a GitHub release publishes it to Orca Cloud.
- The Spoolman bed temperature is set on every bed plate type, not only the smooth and textured
  PEI plates.
- In `orca_settings`, text that isn't one number (say `"0,95"`) is ignored for a number setting
  instead of reaching OrcaSlicer as several values.

### Fixed
- Klipper printers whose Moonraker answers missing objects with an empty one never showed the
  active spool.

## [0.9.1] - 2026-11-09

### Changed
- New Spooler brand: logo in the tab header, tab icon, banner and store images.
- Printer slot cards name the filament only, so names fit four to a row; the matching
  OrcaSlicer preset shows when you hover a slot.

### Fixed
- Preset names containing "conf", "cert" or "secret", which OrcaSlicer refuses to write.
- An offline printer no longer fills the log with a line per retry.

## [0.9.0] - 2026-11-09

First Spooler release: set your Spoolman address once and the rest is automatic.

### Added
- Spoolman filaments become OrcaSlicer filament presets, one per printer, hot-reloaded as a local
  preset bundle. Pick one for a slot in the sidebar and the slot takes the filament's colour.
  Each preset inherits the closest preset OrcaSlicer has for that printer (vendor line, then the
  printer's tuned generic, then the filament library) and carries Spoolman's colour, vendor,
  temperatures, density, diameter and cost.
- Klipper/Moonraker printers are found from the host address on your OrcaSlicer printer presets and
  shown in the Printer tab: Snapmaker U1 toolheads (matched by the spool id the printer reports,
  RFID tag, or colour) and single-extruder printers through Moonraker's Spoolman integration.
- Plugins > Run > "Spooler: Load Printer Filaments" assigns the matching presets to the plate's
  filament slots.
- Unit tests, run in CI on Windows, macOS and Linux.

## [0.8.4] - 2026-11-05

### Fixed
- Spoolio now notes which tray the printer reports as feeding and matches that tray’s RFID tag to the matching spools. Previously Spoolio assumed slicer filament 1 meant the first tray, which if using an AMS would be slot 1, so it read AMS slot 1’s tag and booked to that spool, effectively ignoring the source of where the spool was being fed from e.g. AMS 2 Slot 1. This then caused a booking inconsistency at the end of a print as the AMS 2 Slot 1 would be booked against AMS 1 Slot 1. 

## [0.8.3] - 2026-10-29

### Fixed
- Hide Print Progress now actually does what it says on the tin.  Bambu printers keep reporting “Finished” until the next print starts, and the Printer tab was counting a Finished (or Failed) job as a running print. That meant “Hide Print Progress” never kicked in and the 100% card just stayed there. 

### Changed
- Renamed the 'Show an Idle Line' option to 'Keep Print Progress Visible' to better describe what this was intended for.

## [0.8.2] - 2026-10-23

This update now introduces two major changes. The Spools tab can now show your spools in two columns, and a redesigned Recent Bookings list. Some users may prefer to showcase their spool list in a single column format, so a new option has been added to the Settings menu to choose between layouts.

### Added
- A new Configure Spool List card in Settings lets you choose Single Column or Two Columns for the Spools tab, with a preview beside it. Spool cards look the same in both layouts, and when you group spools, each group's spools are split across the two columns. 

- Filament Usage now has a collapsible Recent Bookings list, currently it only retains the last five prints, otherwise it begins to look a tad cluttered. A chip still persists on prints that still need booking.

- Once a print is booked, its Book button changes to Undo. Undo opens a popup that shows each spool's weight now, the amount being added back, and the new total. If you confirm, Spoolio adds the weight back to each spool in Spoolman. The print stays in the list marked as Undone, so you can book it again later.

### Changed
- Prints waiting to be booked are now shown in Recent Bookings. They have the same spool picker and grams boxes as before, and the Dismiss button has been removed.

- Each print in Recent Bookings is shown as its own card, with the printer, the result and when it ended (for example "Today 08:58" or "Yesterday 21:30").

- Removed the "Booked to Spoolman. Spools are matched by RFID tag." line from the Filament Usage header. The 'Matched by RFID' chip somewhat makes this self explanatory...I hope. 

### Known limitations
- Undo sets the spool's used weight in Spoolman back by the booked amount. If you have changed that spool's weight in Spoolman since it was booked, check it after undoing.
Prints that were waiting to be booked carry over when you update. The older "Booked x g to..." lines don't carry over, because they don't record which print they came from.

## [0.7.2] - 2026-10-20

Live Link now reconnects to your printer within seconds after your computer wakes from sleep, instead of taking a minute or two.  Bump for the OrcaSlicer 2.5.0 Alpha release.

### Fixed
- Faster reconnect after sleep. Spoolio now notices when your computer has woken from sleep and reconnects to the printer straight away, rather than waiting on the old connection until it timed out.

- Dropped connections are spotted sooner. Spoolio checks the printer is still answering every 15 seconds, and if it hasn't replied for 35 seconds, the Live Link is restarted. Previously a printer that went quiet could leave the link stuck until your operating system gave up on it.

- Quicker retries. If the printer can't be reached, Spoolio tries again after 2 seconds, then 5, then every 15, instead of always waiting 15 seconds.

## [0.7.1] - 2026-10-18

A small tidy-up of the Printer tab so the live status reads the same everywhere and the panels match the card style in Settings.

### Changed
- Live status is now consistent. The Print Progress heading and each linked printer show a green dot and "Live" instead of "Live from the printer" and "Live · updated just now". The dot still turns amber if a printer hasn't reported for a few minutes.

- Print Progress text sizes. The panel used a mix of text sizes; titles and job names are now one size, everything else is one smaller size, and the percentage is smaller.

- Removed the divider line under the Print Progress and printer card headings, to match the Settings cards.

## [0.7.0] - 2026-10-16

The Printer tab now includes print progress for each linked printer. The Settings page has been tidied up and follows the card theme throughout and includes a new section for the Printer tab.

### Added
- Print progress. This uses the connected printer(s) own MQTT messaging to draw a live progress bar. This is particularly useful for multiple printers that are connected on the same LAN and doesn't require separate numbers of OrcaSlicer instances for each sliced print to monitor the progress via the Device page.

- Configure Printer in Settings. If you don't have multiple printers then the print progress can be turned off if you wish. The print progress card can be further customised to show estimated finish time, slot in use and whether to show the printer if it's in an idle state.

### Changed
- The order of the Print tab has been changed.  Print Progress is now shown first, then your AMS system, followed by `This Plate`. The filament usage booking now sits underneath this, as it made more logical sense to be here as material is booked after the plate has finished printing.

- Settings page is now laid out in a card style format.  Each section is card with either a live preview or a guide. For narrow window device e.g. laptop, the two halves of each card stack.  Some notes have been removed, as some settings are quite self explanatory e.g. weights as grams or percentage of spools original weight.

## [0.6.0] - 2026-10-12

Filament usage booking now reads what was actually printed straight from the printer, rather than relying on your sliced G-code, and it no longer loses a print if the connection drops or OrcaSlicer is closed part way through. Multi-colour filaments also finally show their colours on the spool cards.

### Added
- Usage booking from the printer's job file (Spoolman source, with a Live Link). When a print starts, Spoolio downloads the job's `.3mf` from the printer over your local network (FTPS) and books the grams it lists for each slot to the matching spool in Spoolman. This means the amounts match the plate that is actually printing, even if it was sliced or sent from somewhere else. If the job file can't be read, Spoolio falls back to the grams from your sliced G-code as before.

- Booking survives link drops and restarts. The print Spoolio is tracking is saved on your computer, so if the Live Link drops or OrcaSlicer is restarted mid print, Spoolio picks it back up when it reconnects.

- Late cards for missed prints. If a print finishes while Spoolio wasn't connected, it shows a card for that print with a note to check the grams before booking. Late cards are never booked automatically, even with *Book Automatically* on.

### Changed
- Multi-colour spool swatches. Spools with more than one colour in Spoolman used to show a grey swatch. The circle now shows the colours, in segments for coaxial filaments and as a smooth gradient for longitudinal ones, on both the spool cards and the `+ Assign Spool` list. The ring and progress bar use one solid colour (the first colour of the spool) so they stay easy to read.

### Known limitations
- Job-file booking needs the printer on the same network, the same as Live Link. If Spoolio can't reach it or find the job file, the grams from your sliced G-code are used instead.

- The filament check and This Plate panel still match spools on their main colour only, so multi-colour spools may not match a slicer slot automatically.

## [0.5.0] - 2026-10-09

I'm excited to say that Spoolio can now read your spools from Bambu Cloud as well as Spoolman! (because variety is the spice of life) and it can also book the filament a print used back to Spoolman for a truly local live filament tracking solution.  This sadly cannot be done via Bambu Cloud due to what their API exposes, see more on the limitations section below.

### Added
- Bambu Cloud as a source. Choose `Spoolman` or `Bambu Cloud` under Choose Your Source in Settings. With Bambu Cloud, your Bambu filament library shows on the same spool cards, and the filament check and `This Plate` panel use it too.

- Sign in to Bambu Cloud inside Spoolio, with no other plugin needed. Enter your Bambu email and password and pick Global or China. Bambu 2FA will be required (emailed, or an authenticator app) ***<ins>Spoolio never stores your password</ins>***, only the sign-in token that Bambu returns, which can be removed with a quick Sign out. The Test Connection checks that you are online and that Bambu still accepts your sign-in. This uses Bambu's unofficial cloud service, so it is marked experimental.

- A Printer tab beside Spools, with a card for each of your printers. The `This Plate` panel now sits underneath, and the tab shows an amber dot when the plate needs attention.

- Set up your printers by hand or automatically. Add a printer, then add an AMS (4 slots), an AMS HT (1 slot) and an external spool. Several AMS units are numbered AMS 1, AMS 2 and so on. Every slot starts empty, and `+ Assign Spool` opens a searchable list of your spools. A spool can only sit in one slot, so once it is assigned it is hidden from the list, while two spools of the same filament are listed separately. The cards are the same as on the Spools tab, with a ✕ to clear a slot. This is stored in Spoolio only and works with either source, it's _only_ a representative view.

- Live AMS. The Printer tab can read what a printer reports for its connected AMS and external spool (material, colour and remaining percentage). Press **Live Link** on a printer and enter it's IP address, serial number (optional) and access code to read it directly over your local network, which works in LAN mode with either Bambu or Spoolman. The access code is kept in its own private file on your computer. Spoolio only connects while the Printer tab is open, or while usage booking is on.
    - With a Bambu Cloud connection, the spools within your library linked to a printer slot also show on the Printer tab. This can lag behind what is physically loaded, so the manual setup option is there to correct it.

- Book filament usage to Spoolman (Spoolman source, with a Live Link). When a print finishes, Spoolio works out which spool was in each slot from its RFID tag (matched against the `tag` extra field on the spool in Spoolman, the long serial Bambu uses for RFID detection if using Bambu filament, falling back to the spool's RFID tags and other extra fields) and books the grams from the sliced G-code to that spool in Spoolman. Choose *Ask Me Before Booking*, *Book Automatically* or *Do Not Track* under *When a Print Finishes*. Slots whose spool can't be identified are always booked by hand, and so are prints that were cancelled, where the grams are estimated from the progress. Nothing is booked twice.

Due to the changes, I've introduced two new tabs, aptly titled Spools and Printer.

### Known limitations
- ***Bambu Cloud is unofficial and experimental.*** Bambu can change it without notice, and your sign-in token expires after 90 days, so you will be asked to asked to sign in again after this time.
    - ***Bambu Cloud is read only.*** Spoolio can only read your Bambu filament library and never write to it.
    - ***No live AMS through Bambu Cloud.*** A printer in LAN mode isn't bound to your account, so the cloud doesn't list it. Use Live Link for live slots.
    - Bambu Cloud slot view can lag behind what is physically loaded, so treat it as **<ins>representative</ins>** only.

- ***Filament usage booking is Spoolman only***. With Bambu Cloud as the source the booking panel is off, because there is no way to write used weight back to the Bambu library. Whether Bambu tracks remaining weight itself for RFID spools is unverified if connected via the Cloud after a print - I'm assuming not if you have no printer connected to your Bambu account via the cloud.

- **Live Link** needs the printer on the same network with LAN mode on, and only connects while the Printer tab is open or usage booking is on.

- **Booking assumes slicer slot order** follows the printer's slots (AMS 1 slots 1 to 4, then the next AMS). Slicer weights are estimates and cancelled prints are estimated from progress, so booked amounts can differ slightly.

### Changed
- RFID badge on spool cards now reads the spool's `tag` extra field when present, failing back to the official Spoolman `tag` field if it cannot reconcile.  Required for the automatic consumption booking via Spoolman.

- Settings: the server section now has a `Choose Your Source` with an updated icon.

- Spool list error messages and the filament check say Bambu Cloud or Spoolman depending on what you use, and a missing or expired Bambu sign-in tells you to sign in from Settings.

## [0.4.0] - 2026-10-08

### Added
- `This Plate` panel on the spool list, shown after each slice (when filament check notifications are on). Each filament the plate uses gets a row with its colour, a progress bar showing what the plate needs against what the spool has left, and a result: Quantity OK, Barely enough, Not enough, Check the spool(s) or Not checked. Re-check runs it again against fresh Spoolman data, Dismiss hides it, and it clears itself on the next slice. 
    - `On this plate chip` on the matching spool cards, showing which slot or slots use that spool.
    - `Sort by: On this plate`, which becomes available while the panel is showing.

- Duplicate marker on cards where you hold more than one spool of the same filament, e.g. `x2 · 300 g together`.

- Spool weight display setting to show the remaining weight on the spool cards and group rows as grams, a percentage or both (the default), with a live sample card on the Settings page. The `This Plate` panel always uses grams.

- Low-stock weight colours: below your low-stock threshold the remaining weight turns amber, shading to red as the spool runs out (fully red at 20% of the threshold, so at 10 g with a 50 g threshold for example).

- Show cart button setting on the Settings page for the reorder cart.

### Changed
- The reorder cart button is now optional and off by default, because the weight colour now flags low stock. Tick `Show a cart button for reordering low-stock spools` in Settings to bring it back.

- Filters, sort and grouping are collapsible behind a Filters button, so the list looks cleaner.

- Settings page rearranged: Getting Started and Filament Reorder Preview now sit on the left, with the Spoolman server and reorder settings beside them. Spool Weights is a new section.

### Behind the scenes code clean up
- Shortened variable and function names across the plugin and tidied the comments and docstrings, with no change in behaviour.

- The filament check and This plate panel share one code path, so the notification and the panel always agree.

## [0.3.0] - 2026-10-06

### Added
- The Settings page now as filament check notification and a safety margin. Currently the safety margin defaults at 10% e.g. 20g of filament required, spool has 22g so is within the 10% but it can be adjusted to user preference, see updated README for a full explanation.

- Filament check at slicing, Spoolio compares the filament the plate needs with what is left on your matching spools and shows a notification in OrcaSlicer. A short-lived one when there's enough, and a persistent message that stays until you dismiss it when there may not be enough filament loaded. Slots holding the same filament are counted together. Switch on Spoolio Filament Check in your process settings, under `Others > Slicing Pipeline Plugin`, to use it.

## [0.2.0] - 2026-10-01

Spoolio now has its own tab in OrcaSlicer's top bar, and is built separately for all OS.

### Added
- Spoolio has migrated to OrcaSlicer's Pages window from the previous floating window method, and still falls back to the floating window on builds without Pages support.

- `Settings` inside the tab as a second page instead of a separate window. `Save & Close` or `Cancel` returns to the spool list, and Settings still opens first on first run.

- Filament Reorder Preview on the Settings page, showing which spools would get a reorder cart at the low-stock level you type in.

- A Diagnostics section with the plugin version, a Check for updates link and the path of the new log file (`spoolio.log`) to attach to bug reports, plus a feedback button on the Settings page.

- Builds for every platform: Windows, Linux and macOS, each for x86_64 and arm64, published as one file per system (`spoolio_win_x86_64.py`, `spoolio_macosx_arm64.py` and so on).

### Changed
- Two-column Settings page, with each setting beside its guide.

- A tidier Settings look.

- Larger remaining weight on the spool cards.

### Fixes
- Network requests (spool refresh, connection test and update check) now run in the background, so OrcaSlicer no longer freezes while waiting on Spoolman.

- If OrcaSlicer's data folder can't be found, settings and the log go to the operating system's standard config location instead of the plugin folder.

- The reorder cart tells you when no web browser could be opened and shows the address to open yourself.

- Swiping left or right on a trackpad no longer takes you to a blank page.

- Buttons and step titles on the Settings page now use the accent colour consistently.

## [0.1.0]

First public release: A Bambu Lab inspired spool card with filtering, sorting and grouping, RFID badges and a user configurable low stock reorder point. Ships as a single cross-platform `spoolio_any.py`.
