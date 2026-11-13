# Changelog

Spooler is a fork of [Spoolio](https://github.com/danm1989/spoolio-orcaslicer); entries before
0.9.0 are Spoolio's.

## [0.22.1] - 2026-11-13

- Releases ship one file, `spooler_any.py`, for every OS instead of six identical per-OS copies (they differed only in the name and a log label). Orca Cloud's automated permission review kept failing on the six-file upload with SECURITY_SCAN_UNAVAILABLE; the other plugins publish one file and go through. Manual install: download `spooler_any.py`.
- Same plugin as 0.22.0 otherwise.

## [0.22.0] - 2026-11-13

- Spool cards show the spool itself: a render of the reel with the filament wound on it in the spool's own colour (multi-colour spools too), drawn fuller or emptier in eight steps from what is left. The colour dot stays next to the name.
- The weight left is the headline of the card ("530 g of 1,000 g", percentage on the right); below the low-stock threshold the number turns warning/danger and says "Low stock" or "Almost empty" in words.
- The level bar is thicker, uses the filament's colours, keeps a light edge for white or black filament in either theme, and marks the low-stock threshold with a notch.
- A stack of identical spools shows two reels with the count; printer slots (AMS, toolheads, external) show the loaded spool the same way.
- In narrow places (a printer slot, two columns on a small window) the reel and the number shrink instead of squeezing the name.
- The stock list U1 Control reads now gives each spool's full weight from the filament when the spool has none, so U1 Control can draw its fill.

## [0.21.2] - 2026-11-12

- Fix Spooler failing to load in OrcaSlicer 2.5 ("Plugin on_load failed: PermissionError … audited operation open"). The load log line called `platform.platform()`, which on macOS reads `/System/Library/CoreServices/SystemVersion.plist` and opens `/dev/null`; the host's audit blocks both. The log now uses `sys.platform` and `platform.machine()`, which read no files. A test loads the tab and the window with file access outside the data folder blocked.

## [0.21.1] - 2026-11-12

- Build tools only: shared Orca UI foundation 2.0.3 (Vite 8.3.8, @vitejs/plugin-vue 6.0.11). No change to spools, printers or the interface.

## [0.21.0] - 2026-11-12

- Browser tests disable Chrome extensions that could leave child processes holding the runner open. `WORKERS=1` runs scenarios sequentially; CI uses this mode.

### Changed
- The Spooler tab, the spool window and the Settings window are one Vue 3 + PrimeVue 4 page (shared Orca UI
  foundation 2.0.2), built from `ui/` and embedded in the single plugin file (`scripts/embed_ui.py`); no CDN,
  no remote font, no eval. English and Brazilian Portuguese, following OrcaSlicer's language unless you pick
  one in Settings. Every flow stays: spool list, filters, groups, card actions, plate check, printers, Live
  Link, Moonraker active spool, usage booking and undo, drying, statistics, Settings and the setup guide.
- An empty Spoolman, a missing address, a failed read and filters that match nothing each say so, with the
  next step (Settings, Try again, Clear filters); Sync and Send are off, with the reason, until the spool
  source works. "Send to Spoolman" is now "Send Preset Edits to Spoolman" and explains what it sends.
- Results and errors are announced; errors stay until dismissed instead of disappearing after 8 s, and an
  action without an answer after 30 s says its outcome is unknown.
- Archive, Add a spool, moving a spool linked to a U1 toolhead, removing a printer or unit and clearing the
  active spool ask in a dialog that names both answers. Leaving Settings with unsaved changes asks first.
- Low stock uses the theme's warning and danger colours (the previous amber text measured 2.05:1); colour
  code and diameter are off by default on spool rows (Settings > Display turns them back on).
- With U1 Control running, the Spools and Printer tabs say the U1 lives in the U1 Control tab and why there
  are two tabs (OrcaSlicer offers no way to hide one).

### Added
- u1control can show Spooler's stock in its U1 Control tab. Spooler writes a presence file in
  OrcaSlicer's data folder while it is loaded, and the live spool list only while u1control's tab
  asks for it. Nothing extra is written to Spoolman or a printer for it.
- The spool list message tells the page whether U1 Control runs in this OrcaSlicer (`peers`) and gives
  failed reads a stable `error_code` (`no_url`, `read_failed`), so the page can explain the state in its
  own language. Read from presence files only.

### Fixed
- Filament presets fall back to the mean price per kg of their non-archived spools when the
  filament has no usable price. A usable filament price still takes precedence. Thanks to
  @jeffersonraimon for the contribution in #20.
- Mark Dried Today and Clear Dried Date on Spoolman older than 0.26 replaced the spool's whole
  extra map, dropping its other extra fields (for example the RFID tag). Spooler now reads the
  fields again and sends them back with only the dried date changed; when it can't read Spoolman's
  version or the fields, it writes nothing and says why.
- Changing the Spoolman address (or the spool source) while a send, a card action, a booking or a
  refresh was running could write data and spool ids read from the old server to the new one.
  Each operation now stays on the server it started with and stops when Settings change; card
  actions and bookings from a list read before the change are refused until you refresh.
- Sending a preset to Spoolman could undo a change made in Spoolman meanwhile to another extra
  field or to orca_settings. Spooler now reads the filament again just before writing, merges your
  edit with what changed there, keeps Spoolman's value where both changed, and on Spoolman 0.26 or
  newer sends only orca_settings.
- A booking whose answer was lost, or whose state couldn't be saved, could be booked twice. Each
  row's state is now saved before it is sent; when Spooler can't tell whether Spoolman applied it,
  the row is marked for you to check in Spoolman and is never sent again by itself. Undo adds the
  grams back in one step on Spoolman's side (Spoolman 0.18 or newer), so use booked meanwhile is no
  longer lost, and usage and history files are written in one step.
- Cancelling Keep Slots Synced while it read the printer still changed slots afterwards; it now
  stops before touching a slot, also when the printer or project changed, and an old run no longer
  clears a newer run's marker. Unloading the plugin stops its live printer links.
- Empty spools (0 g) disappeared from the Bambu Cloud list and showed no percentage on Klipper
  printers.
- An error while handling a page message could write a Bambu password or code to spooler.log.
  Messages are no longer logged whole, and passwords in addresses and secret-looking values are
  masked in every log line.
- A printer could make Spooler read a huge MQTT message or trickle one in forever; an Anycubic
  printer that never sent a report after connecting kept the link waiting. Both now end the session
  and reconnect with the usual backoff.
- When OrcaSlicer refused a new preset bundle, the last accepted one was already overwritten on
  disk; it is now put back.
- A filament box or lane removed from a Klipper or Anycubic printer kept showing.
- Filtering the spool list after a failed refresh showed the old list as current. The error stays,
  and the old list is marked with the time it was read.
- Assign Spool and the spool picker on the Printer tab work with the keyboard (Tab, Enter, Space,
  Down, Escape), and focus returns to the slot.
- The Printer tab no longer redraws every card when only a printer's age changed.
- SECURITY.md now lists every write Spooler makes to Spoolman and printers.
- Settings in a filament's orca_settings field in Spoolman that Spooler didn't know were dropped
  without a word. The nozzle temperature range (nozzle_temperature_range_low and _high) is now
  applied to the presets, along with chamber temperature, overhang fan speed, the layers with the
  fan off, the layer with full fan speed, the auxiliary fan speed and the minimal purge on the wipe
  tower. Any other key is still left out, and Spooler's log now names it once.

## [0.20.0] - 2026-11-11

### Added
- Change Spool on the Printer tab for single-extruder Klipper printers such as the Sovol SV06.
  It opens the spool picker, and the spool you pick becomes Moonraker's active spool, so Moonraker
  books the next print's filament to it. Clear unsets the active spool (with a second click).
  Archived spools are not offered, and the result shows under the card. It is not offered on the
  Snapmaker U1 (u1control binds its toolheads) or on printers with AFC, Happy Hare or another
  filament changer (they manage their own spools), and Spooler refuses it for those printers even
  if asked directly.
- A debug capture for Anycubic printers, the first step toward booking their prints. With
  "kx_capture": true in Spooler's settings file, Spooler writes each kind of message the printer
  sends to its log once, with serial numbers, tokens, addresses and credentials removed, and asks
  the printer for its print status.
- A Sync Presets button in the Spools tab reads Spoolman at once and rebuilds every Spooler
  filament preset in OrcaSlicer, even when nothing changed or a refused set was waiting to be
  tried again, then says how many presets it synced or why it couldn't.

### Fixed
- Opening a group of spools in the two-column list no longer stretches it across both columns and
  leaves a hole beside the card before it. The group stays in its own column, its spools are
  listed under it as normal cards, and the other column keeps filling beside them.

### Not yet
- Booking the filament used by Anycubic Kobra prints. How the printer reports a print in progress
  is not documented, so it needs a capture from one real print first; docs/kobra-booking.md says
  how to make one and what happens next.

## [0.19.0] - 2026-11-11

### Added
- A Details item in a spool's menu opens a panel on the card: the prints that used the spool (date,
  print name, grams, cost), the total grams and cost booked, how many grams a week it has used over
  the last 4 weeks, and about how many weeks are left at that rate.
- Export to CSV in the Stats tab's Print History card. It saves one row per spool of every print in
  the selected period (date, print, printer, result, progress, spool, material, colour, grams, cost
  and the support and purge grams) to a history-YYYYMMDD-HHMM.csv file in Spooler's exports folder,
  opens that folder and shows the file path. The file opens cleanly in Excel, and cells that start
  like a formula are stored as plain text.
- A Stats tile "On the Shelf" with the grams and money left in your non-archived spools, and a card
  that splits it by material. Spools without a price count toward the grams only.
- A Stats tile "Lost to Failed Prints" with the grams and cost of cancelled or failed prints in the
  period. Failed prints in Print History also show the amount they lost.
- A "Closest colour" picker in the Filters panel. Pick a colour and the list shows the 12 spools
  nearest to it, closest first, using the same colour distance as the plate check. A multi-colour
  spool counts by its closest colour. Clear brings the normal list back.

### Fixed
- The store images' footer now also names Anycubic in the "Not affiliated with" line.

## [0.18.0] - 2026-11-11

### Added
- A drying tracker. A spool's menu on the Spools tab has "Mark Dried Today" and "Clear Dried Date",
  and the card shows a "Dried 12 d ago" chip. The date is kept in a Spoolman field Spooler adds
  by itself, so it is also visible and editable in Spoolman. Switch the chip off in Settings >
  Display.
- A drying reminder after slicing. Settings has a new Drying Reminders table with the days each
  material may go since it was dried (PETG 30, TPU 14, PA 7, PVA 7, PC 14; ABS, ASA and PLA are off;
  set 0 for no reminder, and add your own materials). A material also covers its variants, so PA
  covers PA-CF and PETG covers PETG HF. When a loaded spool of one of these materials was dried
  longer ago than that, or never, the notice adds a sentence such as "PETG Black (slot 2) was last
  dried 41 days ago." It comes after the filament-quantity sentences and before the cost, and it
  never turns an all-clear notice into a warning. The chip turns amber past the same number of days.

### Changed
- Spooler now also adds a "Dried" field to the spools in Spoolman, next to its filament
  fields. Spoolman's own extra-fields line on the cards skips it.

## [0.17.0] - 2026-11-11

### Added
- A notification in OrcaSlicer when a spool drops below your low-stock grams: "Spooler: <spool> is
  down to 82 g". It fires once per spool as it crosses, never for the spools that are already low
  when OrcaSlicer starts, and again if you refill the spool and it drops again. Archived spools are
  ignored. Switch it off in Settings > Display.
- The notice after slicing now ends with what the plate costs in filament, for example "About
  €1.23 of filament.", when the matching spools have prices in Spoolman. It uses the currency
  chosen for Stats, and is the first sentence dropped when the notice is too long.
- When a slot is short of filament, the notice suggests a spool of the same filament that is not
  loaded and has enough, with where it is kept: "Swap in spool #12 (Shelf A, 640 g)." It prefers
  the spool you should finish first, otherwise the one with the least left that still covers the
  print.
- A "Use First" chip on the opened spool of a filament that has two or more spools, the one with the
  earliest first use (else earliest registered), so you finish the oldest first. Switch it off in
  Settings > Display.

## [0.16.0] - 2026-11-11

### Added
- The spool list updates by itself when spools change in Spoolman: add, edit, use or delete a spool
  there (or have a printer book filament to it) and the Spools tab shows it within a second or two,
  instead of at the next 60 second refresh. Several changes in a row refresh the list once. When
  Spoolman can't be reached this way (some reverse proxies block it), the list keeps refreshing
  every 60 seconds as before, and the log says so once.
- Spool cards can show the spool's comment, lot number and your own Spoolman extra fields, on a
  muted line under the details. Long text is cut short on the card; hover it to read it all. The
  comment is shown by default; lot number and extra fields are switched on in Settings > Display.
  Spooler's own fields (the RFID tag and its calibration fields) are never listed.

### Changed
- The search box also finds spools by location, lot number and comment, and `#12` finds spool 12
  and only that one.

## [0.15.0] - 2026-11-11

### Added
- A setup guide for first use. The first time Settings opens, a six-step guide explains what
  Spooler does, takes your Spoolman address and tests it right there, and covers permissions, where
  the presets appear and how printers are found. Next unlocks once the connection test passes.
  Back, Skip and Escape work as expected, and the guide never uses browser pop-ups. It opens by
  itself only while no source is set up and it has not been finished or skipped, so existing
  setups never see it. ***Open the setup guide*** in Settings brings it back.
- Install pictures and a complete Orca Cloud listing text (docs/store-description.md), a store
  image of the setup guide, and the README now shows the install steps.

### Changed
- The "How It Works" steps in Settings are replaced by a short note and the setup guide button.
- The store images are redrawn for the spool card menu added in 0.14.0.

## [0.14.0] - 2026-11-11

### Added
- Each spool card has a ⋯ button with actions for that spool in Spoolman: set its weight from a
  scale reading, subtract grams used by hand, move it to another location (Spoolman's locations
  to pick from, or type a new one), archive or unarchive it, add another spool of the same
  filament, and open it in Spoolman. Numbers are typed into the card itself. Archiving and adding
  ask for a second click, and so does moving a spool off a U1 toolhead's location, which unlinks
  it from that toolhead. The result shows in the status line above the list. Not offered for the
  Bambu Cloud source.
- Show archived (in the filters, and in Settings > Display) lists archived spools too, dimmed.
  They still never count for the filament presets, the after-slice check, usage booking or the
  printer slots.

### Changed
- Spooler now changes a spool's location in Spoolman when you move it from its card. It still
  never does so on its own.

## [0.13.0] - 2026-11-11

### Added
- The Stats tab estimates wasted filament (from Spoolio 0.9.6): how much of each print went into
  supports and into purging and the prime tower. There is a new Wasted Filament tile, a Usage
  Ratios card with the three most wasteful prints, and a Waste column in Print History. The
  estimate is read from the plate G-code inside the job file on the printer, so it covers Bambu
  prints booked from the job file, and only prints made after this update.

### Changed
- Configure Stats is now the last card in Settings (from Spoolio 0.9.6).

## [0.12.2] - 2026-11-11

### Fixed
- With the list grouped by material, manufacturer or location, the weight on a group's header
  ("1,871 g of 2,000 g · 94%") no longer wraps onto two lines or runs past the edge of the card.
  It stays on one line with the bar underneath, and a long group name is shortened instead.

## [0.12.1] - 2026-11-10

### Changed
- Spool cards are redrawn: a group of spools of the same filament now looks exactly like a single
  spool's card (swatch, name, weight, bar and detail line), with the number of spools on its swatch
  and an arrow. Closed, it takes one cell of the grid like any spool; open, it spans the row and
  shows its spools inside one panel.
- The manufacturer is part of the card's detail line instead of a badge on top of the card.
- Cards in the same row of the two-column list have the same height.

## [0.12.0] - 2026-11-10

### Added
- Settings > Display switches every part of the Spools and Printer tabs on or off: grouping of
  spools of the same filament, where a spool is loaded, the manufacturer tag, material, colour
  code, diameter, RFID badge, remaining bar, Spoolman location, spool number and exact weights; and
  on each printer slot the manufacturer, material, colour code, grams left, remaining bar, spool
  number and location, OrcaSlicer preset and RFID badge.
- Printer slots (Snapmaker U1 toolheads, AMS slots, lanes) show the loaded spool in full: its
  manufacturer, material and colour, grams left of the spool's weight, spool number and location,
  whether u1control linked it, and its OrcaSlicer preset.
- A spool loaded in a printer shows where ("In Use · Snapmaker U1 · T1"), and inside a group the
  loaded spools come first.

### Changed
- Weights are exact (2,380 g, not 2.38 kg) unless Settings > Display says otherwise, and a group of
  spools shows what is left of the group's total ("1,380 g of 2,000 g").
- Grouped spools stand out as their own card, with the spools inside indented under it.

## [0.11.1] - 2026-11-10

Documentation only; the plugin is the same as 0.11.0.

### Added
- A contributor guide, security policy, code of conduct, a tour of the code
  (`docs/how-it-works.md`), and issue and pull request templates.

## [0.11.0] - 2026-11-10

### Added
- Saving a copy of a Spooler preset in OrcaSlicer (OrcaSlicer can't save over a plugin's preset)
  sends the copy's changed calibration settings to Spoolman, so the Spooler preset gets them on its
  next rebuild. An OrcaSlicer notification says what was sent. `"send_saved_copies": false` in the
  settings file turns it off.
- Spooler's settings show in OrcaSlicer's plugin manager (Plugins > Spooler > Config), with Restore
  defaults. A change made there is checked and saved like one made on the Settings page; the
  Spoolman address is kept on Restore defaults.
- Plugins > Run > "Spooler: Keep Slots Synced" stops when OrcaSlicer cancels it (Speed Dial or the
  Plugins dialog).
- `scripts/build.py` also builds a pure-Python wheel (`spooler-<version>-py3-none-any.whl`) that
  runs on every OS. It is not published yet; the per-OS files stay the release until it is tried
  in OrcaSlicer.

### Fixed
- OrcaSlicer notifications (the plate check after slicing) never showed: Spooler looked for the
  notification levels on `orca.host.ui` instead of `orca.host.ui.NotificationLevel`.
- Links on Windows open with the system's handler, as OrcaSlicer does, since Python's webbrowser
  can report success inside OrcaSlicer without opening anything.
- When OrcaSlicer refuses the preset bundle, the log names the bundles it offers.

## [0.10.0] - 2026-11-10

### Added
- Works with [u1control](https://github.com/bloodf/u1control) on the Snapmaker U1:
  - On stock firmware a toolhead's spool is the one u1control bound to it, read from the spool's
    Spoolman location `<printer name> T<n>`: Spooler's label, the printer model, or any name ending
    in "U1" (u1control's printer name, "Snapmaker U1" unless renamed; the oldest form is `U1 T<n>`).
    The order is the spool id
    the printer reports, then that location, then the RFID tag, then vendor, material and colour.
    Archived spools never match; when two spools claim one toolhead the last used wins and a
    warning is logged. The slot's tooltip says "Spool linked by u1control". Spooler still never
    changes a spool's location.
  - Spooler writes `profiles.json` to `<OrcaSlicer data folder>/spooler/`, listing the preset of
    every Spoolman filament on every printer, so u1control picks the same preset.
  - While Plugins > Run > "Spooler: Keep Slots Synced" runs it keeps `keep_slots.json` fresh, and
    marks it stopped when it stops or the plugin unloads; u1control then leaves slot sync to it.
  - When several spools match a toolhead's vendor, material and colour, the filament sub type
    u1control writes on the printer picks the one with that filament name.
  - Keep Slots Synced leaves a slot that holds a Spooler preset of the same filament, for any
    printer, so the two plugins don't take turns changing it.

### Changed
- Filament used on Moonraker and Anycubic printers is still not booked by Spooler (u1control books
  each U1 toolhead, Moonraker books other Klipper printers); this is now checked by a test.

## [0.9.5] - 2026-11-10

### Fixed
- 0.9.4 put OrcaSlicer's plugin marker on the wrong definition, so OrcaSlicer could not find the
  plugin class and Spooler didn't load. The marker is back on the plugin class.

## [0.9.4] - 2026-11-10

### Changed
- Spooler declares the access it needs when it loads: its data folder, its worker threads and the
  fixed addresses it calls (the GitHub release check and Bambu Cloud sign-in). OrcaSlicer asks
  once; Spoolman, Moonraker and printer addresses are still asked for on first use.

## [0.9.3] - 2026-11-10

Everything in 0.9.2, which never reached Orca Cloud.

### Fixed
- Publishing to Orca Cloud: release notes containing a semicolon no longer break the upload.

## [0.9.2] - 2026-11-10

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
- `orca_settings` also takes Z shrinkage and notes.
- Preset edits made in OrcaSlicer are sent to Spoolman by themselves once they have stayed the same
  for a few seconds while the Spooler tab is open; `"auto_send": false` in the settings file turns
  this off. Density, diameter and cost are written to Spoolman's own filament fields.
- Spooler adds Flow ratio, Pressure advance and Max volumetric speed number fields to Spoolman's
  filament form; the presets take them for every printer.
- Spools of the same filament and colour fold into one accordion row showing their total weight.
- The name filter is always shown, next to a new colour filter with colour swatches.
- Klipper filament changers run by AFC, Happy Hare or anything else that writes Moonraker's
  `lane_data`: every lane shows in the Printer tab, matched to its Spoolman spool, and Load Printer
  Filaments fills the plate's slots lane by lane.
- Plugins > Run > "Spooler: Keep Slots Synced" keeps the plate's slots on the lanes' presets while
  it runs; run it again to stop it.
- A Stats tab (from Spoolio 0.9.5): filament used per week, per material and per spool, filament
  cost, spools running low with an estimate of how many weeks they last, and a print history.
  Prints are recorded in `history.json` as they are booked to Spoolman, even while the tab is
  hidden. Settings > Configure Stats shows or hides the tab and picks the currency: Spoolman's own
  setting, or a £, € or $ symbol.

### Fixed
- A printer reporting an absurd lane number no longer builds a huge lane list.

### Changed
- Publishing a GitHub release publishes it to Orca Cloud.
- The Spoolman bed temperature is set on every bed plate type, not only the smooth and textured
  PEI plates.
- In `orca_settings`, text that isn't one number (say `"0,95"`) is ignored for a number setting
  instead of reaching OrcaSlicer as several values.

### Fixed
- Live Link reads the printer's serial number from its certificate when the field is left blank,
  so printers that refused the wildcard status topic now report (from Spoolio 0.9.5). A printer
  that still refuses it shows "needs its serial number" instead of retrying.
- H2 printers: the tray feeding the print is read from the active extruder, so slots and the
  booked spools follow the real tray (from Spoolio 0.9.5).
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
