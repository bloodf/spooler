# Changelog

Spooler is a fork of [Spoolio](https://github.com/danm1989/spoolio-orcaslicer); entries before
0.9.0 are Spoolio's.

## [Unreleased]
### Added
- The Spools list can show cards as well as the table: **Table** and **Cards** in the list's toolbar. Each card shows the spool filled to what is left, its name, manufacturer, material, colour, weight left with a bar, location and state (low stock, RFID, dried, in a printer, archived). Search, filters, sort, groups and stacks work the same in both, and a card opens the same detail as a row. Your pick is remembered; Settings > Spool list sets the default.
### Fixed
- An empty spool (0 g left) is never marked **Use first**: the next opened spool of its filament gets it, or none does.
- Opening a stack of spools of one filament (×n) no longer shows just its first spool, which could be an empty one: the detail lists the stack's spools with their total, and each opens with **Back to the n spools**. The ×n chevron still opens the stack in the list. When the list shows a stack's spool by itself, it shows the one in use, else the one with the most left.
- A spool at 0 g says **Empty** instead of "Almost empty", and its detail offers **Archive**. Stacks count their empty spools ("2 spools · 1 empty").
- A spool linked to a slot in U1 Control or Kobra Control shows in Spooler at once, and one assigned in Spooler shows in their open tabs at once. Spooler re-reads Spoolman every 30 s while it is visible (was 60 s; Settings > Spool source > **Refresh Spoolman every**: 10 to 300 s, or off), pauses while hidden, waits longer after failed reads (up to 5 minutes, "Spoolman unreachable, retrying") and never while a dialog or picker is open. An ACE slot of a printer renamed in Kobra Control is linked and read under that name.
- Spool cards are at least 260 px wide (two beside the open detail at 1280 px), the cards of a row share one height with the state chips at the bottom, and chips and manufacturer names wrap instead of being cut off.
- On Windows the Spooler tab stayed blank since 0.30.0: the page had grown past what OrcaSlicer can show there (1.5 MB). A page that would be too big now leaves out its embedded font and draws in the system font instead.
- The Spooler page is less than half its old size (about 690 KB instead of 1.58 MB) and keeps its own font on Windows: its script now ships compressed and unpacks when the page opens. The build fails if a page ever gets close to the 1.5 MB OrcaSlicer can show on Windows.

## [0.30.0] - 2026-11-18
### Added
- Assign a spool to a Snapmaker U1 toolhead or an Anycubic ACE slot from the Printer tab. Each slot card has **Assign spool** / **Change spool**, with a search that shows each spool in its colour with its material and weight, and **Unassign** for a linked spool. Spooler saves the link as the spool's Spoolman location, in the form U1 Control (`<printer> T<n>`) and Kobra Control (`<printer> S<n>`) read; the spool that held the slot before loses that location. Nothing is sent to the printer, and Spooler asks first while the printer is printing. Spooler also reads Kobra Control's `S<n>` links on ACE slots before matching by colour. Slots whose spool the printer reports itself (U1 extended firmware) and Bambu, Happy Hare and AFC slots stay read-only. Hand-set slots (added printers, Klipper toolheads and gates) get **Change spool** too.
### Changed
- Settings is split into pages: a list of pages beside the open one, or in a narrow window the list first and one page at a time with a Back button. Version, updates and the log file have their own About page. Settings opens on the page you used last, a page with a problem (such as a failed source test) is marked in the list, and Open Settings from an empty or failed spool list goes straight to the source page, also in the separate Settings window.
- The Printer tab uses the full width: printers, the plate check and the bookings sit in two columns from about 1160 px wide and in three from 1800 px.
- The notes about presets and booking show once, in a collapsible **How booking works** at the top of the Printer tab, with only the parts that apply to your printers. Each printer gets a one-line chip instead, such as "Booked by U1 Control".
- A printer that hasn't reported its slots yet shows a spinner, and after 45 seconds says it may not and what to check.
- Spools are drawn filled to what is left in more places: the spool pickers (assign a slot, pick after a slice), the RFID offers, and the Stats "Most used" and "Running low" lists. The weight and percentage text stay as they were.
- A printer slot's spool picture follows the real amount: Spoolman's weight, else the printer's percentage. When neither is known, a loaded slot shows a full reel in its colour with a small "?" badge instead of a made-up level (before, a slot with no reading was drawn full or at 60 %). An empty slot shows the bare reel.
- NOTICE.md credits Pablo Saura Sánchez (@saurasanchezpablo, #2: Klipper lanes from Moonraker's lane_data, plate slots kept on lanes, preset edits sent to Spoolman's orca_settings, other Spoolman fields kept) and Jefferson J. Raimon (@jeffersonraimon, #20: preset cost from spool prices), whose contributions were made under MIT.
### Fixed
- The Printer tab no longer shows "100 % on the printer" for a U1 toolhead or an ACE slot holding a Spoolman spool: that number was Spoolman's weight. A printer percentage shows only when the printer reports one (Bambu AMS, an Anycubic slot's own reading).
- Long preset and location lines on a slot card are cut short with an ellipsis (the full text shows on hover) instead of running past the card.
- The Happy Hare note no longer shows on a Snapmaker U1, or on a printer without reported gates.
- "Add printer" and "Assign spool" no longer show two plus signs in every language.

## [0.29.1] - 2026-11-17

### Added
- Settings has a Requirements section. It shows the spool source in use (a Spoolman server, or a Bambu Cloud sign-in) as found, missing, not reachable (it answered earlier, so no install steps) or not checked yet, with the reason, what needs it, and how to get it: for Spoolman a Docker command, a line each for macOS, Windows and Linux, and a button that opens Spoolman's install guide. Check again re-runs the connection test Settings already makes when it opens; no extra request is made at start-up.
- Polish (pl) translation. Thanks to @xtronets for asking (u1control#20).
- Use your own tuned filament preset for a spool. Edit Spool has an **OrcaSlicer preset** choice, for the spool and for its filament, listing your own filament presets. Spooler keeps the name in a Spoolman text field, `orca_filament_preset` (added to Spoolman the first time you save one; you can also fill it in Spoolman, and the spool's value wins over the filament's). A linked spool gets no Spooler preset; Load Printer Filaments and Keep Slots Synced pick your preset instead. U1 Control and Kobra Control read the same field. Thanks to @askpete for reporting it (#38).
### Changed
- The plugin icon is the new brand tile.
- Licence is GPL-3.0 again (GPL-3.0-only), as required by Spoolio's licence. The copyright notices of Dan J Moore and of Spooler's contributors are kept in NOTICE.md and at the top of `spooler_any.py`. Thanks to @danm1989 for raising it (#19).
- When the spool source fails two reads in a row, Sync Presets, Send Preset Edits, Add Spool and the spool actions in the detail panel are off, with a one-line reason, even when the last list is still shown. A single failed read is treated as a blip. They come back with the next good read. Automatic sending of preset edits also waits for that read instead of failing every few seconds.
- Spools are drawn with the photo spool again.
- Notifications appear bottom-left and each one can be closed; warnings and notices on the page can be dismissed.
- Notifications wait while OrcaSlicer is in another tab or app; errors stay until closed. A closed warning shows again if its problem goes away and later comes back.
- The page fills the whole tab at every height, also after the window is resized: no more grey under a short page.
- Settings are tabs: one section at a time, and the save bar stays on screen at any window height.
- Spooler's filament presets are now standalone copies: each one holds its parent preset's whole set of settings (with Spooler's values on top) instead of inheriting them, and has a `filament_id` of its own (`SPL` plus a short hash of its filament, printer and, with presets per spool, spool). OrcaSlicer's "sync from AMS" only loads standalone presets, so this is what lets Kobra Control and U1 Control have it load the Spooler preset of a linked spool. Copies are refreshed whenever Spooler rewrites its presets and on Sync Presets, which also re-reads the parent presets. Existing presets are converted the next time they are written and keep their names, so projects still find them. The preset's description says which preset it was copied from.

### Fixed

- The spool detail also lists Spooler's presets for the printers a linked preset doesn't fit, after the linked one, and Send is off, with the reason, for a link set on the spool alone.
- Changing or clearing a spool's or filament's OrcaSlicer preset link in Edit Spool no longer reports a conflict with Spoolman every time.
- Send to Spoolman on your own linked preset no longer mistakes your preset's saved values for changes made in Spoolman, and the spool detail now preselects the preset open in OrcaSlicer's filament settings, else the selected printer's.
- A linked preset is only used on the printers it fits (OrcaSlicer's compatibility for the selected printer, the preset's compatible printers for the others); elsewhere the spool keeps Spooler's preset. Names of a plugin's presets (`_local/...`) can't be linked.
- Send to Spoolman on a Spooler preset with no unsaved edits now just says so, and Spooler reads a parent preset's saved settings even when it is the one being edited.
- A preset linked to one spool only is no longer sent to Spoolman: its settings would land on the filament every spool of it shares. Link the filament instead, or keep the changes in your preset.
- Send to Spoolman always worked on the preset opened last in OrcaSlicer's filament settings and said it had no unsaved changes even after edits: it compared the edited preset with itself. It now compares it with the saved preset, which also makes the automatic sending of edits work. The button moved to the spool's detail, next to an **OrcaSlicer preset** choice of that spool's presets, and acts on the one picked there. With no unsaved edits it says there is nothing to send instead of failing, and for your own linked preset it sends the saved settings that differ from Spooler's (#38).
- With presets per spool, `profiles.json` also lists each spool's own preset under `"spools"`, so U1 Control and Kobra Control pick that spool's preset rather than the one of its filament's lowest-numbered spool. It also lists each standalone preset's `filament_id` under `"ids"` (OrcaSlicer's plugin API doesn't show it). The file keeps version 1 and its `"filaments"` map.

## [0.29.0] - 2026-11-17

### Added
- Add and edit spools without leaving OrcaSlicer. "Add Spool" above the spool list (and in the empty list) walks you through it: pick a filament Spoolman already has to restock it, or make a new one (manufacturer, name, material, one or several colours, diameter, density, nozzle and bed temperatures, filament and empty spool weight), then fill in the spool (starting weight, grams left, location, lot, price, note, archived). The density fills in for common materials.
- A pencil beside each spool's name, in the list and in its detail, opens Edit Spool. Changes to the spool are saved to that spool; changes to the filament (colour, temperatures, density and so on) are saved to the filament in Spoolman, and the editor says how many other spools share it.
- Your own Spoolman extra fields, for spools and filaments, can be filled in there with the input their type calls for: a switch for yes/no, a menu for a choice, a number box with its unit for numbers (two for a range), text otherwise. Spooler's own fields stay hidden.
- A live preview of the spool, drawn like the list's reels, shows its colours, name and amount left as you type.
- Only the fields you changed are sent, after reading the spool from Spoolman again: a field someone changed in Spoolman while you were editing keeps Spoolman's value, and the result says which. Spoolman's refusals show in the editor, which stays open; if a new filament was made but the spool was refused, trying again uses that filament instead of making a second one. Emptying an extra field needs Spoolman 0.26 or newer; older versions say so and nothing is written. Decimals typed or pasted with a point work in every language.
- Klipper printers with several toolheads (up to eight: extruder, extruder1 ... extruder7) show each toolhead on the Printer tab, and you choose the spool on each, as on a PrusaLink or OctoPrint printer. The Snapmaker U1 works as before.
- A Klipper printer whose MMU doesn't report its gates can have up to 16 gates set on the Printer tab, with the spool on each. Gates the printer reports are still read from it and can't be changed here: AFC and Happy Hare through Moonraker's lane_data, and Happy Hare's own gates too, which are never filled from a slice or booked here since Happy Hare books its spools to Spoolman itself. The toolheads and gates to set appear once Spooler has read the printer.
- After a slice for a Klipper printer, each filament's matching spool is put on its toolhead (or gate), as already done for PrusaLink and OctoPrint. A spool put on a slot is taken off any other slot it was on. Bambu printers and printer-reported gates are left alone.
- With two or more of these printers, each one on the Printer tab says which OrcaSlicer printer presets slice for it; a preset not chosen goes by its host address as before. Each Klipper printer has its own switch to turn the slice fill off.
- New Bambu RFID spools are offered for Spoolman. With Live Link on, a Bambu RFID spool in an AMS slot or the external spool holder that no Spoolman spool carries shows on the Printer tab ("New RFID spool in X1C · AMS 1 slot 3", with its colour and how much is left) with Add and Skip. Add opens Add Spool filled in from what the printer reports: Bambu Lab, the material and name, the colour or colours, the diameter, a nozzle temperature in the middle of the spool's range, the weight and the grams left. A Bambu Lab filament in Spoolman with the same material and colour is picked to restock, else a new filament is filled in. The spool's RFID tag is saved with it (in the spool's "tag" field, which Spooler adds to Spoolman when it is missing), so the printer's use is booked to it from then on. Skip stops asking about that spool in that printer; Settings > Printer shows how many you skipped and can ask again. A spool whose tag Spoolman already has, archived spools included, is not offered, and a tag is never stored on two spools. The offer shows with the next spool list read, within a minute. Spooler only reads what the printer reports and sends it nothing.
- The H2D's second external spool holder isn't offered yet: only the first external holder is read.
- Settings > Presets: OrcaSlicer filament presets can now be made per spool instead of per filament. Each is named with the spool's number, like "SUNLU PLA Black #12 @Snapmaker U1", so the name stays the same on every sync and no two clash; archived spools lose theirs and renamed ones leave no old preset behind. Per filament stays the default.
- Use with, in Edit Spool, picks the printers that get a spool's own preset. Left empty, a spool loaded in a printer slot (on the Printer tab or reported by Live Link) gets a preset for that printer only, and a spool on the shelf one for every printer. It is kept in a new "Use with" spool field, which Spooler adds to Spoolman only once presets are per spool or the field is first saved, and saving it follows the same Spoolman version rules as the other extra fields.
- Advanced tuning in Settings > Presets, off by default: per material, choose the OrcaSlicer preset to inherit from and set flow ratio, pressure advance, retraction length and speed, max volumetric speed and fan speeds. A filament's own values in Spoolman still win. Turned off, presets are made exactly as before.
- Settings > Presets says that OrcaSlicer won't reload renamed Spooler presets while the selected one has unsaved changes, and what to do.
- Every preset is checked against the settings and value types OrcaSlicer takes before the set is written. One that fails is left out and named in spooler.log, so it can't make OrcaSlicer refuse all the others.

### Changed
- When a sliced filament matches several spools, Spooler now asks which one is loaded instead of leaving the slot as it is, for PrusaLink, OctoPrint and Klipper printers.
- Saving a copy of a Spooler preset with changed calibration values (flow ratio, pressure advance and the others Spooler keeps in Spoolman) no longer writes them to Spoolman on its own. Spooler shows which filament it is, each setting's value in Spoolman and the new one, and writes nothing until you press Save to Spoolman. Skip leaves Spoolman as it is, and Spooler doesn't ask again about the same values for that filament until they change.
- Unsaved edits of a Spooler preset still reach Spoolman by themselves, except flow ratio, pressure advance and max volumetric speed: those wait in the same prompt. Send Preset Edits to Spoolman still sends everything at once.
- Settings > Spool source has "Save calibrated values to Spoolman": Ask first (the default), Automatically (the old behaviour) or Never. If you had turned off sending saved copies, in the settings file or in OrcaSlicer's plugin manager, it starts on Never.
- A prompt waiting for an answer is still there after OrcaSlicer restarts.

### Fixed
- A Settings save that happened while Spooler was writing a calibration prompt, a printer list or another setting could drop that write. Every settings write now updates only its own keys, one at a time.
- When Spooler can't read Spoolman's version, Send to Spoolman now says so and writes nothing, instead of sending every extra field of the filament back as read, which on a Spoolman that merges them could undo a change made in between.
- On Spoolman 0.22 to 0.25, Clear Dried Date did nothing: the spool kept its dried date while Spooler said it was cleared. These versions can't remove the date, so Spooler now says so and writes nothing; Spoolman 0.26 or newer removes it as before.
- On Spoolman 0.22 to 0.25, Mark Dried Today and Send to Spoolman sent back every extra field of the spool or filament, as read just before, instead of only the one they change, so a change made in Spoolman in between could be undone. They now send only their own field; only Spoolman older than 0.22, which replaces the whole map, still gets it whole.

## [0.28.0] - 2026-11-16

### Added
- Spooler now speaks Spanish, German and Simplified Chinese, next to English and Brazilian Portuguese. The page follows OrcaSlicer's language on its own (Traditional Chinese gets the Simplified texts, any other language English), and Settings > Language lets you pick Español, Deutsch or 简体中文 instead.
- The messages Spooler writes itself are in your language too: the filament check after slicing, the low-stock notice, spool action results, Bambu Cloud sign-in errors, Sync Presets, Send to Spoolman, and the Load Printer Filaments and Keep Slots Synced results. This now includes Brazilian Portuguese, where they were English before. Spool, filament, vendor and colour names stay as Spoolman has them.
- Numbers, weights, money and dates are written the way each language writes them, for example "1.380 g" and "41,20 €" in German, and Bambu print stages use OrcaSlicer's own wording.

### Fixed
- The grams of a print to book take "2.5" typed or pasted as 2.5 g in every language. With a German, Spanish or Portuguese system the "." was dropped and it became 25 g; the field now also writes its number the way the page's language does.

## [0.27.1] - 2026-11-15

### Fixed
- A spool's detail now updates its print history and "Lasts about" after one of its actions goes through and whenever the spool list is read again, instead of keeping what it showed when the spool was first picked.
- Switching the spool source between Spoolman and Bambu Cloud with the same spool number shown could leave the detail on "Loading…". The detail now treats it as a different spool and asks only Spoolman for a history.

## [0.27.0] - 2026-11-15

### Changed
- A new look for the whole page, shared with the other Orca plugins: a magenta bar on top with the Spooler mark, the spool source and when it was last read, and the tabs (Spools, Printer, Stats and Settings, which is now a tab instead of a button). Refresh and Sync Presets sit at the right of the bar. Panels have coloured headers with icons, states are coloured chips, and the page uses the Manrope font.
- Spools is now a list with a detail beside it. Each spool is one row with its drawn spool in the filament's colours, material, location, state chips and what is left; spools of one filament fold into one row with a ×n chip that opens to its spools. Picking a row shows that spool beside the list (under it in a narrow window): how much is left and about how long it lasts, its facts, its use per week, its last prints and every action that was in the card's menu (set weight from scale, use filament, set grams left, move, notes, mark dried, add spools of this filament, open in Spoolman, archive). Close the detail with its × button.
- The spool pictures are drawn instead of using fifteen images, so they stay sharp at any zoom and show multi-colour filaments side by side.
- Printer: each slot, toolhead and external spool is a card with its colour, spool and amount left; print progress is one block with the percentage, time left and finish time.
- Stats: tiles with icons for the totals, and the charts use the page's colour set instead of ten fixed colours, in both themes.
- Settings: an index of sections on the left that follows the scroll, the settings in two columns, and one bar at the bottom with Cancel and Save. The setup guide, the empty and error states and the stale-list warning use the same look; the empty states have the Spooler shelf illustration.
- New Spooler mark (a spool seen from the side) in the tab icon, the page and the README art.

- The licence texts of what the page bundles (Vue, PrimeVue, the Lucide icons and the Manrope font) now travel inside `spooler_any.py`.

### Fixed
- The actions panel of a spool card could draw outside its card. The actions now live in the spool's detail.

## [0.26.0] - 2026-11-14

### Added
- Three spool card actions (Spoolman): ***Set Grams Left*** sets the filament left without a scale (0 for an empty spool); ***Add a Note*** / ***Edit Note*** edits the spool's Spoolman comment (empty removes it); ***Add Spool of This Filament*** asks how many, 1 to 20, for a multi-pack. If Spoolman refuses one of several, the message names the spools that were added.

### Changed
- Changing a Klipper printer's active spool while it prints or is paused now asks first: Moonraker would book the rest of that print to the new spool. Idle printers change at once, as before.
- Stats, spool Details and the CSV export count only the prints booked on the Spoolman in Settings (prints booked before this version, which don't say which Spoolman they were on, still count). Nothing in `history.json` is rewritten.
- The weekly use in Details and Stats divides by the weeks Spooler has history for (one to four), so a new install no longer shows a fraction of the real rate and far too many weeks left.

### Fixed
- A print whose booking had a slot set to 0 g stayed "not booked" for good; such a slot is now settled without a request to Spoolman. The booking panel also stops at the 5,000 g per slot that is booked.
- The spool card offered weights and uses of 0 g and above 100,000 g, which Spoolman's side refused with a confusing message; it now checks the same range and says so.
- Setting the dried date or sending preset edits reads Spoolman's version again first, so a Spoolman downgraded below 0.26 while OrcaSlicer runs can't have its other extra fields wiped.
- A printer link that restarted could hide its status on the Printer tab until the next report.
- In the window build (no tab), a booking, undo or stats request made just before closing the window raised an error and the booking didn't run.
- Test Connection stopped answering for the rest of the session after testing an address that answered with something other than Spoolman's JSON (an empty page, a list, a router page), and Save stayed blocked with it. It now says the address didn't answer like Spoolman. A spool list that isn't a list of spools is a failed read instead of an error in the Spools tab.
- A Spoolman address with a user name and password (`http://user:password@host:7912`, for a Spoolman behind a proxy with basic auth) could never be reached. They are now sent as basic auth, on the live-updates connection too. Only `http://` and `https://` addresses are opened.
- The Bambu Cloud sign-in token and the Anycubic printer's client key are written readable only by you from the moment the file exists; a sign-in that can't be saved now says so instead of leaving Settings waiting.
- A PrusaLink or OctoPrint printer redirecting to another host no longer gets its API key sent there.
- Setting the active spool of a Klipper printer always gets an answer, also when Moonraker's reply is malformed.
- Spooler now declares the Bambu Cloud addresses it really calls (2FA and the filament list) to OrcaSlicer's permissions.

## [0.25.1] - 2026-11-14

### Changed
- Build tools: TypeScript 7.0.2 and the shared Orca UI foundation 3.1.0. vue-tsc type-checks the page on the TypeScript 6 compiler from `@typescript/typescript6`, because TypeScript 7 has no JS API yet. The page and plugin are unchanged.

## [0.25.0] - 2026-11-13

### Changed
- The page now runs on PrimeVue 5.0.5 and @primeuix/themes 3.1.1 through the shared Orca UI foundation 3.0.2 (Aura with the 4.x sizes and the same palette). No visible change is intended.
- PrimeVue 5 colours use CSS `light-dark()`, so OrcaSlicer's page view needs WebKit 17.5 or later on macOS and WebKitGTK 2.44 or later on Linux (Windows uses WebView2, which already supports it).
- PrimeVue 5 is under the PrimeUI License; Spooler ships the Community License key in the shared foundation, checked offline.

### Fixed
- The tab bar no longer shows a scroll arrow over the first tab when the Printer tab is open.

## [0.24.0] - 2026-11-13

### Added
- Keep Slots Synced can start by itself when OrcaSlicer opens: Settings > Printer > "Keep the plate's filament slots synced automatically" (`auto_keep_slots`, also in Plugins > Spooler > Config). It is new and off by default. Running Plugins > Run > Spooler: Keep Slots Synced while it is on stops it until OrcaSlicer restarts; untick the setting to turn it off. It changes the slots from Spooler's own thread, which OrcaSlicer 2.5.0 accepts in its code but which hasn't been confirmed in daily use: if OrcaSlicer refuses it, Spooler turns it off for the session and tells you to use Plugins > Run.

## [0.23.0] - 2026-11-13

### Added
- PrusaLink and OctoPrint printers on the Printer tab: pick the printer type when linking it (PrusaLink takes the username and password from the printer's PrusaLink settings, OctoPrint an application key). Spooler shows live print progress and the spools on each toolhead, and books the grams from the job's G-code to Spoolman. These printers don't report their spools, so you assign one to each toolhead ("Add toolhead").
- Klipper (Moonraker) printers show live print progress. Their prints are booked too when the printer is not a Snapmaker U1 (U1 Control books those) and Moonraker's own Spoolman integration is not connected, so nothing is counted twice. Grams come from Moonraker's file metadata.
- After a slice for a PrusaLink or OctoPrint printer, each filament that matches exactly one spool is put on its toolhead (and taken off any other slot). Several matches leave the toolhead as it was. Can be switched off per printer.
- Stats: calibration prints (flow rate, pressure advance, temperature and retraction towers, max volumetric speed, VFA, input shaping) are their own Calibration slice in Usage Ratios, with a chip in the history and a column in the CSV export. They no longer count as wasted filament or "most wasteful prints".

### Changed
- PrusaLink, OctoPrint and Klipper prints are always asked before booking, even with Book Automatically on.

### Fixed
- OrcaSlicer could freeze while a booking waited on a slow or offline Spoolman: the Printer tab's refresh waited for the booking. It now answers at once.
- After Spoolman answered the spool list with an error, the list could stop refreshing until OrcaSlicer was restarted.
- Errors in background tasks are written to `spooler.log`.
- Two refreshes at once could open two live connections to the same printer (two Bambu sessions knock each other off).
- The spool list is read from Spoolman once when several parts of Spooler ask for it at the same moment (after a slice).

### Known limitations
- PrusaLink, OctoPrint and the Klipper booking were built from the printers' API documentation and tested against simulated answers, not real printers yet. Reports welcome.
- Prusa binary G-code (`.bgcode`) is not read; those prints are booked from the last slice's grams.

## [0.22.2] - 2026-11-13

### Fixed
- Dark theme: a style meant for the spool picture and level bar was applied to the whole page (a faint glow filter and a different background on the page itself). The rules now reach only the reel and the bar.
- Near-black filament on the dark theme, and near-white on the light theme, got a clear edge on the level bar, so a full black spool no longer looks like an empty bar.
- Two-column list: cards in the same row share its height, so the columns read as rows instead of leaving gaps under shorter cards.
- Grouped (stacked) cards line up with single cards: same picture width, same title weight, and the colour dot next to the name.
- The card no longer shows a tooltip repeating its name and weight; it could float over the neighbouring card.
- Stats (same bug as fixed in Spoolio 0.10.1; fixed independently): a single-colour print could be counted entirely as purge when the printer's change-filament template, which OrcaSlicer copies into the G-code settings block, contained a flush marker. Only a bare `; FLUSH_START` / `; FLUSH_END` line counts now, and the settings block is skipped.
- Settings, booking state, stats history and printer codes that cannot be read (for example a file left half written by a crash) are kept as `<name>.bad` instead of being replaced by the next save, so the history can be merged back by hand. Printer codes are now written in one step, private (0600) before they take their real name.

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
