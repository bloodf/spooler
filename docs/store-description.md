<!-- Orca Cloud listing description. The images under install/ are uploaded as listing media; the file names below match assets/orca-cloud/install/. Regenerate them with scripts/store_images/install_guide.py. -->

# Spooler

Spooler turns your Spoolman spools into OrcaSlicer filament presets and shows what is loaded in each printer slot.

## Get started in 4 steps

**1. Subscribe.** Open the Orca Cloud Plugin Hub, find Spooler and click Subscribe. Updates arrive the same way.

![Orca Cloud Plugin Hub card for Spooler with the Subscribe button highlighted](install/01-plugin-hub.png)

**2. Refresh and activate.** In OrcaSlicer open File > Plugins, click Refresh, then tick Activate for Spooler.

![The Plugins dialog with Refresh (1) and Activate (2) highlighted](install/02-plugins-dialog.png)

**3. Allow the permissions.** OrcaSlicer asks before a plugin does anything sensitive. Granting Spooler full access in the permission dialog avoids repeated prompts. Otherwise each new address it reads (Spoolman and each printer) is approved once and remembered.

![A permission prompt for a network address with Allow highlighted](install/03-permission.png)

**4. Follow the setup guide.** A Spooler tab appears in the top bar and opens a short setup guide on first run. Enter your Spoolman server address (for example `http://raspberrypi.local:7912`), click Test, and Next unlocks once the connection is confirmed. The remaining steps cover permissions, presets and printers, and Save & finish takes you to your spool list. Skip it any time and reopen it from Settings.

![The Spooler tab in the top bar and the setup guide's address step with Test highlighted](install/04-spooler-tab.png)

The install pictures are drawn illustrations, simplified, not screenshots. The setup guide in the last picture is the real one.

## Manual install

Download `spooler_any.py` from the latest release on GitHub. It is the same file on Windows, macOS and Linux.

Place it in its own folder called `spooler` inside OrcaSlicer's plugin directory (one Spooler file per folder):

| OS | Plugin directory |
|---|---|
| Windows | `%APPDATA%\OrcaSlicer\orca_plugins\` |
| macOS | `~/Library/Application Support/OrcaSlicer/orca_plugins/` |
| Linux | `~/.config/OrcaSlicer/orca_plugins/` |

Restart OrcaSlicer, then tick Activate for Spooler.

![The orca_plugins/spooler folder with the plugin file and the three plugin directories](install/05-manual-install.png)

## How it works

1. Spooler reads your spools from Spoolman.
2. For each of your printers, every Spoolman filament with a spool in stock becomes a filament preset, for example `3D Procer PLA Pérola @Snapmaker U1`. Each preset inherits the closest preset OrcaSlicer already has for that printer, so the printer's own tuning is kept.
3. Pick the preset in the filament dropdown, under User presets. OrcaSlicer sets the slot to the filament's colour.
4. Plugins > Run > "Spooler: Load Printer Filaments" puts the preset for the filament each toolhead or lane holds into the plate's filament slots, for the printer currently selected.
5. After each slice, Spooler compares the filament the plate needs with what is left on your spools, if Spooler Filament Check is switched on in the process settings (Others > Slicing Pipeline Plugin).
6. With Spoolman as the source and a Live Link on the printer, Spooler can book the filament a print used to the spool that was in each slot. You choose whether it asks first, books automatically or does not track.

## Features

- **A setup guide for first use.** The first time you open Settings, a short step-by-step guide
  explains what Spooler does, takes your Spoolman address and tests it right there, and covers
  permissions, where the presets appear and how printers are found. Skip it any time, and reopen
  it from ***Open the setup guide*** in Settings.
- **Your Spoolman filaments become OrcaSlicer filament presets, one per printer.** For each of your
  printers, every Spoolman filament with a spool in stock shows up under ***User presets*** in the
  sidebar's filament dropdown, for example `3D Procer PLA Pérola @Snapmaker U1` and
  `3D Procer PLA Pérola @Sovol SV06`. Pick it for a slot and OrcaSlicer sets the slot to the
  filament's colour. No more editing colours or cloning profiles.
  - Each preset inherits the closest preset OrcaSlicer already has **for that printer**, so the
    printer's own tuning is kept: Snapmaker SnapSpeed spools on the U1 get
    `Snapmaker PLA SnapSpeed @U1`, other PLA gets `Generic PLA @U1 0.4 nozzle`, silk gets the silk
    preset, and so on. The vendor's own preset wins when OrcaSlicer has one.
  - On top of that it carries the filament's colour, vendor, nozzle and bed temperatures (the bed
    temperature on every plate type), density, diameter and cost from Spoolman.
  - Calibrated settings come along too: add a text extra field `orca_settings` to filaments in
    Spoolman (Settings > Extra Fields) and put a JSON object of OrcaSlicer filament settings in it,
    either for every printer or in sections named after part of a printer preset's name, `*` for
    all:
    `{"*": {"filament_flow_ratio": "0.98"}, "Snapmaker U1": {"filament_max_volumetric_speed": 20}}`.
    Supported: flow ratio, max volumetric speed, pressure advance, retraction length and speeds,
    Z hop, ironing flow, speed, spacing and inset, nozzle and plate temperatures, fan speeds,
    slow-down settings, shrinkage (also in Z), softening temperature, density, diameter, cost and
    notes. Other keys are ignored, and so is text that isn't one number (say `"0,95"`) for a number
    setting.
  - Spooler adds three number fields to Spoolman's filament form, ***Flow ratio***,
    ***Pressure advance*** and ***Max volumetric speed***, for the values people calibrate most.
    They apply to every printer; a value in `orca_settings` wins over them.
  - The presets follow Spoolman: new filaments appear, filaments whose spools are all archived
    disappear, and changes are picked up on each refresh (every 60 seconds while the Spooler tab
    is open).
  - "Your printers" are the printers behind every printer preset with a host address
    (Printer settings > Connection), plus the printer currently selected.
- **Change a preset in OrcaSlicer and it reaches Spoolman.** Edit a Spooler preset in OrcaSlicer's
  filament settings and leave it a few seconds: while the Spooler tab is open the change is sent
  to Spoolman by itself (or press ***Send to Spoolman*** on the Spools tab; never Save, which makes
  a copy that stops following Spoolman). Density, diameter and cost go to Spoolman's own fields;
  the other settings go into the filament's `orca_settings` field, in the section for that preset's
  printer (the field is created when Spoolman doesn't have it). The presets are then rebuilt, so
  the preset keeps your change and shows no unsaved changes. A setting changed in Spoolman
  meanwhile keeps Spoolman's value and stays unsaved in OrcaSlicer, for you to send again or
  discard. Colour, vendor, material and name are changed in Spoolman. To send only by hand, set
  `"auto_send": false` in Spooler's settings file.
- **Spool list:** spools of the same filament (vendor, name and colour) fold into one row with
  their total; click it to see each spool. The name filter and a colour filter, which picks a
  colour family from swatches, sit above the list.
- **Act on a spool from its card (Spoolman).** The ***⋯*** button on each spool card opens its
  actions: ***Set Weight From Scale*** (weigh the spool and enter the gross weight), ***Use
  Filament*** (subtract grams by hand), ***Move*** (pick one of Spoolman's locations or type a new
  one), ***Archive*** / ***Unarchive***, ***Add Spool of This Filament*** and ***Open in
  Spoolman***. Archiving and adding ask for a second click; so does moving a spool off a U1
  toolhead's location, since that unlinks it in u1control. ***Show archived*** in the filters
  lists archived spools, dimmed; they still never count for presets, the filament check or the
  printer slots.
- **You choose what's shown.** Settings > Display switches each part of the spool list and of the
  printer slots on or off; printer slots can show the loaded spool in full (manufacturer, grams
  left, spool number, location, preset).
- **Save a copy, keep the change.** OrcaSlicer's Save on a Spooler preset makes a separate copy;
  Spooler sends that copy's changed calibration settings to Spoolman, so the Spooler preset has
  them after its next rebuild.
- **Settings in OrcaSlicer's plugin manager** too (Plugins > Spooler > Config), with Restore defaults.
- **Works with u1control on the Snapmaker U1.** With [u1control](https://github.com/bloodf/u1control)
  installed, the Printer tab uses the spool u1control bound to each toolhead (on stock firmware it
  is the spool's Spoolman location, `Snapmaker U1 T1` and so on). Spooler publishes its preset names
  in `<OrcaSlicer data folder>/spooler/profiles.json` so both pick the same preset, and while Keep
  Slots Synced runs u1control leaves the plate's slots to it. Filament use on the U1 is booked by
  u1control, not Spooler. The binding is found when u1control's printer name is Spooler's printer
  label or model, or ends in "U1" (the default "Snapmaker U1", or e.g. "Workshop U1"); with two U1s
  name them apart in u1control.
- **Klipper/Moonraker printers are found for you.** Any printer preset with a host address appears
  in the ***Printer*** tab with no further setup:
  - **Snapmaker U1:** all four toolheads, matched to your Spoolman spools by the spool id the
    printer reports, else by RFID tag, else by vendor, material and colour.
  - **Klipper printers with a filament changer run by AFC, Happy Hare or another tool that writes
    Moonraker's `lane_data` (e.g. Elegoo Centauri Carbon with CANVAS on OpenCentauri):** every lane,
    matched to your Spoolman spools by the spool id the lane reports, else by vendor, material and
    colour.
  - **Single-extruder Klipper printers (e.g. Sovol SV06 with Klipper):** the spool Moonraker's
    Spoolman integration has marked as active.
  - **Anycubic Kobra X (and other Anycubic printers in LAN mode):** each slot of the multi-colour
    box (ACE) and the external spool, matched to your Spoolman spools by material and colour.
    Turn on LAN mode on the printer and put its IP address in the printer preset's host field.
  Hover a slot to see which OrcaSlicer preset matches it. Hosts that aren't Moonraker are ignored.
- **Plugins > Run > "Spooler: Load Printer Filaments"** puts the preset for the filament each
  toolhead or lane holds into the plate's filament slots, for the printer currently selected.
- **Plugins > Run > "Spooler: Keep Slots Synced"** does the same and keeps doing it. When it
  starts, and whenever a lane's spool changes, the lane's slot gets the Spooler preset. A slot that
  gets a system preset (OrcaSlicer's own Sync filaments assigns those) gets the Spooler preset back;
  one of your own presets stays until the lane's spool changes. Each change goes through
  OrcaSlicer's normal preset selection, so it can ask about unsaved changes in the filament
  settings. Run it once per OrcaSlicer session; run it again to stop it.
  New and off by default: Settings > Printer > **Keep the plate's filament slots synced
  automatically** (`auto_keep_slots`, also in Plugins > Spooler > Config) starts the same sync by
  itself once OrcaSlicer has opened, so you don't run it every session. Running the action while
  it is on stops it until OrcaSlicer restarts; untick the setting to turn it off for good.

- **Stats, with the filament you waste.** The Stats tab (from Spoolio) shows usage, cost and print
  history, and estimates how much of each print went into supports and into purging and the prime
  tower: a Wasted Filament tile, a Usage Ratios card with the three most wasteful prints, and a
  Waste column in Print History. The estimate is read from the plate G-code in the job file on the
  printer, so it covers Bambu prints booked after updating to 0.13.0.

Everything Spoolio already did is still there: spool cards, the Bambu Cloud source, Bambu Live
Link, filament usage booking, the Stats tab and the after-slice filament check.

## Limits

- Needs a current OrcaSlicer with the plugin preset APIs
  (`orca.host.preset.bundles.reload_local` and `orca.host.preset.filament.begin_update`);
  tested against OrcaSlicer 2.5.0.
- OrcaSlicer documents assigning presets to the plate's slots as something a ***Plugins > Run***
  action does, and gives plugins no way to change a slot's colour. "Load Printer Filaments" and
  "Keep Slots Synced" therefore set the right presets but leave the slot colours as they were;
  picking the filament in the slot's dropdown, or OrcaSlicer's own Sync filaments, sets the colour.
  The automatic Keep Slots Synced changes the slots from Spooler's own background thread instead;
  OrcaSlicer 2.5.0 accepts that in its code, but it is new and not yet confirmed in daily use. If
  OrcaSlicer refuses it, Spooler turns it off for the session, says so, and the Plugins > Run
  action still works.
- Generated presets are owned by Spooler and are rewritten from Spoolman. OrcaSlicer can't save
  over them: Save makes a separate user preset that no longer follows Spoolman. Use ***Send to
  Spoolman*** instead.
- Card actions need Spoolman as the source; Bambu Cloud spools have none. Set Weight From Scale
  needs the spool's empty weight (or the filament's) in Spoolman.
- Filament usage on Klipper printers is best tracked by Moonraker's own
  [Spoolman integration](https://moonraker.readthedocs.io/en/latest/configuration/#spoolman).

## Permissions

OrcaSlicer asks before a plugin does anything sensitive. Granting Spooler full access in the permission dialog avoids repeated prompts; otherwise each new address it reads (Spoolman and each printer) is approved once and remembered. Expect a prompt the first time the plugin connects to Spoolman, Bambu Cloud or a printer, the first time it writes the filament presets into OrcaSlicer's user folder, and the first time you click a reorder cart to open your browser.

## Credits and license

MIT license. Based on [Spoolio](https://github.com/danm1989/spoolio-orcaslicer) by Dan J Moore. This is an independent project and is not affiliated with or endorsed by OrcaSlicer, Spoolman, Snapmaker, Sovol, Anycubic or Bambu Lab.

