# Spooler user guide

Every setting, rule and limit, in the order you meet them. The [README](../README.md) is the short
version; [install.md](install.md) has the install pictures.

## First run

The Spooler tab opens on its Settings page on first run, with a setup guide over it:

1. **Welcome to Spooler.** Your Spoolman spools become OrcaSlicer filament presets, and your printers' slots are shown.
2. **Choose your source.** Enter your Spoolman server address (for example `http://raspberrypi.local:7912`) and click **Test**. **Next** unlocks once the connection is confirmed.
3. **Permissions.** See below.
4. **Your presets.** Where they appear, and that they follow Spoolman every minute.
5. **Printers.** How they are found, and what **Plugins > Run > Spooler: Load Printer Filaments** does.
6. **You're set.** Optional extras, then **Save & finish** saves the settings and takes you to your spool list.

**Next** and **Back** move between steps, **Skip the guide** (or Escape) closes it, and **Open the
setup guide** in Settings brings it back. The guide appears by itself only when no source is set up
yet, so it never shows for an existing setup. The Settings page also holds the low-stock threshold,
the cart button and how weights are shown; reopen it any time from the **Settings** tab.

### Bambu Cloud as the source

Choose **Bambu Cloud** under **Choose your source**, enter your Bambu email and password, pick
Global or China, and enter the verification code if Bambu asks for one. Spooler never stores your
password, only the sign-in token Bambu returns, and **Sign out** removes it. See
[Bambu Cloud limits](#bambu-cloud-limits).

### Permissions

OrcaSlicer asks before a plugin does anything sensitive. Granting Spooler full access in the
permission dialog avoids repeated prompts; otherwise each new address it reads (Spoolman and each
printer) is approved once and remembered. Expect a prompt the first time the plugin connects to
Spoolman, Bambu Cloud or a printer, the first time it writes the filament presets into OrcaSlicer's
user folder, and the first time you click a reorder cart to open your browser.

## Filament presets

For each of your printers, every Spoolman filament with a spool in stock shows up under **User
presets** in the sidebar's filament dropdown, for example `3D Procer PLA Pérola @Snapmaker U1` and
`3D Procer PLA Pérola @Sovol SV06`. Pick it for a slot and OrcaSlicer sets the slot to the
filament's colour, so there are no colours to edit and no profiles to clone.

"Your printers" are the printers behind every printer preset with a host address (Printer settings >
Connection), plus the printer currently selected.

Each preset inherits the closest preset OrcaSlicer already has for that printer, so the printer's
own tuning is kept: Snapmaker SnapSpeed spools on the U1 get `Snapmaker PLA SnapSpeed @U1`, other
PLA gets `Generic PLA @U1 0.4 nozzle`, silk gets the silk preset, and so on. The vendor's own preset
wins when OrcaSlicer has one.

On top of that it carries the filament's colour, vendor, nozzle and bed temperatures (the bed
temperature on every plate type), density, diameter and cost from Spoolman (the filament's price,
else the mean price per kg of its spools in stock).

The presets follow Spoolman: new filaments appear, filaments whose spools are all archived
disappear, and changes are picked up on each refresh (every 60 seconds while the Spooler tab is
open). **Sync Presets** in the bar at the top does it at once and rebuilds every preset, even when
nothing changed.

### Calibrated settings

Add a text extra field `orca_settings` to filaments in Spoolman (Settings > Extra Fields) and put a
JSON object of OrcaSlicer filament settings in it, either for every printer or in sections named
after part of a printer preset's name, `*` for all:

```json
{"*": {"filament_flow_ratio": "0.98"}, "Snapmaker U1": {"filament_max_volumetric_speed": 20}}
```

Supported: flow ratio, max volumetric speed, pressure advance, retraction length and speeds, Z hop,
ironing flow, speed, spacing and inset, nozzle and plate temperatures, the nozzle temperature range,
chamber temperature, fan speeds (also overhang and auxiliary fan, layers with the fan off and the
full-speed layer), slow-down settings, minimal purge on the wipe tower, shrinkage (also in Z),
softening temperature, density, diameter, cost and notes. Other keys are ignored (Spooler's log
names each one once), and so is text that isn't one number (say `"0,95"`) for a number setting.

Spooler adds three number fields to Spoolman's filament form, **Flow ratio**, **Pressure advance**
and **Max volumetric speed**, for the values people calibrate most. They apply to every printer; a
value in `orca_settings` wins over them.

### Sending a change back to Spoolman

Edit a Spooler preset in OrcaSlicer's filament settings and leave it a few seconds: while the
Spooler tab is open the change is sent to Spoolman by itself. **Send Preset Edits to Spoolman** on
the Spools tab sends it at once. Density, diameter and cost go to Spoolman's own fields; the other
settings go into the filament's `orca_settings` field, in the section for that preset's printer (the
field is created when Spoolman doesn't have it). The presets are then rebuilt, so the preset keeps
your change and shows no unsaved changes.

A setting changed in Spoolman meanwhile keeps Spoolman's value and stays unsaved in OrcaSlicer, for
you to send again or discard. Colour, vendor, material and name are changed in Spoolman. To send
only by hand, set `"auto_send": false` in Spooler's settings file.

OrcaSlicer's Save on a Spooler preset makes a separate copy that no longer follows Spoolman. Spooler
shows that copy's changed calibration settings at the top of the Spooler tab, with Spoolman's value
and the new one. Save to Spoolman writes them, so the Spooler preset has them after its next rebuild;
Skip leaves Spoolman alone and isn't asked again for the same values. Settings > Spool source >
"Save calibrated values to Spoolman" can make this Automatically or Never instead.

## Spools tab

Each spool is one row: its drawn spool in the filament's colours, material, state chips and what is
left. Spools of the same filament (vendor, name and colour) fold into one row with their total;
click it to see each spool. Click a spool and its detail opens beside the list.

The search box matches name, location, lot number and comment, and `#12` finds spool 12. Beside it
sit a material filter and a colour filter that picks a colour family from swatches. **Filters**
opens the rest: manufacturer, grouping, sorting, **Show archived** (archived spools are listed
dimmed, and still never count for presets, the filament check or the printer slots) and **Closest
colour**, a picker that lists the 12 nearest spools.

Each row can show the spool's Spoolman comment, lot number and your own extra fields on a muted line
(hover for the full text). Settings > **Display** switches each part of the spool list and of the
printer slots on or off; printer slots can show the loaded spool in full (manufacturer, grams left,
spool number, location, preset).

A spool added, changed, used or deleted in Spoolman shows on the Spools tab within a second or two,
over Spoolman's WebSocket; the 60 second refresh stays as the fallback.

### Spool detail and actions

The detail shows what is left, how long it lasts at the current rate, the prints that used the
spool, the grams and cost booked, and the weekly use over the last 4 weeks. With Spoolman as the
source it also holds the actions:

| Action | What it does |
|---|---|
| **Set weight from scale** | Weigh the spool and enter the gross weight. Needs the spool's empty weight (or the filament's) in Spoolman. |
| **Use filament** | Subtract grams by hand. |
| **Set grams left** | Type the filament left when you have no scale, 0 for an empty spool. Needs the spool's initial weight (or the filament's). |
| **Add a note** / **Edit note** | The spool's Spoolman comment, say "dry before use"; empty removes it. |
| **Move** | Pick one of Spoolman's locations or type a new one. |
| **Mark dried today** | Stores today's date in a Spoolman field (added on demand). |
| **Add a spool of this filament** | 1 to 20 at once, for a multi-pack. |
| **Archive** / **Unarchive** | Takes the spool out of the stock, or brings it back. |
| **Open in Spoolman** | Opens the spool's page in your browser. |

Archiving and adding ask for a second click; so does moving a spool off a U1 toolhead's location,
since that unlinks it in U1 Control.

### Low stock and Use first

A low-stock notification appears in OrcaSlicer when a spool crosses your threshold (once per
crossing, none at start-up). Opened spools of a filament with several spools get a **Use first**
chip on the oldest, to finish it first. Chip and notification each switch off in Settings >
**Display**.

### Drying reminder

**Mark dried today** stores the date in a Spoolman field and the spool shows **Dried 12 d ago**,
amber once it is past the days set for that material in Settings > **Drying reminders** (PETG 30,
TPU 14, PA 7, PVA 7, PC 14 by default; PLA, ABS and ASA off). The after-slice notice mentions a
loaded spool of such a material that was dried too long ago or never. Spoolman only, and the notice
checks the fullest matching spool of each slot.

## Printer tab

The **Printer** tab sits beside **Spools** and shows a panel for each of your printers. Any printer
preset with a host address appears there with no further setup:

| Printer | What is shown | How spools are matched |
|---|---|---|
| Snapmaker U1 | All four toolheads | By the spool id the printer reports, else by RFID tag, else by vendor, material and colour |
| Klipper with a filament changer run by AFC, Happy Hare or another tool that writes Moonraker's `lane_data` (for example Elegoo Centauri Carbon with CANVAS on OpenCentauri) | Every lane | By the spool id the lane reports, else by vendor, material and colour |
| Single-extruder Klipper (for example Sovol SV06 with Klipper) | The spool Moonraker's Spoolman integration has marked as active | It is that spool |
| Anycubic Kobra X, and other Anycubic printers in LAN mode | Each slot of the multi-colour box (ACE) and the external spool | By material and colour |

For an Anycubic printer, turn on LAN mode on the printer and put its IP address in the printer
preset's host field. Hover a slot to see which OrcaSlicer preset matches it. Hosts that aren't
Moonraker are ignored.

On a single-extruder Klipper printer, **Change spool** picks another non-archived spool and
**Clear** unsets it, so Moonraker books the next print to the right spool. While the printer prints
or is paused it asks first, since Moonraker would then book the rest of that print to the new spool.
Not offered on the U1 or on filament changers, which manage their own spools.

### Printers you add yourself

Click **+ Add printer**, then add an AMS or an external spool to match your setup, and assign which
of your spools is in each slot. This is stored in Spooler only and nothing is changed in Spoolman or
Bambu Cloud. With Bambu Cloud, spools your library has linked to a slot also show, but that can lag
behind what is physically loaded.

### Live Link

To read a Bambu printer directly, press **Live Link** on its panel and enter its IP address, its
serial number (optional, Spooler reads it from the printer's certificate when left blank) and its
access code, all found in the printer's network settings with LAN mode on. The slots then show what
the printer reports and how long ago it was updated. Spooler keeps the access code in a private file
on your computer and only reads from the printer. Removing a printer also removes its Live Link.

Live Link also takes a PrusaLink printer (the address, username and password shown on the printer
under Settings > Network > PrusaLink) or an OctoPrint one (an application key). These report
progress but not their spools, so their toolheads stay assigned by hand.

### Putting the loaded filament on the plate

**Plugins > Run > "Spooler: Load Printer Filaments"** puts the preset for the filament each toolhead
or lane holds into the plate's filament slots, for the printer currently selected.

**Plugins > Run > "Spooler: Keep Slots Synced"** does the same and keeps doing it. When it starts,
and whenever a lane's spool changes, the lane's slot gets the Spooler preset. A slot that gets a
system preset (OrcaSlicer's own Sync filaments assigns those) gets the Spooler preset back; one of
your own presets stays until the lane's spool changes. Each change goes through OrcaSlicer's normal
preset selection, so it can ask about unsaved changes in the filament settings. Run it once per
OrcaSlicer session; run it again to stop it.

Off by default: Settings > Printer > **Keep the plate's filament slots synced automatically**
(`auto_keep_slots`, also in Plugins > Spooler > Config) starts the same sync by itself once
OrcaSlicer has opened, so you don't run it every session. Running the action while it is on stops it
until OrcaSlicer restarts; untick the setting to turn it off for good.

## Filament check

After each slice, Spooler compares the filament the plate needs with what is left on your spools.
You get a short-lived notification when there is enough, and one that stays until you dismiss it
when there may not be enough filament loaded.

To use it, switch on **Spooler Filament Check** in your process settings, under **Others > Slicing
Pipeline Plugin**. The results also appear in a **This plate** panel on the Printer tab, where
**Check again** runs it with fresh data and **Dismiss** hides it until the next slice. You can hide
the notifications and the panel, or change the safety margin (10% by default), on the Settings page.

- Each filament the plate uses is matched to spools in Spoolman by vendor, material and colour.
  Slots that hold the same filament are treated as one supply, because the AMS moves on to the next
  spool of the same filament when one runs out: their use is added together and compared with the
  spools' combined weight. Spare spools that aren't loaded never count towards it.
- If a matching spool is too low to cover the print, and you have another spool of that filament
  besides the one that is loaded, you get a warning to make sure the right spool is loaded. Archive
  finished spools in Spoolman so they aren't counted.
- If no spool matches, or Spoolman can't be reached, you get a short note and nothing else.
- Slicer figures are estimates and real use can differ a little, so the safety margin gives you
  headroom.

The notice adds what the print costs in filament when prices are in Spoolman, and when a slot is
short it suggests an unloaded spool of the same filament with enough left and where it is. The swap
suggestion only knows spools loaded in your saved printers or reported live by them.

## Filament usage booking

With Spoolman as your source and a Live Link on the printer, Spooler can book the filament a print
used. When a print finishes, it works out which spool was in each slot from the RFID tag, matching
it to your Spoolman spools by the `tag` extra field on the spool (or the long serial Bambu uses for
RFID detection), and books the grams from the sliced G-code to that spool. Under **When a print
finishes** choose **Ask me before booking**, **Book automatically** or **Don't track**.

Slots whose spool can't be identified, and prints that were cancelled (where the grams are estimated
from the progress), always have to be booked manually, and nothing is booked twice. PrusaLink,
OctoPrint and Klipper prints are always asked before booking, and Klipper prints are booked here
only when Moonraker's own Spoolman integration is off, otherwise the filament would count twice.
Bambu Cloud has no booking, as there is no way to write to its filament library.

## Stats tab

The Stats tab (from Spoolio) shows usage, cost and print history, and estimates how much of each
print went into supports and into purging and the prime tower: a **Wasted filament** tile, a
**Usage ratios** card with the three most wasteful prints, and a Waste column in **Print history**.
The estimate is read from the plate G-code in the job file on the printer, so it covers Bambu prints
booked after updating to 0.13.0.

It also has **On the shelf** (grams and money in stock, by material too; spools without a price
count as grams only), **Lost to failed prints** and an **Export to CSV** button on Print history,
which saves the selected period to an `exports` folder next to Spooler's settings and opens it.

Spool details, stock value and failed-print totals come from what Spooler booked, so they start
empty on a new install.

## Working with U1 Control

With [U1 Control](https://github.com/bloodf/u1control) installed, the Printer tab uses the spool
U1 Control bound to each toolhead (on stock firmware it is the spool's Spoolman location,
`Snapmaker U1 T1` and so on). Spooler publishes its preset names in
`<OrcaSlicer data folder>/spooler/profiles.json` so both pick the same preset, and while Keep Slots
Synced runs U1 Control leaves the plate's slots to it. Filament use on the U1 is booked by
U1 Control, not Spooler. The binding is found when U1 Control's printer name is Spooler's printer
label or model, or ends in "U1" (the default "Snapmaker U1", or for example "Workshop U1"); with two
U1s name them apart in U1 Control.

## Settings in the plugin manager

The settings are also in OrcaSlicer's plugin manager (Plugins > Spooler > Config), with Restore
defaults.

## Limits

- Needs a current OrcaSlicer with the plugin preset APIs (`orca.host.preset.bundles.reload_local`
  and `orca.host.preset.filament.begin_update`); tested against OrcaSlicer 2.5.0.
- OrcaSlicer documents assigning presets to the plate's slots as something a **Plugins > Run**
  action does, and gives plugins no way to change a slot's colour. "Load Printer Filaments" and
  "Keep Slots Synced" therefore set the right presets but leave the slot colours as they were;
  picking the filament in the slot's dropdown, or OrcaSlicer's own Sync filaments, sets the colour.
  The automatic Keep Slots Synced changes the slots from Spooler's own background thread instead;
  OrcaSlicer 2.5.0 accepts that in its code, but it is new and not yet confirmed in daily use. If
  OrcaSlicer refuses it, Spooler turns it off for the session, says so, and the Plugins > Run action
  still works.
- Generated presets are owned by Spooler and are rewritten from Spoolman. OrcaSlicer can't save over
  them: Save makes a separate user preset that no longer follows Spoolman. Use **Send Preset Edits
  to Spoolman** instead.
- Spool actions need Spoolman as the source; Bambu Cloud spools have none.
- Live list updates need Spoolman's WebSocket (`/api/v1/spool`) to be reachable from OrcaSlicer.
  Behind a reverse proxy, the proxy must pass the `Upgrade` and `Connection` headers (nginx:
  `proxy_set_header Upgrade $http_upgrade; proxy_set_header Connection "upgrade";`). Without it the
  list still refreshes every 60 seconds.
- Filament used by Anycubic prints is not booked to Spoolman yet: the printer's print-status
  messages must first be captured from a real print. See [kobra-booking.md](kobra-booking.md) if you
  have a Kobra and want to help.
- Filament usage on Klipper printers is best tracked by Moonraker's own
  [Spoolman integration](https://moonraker.readthedocs.io/en/latest/configuration/#spoolman).
- PrusaLink, OctoPrint and Klipper booking is built from the printers' API documentation and tested
  against simulated answers, not real printers yet.

### Bambu Cloud limits

- Unofficial and experimental. This uses Bambu's unofficial cloud service, which Bambu can change
  without notice. If it stops working, sign out and back in; if that still fails, please report it.
- The sign-in expires. Spooler keeps only the sign-in token, not your password, so when Bambu
  expires the token you'll be asked to sign in again from Settings.
- Spooler can only read your Bambu filament library, so nothing you do in Spooler changes your Bambu
  spools.
- Filament usage booking is only available with Spoolman. Spooler has no way to write used weight
  back to the Bambu library, and it is not verified whether being logged into Bambu Cloud tracks
  remaining weight itself for RFID spools.
- There is no live AMS through the cloud. A printer in LAN mode isn't bound to your account, so
  Bambu Cloud doesn't list it and sends no AMS data. Use **Live Link** (works with either source)
  for live slots, or assign spools by hand.
- The spools your library has linked to a slot are a representative view only and can differ from
  what is physically loaded.
- The Printer tab setup is local. Printers, AMS units and slot assignments you set up are stored in
  Spooler on your computer, not in your Bambu account.

### Live Link and booking limits

- Live Link needs the printer on the same network with LAN mode on, and only connects while the
  Printer tab is open or usage booking is on.
- The Stats tab's wasted-filament estimate needs the job file from a Bambu printer, so it only
  covers prints booked that way, made after updating to 0.13.0.
- Booking assumes the slicer's filament slots follow the order of the printer's slots (AMS 1 slots 1
  to 4, then the next AMS, and so on), so check the first few bookings if you use a different
  mapping.

## Acknowledgements

- [Spoolio](https://github.com/danm1989/spoolio-orcaslicer) by Dan J Moore, which this fork is built
  on, including its interface. Everything Spoolio already did is still there: the spool list, the
  Bambu Cloud source, Bambu Live Link, filament usage booking, the Stats tab and the after-slice
  filament check.
- [Spoolman](https://github.com/Donkie/Spoolman) by Donkie and contributors.
- [OrcaSlicer](https://github.com/OrcaSlicer/OrcaSlicer) by SoftFever and contributors.
- [q2-offload](https://github.com/cedbossneo/q2-offload), whose plugin showed the local preset
  bundle approach.

This is an independent project and is not affiliated with or endorsed by Spoolman, OrcaSlicer,
Snapmaker, Sovol, Anycubic or Bambu Lab.
