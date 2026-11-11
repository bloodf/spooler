# How Spooler works

A tour for contributors. Everything lives in `plugin/spooler/spooler_any.py`; the section comments
there (`# --- ... ---`) follow the same order as this page.

## Presets from Spoolman

OrcaSlicer's plugin API can't create presets, so Spooler writes them as a **local preset bundle**
and asks OrcaSlicer to reload it:

1. `load_spools()` reads the spools from Spoolman (or Bambu Cloud).
2. `profile_files()` makes one preset per stocked filament per printer. Each one inherits the
   closest preset OrcaSlicer already has for that printer (`best_parent()`), and carries the
   filament's colour, vendor, temperatures, density, diameter, cost, Spooler's calibration fields
   and its `orca_settings`.
3. `profile_sync()` writes them to `user/<account>/_local/spooler/` and calls
   `orca.host.preset.bundles.reload_local("spooler")`. A bundle OrcaSlicer refuses is retried
   only after `PROFILE_RETRY` seconds.

Only keys that exist in OrcaSlicer's `PrintConfig.cpp` go into a preset: one unknown key makes
OrcaSlicer refuse the whole bundle.

## Changes the other way

OrcaSlicer won't save over a plugin's preset, so edits reach Spoolman in two ways:

- **Unsaved edits** of a Spooler preset are read every 10 seconds while the tab is open
  (`auto_send()`), and sent once they have stayed the same for one tick.
- **A saved copy** of a Spooler preset (`PresetSaved`) has its changed settings sent too
  (`send_saved_copy()`).

`send_changes()` writes density, diameter and cost to Spoolman's own fields and everything else to
the filament's `orca_settings`, in the section for that printer. A value that changed in Spoolman
meanwhile is kept.

## Printers

Printers come from the host address on your OrcaSlicer printer presets (`auto_printers()`), plus
the ones added by hand for Bambu Live Link:

| Printer | How | Code |
|---|---|---|
| Snapmaker U1 | Moonraker `print_task_config` | `head_tray()` |
| Klipper filament changers | Moonraker `lane_data` | `lane_units()` |
| Other Klipper | Moonraker's Spoolman integration | `moon_report()` |
| Anycubic Kobra X | LAN mode MQTT/TLS | `kx_report()` |
| Bambu Lab | Live Link, MQTT/TLS + FTPS | `live_apply()` |

Each slot is matched to a spool in the same order: the spool id the printer reports, the location
u1control binds (U1 only), the RFID tag, then vendor, material and colour (`slot_tray()`).

## Working with u1control

On the Snapmaker U1, [u1control](https://github.com/bloodf/u1control) can run next to Spooler. They
share files in `<OrcaSlicer data folder>/spooler/`:

- `profiles.json`: every Spooler preset by filament and printer, so u1control picks the same one.
- `keep_slots.json`: refreshed while Keep Slots Synced runs, so u1control leaves the slots alone.

u1control binds a toolhead's spool as the Spoolman location `<printer name> T<n>`. Spooler reads
locations and changes one only when you move a spool from its card (with a second click when
that unlinks a toolhead), and books no filament use on the U1: u1control does that.

## Testing without OrcaSlicer

`tests/plugin_loader.py` imports the plugin with a stand-in `orca` module and points its data folder
at a temporary one. `tests/fake_bundle.py` answers like OrcaSlicer's preset bundle. Printer and
Spoolman answers in `tests/fixtures/` were captured from real devices.
