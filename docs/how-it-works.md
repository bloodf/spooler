# How Spooler works

A tour for contributors. Everything lives in `plugin/spooler/spooler_any.py`; the section comments
there (`# --- ... ---`) follow the same order as this page.


## The page

The tab, the spool window and the Settings window show one Vue 3 + PrimeVue 4 page (the shared Orca UI
foundation, vendored in `ui/shared/`). `ui/` builds it into a single offline HTML file; `scripts/embed_ui.py`
stores it zlib-compressed at the end of `spooler_any.py`, so the plugin is still one file. `page_html()` fills
the boot JSON: which surface (`tab`, `main`, `settings`), the saved settings, the host language and the
user's language choice (`ui_language` in the settings file). The message contract with the plugin is the
same as before: the Settings view tags its messages `view: "settings"` inside the tab.

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
   only after `PROFILE_RETRY` seconds. The files of the last accepted bundle are read first and
   put back when writing or the reload fails (`bundle_files()`, `restore_bundle()`); its digest
   and `profiles.json` only change once OrcaSlicer took the new one.

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
meanwhile is kept: the filament is read again just before the PATCH and the edit is merged
three-way (`merge_settings()`, removals included). From Spoolman 0.26, which merges a PATCH's
extra map key by key, only `orca_settings` is sent; older versions get the whole map back as just
read. Spoolman has no precondition for a PATCH, so a change landing between that last read and the
write can still be overwritten: the merge narrows the window, it doesn't close it.

## One source per operation

Spoolman ids are only unique inside one server. A send, a card action, a booking or a refresh
pins the source it started on (`pinned_origin()`): every request goes to that address, and once
the source or address in Settings changes (`current_origin()` bumps a generation and drops the
cached spools and preset names), it stops before its next request with `OriginChanged`. Lists
sent to the page carry the generation, and the page sends it back with card actions, bookings and
Change Spool, so ids picked from an old list are refused.

## Booking filament use

Only Bambu Live Link prints are booked here (`usage_track()` skips `auto-` printers: u1control
books the U1 and Moonraker books other Klipper printers). Each booked print records the Spoolman
it belongs to and is only booked there; prints recorded before that are left for booking by hand.
Each row is saved as `sending` before its request (`_send_row()`); a request that may have been
applied (timeout, dropped connection, server error) or a state that couldn't be saved leaves the
row `unknown`, which is never sent again by itself: the page asks you to check Spoolman and say
whether it was applied. Undo adds the grams back with `PUT spool/<id>/use` and a negative weight,
one SQL update on Spoolman's side, and is refused unless Spoolman reports 0.18 or newer.
`usage.json` and `history.json` are written in one step (`_write_json()`).

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

Moonraker and Anycubic report every slot each time, so their reports replace the printer's units
(`live_apply(..., full=True)`); Bambu reports are deltas and are merged. MQTT packets over
`MQTT_MAX` bytes or with a malformed length are refused before their body is read, and a packet
must arrive whole within `PACKET_SECS`.

Each slot is matched to a spool in the same order: the spool id the printer reports, the location
u1control binds (U1 only), the RFID tag, then vendor, material and colour (`slot_tray()`).

Single-extruder Klipper printers can have their active spool changed from the Printer tab
(`moon_set_spool()`, which posts to Moonraker's `/server/spoolman/spool_id`). It checks the printer
again first and refuses the U1 and lane printers.

### Anycubic debug capture

Booking Anycubic prints needs their print-status messages, which aren't documented. Add
`"kx_capture": true` to Spooler's settings file (`spooler_settings.json` in Spooler's data folder; there
is no switch for it in Settings) and restart OrcaSlicer. Each Anycubic session then logs every
MQTT message type once (`kx_capture()`): its keys and a sample with serials, tokens, addresses and
credentials replaced (`kx_redact()`), and asks for the `info` report every 20 seconds. Remove the
key to stop. See [kobra-booking.md](kobra-booking.md).

## Working with u1control

On the Snapmaker U1, [u1control](https://github.com/bloodf/u1control) can run next to Spooler. They
share files in `<OrcaSlicer data folder>/spooler/`:

- `profiles.json`: every Spooler preset by filament and printer, so u1control picks the same one.
- `keep_slots.json`: refreshed while Keep Slots Synced runs, so u1control leaves the slots alone.

u1control binds a toolhead's spool as the Spoolman location `<printer name> T<n>`. Spooler reads
locations and changes one only when you move a spool from its card (with a second click when
that unlinks a toolhead), and books no filament use on the U1: u1control does that.

### Presence and the stock list

OrcaSlicer's plugin API can't list loaded plugins, pass messages between them or hide a tab; its
data folder is shared by all plugins. So from load to unload Spooler rewrites
`<OrcaSlicer data folder>/spooler/presence.json` every 5 seconds (`"state": "active"`, a new
`session` per load, the process id and the Spoolman address without user name or password), and
says `"stopped"` when it unloads. OrcaSlicer calls `on_load` even when the Spooler page is turned
off in its Plugins dialog, so presence keeps running then.

u1control does the same in `<OrcaSlicer data folder>/u1control/presence.json`. Only while that
file is active, fresh (20 s), of this OrcaSlicer process and asks for the stock (its tab shows it)
does Spooler write `stock.json` next to its presence: the live spools from its own Spoolman reads,
with low stock and "use first", at most every 30 s or when u1control asks for a refresh. That read
creates no fields and writes nothing to Spoolman or a printer. u1control links a spool to a
toolhead with its own commands and checks; Spooler's role ends at the list. The full contract is
in u1control's `docs/spooler-contract.md`.

Each `spools` message to Spooler's page also carries `peers.u1control` (true only while U1 Control's
presence file is active in this OrcaSlicer process) and, when the list could not be read, an
`error_code` (`no_url`, `read_failed`). Spooler's "set the printer's spool" (Moonraker active spool)
refuses the U1: it has toolheads, so U1 Control's location binding is the only way a U1 spool is set.

## Testing without OrcaSlicer

`tests/plugin_loader.py` imports the plugin with a stand-in `orca` module and points its data folder
at a temporary one. `tests/fake_bundle.py` answers like OrcaSlicer's preset bundle. Printer and
Spoolman answers in `tests/fixtures/` were captured from real devices.
