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

**4. Enter your Spoolman address.** A Spooler tab appears in the top bar and opens on its Settings page on first run. Enter your Spoolman server address (for example `http://raspberrypi.local:7912`), click Test, and once the connection is confirmed click Save & Close.

![The Spooler tab in the top bar, with Test and Save & Close highlighted](install/04-spooler-tab.png)

The images are drawn illustrations, simplified, not screenshots.

## Manual install

Download the file for your system from the latest release on GitHub:

| System | File |
|---|---|
| Windows (x86_64) | `spooler_win_x86_64.py` |
| Windows (arm64) | `spooler_win_arm64.py` |
| Linux (x86_64) | `spooler_linux_x86_64.py` |
| Linux (arm64) | `spooler_linux_arm64.py` |
| macOS (Apple silicon) | `spooler_macosx_arm64.py` |
| macOS (Intel) | `spooler_macosx_x86_64.py` |

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

<!-- existing feature sections follow -->
