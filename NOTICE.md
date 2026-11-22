# Notice

Spooler is built on [Spoolio](https://github.com/danm1989/spoolio-orcaslicer) by Dan J Moore.

Copyright (C) 2026 Dan J Moore
Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors

Spooler is free software, licensed under the GNU General Public License version 3 (GPL-3.0-only), the licence of the Spoolio versions it is derived from. The full text is in [LICENSE](LICENSE). The third-party parts bundled in the page (Vue, PrimeVue, PrimeUIX, the Lucide icons and the Manrope font) keep their own licences, in `licenses/` of the [ui-foundation](https://github.com/bloodf/orca-ui-foundation) package (`ui/node_modules/@orca-plugins/ui-foundation/licenses/`).

It owes thanks to [Spoolman](https://github.com/Donkie/Spoolman), [OrcaSlicer](https://github.com/OrcaSlicer/OrcaSlicer) and [q2-offload](https://github.com/cedbossneo/q2-offload).

Spooler is an independent project, not affiliated with or endorsed by Spoolman, OrcaSlicer, Snapmaker, Sovol, Anycubic or Bambu Lab.

## Contributors

- Pablo Saura Sánchez ([@saurasanchezpablo](https://github.com/saurasanchezpablo)), #2: reading Klipper lanes from Moonraker's `lane_data`, keeping the plate's filament slots on the printer's lanes, sending OrcaSlicer preset edits to Spoolman's `orca_settings` field, and keeping Spoolman's other fields when sending.
- Jefferson J. Raimon ([@jeffersonraimon](https://github.com/jeffersonraimon)), #20: taking a preset's cost from its spool prices when the filament has none.

Both contributions were made under the MIT licence, while Spooler was MIT-licensed (before 0.29.1). Their copyright stays with their authors; they are part of Spooler under GPL-3.0-only, which the MIT licence allows. The MIT licence text follows.

> Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:
>
> The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
>
> THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

## Open Filament Database

With the **Open Filament Database** option on (Settings > Presets, off by default), Spooler reads preset data from the [Open Filament Database](https://openfilamentdatabase.org) at run time. None of it ships with Spooler. That data is Copyright © 2025 OpenFilamentCollective, under the MIT licence: <https://github.com/OpenFilamentCollective/open-filament-database/blob/main/LICENSE>.
