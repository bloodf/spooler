# Releases and the Orca Cloud listing

## Cutting a release

1. Bump the version in the PEP 723 block of `plugin/spooler/__init__.py`, `PLUGIN_VERSION` in `plugin/spooler/core.py`, and `ui/package.json` and its lockfile, date the CHANGELOG section, and rebuild the page with `npm --prefix ui run build` (it writes `plugin/spooler/app.html`).
2. Push a `v<version>` tag. `release.yml` runs the tests, builds `spooler_any.whl` and opens a draft GitHub release with the notes from CHANGELOG.md.
3. Publish the draft. `publish-orcacloud.yml` then publishes that version to Orca Cloud.

The draft release also carries the 512 px store tile, copied from `assets/orca-cloud/spooler-tile.png`.

## The listing

Paste the English block from [orca-cloud-description.md](orca-cloud-description.md) into the description. The listing is English only, well under 4000 characters, and links to [README.md](../README.md) for the full description. The four gallery images are also embedded in the description.

| Slot | File | Size | Bytes |
|---|---|---|---|
| Store tile | `assets/orca-cloud/spooler-tile.png` | 512 x 512 | 203,971 |
| Main image | `assets/orca-cloud/spooler-main-en.png` | 1600 x 900 | 1,300,802 |
| Square image | `assets/orca-cloud/spooler-main-square-en.png` | 900 x 900 | 848,899 |
| Gallery 1: every spool in one list | `assets/orca-cloud/spooler-feature-01-stock-en.png` | 1600 x 900 | 1,338,162 |
| Gallery 2: stock becomes filament presets | `assets/orca-cloud/spooler-feature-02-presets-en.png` | 1600 x 900 | 1,323,926 |
| Gallery 3: what each slot holds | `assets/orca-cloud/spooler-feature-03-slots-en.png` | 1600 x 900 | 1,325,479 |
| Gallery 4: check filament before a print | `assets/orca-cloud/spooler-feature-04-check-en.png` | 1600 x 900 | 1,343,000 |
| GitHub social preview (Settings > Social preview) | `assets/social/spooler-social-preview-en.png` | 1280 x 640 | 832,352 |
| README hero, dark | `assets/readme/spooler-hero-dark-en.png` | 1600 x 900 | 1,323,118 |
| README hero, light | `assets/readme/spooler-hero-light-en.png` | 1600 x 900 | 1,323,029 |

Only English images are exported now. The older Portuguese gallery, hero and screenshot files stay because README.pt-BR.md uses them.

Every export is under 2 MB. `assets/marketing/asset-manifest.json` records each one with its source, operation, size, bytes and date. The generated originals are in `assets/marketing/source/`; `python scripts/store_images/render.py` rebuilds the exports from them with screenshots of the real page.

The install pictures used by [install.md](install.md) are in `assets/orca-cloud/install/` and come from `python scripts/store_images/install_guide.py`.
