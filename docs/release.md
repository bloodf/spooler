# Releases and the Orca Cloud listing

## Cutting a release

1. Bump the version in the PEP 723 block of `plugin/spooler/__init__.py`, `PLUGIN_VERSION` in `plugin/spooler/core.py`, and `ui/package.json` and its lockfile, date the CHANGELOG section, and rebuild the page with `npm --prefix ui run build` (it writes `plugin/spooler/app.html`).
2. Push a `v<version>` tag. `release.yml` runs the tests, builds `spooler_any.whl` and opens a draft GitHub release with the notes from CHANGELOG.md.
3. Publish the draft. `publish-orcacloud.yml` then publishes that version to Orca Cloud.

The draft release also carries the 512 px store tile, copied from `assets/orca-cloud/spooler-tile.png`.

## The listing

Paste the text from [orca-cloud-description.md](orca-cloud-description.md): the English block into the English description and the Portuguese block into the Portuguese one. Each block is under 4000 characters.

| File | Used for | Size |
|---|---|---|
| `assets/orca-cloud/spooler-tile.png` | Store tile | 512 x 512 |
| `assets/orca-cloud/spooler-main-en.png`, `spooler-main-pt-BR.png` | Main image | 1600 x 900 |
| `assets/orca-cloud/spooler-feature-01-stock-*.png` to `spooler-feature-04-check-*.png` | Gallery and the four feature images in the description | 1600 x 900 |
| `assets/orca-cloud/spooler-main-square-*.png` | Square image | 900 x 900 |
| `assets/social/spooler-social-preview-*.png` | GitHub social preview (Settings > Social preview) | 1280 x 640 |
| `assets/readme/spooler-hero-{light,dark}-*.png` | README heroes | 1600 x 900 |

Every export is under 2 MB. `assets/marketing/asset-manifest.json` records each one with its source, operation, size, bytes and date. The generated originals are in `assets/marketing/source/`; `python scripts/store_images/render.py` rebuilds the exports from them with screenshots of the real page.

The install pictures used by [install.md](install.md) are in `assets/orca-cloud/install/` and come from `python scripts/store_images/install_guide.py`.
