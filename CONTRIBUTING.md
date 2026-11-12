# Contributing to Spooler

Thanks for helping. Spooler is a small project, and bug reports, printer data and pull requests all
make a real difference.

## Ways to help

- **Report a bug** with the [bug form](../../issues/new?template=bug_report.yml). The end of
  `spooler.log` (its path is at the bottom of Spooler's Settings page) is the most useful thing
  you can attach.
- **Add a printer.** Most printer support starts from what the printer reports. A Moonraker
  `printer/objects/query` answer, an Anycubic MQTT report or a Bambu `pushall`, with serials and
  codes removed, lets us write a test fixture and support it without the printer.
- **Send a pull request.** Small, focused changes with a test are the easiest to review.

## The code

- `plugin/spooler/spooler_any.py` is the whole plugin: one Python file with the
  compiled Vue page embedded as a compressed string. It stays one file on purpose: OrcaSlicer installs a single file,
  and it keeps merges from [Spoolio](https://github.com/danm1989/spoolio-orcaslicer) possible.
- `tests/` runs it outside OrcaSlicer, with a stand-in for OrcaSlicer's `orca` module
  (`tests/plugin_loader.py`) and a fake preset bundle (`tests/fake_bundle.py`). Fixtures in
  `tests/fixtures/` are real printer and Spoolman answers.
- `scripts/build.py` writes the per-OS files Orca Cloud expects to `dist/`, plus an all-OS wheel.
- `scripts/store_images/render.py` renders the README and store images from the real page.
- [docs/how-it-works.md](docs/how-it-works.md) explains the presets, the sync and the files
  Spooler shares with other plugins.

## Setting up

You need Python 3.12 or newer. There are no runtime dependencies. Development also needs Node.js 24, npm and Chrome/Chromium
for the offline Vue build and browser tests, plus [ruff](https://docs.astral.sh/ruff/) for Python lint.

```sh
WORKERS=1 python -m unittest discover -s tests   # every test (page tests need Node.js 22.6+ and Chrome or Chromium)
npm --prefix ui ci && npm --prefix ui run build       # after changing the page: rebuilds and embeds it in spooler_any.py
ruff check plugin scripts tests        # lint
python scripts/check_version.py        # the two version numbers agree
python scripts/build.py                # dist/: the per-OS files and the wheel
```

CI runs the tests on Windows, macOS and Linux (x86_64 and arm64) and the lint on every pull request.

### Trying it in OrcaSlicer

Install OrcaSlicer 2.5 or later and install the `dist/` file for your OS (or
`plugin/spooler/spooler_any.py`) from OrcaSlicer's Plugins dialog, the same way as a downloaded
plugin. Remove the Orca Cloud copy first so the two don't clash. The log is at the path shown on
Spooler's Settings page.

## Pull requests

- Add a test for the behaviour you change. A bug fix should come with a test that fails without it.
- Keep `ruff check` clean and the tests green on every OS.
- Add a line to [CHANGELOG.md](CHANGELOG.md) under the newest `Unreleased` section, in the same
  style: what changes for the person using Spooler.
- Write commits as [Conventional Commits](https://www.conventionalcommits.org/)
  (`feat:`, `fix:`, `docs:` ...).
- If the page changes, re-render the images with `python scripts/store_images/render.py`.
  Build the Vue page with `npm --prefix ui run build` first. The renderer needs Node 24+ and Chrome;
  use `--out /tmp/spooler-artwork` to preserve existing artwork. Captures use mock data with network
  access blocked and fail if the page cannot render. Failure evidence is saved beside the output.
- OrcaSlicer refuses a whole preset bundle when one preset has a key it doesn't know, so only add
  preset keys that exist in OrcaSlicer's `PrintConfig.cpp` (`tests/test_profiles.py` checks the list).

## Releases

Maintainers release by bumping the version in both places at the top of `spooler_any.py`, dating
the CHANGELOG section, matching the `ui/package.json` and lockfile versions, rebuilding the embedded
page, and pushing a `v<version>` tag. The release workflow tests, builds and opens a
draft GitHub release; publishing it uploads the build to Orca Cloud.

## Conduct

Everyone taking part follows the [code of conduct](CODE_OF_CONDUCT.md).
