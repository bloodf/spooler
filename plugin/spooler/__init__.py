# /// script
# requires-python = ">=3.12"
# dependencies = []
#
# [tool.orcaslicer.plugin]
# name = "Spooler"
# description = "Spoolman inventory for OrcaSlicer: auto-synced filament profiles and live printer slots"
# author = "bloodf (fork of Spoolio by Dan J Moore)"
# version = "0.35.0"
# ///

# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""Spooler, an OrcaSlicer plugin: the package OrcaSlicer imports.

The code is split by domain into the modules below, and app.html next to them is the compiled page. A module
imports the modules its top level needs first, and the ones its functions only call at its end, so any import order
works. The PEP 723 block above carries the name, version and description scripts/build.py writes into the wheel's
METADATA; PLUGIN_VERSION in core.py must match it (scripts/check_version.py).
"""

from . import (  # noqa: F401
    anycubic,
    capabilities,
    core,
    editor,
    filament_profiles,
    filmatch,
    i18n,
    live_updates,
    moonraker,
    netprinters,
    peers,
    plate_check,
    printers,
    rfid,
    sources,
    spoolman_sync,
    stats,
    tab,
    ui_build,
    windows,
)
from .capabilities import SpoolerPlugin  # noqa: F401  (the class OrcaSlicer registers)
