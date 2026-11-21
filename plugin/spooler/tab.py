# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""The tab icon, the page and the UI language."""

import base64
import json
import pkgutil
import re

import orca

from . import core as _core

LOGO_DATA_URI = (
    "data:image/svg+xml;base64,"
    "PHN2ZyB4bWxucz0iaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmciIHZpZXdCb3g9IjAgMCAyNTYg"
    "MjU2Ij4KPHJlY3QgeD0iMCIgeT0iMCIgd2lkdGg9IjI1NiIgaGVpZ2h0PSIyNTYiIHJ4PSI1NiIg"
    "ZmlsbD0iIzE0MTgxRiIvPjxnIGZpbGw9Im5vbmUiIHN0cm9rZS1saW5lY2FwPSJyb3VuZCIgc3Ry"
    "b2tlLWxpbmVqb2luPSJyb3VuZCI+CjxwYXRoIGQ9Ik0xODguMzYgMTA3LjY2QTc3IDc3IDAgMSAx"
    "IDExNiA1N0gyMTZNMjAxIDQyTDIxNiA1N0wyMDEgNzIiIHN0cm9rZT0iI0E5OUJGRiIgc3Ryb2tl"
    "LXdpZHRoPSIxNiIvPgo8cGF0aCBkPSJNODUuNTkgMTAzLjU5QTQzIDQzIDAgMCAxIDE0Ni40MSAx"
    "MDMuNTkiIHN0cm9rZT0iIzc4Q0ZENSIgc3Ryb2tlLXdpZHRoPSIxNCIvPgo8cGF0aCBkPSJNMTU3"
    "LjUzIDEyMi44N0E0MyA0MyAwIDAgMSAxMjcuMTMgMTc1LjUzIiBzdHJva2U9IiNGNENGNzgiIHN0"
    "cm9rZS13aWR0aD0iMTQiLz4KPHBhdGggZD0iTTEwNC44NyAxNzUuNTNBNDMgNDMgMCAwIDEgNzQu"
    "NDcgMTIyLjg3IiBzdHJva2U9IiNGRjk5N0QiIHN0cm9rZS13aWR0aD0iMTQiLz4KPGNpcmNsZSBj"
    "eD0iMTE2IiBjeT0iMTM0IiByPSIxNCIgc3Ryb2tlPSIjRjZGN0ZCIiBzdHJva2Utd2lkdGg9IjEw"
    "Ii8+CjwvZz4KPC9zdmc+Cg=="
)

# Tab icon: the brand tile (assets/orca-cloud/spooler-tile.png) at 40x40, white surround made transparent;
# the same bytes as assets/spooler-plugin-icon.png. OrcaSlicer draws it 20 px high. get_icon() must return the
# path of an image file; SVG markup or a data: URI shows no icon. OrcaSlicer drops the extension and tries .svg
# first, so the file needs a new name: the spooler_tab.svg older versions wrote would win over spooler_tab.png.
TAB_ICON_PNG = (
    "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"
)
TAB_ICON_FILE = _core.DATA_DIR / "spooler-icon.png"


def icon_path() -> str:
    try:
        png = base64.b64decode(TAB_ICON_PNG)
        if not TAB_ICON_FILE.exists() or TAB_ICON_FILE.read_bytes() != png:
            TAB_ICON_FILE.parent.mkdir(parents=True, exist_ok=True)
            TAB_ICON_FILE.write_bytes(png)
    except OSError:
        _core.log.exception("Could not write the tab icon to %s", TAB_ICON_FILE)
        return ""
    return str(TAB_ICON_FILE)


# The UI: one compiled Vue 3 + PrimeVue page (ui/, shared Orca UI foundation), written by scripts/embed_ui.py to
# app.html next to this file (spooler/app.html in the wheel); its hash, size and licences are at the end of this file. The native tab, the separate spool window and the separate Settings window all serve
# it; the boot JSON says which surface it is and carries the saved settings.
UI_LANGUAGES = ("auto", "en", "pt-BR", "es", "de", "zh-CN", "pl")
# OrcaSlicer's language codes ("pt_BR", "es", "de", "zh_CN", "zh_TW", "pl_PL") by their language part. Traditional
# Chinese takes the Simplified texts: closer to its reader than English. The page maps them the same way.
_LANGUAGE_OF = {"en": "en", "pt": "pt-BR", "es": "es", "de": "de", "zh": "zh-CN", "pl": "pl"}
_lang: dict = {"value": None}


def _read_page() -> str:
    """The page file: from the package (pkgutil reads it from a folder or a zip alike), else the file next to this one."""
    if __package__:
        data = pkgutil.get_data(__package__, "app.html")
        if data is None:
            raise FileNotFoundError("app.html is missing from the spooler package")
        return data.decode("utf-8")
    return (_core.PLUGIN_DIR / "app.html").read_text(encoding="utf-8")


# Read once, while the package imports, like the page that used to be inside the code. OrcaSlicer's sandbox checks
# every file a plugin opens during a capability call such as get_ui(), where a refused or failed read leaves the
# tab blank (0.32.1 to 0.32.3 read it there); a module import is not checked. An error is kept and shown instead.
try:
    _PAGE, _PAGE_ERROR = _read_page(), ""
except Exception as exc:  # noqa: BLE001 - shown on the error page, never raised at import
    _PAGE, _PAGE_ERROR = "", f"{type(exc).__name__}: {exc}"
    _core.log.exception("Could not read the page app.html")


def ui_page() -> str:
    """The served page, as read at import."""
    if _PAGE_ERROR:
        raise RuntimeError("Could not read the page app.html: " + _PAGE_ERROR)
    return _PAGE


def _json_for_html(data: object) -> str:
    """JSON safe inside a <script> block: no literal <, > or & can end it or open a tag."""
    return json.dumps(data).replace("<", "\\u003c").replace(">", "\\u003e").replace("&", "\\u0026")


def host_language() -> str | None:
    """OrcaSlicer's UI language (`orca.host.app_language()`, e.g. "pt_BR"), or None when the host doesn't offer it.
    The page and tr() map it to a language Spooler has, else English; an explicit choice wins."""
    try:
        attr = orca.host.app_language
        lang = attr() if callable(attr) else attr
    except Exception:  # noqa: BLE001 - an optional host call; the page has its own fallback
        return None
    return lang if isinstance(lang, str) and lang else None


def ui_language() -> str:
    value = _core.get_settings().get("ui_language")
    return value if value in UI_LANGUAGES else "auto"


def save_ui_language(value: object) -> None:
    """The page's language choice ("auto" or one of UI_LANGUAGES); anything else is ignored."""
    if value in UI_LANGUAGES:
        _core.update_settings({"ui_language": value})
        text_language(fresh=True)


def normalize_language(value: object) -> str | None:
    """A language code as one of Spooler's languages: "pt_BR" → "pt-BR", "es_ES" → "es", "de" → "de",
    "zh_CN" and "zh_TW" → "zh-CN", "pl_PL" → "pl", any English → "en"; None for the rest and for anything
    that isn't text."""
    if not isinstance(value, str):
        return None
    return _LANGUAGE_OF.get(re.split(r"[-_]", value.strip().lower())[0])


def text_language(fresh: bool = False) -> str:
    """The language of the texts worded in Python (notices, dialogs, action results, plate rows): the choice
    made on the page, else OrcaSlicer's language, else English. Kept after the first call, since worker
    threads word texts too; reading it again (fresh) happens on the UI thread: when a page is built and
    when the choice is saved."""
    if fresh or _lang["value"] is None:
        pref = ui_language()
        _lang["value"] = pref if pref != "auto" else normalize_language(host_language()) or "en"
    return _lang["value"]
