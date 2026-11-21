# Spooler - Spoolman inventory for OrcaSlicer, a fork of Spoolio
# Copyright (C) 2026 Dan J Moore
# Copyright (C) 2026 Heitor Ramon Ribeiro and Spooler contributors
# SPDX-License-Identifier: GPL-3.0-only

"""The Spooler tab and its windows: the page bridge."""

import json
import platform
import sys
import threading

import orca

from . import core as _core


class SpoolerWindow(orca.script.ScriptPluginCapabilityBase):
    def __init__(self):
        super().__init__()
        self._panel = None
        self._settings_window = None
        self._verified_url = ""
        self._verified_bambu = False
        self._release_url = ""
        self._refreshing = False
        self._testing = False
        self._checking_update = False

    def get_name(self):
        return _core.PLUGIN_NAME

    def _spoolman_url(self):
        return _core.get_settings().get("spoolman_url", "")

    def _save_settings(self, url, low_stock, plate_check=True,
                       plate_margin=_core.DEFAULT_MARGIN, weight="both", cart=False, src="spoolman",
                       progress=None, columns=None, stats=None):
        _core.sync_config(self)  # take a pending plugin-manager edit first, so this save wins over it
        settings = _core.settings_form(url, low_stock, plate_check, plate_margin, weight, cart, src, progress, columns, stats)
        if _core.update_settings(settings):
            _core.log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                     url, settings["low_stock_grams"], settings["plate_check"],
                     settings["plate_margin_percent"])
            _core.sync_config(self)
            return True
        orca.host.ui.message(
            _i18n.tr("Could not write settings to {file}. Check that this folder is writable.", file=_core.SETTINGS_FILE),
            title=_core.PLUGIN_NAME,
            icon="error",
        )
        return False

    def _after_save(self):
        self._open_panel()
        self._push_data()

    def _open_settings(self, page=None):
        if self._settings_window is not None and self._settings_window.is_open():
            return
        saved_url = self._spoolman_url()
        self._settings_window = orca.host.ui.create_window(
            html=_i18n.settings_html(
                saved_url,
                spoolman_info={"ok": False, "pending": True},
                source=_sources.source(),
                low_stock_grams=_core.parse_low(_core.get_settings().get("low_stock_grams")),
                plate_check=_core.plate_settings()[0],
                plate_margin=_core.plate_settings()[1],
                weight=_core.weight_mode(),
                cart=_core.cart_on(),
                progress=_core.progress_settings(),
                columns=_core.spool_columns(),
                stats=_core.stats_settings(),
                wizard=_core.wizard_pending(),
                page=page or "",
            ),
            title=_i18n.tr("{plugin} - Settings & About", plugin=_core.PLUGIN_NAME),
            width=_core.SETTINGS_SIZE[0],
            height=_core.SETTINGS_SIZE[1],
            on_message=self._on_settings,
            on_close=self._on_settings_close,
        )

    def _check_connection(self, url, window, src=None):
        if self._testing:
            return
        self._testing = True
        src = _sources.parse_source(src or _sources.source())

        def worker():
            info = _sources.bambu_ping() if src == "bambu" else _sources.ping(url)
            _sources.heard(_sources.BAMBU_KEY if src == "bambu" else url, info.get("ok"),
                  (info.get("account") or info.get("version")) if info.get("ok") else info.get("error"), sure=True)
            self._testing = False
            if src == "bambu":
                self._verified_bambu = bool(info.get("ok"))
            elif info.get("ok"):
                self._verified_url = _sources.clean_url(url)
            if window.is_open():
                window.post({"type": "test_result", "source": src, "url": url, **info, "requirements": _sources.requirements()})

        _filament_profiles.spawn(worker)

    def _bambu_sign_in(self, data, window):
        if data.get("action") == "sign_out":
            self._verified_bambu = False

        def worker():
            result = _sources.bambu_sign_in(data)
            if window.is_open():
                window.post({"type": "bambu_auth_result", **result})

        _filament_profiles.spawn(worker)

    def _on_settings(self, data):
        msg_type = data.get("type") if isinstance(data, dict) else None
        if msg_type == "page_error":
            _core.log_page_error(data)
        elif msg_type in ("ready", "requirements"):  # Check again: the same test, counted at once
            # Only check the connection once the page confirms its message
            # listener is registered, so the result can never arrive too early.
            if self._settings_window is not None:
                self._check_connection(self._spoolman_url(), self._settings_window)
        elif msg_type == "test":
            url = (data.get("url") or "").strip()
            if self._settings_window is not None:
                self._check_connection(url, self._settings_window, data.get("source"))
        elif msg_type == "save":
            _core.save_display(data.get("display"))
            _core.save_drying(data.get("drying"))
            _filament_profiles.save_presets(data.get("presets"))
            _capabilities.save_auto_keep(data.get("auto_keep_slots"))
            _capabilities.save_refresh(data.get("refresh_s"))
            _core.save_spool_view(data.get("spool_view"))
            _spoolman_sync.save_calibration_mode(data.get("save_calibration"))
            # The page already gates Save; enforce it here too.
            url = (data.get("url") or "").strip()
            src = _sources.parse_source(data.get("source"))
            verified = self._verified_bambu if src == "bambu" else _sources.clean_url(url) == self._verified_url
            if not verified:
                if self._settings_window is not None:
                    self._settings_window.post({
                        "type": "test_result",
                        "source": src,
                        "ok": False,
                        "url": url,
                        "error": _i18n.tr("Test the connection successfully before saving."),
                    })
                return
            saved = self._save_settings(url, data.get("low_stock"), data.get("plate_check"),
                                        data.get("plate_margin"), data.get("weight_display"),
                                        data.get("show_cart"), src, data.get("progress"),
                                        data.get("spool_columns"), data.get("stats"))
            if saved:
                self._after_save()
                if self._settings_window is not None:
                    self._settings_window.close()
        elif msg_type == "wizard":
            if data.get("done"):
                _core.save_wizard_done()
        elif msg_type == "rfid_unskip":
            _rfid.rfid_unskip()
            if self._settings_window is not None:
                self._settings_window.post({"type": "rfid_skipped", "count": _rfid.rfid_skipped_count()})
        elif msg_type == "bambu_auth":
            if self._settings_window is not None:
                self._bambu_sign_in(data, self._settings_window)
        elif msg_type == "feedback":
            _plate_check.open_url(_core.FEEDBACK_URL)
        elif msg_type == "spoolman_help":
            _plate_check.open_url(_core.SPOOLMAN_HELP)
        elif msg_type == "check_update":
            if self._checking_update or self._settings_window is None:
                return
            self._checking_update = True
            window = self._settings_window

            def worker():
                result = _plate_check.get_release()
                self._checking_update = False
                if result["ok"]:
                    self._release_url = result["url"]
                    result["newer"] = _plate_check.is_newer(result["version"], _core.PLUGIN_VERSION)
                if window.is_open():
                    window.post({"type": "update_result", **result})

            _filament_profiles.spawn(worker)
        elif msg_type == "release" and self._release_url.startswith("https://"):
            _plate_check.open_url(self._release_url)
        elif msg_type == "cancel" and self._settings_window is not None:
            self._settings_window.close()
        elif msg_type == "ui_language":
            _tab.save_ui_language(data.get("value"))

    def _on_settings_close(self):
        self._settings_window = None

    def on_unload(self):
        # Without this, open windows would outlive OrcaSlicer's shutdown.
        _core.log.info("Unloading")
        _live_updates.stop_workers()
        _peers.stop_presence()
        if self._panel is not None and self._panel.is_open():
            self._panel.close()
        if self._settings_window is not None and self._settings_window.is_open():
            self._settings_window.close()

    def _post(self, data):
        """Post to the window if it is still open. Workers answer after their work is done, and the
        window may have closed meanwhile: the work (a booking, say) has still happened."""
        panel = self._panel
        try:
            if panel is not None and panel.is_open():
                panel.post(data)
        except Exception as exc:  # closed between the check and the post
            _core.log.debug("Could not post to the closed window: %s", exc)

    def on_message(self, data):
        msg_type = data.get("type") if isinstance(data, dict) else None
        if msg_type == "page_error":
            _core.log_page_error(data)
        elif msg_type in ("ready", "refresh"):
            _core.sync_config(self)
            self._push_data()
        elif msg_type == "settings":
            self._open_settings(data.get("page"))
        elif msg_type == "order":
            _plate_check.open_search(data.get("query"))
        elif msg_type == "printers":
            _printers.save_printers(data.get("printers"))
        elif msg_type == "live":
            self._post(_printers.live_message())
        elif msg_type == "rfid_skip":
            _rfid.rfid_skip(data.get("printer"), data.get("tag"))
            self._post(_printers.live_message())
        elif msg_type == "slice_pick":
            pick = _netprinters.take_pick(data)  # off the list now, so no reply sent meanwhile asks it again
            _filament_profiles.spawn(lambda: (_netprinters.apply_pick(pick, data), self._post(_printers.live_message())), name="spooler-slice-pick")
        elif msg_type == "slice_map":
            _netprinters.save_slice_map(data.get("map"))
        elif msg_type == "printer_code":
            _live_updates.save_printer_code(data.get("id"), data.get("code"))
        elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
            _filament_profiles.spawn(lambda: self._post({"type": "usage", "usage": _stats.usage_action(data)}), name="spooler-usage")
        elif msg_type == "stats":
            _filament_profiles.spawn(lambda: self._post({"type": "stats", "stats": _stats.stats_data(data.get("period"))}), name="spooler-stats")
        elif msg_type == "stats_export":
            _filament_profiles.spawn(lambda: self._post({"type": "stats_export", **_stats.export_history(data.get("period"))}), name="spooler-export")
        elif msg_type == "spool_detail":
            _filament_profiles.spawn(lambda: self._post({"type": "spool_detail", "detail": _stats.spool_detail(data.get("id"))}), name="spooler-detail")
        elif msg_type == "send":
            _spoolman_sync.start_send(self._post, chosen=data)
        elif msg_type in ("calibration_save", "calibration_skip"):
            _spoolman_sync.answer_calibration(data, self._post)
        elif msg_type == "sync_presets":
            _peers.start_preset_sync(self._post)
        elif msg_type == "spool_action":
            _editor.start_spool_action(data, self._post)
        elif msg_type == "moon_spool":
            _moonraker.start_moon_spool(data, self._post)
        elif msg_type == "tick":
            _spoolman_sync.auto_send(self._post)
        elif msg_type == "ui_language":
            _tab.save_ui_language(data.get("value"))

    def _push_data(self):
        if self._panel is None or not self._panel.is_open():
            return
        _live_updates.ws_sync(self._panel.post)
        url = self._spoolman_url()
        if _sources.source() == "spoolman" and not url:
            self._panel.post({
                "type": "spools",
                "ok": False,
                "error": _i18n.tr("No Spoolman URL configured yet - click Settings to set one."),
                "error_code": "no_url", **_peers.peer_context(),
            })
            return
        if self._refreshing:
            return
        self._refreshing = True
        snapshot = _moonraker.refresh_snapshot()
        _live_updates._local_sync()
        panel = self._panel
        low_stock_grams = _core.parse_low(_core.get_settings().get("low_stock_grams"))

        snapshot = snapshot if _sources.source() == "spoolman" else None

        def worker():
            try:
                result = _peers.fresh_spools(snapshot)
            except Exception as exc:  # never leave _refreshing set: the list would stop refreshing for good
                _core.log.exception("Reading the spool list failed")
                result = {"ok": False, "error": _i18n.tr("Could not read the spool list: {error}", error=exc)}
            finally:
                self._refreshing = False
            if panel.is_open():
                panel.post({"type": "spools", "low_stock_grams": low_stock_grams,
                            "weight_display": _core.weight_mode(), "show_cart": _core.cart_on(), "display": _core.display_settings(),
                            "spool_columns": _core.spool_columns(), "spool_view": _core.spool_view(), "source": _sources.source(), **_printers.printer_state(),
                            "calibration": _spoolman_sync.calibration_asks(),
                            **_peers.spools_message_extras(result), **result})

        _filament_profiles.spawn(worker, name="spooler-refresh")

    def _on_panel_close(self):
        self._panel = None
        _live_updates.ws_sync(None)

    def _open_panel(self):
        if self._panel is not None and self._panel.is_open():
            self._push_data()
            return
        self._panel = orca.host.ui.create_window(
            html=_i18n.main_html(),
            title=_core.PLUGIN_NAME,
            width=_core.MAIN_SIZE[0],
            height=_core.MAIN_SIZE[1],
            on_message=self.on_message,
            on_close=self._on_panel_close,
        )

    def _open(self):
        if not _sources.configured():
            self._open_settings()
            return
        self._open_panel()

    def get_default_config(self):
        return _core.default_config()

    def on_load(self):
        _core.log.info(
            "%s %s loaded (Python %s, %s)",
            _core.PLUGIN_NAME,
            _core.PLUGIN_VERSION,
            platform.python_version(),
            sys.platform + "-" + platform.machine(),  # platform.platform() opens files Orca's audit blocks
        )
        _core.sync_config(self)
        _peers.start_presence()
        self._open()

    def execute(self):
        self._open()
        return orca.ExecutionResult.success(_i18n.tr("Opened {plugin}", plugin=_core.PLUGIN_NAME))



class _SettingsView:
    """Stands in for a settings window when Settings is a view inside the tab.

    Same post / is_open / close calls as a host window, so the settings code is shared.
    """

    def __init__(self, page):
        self._page = page

    def post(self, data):
        self._page.post_message({**data, "view": "settings"})

    def is_open(self):
        return True

    def close(self):
        self._page.post_message({"type": "show_view", "view": "main"})


if _core._PAGES:

    class SpoolerPage(orca.pages.PagesPluginCapabilityBase):
        """The Spooler tab, with Settings as a second view inside it.

        Used instead of SpoolerWindow when orca.pages exists. Its settings methods duplicate
        SpoolerWindow's rather than share a mixin, to avoid multiple inheritance with a
        pybind11 base class.
        """

        def __init__(self):
            super().__init__()
            self._settings_window = _SettingsView(self)
            self._verified_url = ""
            self._verified_bambu = False
            self._release_url = ""
            self._refreshing = False
            self._testing = False
            self._checking_update = False
            _plate_check._plate["page"] = self

        def get_name(self):
            return _core.PLUGIN_NAME

        def get_type(self):
            return orca.PluginType.Pages

        def get_icon(self):
            return _tab.icon_path()

        def get_ui(self):
            try:
                url = self._spoolman_url()
                return _i18n.tab_html(
                    source=_sources.source(),
                    initial_view="main" if _sources.configured() else "settings",
                    current_url=url,
                    low_stock_grams=_core.parse_low(_core.get_settings().get("low_stock_grams")),
                    plate_check=_core.plate_settings()[0],
                    plate_margin=_core.plate_settings()[1],
                    weight=_core.weight_mode(),
                    cart=_core.cart_on(),
                    progress=_core.progress_settings(),
                    columns=_core.spool_columns(),
                    stats=_core.stats_settings(),
                    wizard=_core.wizard_pending(),
                )
            except Exception as exc:  # noqa: BLE001 - raising leaves OrcaSlicer's tab an empty grey panel
                _core.log.exception("get_ui() raised")
                return _i18n.error_page(exc)

        def on_message(self, arg0):
            # The base class hints "arg0: str", but a parsed dict arrives (as with
            # create_window). A string is still accepted in case that changes.
            try:
                data = json.loads(arg0) if isinstance(arg0, str) else arg0
                if not isinstance(data, dict):
                    return
                if data.get("view") == "settings":
                    self._on_settings(data)
                    return
                msg_type = data.get("type")
                if msg_type == "page_error":
                    _core.log_page_error(data)
                elif msg_type in ("ready", "refresh"):
                    _core.sync_config(self)
                    self._push_data()
                    if msg_type == "ready" and _plate_check._plate["payload"]:
                        _plate_check.send_plate(_plate_check._plate["payload"])
                elif msg_type == "settings":
                    self._open_settings()
                elif msg_type == "order":
                    _plate_check.open_search(data.get("query"))
                elif msg_type == "printers":
                    _printers.save_printers(data.get("printers"))
                elif msg_type == "live":
                    self.post_message(_printers.live_message())
                elif msg_type == "rfid_skip":
                    _rfid.rfid_skip(data.get("printer"), data.get("tag"))
                    self.post_message(_printers.live_message())
                elif msg_type == "printer_code":
                    _live_updates.save_printer_code(data.get("id"), data.get("code"))
                elif msg_type in ("usage_mode", "usage_book", "usage_undo", "usage_resolve"):
                    _filament_profiles.spawn(lambda: self.post_message({"type": "usage", "usage": _stats.usage_action(data)}))
                elif msg_type == "stats":
                    _filament_profiles.spawn(lambda: self.post_message({"type": "stats", "stats": _stats.stats_data(data.get("period"))}))
                elif msg_type == "stats_export":
                    _filament_profiles.spawn(lambda: self.post_message({"type": "stats_export", **_stats.export_history(data.get("period"))}))
                elif msg_type == "spool_detail":
                    _filament_profiles.spawn(lambda: self.post_message({"type": "spool_detail", "detail": _stats.spool_detail(data.get("id"))}))
                elif msg_type == "plate_recheck":
                    _filament_profiles.spawn(_plate_check.recheck)
                elif msg_type == "plate_dismiss":
                    _plate_check._plate.update(payload=None, slots=[])
                elif msg_type == "send":
                    _spoolman_sync.start_send(self.post_message, chosen=data)
                elif msg_type in ("calibration_save", "calibration_skip"):
                    _spoolman_sync.answer_calibration(data, self.post_message)
                elif msg_type == "sync_presets":
                    _peers.start_preset_sync(self.post_message)
                elif msg_type == "spool_action":
                    _editor.start_spool_action(data, self.post_message)
                elif msg_type == "moon_spool":
                    _moonraker.start_moon_spool(data, self.post_message)
                elif msg_type == "tick":
                    _spoolman_sync.auto_send(self.post_message)
                elif msg_type == "ui_language":
                    _tab.save_ui_language(data.get("value"))
            except Exception:
                _core.log.exception("on_message() raised (%s)", _core.message_summary(arg0))

        def _spoolman_url(self):
            return _core.get_settings().get("spoolman_url", "")

        def _push_data(self):
            _live_updates.ws_sync(self.post_message)
            url = self._spoolman_url()
            if _sources.source() == "spoolman" and not url:
                self.post_message({
                    "type": "spools",
                    "ok": False,
                    "error": _i18n.tr("No Spoolman URL configured yet - click Settings to set one."),
                "error_code": "no_url", **_peers.peer_context(),
                })
                return
            if self._refreshing:
                return
            self._refreshing = True
            snapshot = _moonraker.refresh_snapshot()
            _live_updates._local_sync()
            low_stock_grams = _core.parse_low(_core.get_settings().get("low_stock_grams"))

            snapshot = snapshot if _sources.source() == "spoolman" else None

            def worker():
                try:
                    result = _peers.fresh_spools(snapshot)
                except Exception as exc:  # never leave _refreshing set: the list would stop refreshing for good
                    _core.log.exception("Reading the spool list failed")
                    result = {"ok": False, "error": _i18n.tr("Could not read the spool list: {error}", error=exc)}
                finally:
                    self._refreshing = False
                self.post_message({"type": "spools", "low_stock_grams": low_stock_grams,
                                   "weight_display": _core.weight_mode(), "show_cart": _core.cart_on(), "display": _core.display_settings(),
                                   "spool_columns": _core.spool_columns(), "spool_view": _core.spool_view(), "source": _sources.source(), **_printers.printer_state(),
                            "calibration": _spoolman_sync.calibration_asks(),
                            **_peers.spools_message_extras(result), **result})

            _filament_profiles.spawn(worker, name="spooler-refresh")

        def _save_settings(self, url, low_stock, plate_check=True,
                           plate_margin=_core.DEFAULT_MARGIN, weight="both", cart=False, src="spoolman",
                           progress=None, columns=None, stats=None):
            _core.sync_config(self)  # take a pending plugin-manager edit first, so this save wins over it
            settings = _core.settings_form(url, low_stock, plate_check, plate_margin, weight, cart, src, progress, columns, stats)
            if _core.update_settings(settings):
                _core.log.info("Settings saved (url=%s, low stock=%s g, filament check=%s, margin=%s%%)",
                         url, settings["low_stock_grams"], settings["plate_check"],
                         settings["plate_margin_percent"])
                _core.sync_config(self)
                return True
            orca.host.ui.message(
                _i18n.tr("Could not write settings to {file}. Check that this folder is writable.", file=_core.SETTINGS_FILE),
                title=_core.PLUGIN_NAME,
                icon="error",
            )
            return False

        def _after_save(self):
            self._push_data()

        def _open_settings(self):
            saved_url = self._spoolman_url()
            self.post_message({
                "type": "show_view",
                "view": "settings",
                "source": _sources.source(),
                "url": saved_url,
                "low_stock": _core.parse_low(_core.get_settings().get("low_stock_grams")),
                "plate_check": _core.plate_settings()[0],
                "plate_margin": _core.plate_settings()[1],
                "weight_display": _core.weight_mode(),
                "show_cart": _core.cart_on(),
                "spool_columns": _core.spool_columns(),
                "spool_view": _core.spool_view(),
                "display": _core.display_settings(),
                "drying": _core.drying_settings(),
                "presets": _filament_profiles.presets_settings(), "parents": _filament_profiles.parent_bases(_filament_profiles._ui_snap.get("parents") or []),
                "progress": _core.progress_settings(),
                "stats": _core.stats_settings(),
                "cur_code": _stats._cur["code"] or "EUR",
                "wizard": _core.wizard_pending(),
                "auto_keep_slots": _capabilities.auto_keep_on(), "refresh_s": _capabilities.refresh_secs(),
                "rfid_skipped": _rfid.rfid_skipped_count(),
                "save_calibration": _spoolman_sync.calibration_mode(),
            })
            self._check_connection(saved_url, self._settings_window)

        def _check_connection(self, url, window, src=None):
            if self._testing:
                return
            self._testing = True
            src = _sources.parse_source(src or _sources.source())

            def worker():
                info = _sources.bambu_ping() if src == "bambu" else _sources.ping(url)
                _sources.heard(_sources.BAMBU_KEY if src == "bambu" else url, info.get("ok"),
                      (info.get("account") or info.get("version")) if info.get("ok") else info.get("error"), sure=True)
                self._testing = False
                if src == "bambu":
                    self._verified_bambu = bool(info.get("ok"))
                elif info.get("ok"):
                    self._verified_url = _sources.clean_url(url)
                if window.is_open():
                    window.post({"type": "test_result", "source": src, "url": url, **info, "requirements": _sources.requirements()})

            _filament_profiles.spawn(worker)

        def _bambu_sign_in(self, data, window):
            if data.get("action") == "sign_out":
                self._verified_bambu = False

            def worker():
                result = _sources.bambu_sign_in(data)
                if window.is_open():
                    window.post({"type": "bambu_auth_result", **result})

            _filament_profiles.spawn(worker)

        def _on_settings(self, data):
            msg_type = data.get("type")
            if msg_type in ("ready", "requirements"):  # Check again: the same test, counted at once
                self._check_connection(self._spoolman_url(), self._settings_window)
            elif msg_type == "test":
                url = (data.get("url") or "").strip()
                self._check_connection(url, self._settings_window, data.get("source"))
            elif msg_type == "save":
                _core.save_display(data.get("display"))
                _core.save_drying(data.get("drying"))
                _filament_profiles.save_presets(data.get("presets"))
                _capabilities.save_auto_keep(data.get("auto_keep_slots"))
                _capabilities.save_refresh(data.get("refresh_s"))
                _core.save_spool_view(data.get("spool_view"))
                _spoolman_sync.save_calibration_mode(data.get("save_calibration"))
                url = (data.get("url") or "").strip()
                src = _sources.parse_source(data.get("source"))
                verified = (self._verified_bambu if src == "bambu"
                            else _sources.clean_url(url) == self._verified_url)
                if not verified:
                    self._settings_window.post({
                        "type": "test_result",
                        "source": src,
                        "ok": False,
                        "url": url,
                        "error": _i18n.tr("Test the connection successfully before saving."),
                    })
                    return
                saved = self._save_settings(url, data.get("low_stock"), data.get("plate_check"),
                                            data.get("plate_margin"), data.get("weight_display"),
                                            data.get("show_cart"), src, data.get("progress"),
                                            data.get("spool_columns"), data.get("stats"))
                if saved:
                    self._after_save()
                    self._settings_window.close()
            elif msg_type == "wizard":
                if data.get("done"):
                    _core.save_wizard_done()
            elif msg_type == "rfid_unskip":
                _rfid.rfid_unskip()
                self._settings_window.post({"type": "rfid_skipped", "count": _rfid.rfid_skipped_count()})
            elif msg_type == "bambu_auth":
                if self._settings_window is not None:
                    self._bambu_sign_in(data, self._settings_window)
            elif msg_type == "feedback":
                _plate_check.open_url(_core.FEEDBACK_URL)
            elif msg_type == "spoolman_help":
                _plate_check.open_url(_core.SPOOLMAN_HELP)
            elif msg_type == "check_update":
                if self._checking_update:
                    return
                self._checking_update = True
                window = self._settings_window

                def worker():
                    result = _plate_check.get_release()
                    self._checking_update = False
                    if result["ok"]:
                        self._release_url = result["url"]
                        result["newer"] = _plate_check.is_newer(result["version"], _core.PLUGIN_VERSION)
                    window.post({"type": "update_result", **result})

                _filament_profiles.spawn(worker)
            elif msg_type == "release" and self._release_url.startswith("https://"):
                _plate_check.open_url(self._release_url)
            elif msg_type == "cancel":
                self._settings_window.close()
            elif msg_type == "ui_language":
                _tab.save_ui_language(data.get("value"))

        def get_default_config(self):
            return _core.default_config()

        def on_load(self):
            _core.log.info(
                "%s %s loaded as a native tab (Python %s, %s)",
                _core.PLUGIN_NAME,
                _core.PLUGIN_VERSION,
                platform.python_version(),
                sys.platform + "-" + platform.machine(),  # platform.platform() opens files Orca's audit blocks
            )
            _core.sync_config(self)
            _peers.start_presence()   # called on load even when the tab is disabled in the Plugins dialog

        def on_unload(self):
            _core.log.info("Unloading")
            _live_updates.stop_workers()
            _peers.stop_presence()


if _core._SLICING:

    class SpoolerFilamentCheck(orca.slicing.SlicingPipelineCapabilityBase):
        """After each slice, checks the plate's filament against the spools in Spoolman."""

        def get_name(self):
            return "Spooler Filament Check"

        def execute(self, ctx):
            try:
                if ctx.step == getattr(orca.slicing.Step, "posSlice", None):
                    if _plate_check._plate["payload"]:
                        _filament_profiles.spawn(_plate_check.clear_plate)
                    return orca.ExecutionResult.success()
                if ctx.step != orca.slicing.Step.psGCodePostProcess:
                    return orca.ExecutionResult.success()
                enabled, margin = _core.plate_settings()
                slots = _plate_check.plate_slots(ctx, _plate_check.parse_usage(_plate_check.read_tail(ctx.gcode_path)))
                _netprinters.usage_plan(slots)
                _netprinters.slice_fill_ctx(ctx, slots)
                if enabled:
                    if any(slot["grams"] > 0 for slot in slots):
                        # Off the slicing thread: it may fetch the spool list, and UI calls from
                        # here can deadlock while the GUI waits for slicing to finish.
                        threading.Thread(target=_plate_check.run_check, args=(slots, margin),
                                         daemon=True).start()
            except Exception:
                _core.log.exception("Filament check failed")
            return orca.ExecutionResult.success()


# Modules used only when a function runs, imported last: they may import this one in turn.
from . import capabilities as _capabilities  # noqa: E402
from . import editor as _editor  # noqa: E402
from . import filament_profiles as _filament_profiles  # noqa: E402
from . import i18n as _i18n  # noqa: E402
from . import live_updates as _live_updates  # noqa: E402
from . import moonraker as _moonraker  # noqa: E402
from . import netprinters as _netprinters  # noqa: E402
from . import peers as _peers  # noqa: E402
from . import plate_check as _plate_check  # noqa: E402
from . import printers as _printers  # noqa: E402
from . import rfid as _rfid  # noqa: E402
from . import sources as _sources  # noqa: E402
from . import spoolman_sync as _spoolman_sync  # noqa: E402
from . import stats as _stats  # noqa: E402
from . import tab as _tab  # noqa: E402
