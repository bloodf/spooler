"""Texts worded in Python (notices, dialogs, action results, plate rows) in all five languages: every
tr() text has an entry with the same placeholders, the language follows the page's choice, then
OrcaSlicer's, and numbers, money and sentences are written the way each language writes them."""

import ast
import re
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from plugin_loader import PLUGIN, load

sp, orca = load()

LANGS = ("pt-BR", "es", "de", "zh-CN")
HAN = re.compile(r"[一-鿿]")


def tr_texts() -> list[str]:
    """Every English text the plugin passes to tr(), constants and both arms of a conditional included."""
    tree = ast.parse(PLUGIN.read_text(encoding="utf-8"))
    consts = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            try:
                consts[node.targets[0].id] = ast.literal_eval(node.value)
            except ValueError:
                continue
    found: list[str] = []

    def collect(arg):
        if isinstance(arg, ast.Constant) and isinstance(arg.value, str):
            found.append(arg.value)
        elif isinstance(arg, ast.IfExp):
            collect(arg.body)
            collect(arg.orelse)
        elif isinstance(arg, ast.Name) and isinstance(consts.get(arg.id), str):
            found.append(consts[arg.id])
        # tr(region) and tr(stage): their values come from BAMBU_REGIONS and STAGES, checked below.

    for node in ast.walk(tree):
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "tr" and node.args:
            collect(node.args[0])
    return found + list(sp.BAMBU_REGIONS.values()) + list(sp.STAGES.values())


def names(text: str) -> list[str]:
    return sorted(re.findall(r"\{(\w*)\}", text))


class Language:
    """Run with the plugin's texts in one language, restored afterwards."""

    def __init__(self, lang):
        self.lang = lang

    def __enter__(self):
        self.saved = sp._lang["value"]
        sp._lang["value"] = self.lang

    def __exit__(self, *exc):
        sp._lang["value"] = self.saved


class TableTest(unittest.TestCase):
    def test_every_text_has_an_entry_in_every_language(self):
        texts = set(tr_texts())
        self.assertGreater(len(texts), 150)
        for lang in LANGS:
            self.assertEqual(sorted(texts - set(sp._TEXTS[lang])), [], lang)
        self.assertEqual(sorted(set(sp._TEXT_ROWS) - texts), [], "entries no tr() call uses")

    def test_same_placeholders_and_nothing_empty(self):
        for english, row in sp._TEXT_ROWS.items():
            self.assertEqual(len(row), len(LANGS), english)
            for lang, text in zip(LANGS, row):
                self.assertEqual(names(text), names(english), f"{lang}: {english!r} -> {text!r}")
                self.assertTrue(text.strip() or english.strip() == "", f"{lang}: {english!r} is empty")

    def test_chinese_is_chinese_with_chinese_punctuation(self):
        for english, text in sp._TEXTS["zh-CN"].items():
            if not re.search(r"[A-Za-z]{3}", re.sub(r"\{\w*\}|Spooler", "", english)):
                continue
            if english in ("Calibrating Micro Lidar", "Keep Slots Synced is already running."):
                self.assertTrue(HAN.search(text), english)
                continue
            self.assertTrue(HAN.search(text), f"untranslated: {english!r}")
            self.assertNotRegex(text, r"[一-鿿][,:;?!]|[一-鿿]\.(\s|$)", english)


class ChoiceTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        for patch in (mock.patch.object(sp, "SETTINGS_FILE", Path(self.tmp.name) / "s.json"),
                      mock.patch.object(sp, "OLD_SETTINGS", Path(self.tmp.name) / "none.json")):
            patch.start()
            self.addCleanup(patch.stop)
        self.addCleanup(self.tmp.cleanup)
        self.addCleanup(lambda: sp.text_language(fresh=True))
        self.addCleanup(lambda: vars(orca.host).pop("app_language", None))

    def host(self, lang):
        orca.host.app_language = lambda: lang
        return sp.text_language(fresh=True)

    def test_orca_codes_map_to_the_page_languages(self):
        cases = {"pt_BR": "pt-BR", "es": "es", "es_ES": "es", "de": "de", "de_DE": "de", "zh_CN": "zh-CN",
                 "zh_TW": "zh-CN", "en": "en", "en_US": "en", "fr_FR": None, "": None, None: None, 5: None}
        for code, lang in cases.items():
            self.assertEqual(sp.normalize_language(code), lang, code)

    def test_follows_orca_then_english_and_the_explicit_choice_wins(self):
        self.assertEqual(self.host("de_DE"), "de")
        self.assertEqual(self.host("zh_TW"), "zh-CN")
        self.assertEqual(self.host("ja"), "en")
        self.assertEqual(self.host("es"), "es")
        self.assertEqual(sp.tr("Unknown spool action."), "Acción de bobina desconocida.")
        sp.save_ui_language("zh-CN")
        self.assertEqual(sp.text_language(), "zh-CN")   # saved: at once, without a new page
        self.assertEqual(sp.tr("No spool chosen."), "未选择料盘。")
        sp.save_ui_language("auto")
        self.assertEqual(sp.text_language(), "es")
        sp.save_ui_language("fr")   # not offered: ignored
        self.assertEqual(sp.ui_language(), "auto")

    def test_no_host_language_is_english(self):
        vars(orca.host).pop("app_language", None)
        self.assertEqual(sp.text_language(fresh=True), "en")
        self.assertEqual(sp.tr("Spool #{id} archived.", id=3), "Spool #3 archived.")


class FormatTest(unittest.TestCase):
    def test_numbers(self):
        expect = {"en": "12,345.5", "pt-BR": "12.345,5", "es": "12.345,5", "de": "12.345,5", "zh-CN": "12,345.5"}
        for lang, text in expect.items():
            with Language(lang):
                self.assertEqual(sp.fmt_num(12345.5, 1, group=True), text, lang)
                self.assertEqual(sp.fmt_grams(1380), "1.38 kg" if lang in ("en", "zh-CN") else "1,38 kg", lang)
        with Language("es"):   # Spanish groups only from 10,000 up, as Intl.NumberFormat does
            self.assertEqual(sp.fmt_num(5000, group=True), "5000")
        with Language("de"):
            self.assertEqual(sp.fmt_num(5000, group=True), "5.000")

    def test_money(self):
        expect = {"en": "€1.25", "pt-BR": "€1,25", "es": "1,25 €", "de": "1,25 €", "zh-CN": "€1.25"}
        for lang, text in expect.items():
            with Language(lang):
                self.assertEqual(sp.fmt_money(1.25, "EUR"), text, lang)

    def test_lists_and_sentences(self):
        with Language("de"):
            self.assertEqual(sp._join(["#1", "#2", "#3"]), "#1, #2 und #3")
            self.assertEqual(sp._sentences(["A.", "B."]), "A. B.")
        with Language("zh-CN"):
            self.assertEqual(sp._join(["#1", "#2", "#3"]), "#1、#2和#3")
            self.assertEqual(sp._sentences(["甲。", "乙。"]), "甲。乙。")
            self.assertEqual(sp.fit_text("甲" * 30 + "。" + "乙" * 30 + "。", 50), "甲" * 30 + "。（另有 1 条，见日志）")


class MessageTest(unittest.TestCase):
    SLOT = {"preset": "", "vendor": "Acme", "material": "PLA", "colour": "111111", "sub_type": "", "n": 2,
            "grams": 100, "ams": True}

    def short(self):
        spool = {"id": 1, "remaining_weight": 20, "initial_weight": 1000, "location": "", "extra": {},
                 "filament": {"id": 5, "name": "Black", "material": "PLA", "color_hex": "111111",
                              "vendor": {"name": "Acme"}}}
        return sp.check_group({"slot": self.SLOT, "pool": 1, "used": [self.SLOT]}, [spool], 10)

    def test_plate_notice_in_each_language(self):
        expect = {
            "en": "Spooler: not enough filament loaded in the AMS. Slot 2 (Black) needs 100.0 g of filament but the spool has 20.0 g.",
            "pt-BR": "Spooler: filamento insuficiente carregado no AMS. Slot 2 (Black) precisa de 100,0 g de filamento, mas a bobina tem 20,0 g.",
            "es": "Spooler: no hay suficiente filamento cargado en el AMS. Ranura 2 (Black) necesita 100,0 g de filamento, pero la bobina tiene 20,0 g.",
            "de": "Spooler: nicht genug Filament im AMS geladen. Slot 2 (Black) braucht 100,0 g Filament, aber die Spule hat 20,0 g.",
            "zh-CN": "Spooler：AMS 中装入的耗材丝不足。槽位 2（Black）需要 100.0 g 耗材丝，但料盘有 20.0 g。",
        }
        for lang, text in expect.items():
            with Language(lang):
                kind, notice = sp.plate_notice([self.short()])
                self.assertEqual((kind, notice), ("warning", text), lang)

    def test_plate_rows_and_spool_data_stay_as_spoolman_has_them(self):
        with Language("de"):
            row = sp.plate_rows([self.short()])[0]
        self.assertEqual((row["slots"], row["headline"], row["name"]), ("Slot 2", "Nicht genug", "Black"))
        self.assertEqual(row["detail"], "100,0 g benötigt · 20,0 g übrig")

    def test_action_results_and_stages(self):
        with Language("zh-CN"):
            self.assertEqual(sp.tr("Spool #{id} moved to {location}.", id=4, location="Shelf A"), "料盘 #4 已移至 Shelf A。")
            self.assertEqual(sp.stage_text(26), "暂停（AMS 断开）")
        with Language("es"):
            self.assertEqual(sp.stage_text(2), "Precalentando la cama")
            self.assertIsNone(sp.stage_text(999))
            self.assertEqual(sp.account_text({"user": "a@b.c", "region": "china"}), "Sesión iniciada como a@b.c (China)")
        with Language("de"):
            self.assertTrue(sp.tr(sp.AUTO_KEEP_REFUSED).startswith("OrcaSlicer hat eine Filament-Slot-Änderung"))


if __name__ == "__main__":
    unittest.main()
