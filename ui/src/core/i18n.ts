import { computed, ref } from 'vue';
import { en, ptBR, type MessageKey } from './messages';
import { interpolate, resolveLocale, type LangPref, type Locale } from './i18n-core';
import { boot } from './boot';

const PREF_KEY = 'spooler.lang';
const dicts: Record<Locale, Record<MessageKey, string>> = { en, 'pt-BR': ptBR };

// The explicit choice lives in the plugin's settings (boot "pref"); localStorage is only a fallback cache.
let persist: (value: LangPref) => void = () => {};
export function onLangPref(fn: (value: LangPref) => void): void { persist = fn; }
function readPref(): LangPref {
  const fromHost = (boot as { pref?: unknown }).pref;
  if (fromHost === 'en' || fromHost === 'pt-BR') return fromHost;
  if (fromHost === 'auto') return 'auto';
  try {
    const v = localStorage.getItem(PREF_KEY);
    return v === 'en' || v === 'pt-BR' ? v : 'auto';
  } catch { return 'auto'; }
}

export const langPref = ref<LangPref>(readPref());
const hostLang = ref<unknown>(null);
export const locale = computed<Locale>(() => resolveLocale(langPref.value, hostLang.value, navigator.languages ?? [navigator.language]));
export const autoLocale = computed<Locale>(() => resolveLocale('auto', hostLang.value, navigator.languages ?? [navigator.language]));

export function setHostLanguage(value: unknown): void { hostLang.value = value; }
export function setLangPref(value: LangPref): void {
  langPref.value = value;
  persist(value);
  try { if (value === 'auto') localStorage.removeItem(PREF_KEY); else localStorage.setItem(PREF_KEY, value); } catch { /* per-viewer only */ }
}

export function t(key: MessageKey, params?: Record<string, unknown>): string {
  return interpolate(dicts[locale.value][key] ?? en[key] ?? key, params);
}
/** Plural keys come in pairs "<base>_one" / "<base>_other". */
export function tn(base: string, n: number, params?: Record<string, unknown>): string {
  const key = (new Intl.PluralRules(locale.value).select(n) === 'one' ? `${base}_one` : `${base}_other`) as MessageKey;
  return t(key, { n, ...params });
}
/** A message key when it exists (state names, codes from Python); otherwise the raw value. */
export function tMaybe(key: string, fallback: string, params?: Record<string, unknown>): string {
  return key in en ? t(key as MessageKey, params) : fallback;
}

export const fmt = {
  number: (v: number, digits = 0) => new Intl.NumberFormat(locale.value, { maximumFractionDigits: digits, minimumFractionDigits: digits }).format(v),
  grams: (v: number | null | undefined) => (v == null ? '? g' : `${new Intl.NumberFormat(locale.value, { maximumFractionDigits: 0 }).format(Math.round(v))} g`),
  bytes(b: number | null | undefined): string {
    if (b == null) return '';
    const nf = (x: number, d: number) => new Intl.NumberFormat(locale.value, { maximumFractionDigits: d }).format(x);
    return b > 1e9 ? `${nf(b / 1e9, 1)} GB` : b > 1e6 ? `${nf(b / 1e6, 1)} MB` : `${nf(b / 1e3, 0)} kB`;
  },
  duration(s: number | null | undefined): string {
    if (s == null || !isFinite(s)) return '—';
    const h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60);
    return (h ? `${h} h ` : '') + `${m} min`;
  },
  dateTime: (unix: number) => new Intl.DateTimeFormat(locale.value, { dateStyle: 'short', timeStyle: 'short' }).format(new Date(unix * 1000)),
  time: (unix: number) => new Intl.DateTimeFormat(locale.value, { timeStyle: 'short' }).format(new Date(unix * 1000)),
  ago(unix: number | null | undefined, now = Date.now() / 1000): string {
    if (unix == null) return '';
    const s = Math.max(0, Math.round(now - unix));
    return s < 60 ? t('age.seconds', { n: s }) : s < 3600 ? t('age.minutes', { n: Math.round(s / 60) }) : t('age.at', { time: fmt.time(unix) });
  },
};
