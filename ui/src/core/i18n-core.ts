// Locale resolution, kept free of Vue so the unit tests can import it directly.
export type Locale = 'en' | 'pt-BR';
export type LangPref = 'auto' | Locale;

/** "pt_BR", "pt-br", "pt" → "pt-BR"; any English → "en"; anything else → null (caller falls back). */
export function normalizeLocale(value: unknown): Locale | null {
  if (typeof value !== 'string' || !value.trim()) return null;
  const tag = value.trim().replace('_', '-').toLowerCase();
  if (tag === 'pt' || tag.startsWith('pt-')) return 'pt-BR';
  if (tag === 'en' || tag.startsWith('en-')) return 'en';
  return null;
}

/** Explicit choice first, then the host's language, then the browser's, then English. */
export function resolveLocale(pref: LangPref, host: unknown, browser: readonly string[]): Locale {
  if (pref === 'en' || pref === 'pt-BR') return pref;
  return normalizeLocale(host) ?? browser.map(normalizeLocale).find((l): l is Locale => !!l) ?? 'en';
}

export function interpolate(text: string, params?: Record<string, unknown>): string {
  if (!params) return text;
  return text.replace(/\{(\w+)\}/g, (_, k: string) => (k in params ? String(params[k]) : `{${k}}`));
}
