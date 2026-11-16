// Locale resolution, kept free of Vue so the unit tests can import it directly.
export const LOCALES = ['en', 'pt-BR', 'es', 'de', 'zh-CN'] as const;
export type Locale = typeof LOCALES[number];
export type LangPref = 'auto' | Locale;
export const isLocale = (value: unknown): value is Locale => (LOCALES as readonly unknown[]).includes(value);

// By primary subtag: OrcaSlicer reports "pt_BR", "es", "de", "zh_CN" or "zh_TW"; browsers "es-MX", "de-AT", "zh-Hans-CN".
// Traditional Chinese takes the Simplified page: closer to its reader than English.
const BY_LANGUAGE: Record<string, Locale> = { en: 'en', pt: 'pt-BR', es: 'es', de: 'de', zh: 'zh-CN' };

/** "pt_BR", "pt" → "pt-BR"; "es_ES" → "es"; "de-AT" → "de"; "zh_CN", "zh_TW" → "zh-CN"; any English → "en"; anything else → null. */
export function normalizeLocale(value: unknown): Locale | null {
  if (typeof value !== 'string' || !value.trim()) return null;
  return BY_LANGUAGE[value.trim().toLowerCase().split(/[-_]/)[0]] ?? null;
}

/** Explicit choice first, then the host's language, then English: the same rule as the plugin's own texts (text_language). */
export function resolveLocale(pref: LangPref, host: unknown): Locale {
  if (isLocale(pref)) return pref;
  return normalizeLocale(host) ?? 'en';
}

export function interpolate(text: string, params?: Record<string, unknown>): string {
  if (!params) return text;
  return text.replace(/\{(\w+)\}/g, (_, k: string) => (k in params ? String(params[k]) : `{${k}}`));
}

/** Money as the language writes it: the sign after the amount in German and Spanish ("41,20 €"), before it elsewhere. */
export function formatMoney(sign: string, amount: string, locale: Locale): string {
  return locale === 'de' || locale === 'es' ? `${amount}\u00a0${sign.trim()}`.trim() : sign + amount;
}
