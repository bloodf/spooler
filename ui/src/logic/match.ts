// Preset match reasons: filmatch.py scores a preset and says why as [code, value] pairs; the page words them.
export const REASON_CODES = ['material', 'variant', 'vendor', 'generic', 'other_vendor', 'word', 'extra_word', 'printer', 'other_printer', 'nozzle'] as const;
export type ReasonCode = typeof REASON_CODES[number];

/** The reasons a page can word, in order; anything of another shape or code is left out. */
export function reasonTexts(reasons: unknown, word: (code: ReasonCode, value: string) => string): string[] {
  if (!Array.isArray(reasons)) return [];
  return reasons.filter((r): r is [ReasonCode, unknown] => Array.isArray(r) && (REASON_CODES as readonly string[]).includes(r[0]))
    .map(r => word(r[0], String(r[1] ?? '')));
}
