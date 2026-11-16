// PrimeVue's InputNumber only takes the locale's decimal sign: in German, Spanish or Portuguese a typed "." is
// dropped ("2.5" becomes 25), and any paste is re-inserted as "2.5" and read as 25 too. These handlers sit on the
// element around a decimal InputNumber (capture phase) and let "." and the locale's sign both mean the decimal.

/** The decimal sign the language writes: "," in de, es and pt-BR, "." in en and zh-CN. */
export function decimalSign(locale: string): string {
  return new Intl.NumberFormat(locale).formatToParts(1.5).find(p => p.type === 'decimal')?.value ?? '.';
}

/** A typed "." in a field whose decimal sign differs and that has none yet: the sign to type instead, else null. */
export function typedDecimal(key: string, value: string, sign: string): string | null {
  return key === '.' && sign !== '.' && !value.includes(sign) ? sign : null;
}

/** Pasted "2.5" or "2,5" (in the language's sign) as the keys to type, with the language's sign; null leaves the paste
 * to InputNumber (no decimal, or "1,500" in English, where "," groups). A single "." with no "," is a decimal everywhere. */
export function pastedDecimal(text: string, sign: string): string | null {
  const m = /^(\d+)([.,])(\d+)$/.exec(text.trim());
  return m && (m[2] === '.' || m[2] === sign) ? m[1] + sign + m[3] : null;
}

/** Capture handlers for the wrapper of a decimal InputNumber. Both go through InputNumber's own key handling, so the
 * selection, caret, min/max and fraction digits behave as when typing. */
export function decimalKeys(locale: () => string) {
  const press = (input: EventTarget, key: string) => input.dispatchEvent(new KeyboardEvent('keypress', { key, bubbles: true, cancelable: true }));
  return {
    onKeypress(e: KeyboardEvent): void {
      const input = e.target as HTMLInputElement;
      const sign = typedDecimal(e.key, input.value, decimalSign(locale()));
      if (!sign) return;
      e.preventDefault(); e.stopPropagation();
      press(input, sign);
    },
    onPaste(e: ClipboardEvent): void {
      const keys = pastedDecimal(e.clipboardData?.getData('text') ?? '', decimalSign(locale()));
      if (keys === null || !e.target) return;
      e.preventDefault(); e.stopPropagation();
      for (const key of keys) press(e.target, key);
    },
  };
}
