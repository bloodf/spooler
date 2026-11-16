<script setup lang="ts">
import InputNumber from 'primevue/inputnumber';
import { decimalKeys } from '../core/decimal';
import { locale } from '../core/i18n';

// A number box of the spool editor, with its unit. "2.5" typed or pasted is 2.5 in every language (core/decimal).
const props = defineProps<{ id?: string; label?: string; min?: number; max?: number; digits?: number; unit?: string | null; invalid?: boolean; describedby?: string }>();
const model = defineModel<number | null>({ required: true });
const keys = decimalKeys(() => locale.value);
// InputNumber writes back its own rounded text on blur (734.5678 becomes 734.6): a value that only differs by that rounding
// is no edit, so it never reaches the form and is never sent.
const shown = (v: number) => Number(v.toFixed(props.digits ?? 0));
function set(v: unknown): void {
  const next = typeof v === 'number' && Number.isFinite(v) ? v : null;
  if (next === model.value || (next !== null && typeof model.value === 'number' && shown(next) === shown(model.value) && next === shown(next))) return;
  model.value = next;
}
</script>
<template>
  <span class="en-num" @keypress.capture="keys.onKeypress" @paste.capture="keys.onPaste">
    <InputNumber :model-value="model" :input-id="id" :aria-label="label" :min="min" :max="max" :max-fraction-digits="digits ?? 0" :use-grouping="false" :locale="locale"
                 :suffix="unit ? ' ' + unit : undefined" :invalid="invalid" :aria-describedby="describedby" fluid
                 @update:model-value="set" @input="e => set(e.value)" />
  </span>
</template>
<style>
.en-num { flex: 1 1 140px; min-width: 0; display: flex; }
.en-num > .p-inputnumber { flex: 1; min-width: 0; }
</style>
