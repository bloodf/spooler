<script setup lang="ts">
import InputNumber from 'primevue/inputnumber';
import { decimalKeys } from '../core/decimal';
import { locale } from '../core/i18n';

// A number box of the spool editor, with its unit. "2.5" typed or pasted is 2.5 in every language (core/decimal).
defineProps<{ id?: string; label?: string; min?: number; max?: number; digits?: number; unit?: string | null; invalid?: boolean; describedby?: string }>();
const model = defineModel<number | null>({ required: true });
const keys = decimalKeys(() => locale.value);
</script>
<template>
  <span class="en-num" @keypress.capture="keys.onKeypress" @paste.capture="keys.onPaste">
    <InputNumber v-model="model" :input-id="id" :aria-label="label" :min="min" :max="max" :max-fraction-digits="digits ?? 0" :use-grouping="false" :locale="locale"
                 :suffix="unit ? ' ' + unit : undefined" :invalid="invalid" :aria-describedby="describedby" fluid
                 @input="e => (model = typeof e.value === 'number' ? e.value : null)" />
  </span>
</template>
<style>
.en-num { flex: 1 1 140px; min-width: 0; display: flex; }
.en-num > .p-inputnumber { flex: 1; min-width: 0; }
</style>
