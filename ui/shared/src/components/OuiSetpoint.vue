<script setup lang="ts">
import { computed, ref, useId, watch } from 'vue';
import Button from 'primevue/button';
import InputNumber from 'primevue/inputnumber';
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';
import OuiSpark from './OuiSpark.vue';
import type { OuiTone } from './tones';

/*
 * A controlled value (a heater, a fan): what it reads now, what it is set to, and the control to change it.
 * The reading is the large figure; the target sits under it. A missing reading is a dash, never 0.
 *
 * With none of `inputId`, `error`, `validate` and `offAlways` it behaves as it always has: the field clamps what is typed
 * to `min`..`max`, Set emits `set`, and Off is disabled while there is no target. With `validate` the field no longer
 * clamps: what is typed stays as typed, `validate` is asked before every `set`, and a value it refuses is not emitted;
 * the reason is shown in a line under the row, the field is marked invalid, and the line is the field's description.
 */
const props = defineProps<{ label: string; icon?: OuiIconData; /** Recent readings, oldest first: drawn as a small line. */ history?: (number | null)[]; historyLabel?: string; current?: number | null; target?: number | null; unit: string;
  min?: number; max?: number; digits?: number; disabled?: boolean; describedby?: string;
  /** What the heater is doing: heating is orange, at target green, cooling blue, off grey. Always said in words too (`phaseLabel`). */ phase?: 'heating' | 'target' | 'cooling' | 'off'; phaseLabel?: string;
  /** Last known values of a printer the page can no longer see: drawn grey, with no phase. */ stale?: boolean;
  setLabel: string; offLabel: string; targetLabel: string; offText: string; inputLabel: string; name?: string;
  /** An id for the number field, so the page can find it and the row's label is a real <label> for it. */ inputId?: string;
  /** A line under the row, from the page: the printer refused the target, the command was not confirmed. Shown until the page clears it. */ error?: string | null;
  /** Asked before every `set`. Return nothing or true to let it through; a string to refuse it and show that reason; false to refuse it without a reason (the page says why, in `error`). May be async (a confirmation). Turns the field's own clamping off. */
  validate?: (value: number) => string | boolean | void | Promise<string | boolean | void>;
  /** Off stays enabled while there is no target (some printers need Off sent anyway). */ offAlways?: boolean }>();
const emit = defineEmits<{ set: [value: number]; off: [] }>();
const draft = ref<number | null>(null);
const refused = ref<string | null>(null);   // why validate() refused the last value, until the value changes
const asking = ref(false);
const errorId = useId();
const shownError = computed(() => props.error || refused.value);
// On the field itself: PrimeVue puts plain attributes of InputNumber on its wrapper, where a screen reader does not read them.
const describes = computed(() => [props.describedby, shownError.value ? errorId : ''].filter(Boolean).join(' ') || undefined);
watch(draft, () => { refused.value = null; });
// The reason goes at the first keystroke after a refusal, not only when the field is left. PrimeVue's field keeps what is
// being typed out of its model until then, and redraws from the model when its props change (here: no longer invalid),
// so the model is brought up to what has been typed in the same step, or that keystroke would be undone.
function onType(event: { value: number | string | null | undefined }) {
  if (refused.value == null) return;
  draft.value = typeof event.value === 'number' ? event.value : null;
}
async function send() {
  const value = draft.value;
  if (value == null || props.disabled || asking.value) return;
  if (props.validate) {
    asking.value = true;
    let verdict: string | boolean | void;
    try { verdict = await props.validate(value); } finally { asking.value = false; }
    if (typeof verdict === 'string' || verdict === false) { refused.value = verdict || null; return; }
  }
  refused.value = null;
  emit('set', value);
}
const hue = computed<OuiTone>(() => (props.stale ? 'neutral' : ({ heating: 'orange', target: 'success', cooling: 'sky', off: 'neutral' } as const)[props.phase ?? (props.target ? 'heating' : 'off')]));
// Enter in the field sets the value, like the Set button.
function onEnter(event: KeyboardEvent) { if (event.target instanceof HTMLInputElement) void send(); }
const show = (n: number | null | undefined) => (n == null || !Number.isFinite(n) ? '—' : n.toFixed(props.digits ?? 0));
</script>
<template>
  <div class="oui-setpoint" :data-heater-row="name"><div class="oui-setpoint-row">
    <div class="oui-setpoint-label"><slot name="lead"><OuiIcon v-if="icon" :icon="icon" :size="14" tile :tone="hue" /></slot><label v-if="inputId" :for="inputId" class="oui-strong">{{ label }}</label><span v-else class="oui-strong">{{ label }}</span></div>
    <div class="oui-setpoint-read oui-num">
      <span class="oui-setpoint-now" :data-tone="hue">{{ show(current) }}<span class="oui-setpoint-unit">{{ unit }}</span></span>
      <span class="oui-meta">{{ targetLabel }} {{ target ? show(target) + ' ' + unit : offText }}<template v-if="phaseLabel && !stale"> · <span class="oui-setpoint-phase" :data-tone="hue">{{ phaseLabel }}</span></template></span>
    </div>
    <OuiSpark v-if="history" class="oui-setpoint-spark" :values="history" :tone="hue" :target="target || null" :label="historyLabel ?? label" :width="88" :height="28" />
    <div class="oui-setpoint-control" @keydown.enter="onEnter">
      <InputNumber v-model="draft" :min="validate ? undefined : min" :max="validate ? undefined : max" :placeholder="`${min ?? 0}–${max ?? ''}`" :disabled="disabled" :aria-label="inputLabel"
        :input-id="inputId" :invalid="!!shownError || undefined" :pt="{ pcInputText: { root: { 'aria-describedby': describes } } }" size="small" :input-style="{ width: '64px' }" @input="onType" />
      <Button :label="setLabel" severity="secondary" size="small" :disabled="disabled || draft == null || asking" :data-set="name" :aria-describedby="describedby" @click="send" />
      <Button :label="offLabel" severity="secondary" text size="small" :disabled="disabled || (!target && !offAlways)" :data-off="name" :aria-describedby="describedby" @click="emit('off')" />
    </div>
    <p v-if="shownError" :id="errorId" class="oui-setpoint-error" role="alert">{{ shownError }}</p>
  </div></div>
</template>
<style>
.oui-setpoint { container: oui-setpoint / inline-size; }
.oui-setpoint-row { display: grid; grid-template-columns: minmax(84px, 1fr) minmax(96px, auto) minmax(0, 1fr) auto; align-items: center; gap: var(--oui-s2) var(--oui-s3); min-height: 44px; }
.oui-setpoint-label { display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; color: var(--oui-text); }
.oui-setpoint-spark { justify-self: start; }
.oui-setpoint-phase { font-weight: 600; color: var(--oui-tone); }
.oui-setpoint-read { display: grid; }
.oui-setpoint-now[data-tone='neutral'] { color: var(--oui-text); }
.oui-setpoint-now { color: var(--oui-tone); font-size: var(--oui-text-xl); font-weight: 700; line-height: 1.15; letter-spacing: -.01em; }
.oui-setpoint-unit { margin-inline-start: .2em; font-size: .6em; font-weight: 600; }
.oui-setpoint-control { display: flex; align-items: center; gap: var(--oui-s1); grid-column: -2 / -1; }
.oui-setpoint-error { grid-column: 1 / -1; padding-bottom: var(--oui-s2); font-size: var(--oui-text-sm); text-align: end; color: var(--oui-danger); }
@container oui-setpoint (max-width: 520px) { .oui-setpoint-spark { display: none; } .oui-setpoint-row { grid-template-columns: minmax(84px, 1fr) minmax(96px, 1fr) auto; } }
@container oui-setpoint (max-width: 400px) { .oui-setpoint-row { grid-template-columns: minmax(0, 1fr) auto; } .oui-setpoint-control { grid-column: 1 / -1; justify-content: flex-end; } }
</style>
