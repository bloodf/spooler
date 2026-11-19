<script setup lang="ts">
import { computed, ref } from 'vue';
import Button from 'primevue/button';
import InputNumber from 'primevue/inputnumber';
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';
import OuiSpark from './OuiSpark.vue';
import type { OuiTone } from './tones';

/*
 * A controlled value (a heater, a fan): what it reads now, what it is set to, and the control to change it.
 * The reading is the large figure; the target sits under it. A missing reading is a dash, never 0.
 */
const props = defineProps<{ label: string; icon?: OuiIconData; /** Recent readings, oldest first: drawn as a small line. */ history?: (number | null)[]; historyLabel?: string; current?: number | null; target?: number | null; unit: string;
  min?: number; max?: number; digits?: number; disabled?: boolean; describedby?: string;
  /** What the heater is doing: heating is orange, at target green, cooling blue, off grey. Always said in words too (`phaseLabel`). */ phase?: 'heating' | 'target' | 'cooling' | 'off'; phaseLabel?: string;
  /** Last known values of a printer the page can no longer see: drawn grey, with no phase. */ stale?: boolean;
  setLabel: string; offLabel: string; targetLabel: string; offText: string; inputLabel: string; name?: string }>();
const emit = defineEmits<{ set: [value: number]; off: [] }>();
const draft = ref<number | null>(null);
const hue = computed<OuiTone>(() => (props.stale ? 'neutral' : ({ heating: 'orange', target: 'success', cooling: 'sky', off: 'neutral' } as const)[props.phase ?? (props.target ? 'heating' : 'off')]));
// Enter in the field sets the value, like the Set button.
function onEnter(event: KeyboardEvent) { if (event.target instanceof HTMLInputElement && draft.value != null && !props.disabled) emit('set', draft.value); }
const show = (n: number | null | undefined) => (n == null || !Number.isFinite(n) ? '—' : n.toFixed(props.digits ?? 0));
</script>
<template>
  <div class="oui-setpoint" :data-heater-row="name"><div class="oui-setpoint-row">
    <div class="oui-setpoint-label"><slot name="lead"><OuiIcon v-if="icon" :icon="icon" :size="14" tile :tone="hue" /></slot><span class="oui-strong">{{ label }}</span></div>
    <div class="oui-setpoint-read oui-num">
      <span class="oui-setpoint-now" :data-tone="hue">{{ show(current) }}<span class="oui-setpoint-unit">{{ unit }}</span></span>
      <span class="oui-meta">{{ targetLabel }} {{ target ? show(target) + ' ' + unit : offText }}<template v-if="phaseLabel && !stale"> · <span class="oui-setpoint-phase" :data-tone="hue">{{ phaseLabel }}</span></template></span>
    </div>
    <OuiSpark v-if="history" class="oui-setpoint-spark" :values="history" :tone="hue" :target="target || null" :label="historyLabel ?? label" :width="88" :height="28" />
    <div class="oui-setpoint-control" @keydown.enter="onEnter">
      <InputNumber v-model="draft" :min="min" :max="max" :placeholder="`${min ?? 0}–${max ?? ''}`" :disabled="disabled" :aria-label="inputLabel"
        :aria-describedby="describedby" size="small" :input-style="{ width: '64px' }" />
      <Button :label="setLabel" severity="secondary" size="small" :disabled="disabled || draft == null" :data-set="name" :aria-describedby="describedby"
        @click="draft != null && emit('set', draft)" />
      <Button :label="offLabel" severity="secondary" text size="small" :disabled="disabled || !target" :data-off="name" :aria-describedby="describedby" @click="emit('off')" />
    </div>
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
@container oui-setpoint (max-width: 520px) { .oui-setpoint-spark { display: none; } .oui-setpoint-row { grid-template-columns: minmax(84px, 1fr) minmax(96px, 1fr) auto; } }
@container oui-setpoint (max-width: 400px) { .oui-setpoint-row { grid-template-columns: minmax(0, 1fr) auto; } .oui-setpoint-control { grid-column: 1 / -1; justify-content: flex-end; } }
</style>
