<script setup lang="ts">
import { computed } from 'vue';
import type { OuiTone } from './tones';

/*
 * A small chart of one series over time: a line (a temperature, a rate) or bars (grams per week, prints per day).
 * It shows shape, not values: the current value is always in text beside it, and `label` describes it to a screen reader.
 */
const props = defineProps<{ values: (number | null)[]; type?: 'line' | 'bars'; tone?: OuiTone; width?: number; height?: number; label: string;
  /** Fixed scale; default is the series' own range (bars always start at 0). */ min?: number; max?: number;
  /** A value to hold (a heater's target): drawn as a dashed line. */ target?: number | null }>();
const W = computed(() => props.width ?? 96); const H = computed(() => props.height ?? 28);
const known = computed(() => props.values.filter((v): v is number => typeof v === 'number' && Number.isFinite(v)));
const withTarget = computed(() => (typeof props.target === 'number' ? [...known.value, props.target] : known.value));
const lo = computed(() => props.min ?? (props.type === 'bars' ? 0 : Math.min(...withTarget.value)));
const hi = computed(() => { const top = props.max ?? Math.max(...withTarget.value); return top > lo.value ? top : lo.value + 1; });
const y = (v: number) => H.value - 2 - ((v - lo.value) / (hi.value - lo.value)) * (H.value - 4);
const points = computed(() => props.values.map((v, i) => (typeof v === 'number' ? [props.values.length > 1 ? (i / (props.values.length - 1)) * (W.value - 2) + 1 : W.value / 2, y(v)] : null))
  .filter((p): p is number[] => p !== null));
const line = computed(() => points.value.map((p, i) => (i ? 'L' : 'M') + p[0].toFixed(1) + ' ' + p[1].toFixed(1)).join(''));
const area = computed(() => (points.value.length > 1 ? `${line.value}L${points.value[points.value.length - 1][0].toFixed(1)} ${H.value}L${points.value[0][0].toFixed(1)} ${H.value}Z` : ''));
const bars = computed(() => { const slot = W.value / Math.max(1, props.values.length); const w = Math.max(2, slot - 2);
  return props.values.map((v, i) => (typeof v === 'number' ? { x: i * slot + (slot - w) / 2, y: Math.min(y(v), H.value - 3), w, h: Math.max(1, H.value - 2 - Math.min(y(v), H.value - 3)) } : null)); });
</script>
<template>
  <svg class="oui-spark" :data-tone="tone ?? 'accent'" :width="W" :height="H" :viewBox="`0 0 ${W} ${H}`" role="img" :aria-label="label" focusable="false">
    <template v-if="!known.length"><path class="oui-spark-none" :d="`M1 ${H / 2}H${W - 1}`" /></template>
    <template v-else-if="type === 'bars'">
      <template v-for="(b, i) in bars" :key="i"><rect v-if="b" :x="b.x" :y="b.y" :width="b.w" :height="b.h" rx="1.5" :class="{ 'oui-spark-last': i === values.length - 1 }" /></template>
    </template>
    <template v-else>
      <path v-if="area" class="oui-spark-area" :d="area" /><path v-if="typeof target === 'number'" class="oui-spark-target" :d="`M0 ${y(target).toFixed(1)}H${W}`" /><path class="oui-spark-line" :d="line" />
      <circle v-if="points.length" class="oui-spark-dot" :cx="points[points.length - 1][0]" :cy="points[points.length - 1][1]" r="2.5" />
    </template>
  </svg>
</template>
<style>
.oui-spark { flex: none; display: block; overflow: visible; }
.oui-spark-line { fill: none; stroke: var(--oui-tone); stroke-width: 2; stroke-linecap: round; stroke-linejoin: round; }
.oui-spark-area { fill: color-mix(in srgb, var(--oui-tone) 34%, transparent); stroke: none; }
.oui-spark-target { fill: none; stroke: var(--oui-tone); stroke-width: 1; stroke-dasharray: 2 3; }
.oui-spark-dot { fill: var(--oui-tone); stroke: var(--oui-surface); stroke-width: 1.5; }
.oui-spark rect { fill: color-mix(in srgb, var(--oui-tone) 55%, var(--oui-tone-soft)); }
.oui-spark rect.oui-spark-last { fill: var(--oui-tone); }
.oui-spark-none { stroke: var(--oui-control-border); stroke-width: 1.5; stroke-dasharray: 3 4; fill: none; }
</style>
