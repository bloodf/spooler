<script setup lang="ts">
import { computed } from 'vue';

/*
 * How much filament is left, as a bar in the filament's own colour.
 *
 * The track is the full spool; the fill is what is left. A small notch marks the low-stock threshold, so a
 * glance shows how far the spool is from it. Light colours (white, natural) get an inner edge so the fill
 * never disappears into a light track. Below the threshold the empty part of the track turns warning/danger.
 */
const props = defineProps<{
  /** 0..100, or null for unknown. */
  pct: number | null;
  /** CSS paint for the fill (colour or gradient). */
  paint: string;
  /** Low-stock threshold as 0..100 of this spool, or null when not meaningful. */
  lowPct?: number | null;
  /** '' | 'low' | 'out', from lowLevel(). */
  level?: '' | 'low' | 'out';
  title?: string;
}>();
const width = computed(() => Math.max(0, Math.min(100, props.pct ?? 0)));
const notch = computed(() => (props.lowPct != null && props.lowPct > 0 && props.lowPct < 100 ? props.lowPct : null));
</script>

<template>
  <span class="lb" :class="[level, { unknown: pct === null }]" :title="title" role="presentation">
    <i class="lb-fill" :style="{ width: width + '%', background: paint }" />
    <b v-if="notch !== null" class="lb-notch" :style="{ left: notch + '%' }" />
  </span>
</template>

<style scoped>
.lb { position: relative; display: block; height: 10px; border-radius: 999px; overflow: hidden;
  background: color-mix(in srgb, var(--oui-border) 70%, transparent); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-text) 10%, transparent); }
.lb.low { background: color-mix(in srgb, var(--oui-warning, #c80) 16%, var(--oui-border)); }
.lb.out { background: color-mix(in srgb, var(--oui-danger, #c33) 18%, var(--oui-border)); }
.lb.unknown { background: repeating-linear-gradient(135deg, var(--oui-border) 0 6px, transparent 6px 12px); }
.lb-fill { position: absolute; inset: 0 auto 0 0; display: block; border-radius: inherit;
  /* inner edge + soft top highlight: white filament stays visible and the bar reads as a strand, not a flat block */
  box-shadow: inset 0 0 0 1px rgb(0 0 0 / 0.18), inset 0 2px 2px -1px rgb(255 255 255 / 0.45); transition: width 240ms ease; }
.lb-notch { position: absolute; top: 1px; bottom: 1px; width: 2px; margin-left: -1px; border-radius: 1px; background: var(--oui-text); opacity: 0.35; }
/* dark theme: a dark filament (black, navy) keeps a light edge so it does not merge into the track */
:global(.orca-dark) .lb-fill { box-shadow: inset 0 0 0 1px rgb(255 255 255 / 0.28), inset 0 2px 2px -1px rgb(255 255 255 / 0.35); }
@media (prefers-reduced-motion: reduce) { .lb-fill { transition: none; } }
</style>
