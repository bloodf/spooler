<script setup lang="ts">
import { computed } from 'vue';

/*
 * A spool, drawn: the reel seen from the side with the winding in the filament's own colour, as deep as the
 * filament left. Vector, so it is exact at any size and costs no image bytes. Decorative: the weight and the
 * colour name are always in text next to it.
 */
const props = defineProps<{ color?: string | null; colors?: string[] | null; /** Filament left, 0..1; null when unknown. */ fraction?: number | null; size?: number }>();
const HUB = 6.5; const FULL = 21;
const known = computed(() => typeof props.fraction === 'number' && Number.isFinite(props.fraction));
const wound = computed(() => (known.value ? Math.max(0, Math.min(1, props.fraction as number)) : 0));
// The winding is an annulus: equal weight is equal area, so the radius follows the square root.
// Any filament left keeps a band wide enough to show its colour.
const outer = computed(() => (wound.value > 0 ? Math.max(HUB + 4, Math.sqrt(HUB * HUB + wound.value * (FULL * FULL - HUB * HUB))) : HUB));
const bands = computed(() => {
  const list = props.colors && props.colors.length > 1 ? props.colors : [props.color || ''];
  const mid = (outer.value + HUB) / 2; const girth = 2 * Math.PI * mid;
  return list.map((paint, i) => ({ paint, mid, width: outer.value - HUB, dash: `${girth / list.length} ${girth}`, offset: -(girth / list.length) * i }));
});
</script>
<template>
  <svg class="oui-spool" :width="size ?? 40" :height="size ?? 40" viewBox="0 0 48 48" aria-hidden="true" focusable="false" :data-unknown="!known || undefined">
    <circle class="oui-spool-flange" cx="24" cy="24" r="23" />
    <g v-if="wound > 0" transform="rotate(-90 24 24)">
      <circle v-for="(b, i) in bands" :key="i" cx="24" cy="24" :r="b.mid" fill="none" :stroke="b.paint || 'currentColor'" :stroke-width="b.width"
        :stroke-dasharray="b.dash" :stroke-dashoffset="b.offset" :class="{ 'oui-spool-plain': !b.paint }" />
    </g>
    <circle v-if="wound > 0" class="oui-spool-edge" cx="24" cy="24" :r="outer" />
    <circle class="oui-spool-hub" cx="24" cy="24" :r="HUB" />
    <circle class="oui-spool-bore" cx="24" cy="24" r="2.4" />
  </svg>
</template>
<style>
/* Flange, winding, hub: three flat shapes. The winding always has a thin edge so black, white and clear filament
   stay visible on both themes. */
.oui-spool { flex: none; display: block; color: var(--oui-muted); }
.oui-spool-flange { fill: color-mix(in srgb, var(--oui-control-border) 22%, var(--oui-surface)); stroke: color-mix(in srgb, var(--oui-control-border) 70%, transparent); stroke-width: 1; }
.oui-spool[data-unknown] .oui-spool-flange { stroke-dasharray: 3 3; }
.oui-spool-plain { opacity: .5; }
.oui-spool-edge { fill: none; stroke: color-mix(in srgb, var(--oui-text) 50%, transparent); stroke-width: 1; }
.oui-spool-hub { fill: var(--oui-surface); stroke: color-mix(in srgb, var(--oui-text) 50%, transparent); stroke-width: 1; }
.oui-spool-bore { fill: var(--oui-control-border); }
/* On a band the reel is white, so the filament colour keeps a neutral frame. */
.oui-on-band .oui-spool-flange, .oui-on-band .oui-spool-hub { fill: var(--oui-on-band); stroke: rgb(0 0 0 / .25); }
.oui-on-band .oui-spool-bore { fill: rgb(0 0 0 / .45); }
</style>
