<script setup lang="ts">
import { computed } from 'vue';

/*
 * A spool as an object: a product render of the reel with the winding in the filament's own colour, as deep as the
 * filament left. Eight renders of the same spool, from full (1) to an empty reel (8), each in two layers
 * (src/assets/spool): "corpo", the neutral black reel, and "fio", a grey light map whose alpha says where the filament
 * is. The colour is in no file: it is painted under the map and mixed with hard-light, so mid-grey gives the exact
 * colour, shadow darkens and highlights lighten. White stays white, black keeps its relief, and multi-colour paints
 * (gradients) work the same way. Decorative: the weight and the colour name are always in text next to it.
 */
const props = defineProps<{ color?: string | null; colors?: string[] | null;
  /** How a multi-colour filament's colours run: side by side (default), around the spool (coaxial) or along it (longitudinal). */
  direction?: 'coaxial' | 'longitudinal' | null;
  /** Filament left, 0..1; null when unknown (drawn as the bare reel). */ fraction?: number | null; size?: number }>();

/** How much each render shows wound on the reel. */
const LEVEL_FILL = [1, 0.85, 0.7, 0.55, 0.4, 0.25, 0.08, 0];
const files = import.meta.glob('../assets/spool/*.webp', { eager: true, import: 'default' }) as Record<string, string>;
const src = (name: string) => files[`../assets/spool/${name}.webp`];

const known = computed(() => typeof props.fraction === 'number' && Number.isFinite(props.fraction));
// The render closest to the fraction. Any filament left, however little, is still level 7 ("almost empty"): the bare
// reel (8) is only for a spool with nothing on it or an unknown amount.
const level = computed(() => {
  const f = known.value ? Math.min(1, props.fraction as number) : 0;
  if (f <= 0) return 8;
  let best = 0;
  for (let n = 1; n < 7; n++) if (Math.abs(LEVEL_FILL[n] - f) < Math.abs(LEVEL_FILL[best] - f)) best = n;
  return best + 1;
});
const body = computed(() => src(`n${level.value}-corpo`));
const wind = computed(() => (level.value < 8 ? src(`n${level.value}-fio`) : ''));
// Empty paints the raw grey filament.
const paint = computed(() => {
  const cs = props.colors && props.colors.length > 1 ? props.colors : null;
  if (!cs) return props.color || '#9a9a9a';
  if (props.direction === 'longitudinal') return `linear-gradient(135deg, ${cs.join(', ')})`;
  if (props.direction === 'coaxial') {
    const step = 360 / cs.length;
    return 'conic-gradient(' + cs.map((c, i) => `${c} ${i * step}deg ${(i + 1) * step}deg`).join(', ') + ')';
  }
  return 'linear-gradient(90deg, ' + cs.map((c, i) => `${c} ${(i * 100) / cs.length}% ${((i + 1) * 100) / cs.length}%`).join(', ') + ')';
});
// Plain pixels on the element itself: the box never depends on a custom property or aspect-ratio being supported.
const px = computed(() => `${props.size ?? 40}px`);
</script>
<template>
  <span class="oui-spool" :data-level="level" :data-unknown="!known || undefined" :style="{ width: px, height: px, '--oui-spool-paint': paint }" aria-hidden="true">
    <img class="oui-spool-body" :src="body" alt="" width="160" height="160" draggable="false" />
    <span v-if="wind" class="oui-spool-wind" :style="{ '--oui-spool-map': `url(${wind})` }"><img :src="wind" alt="" width="160" height="160" draggable="false" /></span>
  </span>
</template>
<style>
/* A fixed square box (width and height inline in px) with the images contained in it: in a table cell WebKit does not
   resolve an image's height: 100% against an aspect-ratio box, so the 160 px source would grow the row. Not clipped,
   so the dark theme's rim light fades out instead of ending in a square. */
.oui-spool { position: relative; display: block; flex: none; isolation: isolate; }
.oui-spool img { display: block; width: 100%; height: 100%; max-width: 100%; max-height: 100%; object-fit: contain; user-select: none; }
.oui-spool-wind { position: absolute; inset: 0; background: var(--oui-spool-paint);
  -webkit-mask: var(--oui-spool-map) center / 100% 100% no-repeat; mask: var(--oui-spool-map) center / 100% 100% no-repeat; }
.oui-spool-wind img { mix-blend-mode: hard-light; }
/* A contact shadow: the spool stands on the card, it does not float. */
.oui-spool::after { content: ''; position: absolute; z-index: -1; left: 14%; right: 14%; bottom: 1%; height: 8%; border-radius: 50%;
  background: radial-gradient(closest-side, rgb(0 0 0 / .28), transparent); }
/* The reel is black: on the dark theme it gets a soft light rim so it does not disappear into the card. */
.orca-dark .oui-spool-body { filter: drop-shadow(0 0 .6px rgb(255 255 255 / .55)) drop-shadow(0 0 6px rgb(255 255 255 / .1)); }
</style>
