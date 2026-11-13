<script setup lang="ts">
import { computed } from 'vue';
import { spoolLevel } from '../logic/spools';

/*
 * The spool as an object: a product render with the winding in the filament's own colour.
 *
 * Each level has two layers (src/assets/spool): the "corpo", a neutral black reel, and the "fio", a grey light
 * map whose alpha says where filament is. The colour is not in any file: it is painted under the map and
 * mixed with hard-light, so mid-grey gives the exact colour, shadow darkens and highlights lighten. White
 * stays white, black keeps its relief, and multi-colour paints (gradients) work the same way.
 *
 * Decorative: the card always says the weight and colour in text next to it.
 */
const props = defineProps<{
  /** CSS paint for the filament (a colour or a gradient); empty draws raw grey filament. */
  paint?: string;
  /** Filament left, 0..1; null for unknown (drawn as the bare reel). */
  fraction: number | null | undefined;
  /** Width in px. */
  size?: number;
}>();

const files = import.meta.glob('../assets/spool/*.webp', { eager: true, import: 'default' }) as Record<string, string>;
const src = (name: string) => files[`../assets/spool/${name}.webp`];
const level = computed(() => spoolLevel(props.fraction));
const body = computed(() => src(`n${level.value}-corpo`));
const wind = computed(() => (level.value < 8 ? src(`n${level.value}-fio`) : ''));
</script>

<template>
  <span class="sf" :data-level="level" :style="{ '--sf-size': (size ?? 64) + 'px', '--sf-paint': paint || '#9a9a9a' }" aria-hidden="true">
    <img class="sf-body" :src="body" alt="" width="160" height="160" draggable="false" />
    <span v-if="wind" class="sf-wind" :style="{ '--sf-map': `url(${wind})` }"><img :src="wind" alt="" width="160" height="160" draggable="false" /></span>
  </span>
</template>

<style scoped>
.sf { position: relative; display: block; flex: none; width: var(--sf-w, var(--sf-size)); aspect-ratio: 1; isolation: isolate; }
.sf img { display: block; width: 100%; height: 100%; user-select: none; }
.sf-wind { position: absolute; inset: 0; background: var(--sf-paint);
  -webkit-mask: var(--sf-map) center / 100% 100% no-repeat; mask: var(--sf-map) center / 100% 100% no-repeat; }
.sf-wind img { mix-blend-mode: hard-light; }
/* contact shadow: the spool stands on the card, it does not float */
.sf::after { content: ''; position: absolute; z-index: -1; left: 14%; right: 14%; bottom: 1%; height: 8%; border-radius: 50%;
  background: radial-gradient(closest-side, rgb(0 0 0 / 0.28), transparent); }
/* the reel is black: on a dark theme it gets a soft light rim so it does not disappear into the card */
.orca-dark .sf-body { filter: drop-shadow(0 0 0.6px rgb(255 255 255 / 0.55)) drop-shadow(0 0 6px rgb(255 255 255 / 0.10)); }
</style>
