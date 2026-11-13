<script setup lang="ts">
import { computed, ref } from 'vue';
import SpoolCard from './SpoolCard.vue';
import SpoolFigure from './SpoolFigure.vue';
import LevelBar from './LevelBar.vue';
import { m } from '../state/main';
import { t, tn, locale } from '../core/i18n';
import { barFill, formatWeight, shown, swatch, totals, type Spool } from '../logic/spools';

// Spools of one filament fold into one card showing their total; opening it lists each spool in its column.
const props = defineProps<{ items: Spool[]; used: number; stackKey: string }>();
const open = ref(false);
const f = computed(() => props.items[0].filament || {});
const tt = computed(() => totals(props.items));
const ex = computed(() => shown(m.disp, 'exact_weight'));
const fw = (g: number) => formatWeight(g, ex.value, locale.value);
const big = computed(() => (tt.value.percent !== null && m.wMode === 'percent' ? `${tt.value.percent}%` : tt.value.remaining === null ? '?' : fw(tt.value.remaining)));
const ofTotal = computed(() => (m.wMode !== 'percent' && tt.value.original !== null ? t('weight.of', { total: fw(tt.value.original) }) : ''));
const pctSide = computed(() => (tt.value.percent !== null && m.wMode === 'both' ? `${tt.value.percent}%` : ''));
const sub = computed(() => [f.value.vendor?.name && shown(m.disp, 'vendor') ? f.value.vendor.name : '', f.value.material && shown(m.disp, 'material') ? f.value.material : '',
  tn('group.count', props.items.length), props.used ? tn('stack.inUse', props.used) : ''].filter(Boolean).join(' · '));
</script>
<template>
  <section class="st" :class="{ open }" :style="{ '--rows': items.length + 1 }" :data-stack="stackKey">
    <button type="button" class="st-head" :aria-expanded="open" @click="open = !open">
      <span class="st-sw"><SpoolFigure class="st-back" :paint="swatch(f)" :fraction="1" :size="58" /><SpoolFigure :paint="swatch(f)" :fraction="tt.percent === null ? null : tt.percent / 100" :size="72" /><span class="st-count">{{ items.length }}</span></span>
      <span class="st-main">
        <span class="st-top"><strong class="st-title"><span class="st-dot" :style="{ background: swatch(f) }" aria-hidden="true" />{{ f.name || t('spool.numbered', { id: items[0].id }) }}</strong><span class="st-arrow" aria-hidden="true">{{ open ? '▾' : '▸' }}</span></span>
        <span class="st-weight sp-num"><strong class="st-big">{{ big }}</strong> <span v-if="ofTotal" class="st-of">{{ ofTotal }}</span> <span v-if="pctSide" class="st-pct">{{ pctSide }}</span></span>
        <LevelBar v-if="shown(m.disp, 'bar')" class="st-track" :pct="tt.percent" :paint="barFill(f)" />
        <span class="st-sub">{{ sub }}</span>
      </span>
    </button>
    <div v-show="open" class="st-items"><SpoolCard v-for="s in items" :key="s.id" :spool="s" in-stack /></div>
  </section>
</template>
<style scoped>
.st { display: grid; gap: 8px; grid-row: span var(--rows, 1); }
.st:not(.open) { grid-row: auto; grid-template-rows: 1fr; }
/* an open stack spans several rows: its head keeps its own height */
.st.open { align-self: start; }
.st-head { display: flex; align-items: center; gap: 10px; width: 100%; padding: 10px 14px 10px 8px; border: 1px solid var(--oui-border); border-radius: 14px; background: var(--oui-surface);
  color: var(--oui-text); font: inherit; text-align: left; cursor: pointer; min-width: 0; height: 100%; }
.st-head:hover { border-color: color-mix(in srgb, var(--oui-text) 22%, var(--oui-border)); }
/* a stack: the same spool twice, one behind the other, with the count as a badge */
.st-sw { position: relative; display: block; width: 84px; height: 84px; flex: none; }
.st-sw > :deep(.sf) { position: absolute; right: 0; bottom: 0; }
.st-sw > :deep(.st-back) { left: 0; top: 0; right: auto; bottom: auto; opacity: 0.55; filter: saturate(0.85); }
.st-count { position: absolute; right: -2px; top: -2px; min-width: 20px; text-align: center; background: var(--oui-text); color: var(--oui-surface);
  border-radius: 999px; font-size: 12px; font-weight: 700; padding: 1px 6px; box-shadow: 0 0 0 2px var(--oui-surface); }
.st-main { flex: 1; display: grid; gap: 4px; min-width: 0; }
.st-top { display: flex; gap: 8px; align-items: center; }
.st-weight { display: flex; flex-wrap: wrap; align-items: baseline; gap: 2px 6px; }
.st-big { font-size: 20px; font-weight: 700; line-height: 1.1; }
.st-of, .st-pct { color: var(--oui-muted); font-size: 12px; }
.st-pct { margin-left: auto; font-weight: 600; }
.st-title { flex: 1; font-size: 14px; font-weight: 600; min-width: 0; overflow-wrap: anywhere; }
.st-dot { display: inline-block; width: 10px; height: 10px; margin-right: 6px; border-radius: 50%; border: 1px solid color-mix(in srgb, var(--oui-text) 25%, transparent); }
.st-sub { color: var(--oui-muted); font-size: 12px; }
.st-items { display: grid; gap: 8px; padding-left: 16px; border-left: 2px solid var(--oui-border); }
@media (prefers-reduced-motion: reduce) { .st-arrow { transition: none; } }
</style>
