<script setup lang="ts">
import { computed, ref } from 'vue';
import SpoolCard from './SpoolCard.vue';
import { m } from '../state/main';
import { t, tn, locale } from '../core/i18n';
import { formatWeight, shown, swatch, swatchCols, swatchMain, totals, type Spool } from '../logic/spools';

// Spools of one filament fold into one card showing their total; opening it lists each spool in its column.
const props = defineProps<{ items: Spool[]; used: number; stackKey: string }>();
const open = ref(false);
const f = computed(() => props.items[0].filament || {});
const tt = computed(() => totals(props.items));
const ex = computed(() => shown(m.disp, 'exact_weight'));
const w = computed(() => (tt.value.remaining === null ? '?' : formatWeight(tt.value.remaining, ex.value, locale.value)
  + (tt.value.original === null ? '' : ' ' + t('weight.of', { total: formatWeight(tt.value.original, ex.value, locale.value) }))));
const label = computed(() => (tt.value.percent === null || m.wMode === 'grams' ? w.value : m.wMode === 'percent' ? `${tt.value.percent}%` : `${tt.value.percent}% · ${w.value}`));
const sub = computed(() => [f.value.vendor?.name && shown(m.disp, 'vendor') ? f.value.vendor.name : '', f.value.material && shown(m.disp, 'material') ? f.value.material : '',
  tn('group.count', props.items.length), props.used ? tn('stack.inUse', props.used) : ''].filter(Boolean).join(' · '));
</script>
<template>
  <section class="st" :class="{ open }" :style="{ '--rows': items.length + 1 }" :data-stack="stackKey">
    <button type="button" class="st-head" :aria-expanded="open" @click="open = !open">
      <span class="st-sw" :style="{ background: swatch(f), borderColor: swatchCols(f).length > 1 ? swatchMain(f) : undefined }"><span class="st-count">{{ items.length }}</span></span>
      <span class="st-main">
        <span class="st-top"><strong class="st-title">{{ f.name || t('spool.numbered', { id: items[0].id }) }}</strong>
          <span class="sp-num">{{ label }}</span><span class="st-arrow" aria-hidden="true">{{ open ? '▾' : '▸' }}</span></span>
        <span v-if="shown(m.disp, 'bar')" class="st-track"><i :style="{ width: (tt.percent ?? 0) + '%', background: swatchMain(f) }" /></span>
        <span class="st-sub">{{ sub }}</span>
      </span>
    </button>
    <div v-show="open" class="st-items"><SpoolCard v-for="s in items" :key="s.id" :spool="s" in-stack /></div>
  </section>
</template>
<style scoped>
.st { display: grid; gap: 8px; grid-row: span var(--rows, 1); }
.st:not(.open) { grid-row: auto; }
.st-head { display: flex; gap: 12px; width: 100%; padding: 10px 12px; border: 1px solid var(--oui-border); border-radius: 12px; background: var(--oui-surface);
  color: var(--oui-text); font: inherit; text-align: left; cursor: pointer; min-width: 0; }
.st-sw { width: 36px; height: 36px; border-radius: 50%; border: 2px solid var(--oui-control-border, var(--oui-border)); display: grid; place-items: center; flex: none; }
.st-count { background: var(--oui-surface); color: var(--oui-text); border-radius: 999px; font-size: 12px; font-weight: 700; padding: 0 6px; }
.st-main { flex: 1; display: grid; gap: 4px; min-width: 0; }
.st-top { display: flex; gap: 8px; align-items: center; }
.st-title { flex: 1; min-width: 0; overflow-wrap: anywhere; }
.st-track { display: block; height: 6px; border-radius: 3px; background: var(--oui-border); overflow: hidden; }
.st-track i { display: block; height: 100%; }
.st-sub { color: var(--oui-muted); font-size: 12px; }
.st-items { display: grid; gap: 8px; padding-left: 16px; border-left: 2px solid var(--oui-border); }
@media (prefers-reduced-motion: reduce) { .st-arrow { transition: none; } }
</style>
