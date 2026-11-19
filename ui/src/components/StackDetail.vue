<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiIcon, OuiLevel, OuiPanel, OuiSpool, OuiSwatch } from '../../shared/src/components';
import { layers, mapPin, x } from '../../shared/src/icons';
import SpoolChips from './SpoolChips.vue';
import { m } from '../state/main';
import { closeDetail, pickSpool } from '../state/menu';
import { t, tn, locale } from '../core/i18n';
import { emptyCount, formatWeight, leftLabel, levelTone, lowLevel, originalWeight, percentLeft, shown, spoolDirection, spoolPaint, totals, type Spool } from '../logic/spools';

// A stack (×n) opened from the list: its filament, what its spools hold together, and each spool to open.
const props = defineProps<{ spools: Spool[] }>();
const f = computed(() => props.spools[0]?.filament || {});
const sum = computed(() => totals(props.spools));
const ex = computed(() => shown(m.disp, 'exact_weight'));
const w = (g: number | null) => (g === null ? '' : formatWeight(g, ex.value, locale.value));
const left = (r: number | null, pct: number | null) => leftLabel(r, pct, m.wMode, ex.value, locale.value);
const of = (o: number | null | undefined) => (typeof o === 'number' ? ' ' + t('weight.of', { total: w(o) }) : '');
const count = computed(() => [tn('group.count', props.spools.length), emptyCount(props.spools) ? tn('stack.empty', emptyCount(props.spools)) : ''].filter(Boolean).join(' · '));
const frac = (p: number | null) => (p === null ? null : p / 100);
</script>

<template>
  <OuiPanel :title="f.name || t('spool.numbered', { id: spools[0]?.id })" :icon="layers" tone="accent" :meta="count" data-test="stack-detail">
    <template #actions>
      <Button severity="secondary" text size="small" :aria-label="t('detail.close')" :title="t('detail.close')" data-test="detail-close" @click="closeDetail"><template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
    </template>
    <div class="sk-head">
      <OuiSpool v-bind="spoolPaint(f)" :direction="spoolDirection(f)" :fraction="frac(sum.percent)" :size="88" />
      <div class="sk-sum">
        <p class="oui-meta sd-sub"><OuiSwatch v-bind="spoolPaint(f)" />{{ [f.vendor?.name, f.material].filter(Boolean).join(' · ') }}</p>
        <p class="oui-num" data-test="stack-total"><strong>{{ left(sum.remaining, sum.percent) }}</strong><span class="oui-muted">{{ of(sum.original) }}<template v-if="sum.percent !== null"> · {{ sum.percent }}%</template></span></p>
        <OuiLevel :fraction="frac(sum.percent)" />
      </div>
    </div>
    <ul class="sk-list" :aria-label="count">
      <li v-for="s in spools" :key="s.id">
        <button type="button" class="sk-spool" :data-pick="s.id" aria-controls="sp-detail" @click="pickSpool(s.id, true)">
          <OuiSpool v-bind="spoolPaint(s.filament || {})" :direction="spoolDirection(s.filament || {})" :fraction="frac(percentLeft(s))" :size="44" />
          <span class="sk-body">
            <span class="oui-num"><strong>#{{ s.id }}</strong> · {{ left(typeof s.remaining_weight === 'number' ? s.remaining_weight : null, percentLeft(s)) }}<span class="oui-muted">{{ of(originalWeight(s)) }}</span></span>
            <OuiLevel :fraction="frac(percentLeft(s))" :tone="levelTone(lowLevel(s.remaining_weight, m.low))" />
            <span v-if="s.location" class="sp-loc oui-meta"><OuiIcon :icon="mapPin" :size="13" /><span class="oui-truncate">{{ s.location }}</span></span>
            <SpoolChips :spool="s" band />
          </span>
        </button>
      </li>
    </ul>
  </OuiPanel>
</template>

<style>
.sk-head { display: flex; align-items: center; gap: var(--oui-s4); }
.sk-sum { display: grid; gap: var(--oui-s1); flex: 1; min-width: 0; font-size: var(--oui-text-lg); }
.sk-list { display: grid; gap: var(--oui-s2); margin: var(--oui-s4) 0 0; padding: 0; list-style: none; }
.orca-ui .sk-spool { display: flex; align-items: center; gap: var(--oui-s3); width: 100%; padding: var(--oui-s2) var(--oui-s3); border: 1px solid var(--oui-border); border-radius: var(--oui-radius);
  background: none; color: var(--oui-text); font: inherit; text-align: start; cursor: pointer; }
.orca-ui .sk-spool:hover { border-color: var(--oui-primary); }
.orca-ui .sk-spool:focus-visible { outline: 2px solid var(--oui-primary); outline-offset: 1px; }
.sk-body { display: grid; gap: 4px; flex: 1; min-width: 0; }
</style>
