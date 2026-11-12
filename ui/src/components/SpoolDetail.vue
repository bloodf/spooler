<script setup lang="ts">
import { t, tn, fmt } from '../core/i18n';
const props = defineProps<{ detail: null | { prints: { time: number; name?: string; grams: number; cost?: number | null }[]; grams: number;
  cost: number | null; sign: string; rate: number | null; weeks: number | null } }>();
const money = (v: unknown) => (typeof v === 'number' ? (props.detail?.sign ?? '') + fmt.number(v, 2) : '–');
const date = (unix: number) => new Intl.DateTimeFormat(document.documentElement.lang || undefined, { dateStyle: 'medium' }).format(new Date(unix * 1000));
</script>
<template>
  <div class="sd" role="status" aria-live="polite">
    <p v-if="!detail" class="oui-meta">{{ t('common.loading') }}</p>
    <p v-else-if="!detail.prints.length" class="oui-meta">{{ t('detail.none') }}</p>
    <template v-else>
      <p class="oui-meta">{{ tn('detail.prints', detail.prints.length) }} · {{ fmt.number(detail.grams, 1) }} g · {{ money(detail.cost) }}</p>
      <p class="oui-meta">{{ detail.rate === null ? t('detail.noRate') : t('detail.rate', { g: Math.round(detail.rate) }) }}<template
        v-if="detail.rate !== null && detail.weeks !== null"> · {{ detail.weeks < 1 ? t('detail.lessWeek') : tn('detail.weeksLeft', Math.round(detail.weeks)) }}</template></p>
      <table class="sp-table"><thead><tr><th scope="col">{{ t('stats.col.date') }}</th><th scope="col">{{ t('stats.col.print') }}</th>
        <th scope="col" class="r">{{ t('stats.col.weight') }}</th><th scope="col" class="r">{{ t('stats.col.cost') }}</th></tr></thead>
        <tbody><tr v-for="(p, i) in detail.prints.slice(0, 20)" :key="i"><td>{{ date(p.time) }}</td><td>{{ p.name || t('stats.print') }}</td>
          <td class="r sp-num">{{ fmt.number(p.grams, 1) }} g</td><td class="r sp-num">{{ money(p.cost) }}</td></tr></tbody></table>
      <p v-if="detail.prints.length > 20" class="oui-meta">{{ t('detail.latest', { n: detail.prints.length }) }}</p>
    </template>
  </div>
</template>
<style scoped>.sd { display: grid; gap: 6px; } .sd p { margin: 0; }</style>
