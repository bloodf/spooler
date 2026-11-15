<script setup lang="ts">
import { computed } from 'vue';
import Column from 'primevue/column';
import DataTable from 'primevue/datatable';
import { OuiIcon, OuiLevel, OuiSpool, materialTone } from '../../shared/src/components';
import { chevronDown, chevronRight, mapPin } from '../../shared/src/icons';
import SpoolChips from './SpoolChips.vue';
import { boot } from '../core/boot';
import { m, dupes } from '../state/main';
import { pickSpool } from '../state/menu';
import { t, tn, locale } from '../core/i18n';
import { formatWeight, leftLabel, levelTone, lowLevel, noteText, originalWeight, percentLeft, shown, spoolPaint, totals, type Spool, type Totals } from '../logic/spools';

// The stock list. One row per spool; spools of one filament fold into a stack row (×n) that opens to its spools,
// and a group (by location, material or manufacturer) is a header row that closes. Picking a row opens its detail.
export type Row = { key: string; group?: string; hidden?: boolean } & ({ kind: 'spool'; spool: Spool; child?: boolean } | { kind: 'stack'; items: Spool[]; used: number; open: boolean });
export interface GroupInfo { label: string; count: number; totals: Totals; open: boolean }
const props = defineProps<{ rows: Row[]; groups?: Record<string, GroupInfo> | null; selected: number | null }>();
const emit = defineEmits<{ stack: [key: string]; group: [key: string] }>();

const ex = computed(() => shown(m.disp, 'exact_weight'));
const first = (r: Row) => (r.kind === 'stack' ? r.items[0] : r.spool);
const fil = (r: Row) => first(r).filament || {};
const name = (r: Row) => fil(r).name || t('spool.numbered', { id: first(r).id });
const sum = (r: Row): Totals => (r.kind === 'stack' ? totals(r.items)
  : { percent: percentLeft(r.spool), remaining: typeof r.spool.remaining_weight === 'number' ? r.spool.remaining_weight : null, original: originalWeight(r.spool) ?? null });
const frac = (tt: Totals) => (tt.percent === null ? null : tt.percent / 100);
const level = (r: Row) => (r.kind === 'stack' ? '' : lowLevel(r.spool.remaining_weight, m.low));
const left = (tt: Totals) => leftLabel(tt.remaining, tt.percent, m.wMode, ex.value, locale.value);
const leftOf = (tt: Totals) => (m.wMode !== 'percent' && tt.remaining !== null && tt.original !== null ? t('weight.of', { total: formatWeight(tt.original, ex.value, locale.value) }) : '');
const pctSide = (tt: Totals) => (m.wMode === 'both' && tt.remaining !== null && tt.percent !== null ? `${tt.percent}%` : '');
const meta = (r: Row) => {
  const f = fil(r), s = first(r);
  const base = [f.vendor?.name && shown(m.disp, 'vendor') ? f.vendor.name : ''];
  if (r.kind === 'stack') return [...base, tn('group.count', r.items.length), r.used ? tn('stack.inUse', r.used) : ''].filter(Boolean).join(' · ');
  return [...base, f.color_hex && shown(m.disp, 'colour_code') ? '#' + f.color_hex.replace(/^#/, '').toUpperCase() : '',
    typeof f.diameter === 'number' && shown(m.disp, 'diameter') ? `${f.diameter} mm` : '', shown(m.disp, 'spool_id') ? `#${s.id}` : '', together(r)].filter(Boolean).join(' · ');
};
// With grouping off, a spool says how many of its filament there are and what they hold together.
const together = (r: Row) => { const d = r.kind === 'spool' && !r.child ? dupes.value.get(fil(r).id as number) : null; return d && d.count > 1 ? t('spool.together', { n: d.count, w: formatWeight(d.total, ex.value, locale.value) }) : ''; };
const note = (r: Row) => (r.kind === 'spool' ? noteText(r.spool, m.disp, boot.own_fields, v => t('spool.lot', { lot: v })) : '');
const selectedRow = computed(() => props.rows.find(r => (r.kind === 'spool' ? r.spool.id === props.selected : !r.open && r.items.some(s => s.id === props.selected))) ?? null);
const rowClass = (r: Row) => ({ 'sp-hidden': r.hidden, 'sp-child': r.kind === 'spool' && r.child, 'sp-archived': r.kind === 'spool' && r.spool.archived });
const rowAttrs = (r?: Row) => (r?.kind === 'spool' ? { 'data-spool': r.spool.id, 'aria-controls': 'sp-detail' } : r ? { 'data-stack': r.key } : {});
function onRow(r: Row) { if (r.kind === 'stack') emit('stack', r.key); else pickSpool(r.spool.id); }
</script>

<template>
  <DataTable :value="rows" data-key="key" size="small" selection-mode="single" :selection="selectedRow" :row-class="rowClass" class="sp-table"
             :row-group-mode="groups ? 'subheader' : undefined" group-rows-by="group"
             :pt="{ bodyRow: ({ context }: { context: { index: number } }) => rowAttrs(rows[context.index]) }" @row-click="e => onRow(e.data)">
    <template v-if="groups" #groupheader="{ data }">
      <button type="button" class="sv-ghead" :aria-expanded="groups[data.group].open" @click="emit('group', data.group)">
        <OuiIcon :icon="groups[data.group].open ? chevronDown : chevronRight" :size="14" />
        <span class="sv-gname"><strong>{{ groups[data.group].label }}</strong> <span class="oui-meta">{{ tn('group.count', groups[data.group].count) }}</span></span>
        <span class="sv-gbar"><span class="oui-meta oui-num">{{ left(groups[data.group].totals) }} {{ leftOf(groups[data.group].totals) }}<template v-if="pctSide(groups[data.group].totals)"> · {{ pctSide(groups[data.group].totals) }}</template></span>
          <OuiLevel :fraction="frac(groups[data.group].totals)" /></span>
      </button>
    </template>
    <Column :header="t('list.col.spool')" class="sp-c-spool">
      <template #body="{ data: r }">
        <div class="sp-spool">
          <OuiSpool v-bind="spoolPaint(fil(r))" :fraction="frac(sum(r))" :size="r.child ? 32 : 40" />
          <div class="sp-spool-id">
            <p class="sp-name" :title="name(r)"><span class="oui-truncate oui-strong">{{ name(r) }}</span>
              <button v-if="r.kind === 'stack'" type="button" class="oui-chip oui-num st-head" :aria-expanded="r.open" :aria-label="t('stack.toggle', { n: r.items.length, name: name(r) })" @click.stop="emit('stack', r.key)">
                <span class="st-count">×{{ r.items.length }}</span><OuiIcon :icon="r.open ? chevronDown : chevronRight" :size="12" /></button></p>
            <p v-if="meta(r) || note(r)" class="oui-meta oui-truncate"><span class="sc-subtext">{{ meta(r) }}</span><span v-if="note(r)" class="sc-note" :title="note(r)">{{ meta(r) ? ' · ' : '' }}{{ note(r) }}</span></p>
            <span v-if="r.kind === 'spool'" class="sp-narrow"><span v-if="fil(r).material && shown(m.disp, 'material')" class="oui-chip" :data-tone="materialTone(fil(r).material)">{{ fil(r).material }}</span><SpoolChips :spool="r.spool" /></span>
          </div>
        </div>
      </template>
    </Column>
    <Column v-if="shown(m.disp, 'material')" :header="t('filters.material')" class="sp-wide sp-c-mat">
      <template #body="{ data: r }"><span v-if="fil(r).material" class="oui-chip" :data-tone="materialTone(fil(r).material)">{{ fil(r).material }}</span></template>
    </Column>
    <Column v-if="shown(m.disp, 'location')" :header="t('menu.location')" class="sp-wider sp-c-loc">
      <template #body="{ data: r }"><span v-if="r.kind === 'spool'" class="sp-loc" :class="{ 'oui-muted': !r.spool.location }" :title="r.spool.location || undefined">
        <OuiIcon v-if="r.spool.location" :icon="mapPin" :size="13" /><span class="oui-truncate">{{ r.spool.location || '—' }}</span></span></template>
    </Column>
    <Column :header="t('list.col.state')" class="sp-wide sp-c-state">
      <template #body="{ data: r }"><SpoolChips v-if="r.kind === 'spool'" :spool="r.spool" data-col="state" /></template>
    </Column>
    <Column :header="t('list.col.left')" class="oui-num sp-c-left">
      <template #body="{ data: r }">
        <div class="sp-left" data-test="weight" :title="[left(sum(r)), leftOf(sum(r))].filter(Boolean).join(' ')">
          <span><strong>{{ left(sum(r)) }}</strong><span v-if="leftOf(sum(r))" class="oui-muted sp-of">{{ ' ' + leftOf(sum(r)) }}</span><span v-if="pctSide(sum(r))" class="oui-muted"> · {{ pctSide(sum(r)) }}</span></span>
          <OuiLevel v-if="shown(m.disp, 'bar')" class="sc-track" :fraction="frac(sum(r))" :tone="levelTone(level(r))"
                    :label="sum(r).percent === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct: sum(r).percent })" />
        </div>
      </template>
    </Column>
  </DataTable>
</template>

<style>
.sp-table table { table-layout: fixed; width: 100%; }
/* The name column has a share of the width; the state column takes the rest, so its chips sit side by side and wrap
   only when they must instead of stacking one per line. */
.sp-c-spool { width: 36%; } .sp-c-mat { width: 84px; } .sp-c-loc { width: 116px; } .sp-c-left { width: 148px; }
/* "of 1,000 g" is read out and in the tooltip always; it is written where the list has the room. */
.sp-of { position: absolute; width: 1px; height: 1px; overflow: hidden; clip-path: inset(50%); white-space: nowrap; }
@container sp-col (min-width: 900px) { .sp-c-left { width: 200px; } .sp-of { position: static; width: auto; height: auto; clip-path: none; } }
.sp-table tbody > tr { cursor: pointer; }
.orca-ui .sp-table tr.sp-hidden { display: none; }
.sp-spool { display: flex; align-items: center; gap: var(--oui-s3); min-width: 0; }
.sp-child .sp-spool { padding-inline-start: var(--oui-s5); }
.sp-archived .sp-spool { opacity: .72; }
.sp-spool-id { display: grid; gap: 1px; min-width: 0; }
.sp-name { display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; }
.orca-ui .st-head { flex: none; border: 0; cursor: pointer; font: inherit; font-size: var(--oui-text-xs); font-weight: 600; }
.sp-left { display: grid; gap: 4px; }
.sp-loc { display: flex; align-items: center; gap: 5px; min-width: 0; }
.sp-loc > .oui-icon { color: var(--oui-muted); }
.sp-narrow { display: none; flex-wrap: wrap; gap: var(--oui-s1); margin-top: 2px; }
/* The group header: name and count on the left, what is left in the whole group on the right (never squeezed). */
.orca-ui .sv-ghead { display: flex; align-items: center; gap: var(--oui-s2); width: 100%; padding: 2px 0; border: 0; background: none; color: var(--oui-text); font: inherit; text-align: start; cursor: pointer; }
.sv-gname { flex: 1; min-width: 0; overflow-wrap: anywhere; }
.sv-gbar { display: grid; gap: 4px; min-width: 90px; white-space: nowrap; text-align: end; }
/* Narrow list: the location goes first, then material and state move under the name. */
@container sp-col (max-width: 760px) { .orca-ui .sp-wider { display: none; } }
@container sp-col (max-width: 500px) { .orca-ui .sp-wide { display: none; } .sp-narrow { display: flex; } .sp-c-spool { width: auto; } }
</style>
