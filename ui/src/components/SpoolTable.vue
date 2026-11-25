<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, ref, watch } from 'vue';
import Column from 'primevue/column';
import DataTable from 'primevue/datatable';
import { OuiIcon, OuiLevel, OuiSpool, OuiSwatch } from '@orca-plugins/ui-foundation/src/components';
import { chevronDown, chevronRight, edit, mapPin } from '@orca-plugins/ui-foundation/src/icons';
import SpoolChips from './SpoolChips.vue';
import { boot } from '../core/boot';
import { m, dupes } from '../state/main';
import { menu, pickSpool, pickStack, openEditor } from '../state/menu';
import { t, tn, locale } from '../core/i18n';
import { colorFamily, emptyCount, formatWeight, leftLabel, levelTone, lowLevel, noteText, originalWeight, percentLeft, shown, spoolDirection, spoolPaint, totals, type Spool, type Totals } from '../logic/spools';

// The stock list. One row per spool; spools of one filament fold into a stack row (×n) that opens to its spools,
// and a group (by location, material or manufacturer) is a header row that closes. Picking a row opens its detail.
// With `cards` the same rows draw as a grid of cards (Spools toolbar > Cards): a stack card opens to its spools' cards.
export type Row = { key: string; group?: string; hidden?: boolean } & ({ kind: 'spool'; spool: Spool; child?: boolean } | { kind: 'stack'; items: Spool[]; used: number; open: boolean });
export interface GroupInfo { label: string; count: number; totals: Totals; open: boolean }
const props = defineProps<{ rows: Row[]; groups?: Record<string, GroupInfo> | null; selected: number | null; cards?: boolean }>();
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
  if (r.kind === 'stack') return [...base, tn('group.count', r.items.length), emptyCount(r.items) ? tn('stack.empty', emptyCount(r.items)) : '', r.used ? tn('stack.inUse', r.used) : ''].filter(Boolean).join(' · ');
  return [...base, f.color_hex && shown(m.disp, 'colour_code') ? '#' + f.color_hex.replace(/^#/, '').toUpperCase() : '',
    typeof f.diameter === 'number' && shown(m.disp, 'diameter') ? `${f.diameter} mm` : '', shown(m.disp, 'spool_id') ? `#${s.id}` : '', together(r)].filter(Boolean).join(' · ');
};
// With grouping off, a spool says how many of its filament there are and what they hold together.
const together = (r: Row) => { const d = r.kind === 'spool' && !r.child ? dupes.value.get(fil(r).id as number) : null; return d && d.count > 1 ? t('spool.together', { n: d.count, w: formatWeight(d.total, ex.value, locale.value) }) : ''; };
const note = (r: Row) => (r.kind === 'spool' ? noteText(r.spool, m.disp, boot.own_fields, v => t('spool.lot', { lot: v })) : '');
// The row of the open detail: the spool's, or its closed stack's; a stack whose list is open is its own row.
const stackOpen = (r: Row) => r.kind === 'stack' && !!menu.stack && menu.id == null && r.items.every(s => menu.stack!.includes(s.id));
const selectedRow = computed(() => props.rows.find(r => stackOpen(r) || (r.kind === 'spool' ? r.spool.id === props.selected : !r.open && r.items.some(s => s.id === props.selected))) ?? null);
const rowClass = (r: Row) => ({ 'sp-hidden': r.hidden, 'sp-child': r.kind === 'spool' && r.child, 'sp-archived': r.kind === 'spool' && r.spool.archived });
const rowAttrs = (r?: Row) => (r?.kind === 'spool' ? { 'data-spool': r.spool.id, 'aria-controls': 'sp-detail' } : r ? { 'data-stack': r.key } : {});
const colourOf = (r: Row) => { const f = fil(r), fam = colorFamily(f);
  return [fam ? t(`colour.${fam}` as any) : '', f.color_hex ? '#' + f.color_hex.replace(/^#/, '').toUpperCase() : ''].filter(Boolean).join(' · '); };
const isSel = (r: Row) => r === selectedRow.value;
// A stack opens its list in the detail; its ×n chevron opens it in place.
function onRow(r: Row) { if (r.kind === 'stack') pickStack(r.items.map(s => s.id)); else pickSpool(r.spool.id); }

// Only the parts of the list near the view are drawn. The rows go in parts of PART; a part out of view is an empty box as
// tall as it was when drawn (or as tall as its rows are on average), so the scroll bar, scroll position and every row
// stay reachable. Thousands of spools drew every row on each Spoolman refresh and held the page for seconds.
// ponytail: parts are whole tables or card grids, so the table's Up/Down keys stop at a part's edge (Tab still moves on).
const PART = 48;   // a multiple of 1 to 4 (and 6) card columns: no half-filled card row at a part's end
const parts = computed(() => { const out: { start: number; rows: Row[] }[] = [];
  for (let i = 0; i < props.rows.length; i += PART) out.push({ start: i, rows: props.rows.slice(i, i + PART) }); return out; });
const near = ref(new Set([0, 1]));
const tall = new Map<number, number>();   // drawn height of a part, by its index
const perRow = ref(0);                    // average drawn row height
const boxHeight = (i: number) => `${tall.get(i) ?? parts.value[i].rows.length * (perRow.value || (props.cards ? 60 : 56))}px`;
const index = computed(() => new Map(props.rows.map((r, i) => [r.key, i])));
// A group's header shows once, at its first row, also where that row starts a part.
const groupStart = (r: Row) => { const i = index.value.get(r.key) ?? 0; return i === 0 || props.rows[i - 1].group !== r.group; };
let seen: IntersectionObserver | undefined;
let sizes: ResizeObserver | undefined;
const boxes = new Map<number, HTMLElement>();
function box(el: unknown, i: number) {
  const old = boxes.get(i);
  if (old === el) return;
  if (old) { seen?.unobserve(old); sizes?.unobserve(old); boxes.delete(i); }
  if (!(el instanceof HTMLElement)) return;
  boxes.set(i, el);
  if (typeof IntersectionObserver !== 'undefined' && !seen) {
    seen = new IntersectionObserver(entries => {
      const next = new Set(near.value);
      // A hidden list (another tab) reports nothing in view: keep what was drawn, so it is there when the tab comes back.
      for (const e of entries) { const k = Number((e.target as HTMLElement).dataset.part);
        if (e.isIntersecting) next.add(k); else if (e.boundingClientRect.height > 0) next.delete(k); }
      near.value = next;
    }, { root: el.closest('.sp-scroll'), rootMargin: '600px 0px' });
  }
  if (typeof ResizeObserver !== 'undefined' && !sizes) {
    sizes = new ResizeObserver(entries => {
      for (const e of entries) {
        const t = e.target as HTMLElement, k = Number(t.dataset.part);
        if (t.dataset.drawn !== '1' || !e.contentRect.height) continue;
        tall.set(k, e.contentRect.height);
        // Next frame: a size change made inside this callback would be a ResizeObserver loop.
        if (!perRow.value) { const h = e.contentRect.height / Math.max(1, parts.value[k]?.rows.length ?? 1); requestAnimationFrame(() => { perRow.value ||= h; }); }
      }
    });
  }
  seen?.observe(el); sizes?.observe(el);
}
// Other rows (filter, sort, group, a refresh that changed them): the old heights no longer fit.
watch(() => props.rows, () => tall.clear());
watch(() => props.cards, () => { tall.clear(); perRow.value = 0; });
onBeforeUnmount(() => { seen?.disconnect(); sizes?.disconnect(); });
// Up/Down on the last (first) row of a table part go on to the next (previous) part's row.
async function partKeys(e: KeyboardEvent, i: number) {
  if (props.cards || (e.key !== 'ArrowDown' && e.key !== 'ArrowUp')) return;
  const row = (e.target as HTMLElement).closest('tr');
  const down = e.key === 'ArrowDown';
  if (!row || (down ? row.nextElementSibling : row.previousElementSibling)) return;
  const j = i + (down ? 1 : -1);
  if (j < 0 || j >= parts.value.length) return;
  e.preventDefault();
  boxes.get(j)?.scrollIntoView({ block: 'nearest' });
  near.value = new Set([...near.value, j]);
  await nextTick();
  const rows = boxes.get(j)?.querySelectorAll<HTMLElement>('tbody tr[data-spool], tbody tr[data-stack]');
  (down ? rows?.[0] : rows?.[rows.length - 1])?.focus();
}
</script>

<template>
  <div class="sp-parts">
  <div v-for="(part, pi) in parts" :key="pi" :ref="el => box(el, pi)" class="sp-part" :class="{ 'sp-cont': pi > 0 }" :data-part="pi"
       :data-drawn="near.has(pi) ? '1' : undefined" @keydown="e => partKeys(e, pi)">
  <div v-if="!near.has(pi)" class="sp-part-box" :style="{ height: boxHeight(pi) }" />
  <div v-else-if="cards" class="sc-grid" data-test="cards">
    <template v-for="r in part.rows" :key="r.key">
      <button v-if="groups && groupStart(r)" type="button" class="sv-ghead sc-ghead" :aria-expanded="groups[r.group!].open" @click="emit('group', r.group!)">
        <OuiIcon :icon="groups[r.group!].open ? chevronDown : chevronRight" :size="14" />
        <span class="sv-gname"><strong>{{ groups[r.group!].label }}</strong> <span class="oui-meta">{{ tn('group.count', groups[r.group!].count) }}</span></span>
        <span class="sv-gbar"><span class="oui-meta oui-num">{{ left(groups[r.group!].totals) }} {{ leftOf(groups[r.group!].totals) }}</span><OuiLevel :fraction="frac(groups[r.group!].totals)" /></span>
      </button>
      <button v-if="!r.hidden" type="button" class="sc-card" :class="[rowClass(r), { 'sc-sel': isSel(r) }]" v-bind="rowAttrs(r)"
 :aria-current="isSel(r) || undefined" @click="onRow(r)">
        <OuiSpool v-bind="spoolPaint(fil(r))" :direction="spoolDirection(fil(r))" :fraction="frac(sum(r))" :size="r.kind === 'spool' && r.child ? 48 : 64" />
        <span class="sc-body">
          <span class="sp-name"><span class="oui-truncate oui-strong" :title="name(r)">{{ name(r) }}</span>
            <span v-if="r.kind === 'stack'" class="oui-chip oui-num st-head"><span class="st-count">×{{ r.items.length }}</span></span></span>
          <span v-if="fil(r).vendor?.name && shown(m.disp, 'vendor')" class="oui-meta sc-wrap" :title="fil(r).vendor!.name">{{ fil(r).vendor!.name }}</span>
          <span class="sc-line"><span v-if="fil(r).material && shown(m.disp, 'material')" class="oui-chip">{{ fil(r).material }}</span>
            <span v-if="colourOf(r)" class="sc-colour oui-meta"><OuiSwatch :color="spoolPaint(fil(r)).color || '#9a9a9a'" /><span class="oui-truncate">{{ colourOf(r) }}</span></span></span>
          <span class="sp-left oui-num" data-test="weight"><span><strong>{{ left(sum(r)) }}</strong><span v-if="leftOf(sum(r))" class="oui-muted">{{ ' ' + leftOf(sum(r)) }}</span><span v-if="pctSide(sum(r))" class="oui-muted"> · {{ pctSide(sum(r)) }}</span></span>
            <OuiLevel v-if="shown(m.disp, 'bar')" class="sc-track" :fraction="frac(sum(r))" :tone="levelTone(level(r))"
                      :label="sum(r).percent === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct: sum(r).percent })" /></span>
          <span v-if="r.kind === 'spool' && r.spool.location && shown(m.disp, 'location')" class="sp-loc oui-meta"><OuiIcon :icon="mapPin" :size="13" /><span class="oui-truncate">{{ r.spool.location }}</span></span>
          <span v-if="r.kind === 'stack'" class="oui-meta">{{ [emptyCount(r.items) ? tn('stack.empty', emptyCount(r.items)) : '', r.used ? tn('stack.inUse', r.used) : ''].filter(Boolean).join(' · ') }}</span>
          <SpoolChips v-if="r.kind === 'spool'" :spool="r.spool" band />
        </span>
      </button>
    </template>
  </div>
  <DataTable v-else :value="part.rows" data-key="key" size="small" selection-mode="single" :selection="selectedRow" :row-class="rowClass" class="sp-table"
             :row-group-mode="groups ? 'subheader' : undefined" group-rows-by="group"
             :pt="{ bodyRow: ({ context }: { context: { index: number } }) => rowAttrs(part.rows[context.index]) }" @row-click="e => onRow(e.data)">
    <template v-if="groups" #groupheader="{ data }">
      <span v-if="!groupStart(data)" class="sp-gcont" />
      <button v-else type="button" class="sv-ghead" :aria-expanded="groups[data.group].open" @click="emit('group', data.group)">
        <OuiIcon :icon="groups[data.group].open ? chevronDown : chevronRight" :size="14" />
        <span class="sv-gname"><strong>{{ groups[data.group].label }}</strong> <span class="oui-meta">{{ tn('group.count', groups[data.group].count) }}</span></span>
        <span class="sv-gbar"><span class="oui-meta oui-num">{{ left(groups[data.group].totals) }} {{ leftOf(groups[data.group].totals) }}<template v-if="pctSide(groups[data.group].totals)"> · {{ pctSide(groups[data.group].totals) }}</template></span>
          <OuiLevel :fraction="frac(groups[data.group].totals)" /></span>
      </button>
    </template>
    <Column :header="t('list.col.spool')" class="sp-c-spool">
      <template #body="{ data: r }">
        <div class="sp-spool">
          <OuiSpool v-bind="spoolPaint(fil(r))" :direction="spoolDirection(fil(r))" :fraction="frac(sum(r))" :size="r.child ? 32 : 40" />
          <div class="sp-spool-id">
            <p class="sp-name" :title="name(r)"><span class="oui-truncate oui-strong">{{ name(r) }}</span>
              <button v-if="r.kind === 'stack'" type="button" class="oui-chip oui-num st-head" :aria-expanded="r.open" :aria-label="t('stack.toggle', { n: r.items.length, name: name(r) })" @click.stop="emit('stack', r.key)">
                <span class="st-count">×{{ r.items.length }}</span><OuiIcon :icon="r.open ? chevronDown : chevronRight" :size="12" /></button>
              <button v-else-if="m.source === 'spoolman'" type="button" class="sp-edit" :aria-label="t('editor.editTitle', { id: r.spool.id })" :title="t('editor.editTitle', { id: r.spool.id })"
                      :data-edit="r.spool.id" @click.stop="openEditor(r.spool.id)"><OuiIcon :icon="edit" :size="13" /></button></p>
            <p v-if="meta(r) || note(r)" class="oui-meta oui-truncate"><span class="sc-subtext">{{ meta(r) }}</span><span v-if="note(r)" class="sc-note" :title="note(r)">{{ meta(r) ? ' · ' : '' }}{{ note(r) }}</span></p>
            <span v-if="r.kind === 'spool'" class="sp-narrow"><span v-if="fil(r).material && shown(m.disp, 'material')" class="oui-chip">{{ fil(r).material }}</span><SpoolChips :spool="r.spool" /></span>
          </div>
        </div>
      </template>
    </Column>
    <Column v-if="shown(m.disp, 'material')" :header="t('filters.material')" class="sp-wide sp-c-mat">
      <template #body="{ data: r }"><span v-if="fil(r).material" class="oui-chip">{{ fil(r).material }}</span></template>
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
  </div>
  </div>
</template>

<style>
/* A part of the list after the first: one table under the other, its header row not repeated. */
.orca-ui .sp-cont thead { display: none; }
.sp-cont > .sc-grid { padding-top: 0; } .sp-part:not(:last-child) > .sc-grid { padding-bottom: var(--oui-s2); }
.orca-ui tr:has(> td > .sp-gcont) { display: none; }
/* Cards: neutral, as many 248 px columns as fit (three beside the open detail at 1280 px), one in a narrow window. The
   drawn spool is the colour on the card. The cards of a row share its height, with the state chips at the bottom; chips
   and names wrap rather than cut. The open one has the teal frame. */
.sc-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(min(248px, 100%), 1fr)); gap: var(--oui-s2); padding: var(--oui-s3); }
.orca-ui .sc-ghead { grid-column: 1 / -1; padding: var(--oui-s1) 0; border-bottom: 1px solid var(--oui-border); }
.orca-ui .sc-card { display: flex; gap: var(--oui-s3); align-items: flex-start; min-width: 0; padding: var(--oui-s3); border: 0; border-radius: var(--oui-radius-lg);
  background: var(--oui-raised); box-shadow: inset 0 0 0 1px var(--oui-border); color: var(--oui-text); font: inherit; text-align: start; cursor: pointer; }
.orca-ui .sc-card:hover { box-shadow: inset 0 0 0 1px var(--oui-control-border); }
.orca-ui .sc-card:focus-visible { outline: 2px solid var(--oui-primary-mark); outline-offset: 1px; }
.orca-ui .sc-card.sc-sel { box-shadow: inset 0 0 0 2px var(--oui-primary-mark); }
.sc-card.sp-child { margin-inline-start: var(--oui-s4); }
.sc-card.sp-archived > * { opacity: .72; }
.sc-body { display: flex; flex-direction: column; gap: 4px; flex: 1; align-self: stretch; min-width: 0; }
.sc-body > .sp-chips { margin-top: auto; padding-top: 2px; }
.orca-ui .sc-body .oui-chip, .orca-ui .sc-body .oui-status { height: auto; min-height: 20px; padding-block: 2px; line-height: 1.25; white-space: normal; overflow-wrap: anywhere; }
.sc-body .oui-chip .oui-truncate, .sc-wrap { overflow: visible; white-space: normal; overflow-wrap: anywhere; }
.sc-body .sp-name > .oui-truncate { display: -webkit-box; -webkit-line-clamp: 2; -webkit-box-orient: vertical; white-space: normal; overflow-wrap: anywhere; }
.sc-line { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); min-width: 0; }
.sc-colour { display: inline-flex; align-items: center; gap: 5px; min-width: 0; }
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
.sp-edit { flex: none; display: inline-grid; place-items: center; width: 24px; height: 24px; padding: 0; border: 0; border-radius: var(--oui-radius); color: var(--oui-muted); background: none; cursor: pointer; }
.sp-edit:hover { color: var(--oui-text); background: var(--oui-control); }
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
