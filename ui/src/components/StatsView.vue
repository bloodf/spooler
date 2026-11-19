<script setup lang="ts">
import { computed, onBeforeUnmount, onMounted, ref } from 'vue';
import Button from 'primevue/button';
import Column from 'primevue/column';
import DataTable from 'primevue/datatable';
import Select from 'primevue/select';
import { OuiBanner, OuiEmpty, OuiIcon, OuiLevel, OuiPageHeader, OuiPanel, OuiReadout, OuiSpool, OuiStatus, OuiSwatch, type OuiTone } from '../../shared/src/components';
import { boxes, chart, chevronDown, chevronRight, coins, download, error as errorIcon, history, hourglass, layers, percent, printer, refresh, scale, target, trash, warehouse, warning } from '../../shared/src/icons';
import * as bridge from '../core/bridge';
import { m, note, on } from '../state/main';
import { spoolFraction } from '../logic/spools';
import { t, tn, fmt, locale } from '../core/i18n';

// Stats from the prints Spooler booked: tiles, weekly use, materials, most used, running low, shelf, waste and
// history (CSV export). Weights and money follow the page language; the currency sign comes from the plugin.
// Chart colours are the system's seven hues, one per series in the order of the legend beside it (a material keeps its
// hue across the charts of the page); filament colours stay in swatches and in the weekly bars.
const period = ref(readPeriod());
function readPeriod() { try { return localStorage.getItem('spooler.period') || '30'; } catch { return '30'; } }
const data = ref<any>(null);
const error = ref('');
const exporting = ref(false);
const histOpen = ref(readFlag());
function readFlag() { try { return localStorage.getItem('spooler.history') === '1'; } catch { return false; } }
const shownN = ref(7);
const W_TONES: Record<string, OuiTone> = { model: 'magenta', support: 'cobalt', purge: 'violet', calibration: 'teal' };
const SERIES: OuiTone[] = ['magenta', 'cobalt', 'teal', 'orange', 'violet', 'sky', 'lime'];
const W_KEYS = [['model', 'mcost'], ['support', 'scost'], ['purge', 'pcost'], ['calibration', 'ccost']] as const;

function ask() { bridge.postMain({ type: 'stats', period: period.value }); }
let offs: (() => void)[] = [];
onMounted(() => {
  offs = [on('stats', (d: any) => { if (d && d.period === period.value) { data.value = d; error.value = d.error || ''; } }),
    on('statsExport', (d: any) => { exporting.value = false; if (d.text) note(d.ok !== false ? 'success' : 'error', d.text, 'stats-export'); })];
  ask();
});
onBeforeUnmount(() => offs.forEach(f => f()));
function setPeriod(v: string) {
  period.value = v; shownN.value = 7; data.value = null;
  try { localStorage.setItem('spooler.period', v); } catch { /* per viewer */ }
  ask();
}
function toggleHist() { histOpen.value = !histOpen.value; try { localStorage.setItem('spooler.history', histOpen.value ? '1' : '0'); } catch { /* per viewer */ } }
function exportCsv() { exporting.value = true; bridge.postMain({ type: 'stats_export', period: period.value }); }

const periods = computed(() => (['30', '90', 'year', 'all'] as const).map(v => ({ value: v, label: t(`stats.period.${v}`) })));
const w = (g: number) => (g >= 1000 ? `${fmt.number(g / 1000, 2)} kg` : `${fmt.number(Math.round(g))} g`);
const split = (text: string) => { const i = text.lastIndexOf(' '); return i < 0 ? { value: text, unit: '' } : { value: text.slice(0, i), unit: text.slice(i + 1) }; };
const money = (v: unknown) => (typeof v === 'number' ? fmt.money(data.value?.sign ?? '', v) : '—');
const col = (c?: string) => (c ? '#' + c : null);
// A most-used spool's fill from the stock list; gone from it (or never identified) draws the bare reel.
const topFill = (id: unknown) => spoolFraction(m.spools.find(s => s.id === id));
const date = (unix: number) => {
  const d = new Date(unix * 1000), now = new Date(), day = new Date(now.getFullYear(), now.getMonth(), now.getDate()).getTime();
  const hm = fmt.time(unix);
  if (d.getTime() >= day) return t('when.today', { time: hm });
  if (d.getTime() >= day - 86400000) return t('when.yesterday', { time: hm });
  return new Intl.DateTimeFormat(locale.value, { day: 'numeric', month: 'short', ...(d.getFullYear() !== now.getFullYear() ? { year: 'numeric' } : {}) }).format(d) + ' ' + hm;
};
const since = computed(() => (data.value?.since ? new Intl.DateTimeFormat(locale.value, { dateStyle: 'medium' }).format(new Date(data.value.since * 1000)) : ''));
const sum = (parts: any[]) => parts.reduce((a, p) => a + p.g, 0);
const weekMax = computed(() => Math.max(0, ...(data.value?.weeks ?? []).map((wk: any) => sum(wk.parts))));
const weekDay = (unix: number) => new Intl.DateTimeFormat(locale.value, { day: 'numeric', month: 'short' }).format(new Date(unix * 1000));
const weekTip = (wk: any) => wk.parts.map((p: any) => `${p.label}: ${Math.round(p.g)} g`).join(' · ');
// A material's hue: its place among the materials used, then among those only on the shelf.
const matTones = computed(() => {
  const names = [...new Set([...(data.value?.mats ?? []), ...(data.value?.shelf?.mats ?? [])].map((x: any) => x.name as string))];
  return new Map(names.map((n, i) => [n, i < SERIES.length ? SERIES[i] : 'neutral' as OuiTone]));
});
const matTone = (name: string) => matTones.value.get(name) ?? 'neutral';
const mats = computed(() => {
  const d = data.value;
  if (!d?.mats?.length) return [];
  const top = d.mats.slice(0, 6).map((x: any) => ({ ...x, tone: matTone(x.name) }));
  const rest = d.mats.slice(6).reduce((a: number, x: any) => a + x.g, 0);
  return rest ? [...top, { name: t('stats.other'), g: rest, tone: 'neutral' as OuiTone }] : top;
});
const wasted = computed(() => (data.value?.waste ? data.value.waste.support + data.value.waste.purge : null));
const wTotal = computed(() => { const x = data.value?.waste; return x ? x.model + x.support + x.purge + (x.calibration || 0) : 0; });
const wasteRows = (e: any) => { if (e.cal) return null; const rows = e.rows.filter((r: any) => typeof r.ws === 'number'); return rows.length ? rows.reduce((a: number, r: any) => a + r.grams * (r.ws + r.wp), 0) : null; };
const rowCost = (e: any) => { const c = e.rows.filter((r: any) => typeof r.cost === 'number'); return c.length ? c.reduce((a: number, r: any) => a + r.cost, 0) : null; };
const rowG = (e: any) => e.rows.reduce((a: number, r: any) => a + r.grams, 0);
const soonLabel = (s: any) => {
  if (s.low || s.weeks === null) return w(s.left);
  return s.weeks < 1 ? t('stats.lessWeek') : tn('stats.weeks', Math.round(s.weeks));
};
</script>

<template>
  <div class="oui-stack stv">
    <OuiPageHeader :title="t('nav.stats')" :meta="since ? t('stats.since', { date: since }) : t('stats.fillIn')">
      <template #actions>
        <label id="stv-p" class="oui-sr">{{ t('stats.periodLabel') }}</label>
        <Select :model-value="period" :options="periods" option-label="label" option-value="value" aria-labelledby="stv-p" data-test="period" @update:model-value="setPeriod" />
      </template>
    </OuiPageHeader>
    <OuiBanner :show="!!error" tone="error" :title="error" dismissible :dismiss-key="`stats-error:${period}:${error}`" :close-label="t('common.close')" data-test="stats-error">
      <template #actions><Button severity="secondary" size="small" :label="t('common.retry')" @click="ask"><template #icon><OuiIcon :icon="refresh" :size="14" /></template></Button></template></OuiBanner>
    <OuiPanel v-if="!data"><OuiEmpty compact state="loading" :title="t('stats.loading')" role="status" /></OuiPanel>
    <template v-else>
      <!-- The period in numbers: one block of readouts in the text colour; only a state (low stock, failed prints) has a colour. -->
      <OuiPanel><div class="stv-tiles">
        <OuiReadout :icon="scale" :label="t('stats.used')" v-bind="split(w(data.grams))" size="lg" />
        <OuiReadout :icon="printer" :label="t('stats.prints')" :value="data.prints" size="lg" />
        <OuiReadout :icon="coins" :label="t('stats.cost')" :value="typeof data.cost === 'number' ? money(data.cost) : null" size="lg" />
        <OuiReadout :icon="warning" :tone="data.low ? 'warn' : 'neutral'" :label="t('stats.low')" :value="data.low" size="lg" />
        <OuiReadout :icon="trash" :label="t('stats.wasted')" v-bind="wasted === null ? { value: null } : split(w(wasted))" size="lg"
          :sub="data.waste ? (data.waste.cost ? money(data.waste.cost) + ' · ' : '') + t('stats.pctAll', { pct: Math.round((wasted as number) / (wTotal || 1) * 100) }) : t('stats.fromJob')" />
        <OuiReadout :icon="warehouse" :label="t('stats.shelf')" v-bind="data.shelf ? split(w(data.shelf.g)) : { value: null }" size="lg"
          :sub="data.shelf ? money(data.shelf.value) + (data.shelf.unpriced ? ' · ' + tn('stats.unpriced', data.shelf.unpriced) : '') : t('stats.needsSpoolman')" />
        <OuiReadout :icon="errorIcon" :tone="data.failed.prints ? 'danger' : 'neutral'" :label="t('stats.failed')" v-bind="split(w(data.failed.g))" size="lg"
          :sub="tn('stats.printsN', data.failed.prints) + (data.failed.cost !== null ? ' · ' + money(data.failed.cost) : '')" />
      </div></OuiPanel>
      <div class="stv-grid">
        <OuiPanel :title="t('stats.perWeek')" :icon="chart" tone="magenta" :hint="weekMax ? t('stats.weekNote') : undefined">
          <p v-if="!weekMax" class="oui-muted">{{ t('stats.noWeeks') }}</p>
          <template v-else>
            <div class="stv-weeks" role="img" :aria-label="t('stats.perWeekAria') + ': ' + data.weeks.map((wk: any) => [w(sum(wk.parts)), weekTip(wk)].filter(Boolean).join(', ')).join('; ')">
              <div v-for="wk in data.weeks" :key="wk.start" class="stv-week" :title="weekTip(wk) || undefined">
                <span class="oui-meta oui-num stv-wv">{{ sum(wk.parts) ? w(sum(wk.parts)) : '' }}</span>
                <!-- One part per filament, in its own colour, inside a neutral frame (this week's frame in teal). -->
                <span class="stv-bar" :class="{ now: wk.now }" :style="{ height: (sum(wk.parts) ? Math.max(3, sum(wk.parts) / weekMax * 100) : 0) + '%' }">
                  <i v-for="(p, i) in wk.parts" :key="i" :style="{ flex: p.g, background: col(p.colour) ?? 'var(--oui-muted)' }" :title="`${p.label}: ${Math.round(p.g)} g`" /></span>
                <span class="oui-meta stv-wl">{{ wk.now ? t('stats.thisWeek') : weekDay(wk.start) }}</span>
              </div>
            </div>
          </template></OuiPanel>
        <OuiPanel :title="t('stats.materials')" :icon="layers" tone="magenta" :meta="mats.length ? t('stats.materialsAria', { w: w(data.grams), n: data.mats.length }) : undefined">
          <p v-if="!mats.length" class="oui-muted">{{ t('stats.nothing') }}</p>
          <template v-else>
            <div class="stv-seg" role="img" :aria-label="t('stats.materialsAria', { w: w(data.grams), n: data.mats.length })"><i v-for="s in mats" :key="s.name" :data-tone="s.tone" :style="{ flex: s.g }" :title="`${s.name}: ${w(s.g)}`" /></div>
            <ul class="stv-leg"><li v-for="s in mats" :key="s.name"><span class="stv-k" :data-tone="s.tone" /><span>{{ s.name }}</span>
              <span class="oui-num">{{ w(s.g) }} · {{ Math.round(s.g / data.grams * 100) }}%</span></li></ul>
          </template></OuiPanel>
        <OuiPanel :title="t('stats.top')" :icon="target" tone="magenta">
          <p v-if="!data.top.length" class="oui-muted">{{ t('stats.nothing') }}</p>
          <div v-for="(x, i) in data.top" :key="i" class="stv-row stv-sp"><OuiSpool :color="col(x.colour)" :fraction="topFill(x.spool)" :size="32" /><span class="stv-l">{{ x.label }}</span>
            <span class="stv-t"><i data-tone="primary" :style="{ width: (x.g / data.top[0].g * 100) + '%' }" /></span><span class="oui-num">{{ w(x.g) }}</span></div></OuiPanel>
        <OuiPanel :title="t('stats.soon')" :icon="hourglass" tone="magenta">
          <p v-if="!data.soon.length" class="oui-muted">{{ t('stats.noSoon') }}</p>
          <div v-for="(x, i) in data.soon" :key="i" class="stv-row stv-sp"><OuiSpool :color="col(x.colour)" :fraction="x.pct === null ? null : x.pct / 100" :size="32" /><span class="stv-l">{{ x.label }}</span>
            <OuiLevel :fraction="x.pct === null ? null : x.pct / 100" :tone="x.low ? 'critical' : 'low'" /><span class="oui-num">{{ soonLabel(x) }}</span></div></OuiPanel>
        <OuiPanel :title="t('stats.shelfBy')" :icon="boxes" tone="lime">
          <p v-if="!data.shelf || !data.shelf.mats.length" class="oui-muted">{{ t('stats.shelfNone') }}</p>
          <div v-for="x in data.shelf?.mats ?? []" :key="x.name" class="stv-row"><span class="stv-k" :data-tone="matTone(x.name)" /><span class="stv-l">{{ x.name }}</span>
            <span class="stv-t"><i :data-tone="matTone(x.name)" :style="{ width: (x.g / (data.shelf.mats[0].g || 1) * 100) + '%' }" /></span><span class="oui-num">{{ w(x.g) }}<template v-if="x.value"> · {{ money(x.value) }}</template></span></div></OuiPanel>
        <OuiPanel class="stv-wide" :title="t('stats.ratios')" :icon="percent" tone="magenta" data-test="waste"
                  :hint="data.waste ? `${t('stats.wasteNote')} ${data.waste.prints < data.prints ? t('stats.wasteSome', { n: data.waste.prints, total: data.prints }) : t('stats.wasteSince')}` : undefined">
          <p v-if="!data.waste" class="oui-muted">{{ t('stats.ratiosNone') }}</p>
          <div v-else class="stv-wi">
            <div class="oui-stack">
              <div class="stv-seg" role="img" :aria-label="t('stats.ratios')"><i v-for="[k] in W_KEYS" v-show="data.waste[k] > 0" :key="k" :data-tone="W_TONES[k]" :style="{ flex: data.waste[k] }" :title="`${t(`stats.waste.${k}` as any)}: ${w(data.waste[k])}`" /></div>
              <ul class="stv-leg"><li v-for="[k, cost] in W_KEYS" v-show="k !== 'calibration' || data.waste.calibration > 0" :key="k"><span class="stv-k" :data-tone="W_TONES[k]" />
                <span>{{ t(`stats.waste.${k}` as any) }}</span><span class="oui-num">{{ w(data.waste[k]) }} · {{ Math.round(data.waste[k] / (wTotal || 1) * 100) }}%<template
                  v-if="data.waste.cost || data.waste.mcost"> · {{ money(data.waste[cost]) }}</template></span></li></ul>
            </div>
            <div><h3 class="oui-label stv-h">{{ t('stats.worst') }}</h3>
              <p v-if="!data.worst.length" class="oui-muted">{{ t('stats.noWaste') }}</p>
              <div v-for="(x, i) in data.worst" :key="i" class="stv-row"><span class="stv-k" :data-tone="W_TONES[x.kind]" /><span class="stv-l">{{ x.name || t('stats.print') }}</span>
                <span class="stv-t"><i :data-tone="W_TONES[x.kind]" :style="{ width: (x.g / data.worst[0].g * 100) + '%' }" /></span>
                <span class="oui-num">{{ w(x.g) }}<template v-if="x.cost"> · {{ money(x.cost) }}</template></span></div>
            </div>
          </div></OuiPanel>
        <OuiPanel class="stv-wide" :icon="history" tone="neutral" flush data-test="history">
          <template #title><button type="button" class="stv-hh" :aria-expanded="histOpen" aria-controls="stv-hist" @click="toggleHist">{{ t('stats.history') }}<OuiIcon :icon="histOpen ? chevronDown : chevronRight" :size="14" /></button></template>
          <template #meta>{{ tn('stats.printsN', data.prints) }} · {{ w(data.grams) }}<template v-if="data.cost !== null"> · {{ money(data.cost) }}</template><template
            v-if="data.waste"> · {{ t('stats.wastedN', { w: w(data.waste.support + data.waste.purge) }) }}</template></template>
          <div v-show="histOpen" id="stv-hist">
            <p v-if="!data.history.length" class="oui-muted stv-pad">{{ t('stats.noHistory') }}</p>
            <div v-else class="oui-table-wrap"><DataTable :value="data.history.slice(0, shownN)" size="small" class="stv-table">
              <Column :header="t('stats.col.date')" class="oui-num stv-c-date"><template #body="{ data: e }">{{ date(e.time) }}</template></Column>
              <Column :header="t('stats.col.print')"><template #body="{ data: e }">
                <div class="stv-print"><strong>{{ e.name || t('stats.print') }}</strong><span v-if="e.cal" class="oui-chip" :title="t('stats.calHelp')">{{ t('stats.waste.calibration') }}</span>
                  <OuiStatus v-if="e.result === 'cancelled' || e.result === 'failed'" state="error">{{ t('stats.failedAt', { pct: e.pct || 0, g: fmt.number(rowG(e), 1) }) }}<template v-if="rowCost(e) !== null"> · {{ money(rowCost(e)) }}</template></OuiStatus></div>
                <div v-if="e.printer" class="oui-meta">{{ e.printer }}</div></template></Column>
              <Column :header="t('stats.col.material')"><template #body="{ data: e }"><span v-for="(r, k) in e.rows" :key="k" class="stv-m" :title="r.label"><OuiSwatch :color="col(r.colour)" :size="10" />{{ r.material || '' }} {{ fmt.number(r.grams, 1) }} g</span></template></Column>
              <Column :header="t('stats.col.weight')" class="oui-num stv-c-num"><template #body="{ data: e }">{{ fmt.number(rowG(e), 1) }} g</template></Column>
              <Column :header="t('stats.col.waste')" class="oui-num stv-c-num"><template #body="{ data: e }">{{ wasteRows(e) === null ? '—' : fmt.number(wasteRows(e) as number, 1) + ' g' }}</template></Column>
              <Column :header="t('stats.col.cost')" class="oui-num stv-c-num"><template #body="{ data: e }">{{ money(rowCost(e)) }}</template></Column>
            </DataTable></div>
            <div class="oui-row stv-pad">
              <Button v-if="data.history.length > shownN" severity="secondary" size="small" :label="t('stats.more')" @click="shownN += 20" />
              <Button v-if="data.history.length" severity="secondary" size="small" :label="t('stats.export')" :loading="exporting" data-test="export" @click="exportCsv"><template #icon><OuiIcon :icon="download" :size="14" /></template></Button>
            </div>
          </div></OuiPanel>
      </div>
    </template>
  </div>
</template>

<style>
.stv-tiles { display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: var(--oui-s4) var(--oui-s3); }
.stv-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 340px), 1fr)); gap: var(--oui-s3); align-items: start; }
.stv-wide { grid-column: 1 / -1; }
/* weekly use: one bar per week, split by filament; the grams are written over each bar */
.stv-weeks { display: grid; grid-template-columns: repeat(8, minmax(0, 1fr)); gap: var(--oui-s2); height: 168px; margin-bottom: var(--oui-s2); }
.stv-week { display: grid; grid-template-rows: auto minmax(0, 1fr) auto; justify-items: center; gap: 3px; min-width: 0; text-align: center; }
.stv-wv, .stv-wl { white-space: nowrap; font-size: var(--oui-text-xs); }
/* "Diese Woche" is wider than a week's column in a narrow dock: the label may take two lines. */
.stv-wl { white-space: normal; line-height: 1.15; }
.stv-bar { align-self: end; display: flex; flex-direction: column-reverse; gap: 1px; width: 72%; max-width: 44px; padding: 2px; border-radius: 4px 4px 0 0;
  background: var(--oui-raised); box-shadow: inset 0 0 0 1px var(--oui-border); overflow: hidden; }
/* A thin edge in the text colour keeps a near-black or near-white filament visible against the frame in either theme. */
.stv-bar > i { min-height: 2px; border-radius: 2px; box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-text) 22%, transparent); }
.stv-bar.now { box-shadow: inset 0 0 0 2px var(--oui-primary-mark); }
/* a composition: one segmented bar and a legend of squares */
.stv-seg { display: flex; gap: 2px; height: 10px; margin-bottom: var(--oui-s3); }
.stv-seg i { min-width: 3px; border-radius: 2px; background: var(--oui-tone); }
.stv-leg { list-style: none; padding: 0; display: grid; gap: 6px; }
.stv-leg li { display: flex; gap: var(--oui-s2); align-items: center; } .stv-leg li .oui-num { margin-inline-start: auto; white-space: nowrap; }
.stv-k { flex: none; width: 10px; height: 10px; border-radius: 2px; background: var(--oui-tone); }
.stv-row { display: grid; grid-template-columns: 12px minmax(0, 1.4fr) minmax(48px, 1fr) auto; gap: var(--oui-s2); align-items: center; padding: 4px 0; }
.stv-l { overflow-wrap: anywhere; }
.stv-row.stv-sp { grid-template-columns: 32px minmax(0, 1.4fr) minmax(48px, 1fr) auto; padding: 0; }
.stv-t { height: 6px; border-radius: 3px; background: var(--oui-border); overflow: hidden; }
.stv-t i { display: block; height: 100%; min-width: 3px; border-radius: 3px; background: var(--oui-tone); }
.stv-wi { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 280px), 1fr)); gap: var(--oui-s4) var(--oui-s6); }
.stv-h { margin-bottom: var(--oui-s2); }
.orca-ui .stv-hh { display: inline-flex; align-items: center; gap: var(--oui-s2); padding: 0; border: 0; background: none; color: inherit; font: inherit; cursor: pointer; }
.stv-pad { padding: var(--oui-s3); }
.stv-table table { min-width: 620px; }
.stv-c-date { width: 132px; } .stv-c-num { width: 84px; }
.stv-print { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); }
.stv-m { display: inline-flex; gap: 4px; align-items: center; margin-inline-end: var(--oui-s2); white-space: nowrap; font-size: var(--oui-text-sm); }
</style>
