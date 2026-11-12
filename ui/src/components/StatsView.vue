<script setup lang="ts">
import { computed, onBeforeUnmount, onMounted, ref } from 'vue';
import Button from 'primevue/button';
import Select from 'primevue/select';
import Message from 'primevue/message';
import * as bridge from '../core/bridge';
import { on } from '../state/main';
import { t, tn, fmt, locale } from '../core/i18n';

// Stats from the prints Spooler booked: tiles, weekly use, materials, most used, running low, shelf, waste and
// history (CSV export). Weights and money follow the page language; the currency sign comes from the plugin.
const period = ref(readPeriod());
function readPeriod() { try { return localStorage.getItem('spooler.period') || '30'; } catch { return '30'; } }
const data = ref<any>(null);
const error = ref('');
const exportNote = ref<{ ok: boolean; text: string } | null>(null);
const exporting = ref(false);
const histOpen = ref(readFlag());
function readFlag() { try { return localStorage.getItem('spooler.history') === '1'; } catch { return false; } }
const shownN = ref(7);
const COLS = ['var(--p-primary-color)', '#5b8def', '#c27c0e', '#9b6bd6', '#2f9a8f', '#c43d38', '#888'];
const W_COLS: Record<string, string> = { model: 'var(--p-primary-color)', support: '#c27c0e', purge: '#c43d38' };

function ask() { bridge.postMain({ type: 'stats', period: period.value }); }
let offs: (() => void)[] = [];
onMounted(() => {
  offs = [on('stats', (d: any) => { if (d && d.period === period.value) { data.value = d; error.value = d.error || ''; } }),
    on('statsExport', (d: any) => { exporting.value = false; exportNote.value = { ok: d.ok !== false, text: d.text || '' }; })];
  ask();
});
onBeforeUnmount(() => offs.forEach(f => f()));
function setPeriod(v: string) {
  period.value = v; shownN.value = 7; data.value = null;
  try { localStorage.setItem('spooler.period', v); } catch { /* per viewer */ }
  ask();
}
function toggleHist() { histOpen.value = !histOpen.value; try { localStorage.setItem('spooler.history', histOpen.value ? '1' : '0'); } catch { /* per viewer */ } }
function exportCsv() { exporting.value = true; exportNote.value = null; bridge.postMain({ type: 'stats_export', period: period.value }); }

const periods = computed(() => (['30', '90', 'year', 'all'] as const).map(v => ({ value: v, label: t(`stats.period.${v}`) })));
const w = (g: number) => (g >= 1000 ? `${fmt.number(g / 1000, 2)} kg` : `${fmt.number(Math.round(g))} g`);
const money = (v: unknown) => (typeof v === 'number' ? (data.value?.sign ?? '') + fmt.number(v, 2) : '–');
const col = (c?: string) => (c ? '#' + c : '#888');
const date = (unix: number) => {
  const d = new Date(unix * 1000), now = new Date(), day = new Date(now.getFullYear(), now.getMonth(), now.getDate()).getTime();
  const hm = fmt.time(unix);
  if (d.getTime() >= day) return t('when.today', { time: hm });
  if (d.getTime() >= day - 86400000) return t('when.yesterday', { time: hm });
  return new Intl.DateTimeFormat(locale.value, { day: 'numeric', month: 'short', ...(d.getFullYear() !== now.getFullYear() ? { year: 'numeric' } : {}) }).format(d) + ' ' + hm;
};
const since = computed(() => (data.value?.since ? new Intl.DateTimeFormat(locale.value, { dateStyle: 'medium' }).format(new Date(data.value.since * 1000)) : ''));
const weekMax = computed(() => Math.max(0, ...(data.value?.weeks ?? []).map((wk: any) => wk.parts.reduce((a: number, p: any) => a + p.g, 0))));
const sum = (parts: any[]) => parts.reduce((a, p) => a + p.g, 0);
const donut = computed(() => {
  const d = data.value;
  if (!d?.mats?.length) return [];
  const top = d.mats.slice(0, 6).map((x: any) => ({ ...x }));
  const rest = d.mats.slice(6).reduce((a: number, x: any) => a + x.g, 0);
  if (rest) top.push({ name: t('stats.other'), g: rest });
  let at = 0;
  return top.map((x: any, i: number) => { const len = (x.g / d.grams) * 100; const seg = { ...x, colour: COLS[i], len, at }; at += len; return seg; });
});
const wasted = computed(() => (data.value?.waste ? data.value.waste.support + data.value.waste.purge : null));
const wasteRows = (e: any) => { const rows = e.rows.filter((r: any) => typeof r.ws === 'number'); return rows.length ? rows.reduce((a: number, r: any) => a + r.grams * (r.ws + r.wp), 0) : null; };
const rowCost = (e: any) => { const c = e.rows.filter((r: any) => typeof r.cost === 'number'); return c.length ? c.reduce((a: number, r: any) => a + r.cost, 0) : null; };
const rowG = (e: any) => e.rows.reduce((a: number, r: any) => a + r.grams, 0);
const soonLabel = (s: any) => {
  if (s.low || s.weeks === null) return w(s.left);
  return s.weeks < 1 ? t('stats.lessWeek') : tn('stats.weeks', Math.round(s.weeks));
};
</script>

<template>
  <div class="stv">
    <div class="sp-row">
      <label id="stv-p" class="sp-sr">{{ t('stats.periodLabel') }}</label>
      <Select :model-value="period" :options="periods" option-label="label" option-value="value" aria-labelledby="stv-p" data-test="period" @update:model-value="setPeriod" />
      <span class="oui-meta">{{ since ? t('stats.since', { date: since }) : t('stats.fillIn') }}</span>
    </div>
    <Message v-if="error" severity="error" role="alert">{{ error }} <Button text size="small" :label="t('common.retry')" @click="ask" /></Message>
    <p v-if="!data" class="sp-card oui-muted" role="status">{{ t('stats.loading') }}</p>
    <template v-else>
      <div class="stv-tiles">
        <div class="stv-tile"><span>{{ t('stats.used') }}</span><b>{{ w(data.grams) }}</b></div>
        <div class="stv-tile"><span>{{ t('stats.prints') }}</span><b>{{ data.prints }}</b></div>
        <div class="stv-tile"><span>{{ t('stats.cost') }}</span><b>{{ money(data.cost) }}</b></div>
        <div class="stv-tile" :class="{ warn: data.low }"><span>{{ t('stats.low') }}</span><b>{{ data.low }}</b></div>
        <div class="stv-tile"><span>{{ t('stats.wasted') }}</span><b>{{ wasted === null ? '–' : w(wasted) }}</b>
          <small>{{ data.waste ? (data.waste.cost ? money(data.waste.cost) + ' · ' : '') + t('stats.pctAll', { pct: Math.round((wasted as number) / (data.waste.model + data.waste.support + data.waste.purge) * 100) }) : t('stats.fromJob') }}</small></div>
        <div class="stv-tile"><span>{{ t('stats.shelf') }}</span><b>{{ data.shelf ? w(data.shelf.g) : '–' }}</b>
          <small>{{ data.shelf ? money(data.shelf.value) + (data.shelf.unpriced ? ' · ' + tn('stats.unpriced', data.shelf.unpriced) : '') : t('stats.needsSpoolman') }}</small></div>
        <div class="stv-tile" :class="{ warn: data.failed.prints }"><span>{{ t('stats.failed') }}</span><b>{{ w(data.failed.g) }}</b>
          <small>{{ tn('stats.printsN', data.failed.prints) }}<template v-if="data.failed.cost !== null"> · {{ money(data.failed.cost) }}</template></small></div>
      </div>
      <div class="stv-grid">
        <section class="sp-card"><h2>{{ t('stats.perWeek') }}</h2>
          <p v-if="!weekMax" class="oui-muted">{{ t('stats.noWeeks') }}</p>
          <template v-else>
            <div class="stv-weeks" role="img" :aria-label="t('stats.perWeekAria')">
              <div v-for="wk in data.weeks" :key="wk.start" class="stv-week">
                <em>{{ sum(wk.parts) ? w(sum(wk.parts)) : '' }}</em>
                <span class="stv-stack" :class="{ now: wk.now }" :style="{ height: (sum(wk.parts) ? Math.max(3, sum(wk.parts) / weekMax * 80) : 0) + '%' }">
                  <i v-for="(p, i) in wk.parts" :key="i" :style="{ flex: p.g, background: col(p.colour) }" :title="`${p.label}: ${Math.round(p.g)} g`" /></span>
                <span class="oui-meta">{{ wk.now ? t('stats.thisWeek') : new Intl.DateTimeFormat(locale, { day: 'numeric', month: 'short' }).format(new Date(wk.start * 1000)) }}</span>
              </div>
            </div>
            <p class="oui-meta">{{ t('stats.weekNote') }}</p>
          </template></section>
        <section class="sp-card"><h2>{{ t('stats.materials') }}</h2>
          <p v-if="!donut.length" class="oui-muted">{{ t('stats.nothing') }}</p>
          <div v-else class="stv-donut">
            <svg viewBox="0 0 42 42" role="img" :aria-label="t('stats.materialsAria', { w: w(data.grams), n: data.mats.length })"><g transform="rotate(-90 21 21)" fill="none" stroke-width="6">
              <circle v-for="s in donut" :key="s.name" cx="21" cy="21" r="15.915" :stroke="s.colour"
                      :stroke-dasharray="`${Math.max(0, s.len - 0.5).toFixed(2)} ${(100 - Math.max(0, s.len - 0.5)).toFixed(2)}`" :stroke-dashoffset="(-s.at).toFixed(2)" /></g>
              <text x="21" y="21.6" text-anchor="middle" class="c1">{{ w(data.grams) }}</text>
              <text x="21" y="26.4" text-anchor="middle" class="c2">{{ tn('stats.materialsN', data.mats.length) }}</text></svg>
            <ul class="stv-leg"><li v-for="s in donut" :key="s.name"><span class="stv-k" :style="{ background: s.colour }" /><span>{{ s.name }}</span>
              <span class="sp-num">{{ w(s.g) }} · {{ Math.round(s.g / data.grams * 100) }}%</span></li></ul>
          </div></section>
        <section class="sp-card"><h2>{{ t('stats.top') }}</h2>
          <p v-if="!data.top.length" class="oui-muted">{{ t('stats.nothing') }}</p>
          <div v-for="(x, i) in data.top" :key="i" class="stv-row"><span class="stv-sw" :style="{ background: col(x.colour) }" /><span class="stv-l">{{ x.label }}</span>
            <span class="stv-t"><i :style="{ width: (x.g / data.top[0].g * 100) + '%' }" /></span><span class="sp-num">{{ w(x.g) }}</span></div></section>
        <section class="sp-card"><h2>{{ t('stats.soon') }}</h2>
          <p v-if="!data.soon.length" class="oui-muted">{{ t('stats.noSoon') }}</p>
          <div v-for="(x, i) in data.soon" :key="i" class="stv-row"><span class="stv-sw" :style="{ background: col(x.colour) }" /><span class="stv-l">{{ x.label }}</span>
            <span class="stv-t"><i :class="{ red: x.low }" :style="{ width: (x.pct === null ? 100 : x.pct) + '%' }" /></span><span class="sp-num">{{ soonLabel(x) }}</span></div></section>
        <section class="sp-card"><h2>{{ t('stats.shelfBy') }}</h2>
          <p v-if="!data.shelf || !data.shelf.mats.length" class="oui-muted">{{ t('stats.shelfNone') }}</p>
          <div v-for="(x, i) in data.shelf?.mats ?? []" :key="x.name" class="stv-row"><span class="stv-sw" :style="{ background: COLS[Number(i) % COLS.length] }" /><span class="stv-l">{{ x.name }}</span>
            <span class="stv-t"><i :style="{ width: (x.g / (data.shelf.mats[0].g || 1) * 100) + '%' }" /></span><span class="sp-num">{{ w(x.g) }}<template v-if="x.value"> · {{ money(x.value) }}</template></span></div></section>
        <section class="sp-card stv-wide" data-test="waste"><h2>{{ t('stats.ratios') }}</h2>
          <p v-if="!data.waste" class="oui-muted">{{ t('stats.ratiosNone') }}</p>
          <div v-else class="stv-wi">
            <div>
              <div class="stv-wbar"><i v-for="k in ['model', 'support', 'purge']" v-show="data.waste[k] > 0" :key="k" :style="{ flex: data.waste[k], background: W_COLS[k] }" :title="`${t(`stats.waste.${k}` as any)}: ${w(data.waste[k])}`" /></div>
              <ul class="stv-leg"><li v-for="[k, cost] in [['model', 'mcost'], ['support', 'scost'], ['purge', 'pcost']]" :key="k"><span class="stv-k" :style="{ background: W_COLS[k] }" />
                <span>{{ t(`stats.waste.${k}` as any) }}</span><span class="sp-num">{{ w(data.waste[k]) }} · {{ Math.round(data.waste[k] / (data.waste.model + data.waste.support + data.waste.purge) * 100) }}%<template
                  v-if="data.waste.cost || data.waste.mcost"> · {{ money(data.waste[cost]) }}</template></span></li></ul>
              <p class="oui-meta">{{ t('stats.wasteNote') }} {{ data.waste.prints < data.prints ? t('stats.wasteSome', { n: data.waste.prints, total: data.prints }) : t('stats.wasteSince') }}</p>
            </div>
            <div><h3>{{ t('stats.worst') }}</h3>
              <p v-if="!data.worst.length" class="oui-muted">{{ t('stats.noWaste') }}</p>
              <div v-for="(x, i) in data.worst" :key="i" class="stv-row"><span class="stv-sw" :style="{ background: W_COLS[x.kind] }" /><span class="stv-l">{{ x.name || t('stats.print') }}</span>
                <span class="stv-t"><i :style="{ width: (x.g / data.worst[0].g * 100) + '%', background: W_COLS[x.kind] }" /></span>
                <span class="sp-num">{{ w(x.g) }}<template v-if="x.cost"> · {{ money(x.cost) }}</template></span></div>
            </div>
          </div></section>
        <section class="sp-card stv-wide" data-test="history">
          <button type="button" class="stv-hh" :aria-expanded="histOpen" aria-controls="stv-hist" @click="toggleHist">
            <h2>{{ t('stats.history') }}</h2><span class="oui-meta">{{ tn('stats.printsN', data.prints) }} · {{ w(data.grams) }}<template v-if="data.cost !== null"> · {{ money(data.cost) }}</template><template
              v-if="data.waste"> · {{ t('stats.wastedN', { w: w(data.waste.support + data.waste.purge) }) }}</template></span><span aria-hidden="true">{{ histOpen ? '▴' : '▾' }}</span></button>
          <div v-show="histOpen" id="stv-hist">
            <p v-if="!data.history.length" class="oui-muted">{{ t('stats.noHistory') }}</p>
            <div v-else class="oui-table-wrap"><table class="sp-table">
              <thead><tr><th scope="col">{{ t('stats.col.date') }}</th><th scope="col">{{ t('stats.col.print') }}</th><th scope="col">{{ t('stats.col.material') }}</th>
                <th scope="col" class="r">{{ t('stats.col.weight') }}</th><th scope="col" class="r">{{ t('stats.col.waste') }}</th><th scope="col" class="r">{{ t('stats.col.cost') }}</th></tr></thead>
              <tbody><tr v-for="(e, i) in data.history.slice(0, shownN)" :key="i">
                <td class="sp-num">{{ date(e.time) }}</td>
                <td><strong>{{ e.name || t('stats.print') }}</strong><span v-if="e.result === 'cancelled' || e.result === 'failed'" class="sp-chip bad stv-fail">
                  {{ t('stats.failedAt', { pct: e.pct || 0, g: fmt.number(rowG(e), 1) }) }}<template v-if="rowCost(e) !== null"> · {{ money(rowCost(e)) }}</template></span>
                  <div v-if="e.printer" class="oui-meta">{{ e.printer }}</div></td>
                <td><span v-for="(r, k) in e.rows" :key="k" class="stv-m" :title="r.label"><i :style="{ background: col(r.colour) }" />{{ r.material || '' }} {{ fmt.number(r.grams, 1) }} g</span></td>
                <td class="r sp-num">{{ fmt.number(rowG(e), 1) }} g</td><td class="r sp-num">{{ wasteRows(e) === null ? '–' : fmt.number(wasteRows(e) as number, 1) + ' g' }}</td>
                <td class="r sp-num">{{ money(rowCost(e)) }}</td></tr></tbody></table></div>
            <div class="sp-row stv-hbar">
              <Button v-if="data.history.length > shownN" severity="secondary" outlined :label="t('stats.more')" @click="shownN += 20" />
              <Button v-if="data.history.length" severity="secondary" outlined :label="t('stats.export')" :loading="exporting" data-test="export" @click="exportCsv" />
              <span v-if="exportNote" :class="exportNote.ok ? 'oui-meta' : 'sp-err'" role="status">{{ exportNote.text }}</span>
            </div>
          </div></section>
      </div>
    </template>
  </div>
</template>

<style scoped>
.stv { display: grid; gap: 16px; }
.stv-tiles { display: grid; grid-template-columns: repeat(auto-fill, minmax(150px, 1fr)); gap: 12px; }
.stv-tile { display: grid; gap: 2px; padding: 12px; background: var(--oui-surface); border: 1px solid var(--oui-border); border-radius: 12px; }
.stv-tile span { color: var(--oui-muted); font-size: 12px; } .stv-tile b { font-size: 20px; font-variant-numeric: tabular-nums; } .stv-tile small { color: var(--oui-muted); font-size: 12px; }
.stv-tile.warn { border-color: var(--oui-warning); }
.stv-grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(320px, 1fr)); gap: 16px; }
.stv-grid h2 { margin: 0 0 8px; }
.stv-wide { grid-column: 1 / -1; }
.stv-weeks { display: grid; grid-template-columns: repeat(8, minmax(0, 1fr)); gap: 6px; height: 160px; align-items: end; }
.stv-week { display: grid; grid-template-rows: auto 1fr auto; height: 100%; align-items: end; justify-items: center; gap: 2px; text-align: center; font-size: 12px; }
.stv-week em { font-style: normal; font-size: 12px; color: var(--oui-muted); white-space: nowrap; }
.stv-stack { display: flex; flex-direction: column-reverse; width: 70%; border-radius: 4px 4px 0 0; overflow: hidden; align-self: end; }
.stv-stack.now { outline: 2px solid var(--p-primary-color); outline-offset: 1px; }
.stv-donut { display: flex; gap: 16px; align-items: center; flex-wrap: wrap; }
.stv-donut svg { width: 150px; height: 150px; }
.stv-donut .c1 { font-size: 5px; font-weight: 700; fill: var(--oui-text); } .stv-donut .c2 { font-size: 3px; fill: var(--oui-muted); }
.stv-leg { list-style: none; margin: 0; padding: 0; display: grid; gap: 4px; flex: 1; }
.stv-leg li { display: flex; gap: 8px; align-items: center; } .stv-leg li .sp-num { margin-left: auto; }
.stv-k, .stv-sw { width: 12px; height: 12px; border-radius: 3px; flex: none; }
.stv-row { display: grid; grid-template-columns: 12px minmax(0, 1.4fr) minmax(60px, 1fr) auto; gap: 8px; align-items: center; padding: 3px 0; }
.stv-l { overflow-wrap: anywhere; }
.stv-t { height: 8px; border-radius: 4px; background: var(--oui-border); overflow: hidden; }
.stv-t i { display: block; height: 100%; background: var(--p-primary-color); }
.stv-t i.red { background: var(--oui-danger); }
.stv-wi { display: grid; grid-template-columns: repeat(auto-fit, minmax(280px, 1fr)); gap: 16px; }
.stv-wi h3 { font-size: 12px; text-transform: uppercase; letter-spacing: .04em; color: var(--oui-muted); margin: 0 0 6px; }
.stv-wbar { display: flex; height: 14px; border-radius: 7px; overflow: hidden; margin-bottom: 8px; }
.stv-hh { display: flex; gap: 12px; align-items: center; width: 100%; border: 0; background: none; color: var(--oui-text); font: inherit; cursor: pointer; text-align: left; flex-wrap: wrap; padding: 0; }
.stv-hh h2 { margin: 0; }
.stv-fail { margin-left: 6px; }
.stv-m { display: inline-flex; gap: 4px; align-items: center; margin-right: 8px; white-space: nowrap; font-size: 12px; }
.stv-m i { width: 10px; height: 10px; border-radius: 50%; display: inline-block; }
.stv-hbar { margin-top: 8px; }
</style>
