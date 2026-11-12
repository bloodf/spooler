<script setup lang="ts">
import { computed, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import Message from 'primevue/message';
import SpoolCard from './SpoolCard.vue';
import StackCard from './StackCard.vue';
import PlatePanel from './PlatePanel.vue';
import PeerNote from './PeerNote.vue';
import * as bridge from '../core/bridge';
import { m, inUse, sourceOff, note, pending } from '../state/main';
import { t, tn, fmt, locale } from '../core/i18n';
import { COLOR_FAMILIES, colorFamily, closestSpools, compareSpools, groupSpools, spoolMatches, stackEntries, shown,
  totals, formatWeight, type SortKey, type Spool } from '../logic/spools';

const query = ref('');
const material = ref<string | null>(null);
const vendor = ref<string | null>(null);
const colour = ref('');
const group = ref<'none' | 'location' | 'material' | 'vendor'>('none');
const sortKey = ref<SortKey>('remaining');
const lastSort = ref<SortKey>('remaining');
const sortDir = ref<'asc' | 'desc'>('asc');
const matchHex = ref('');
const filtersOpen = ref(readFlag('spooler.filters'));
const collapsed = ref(new Set<string>());
function readFlag(k: string) { try { return localStorage.getItem(k) === '1'; } catch { return false; } }
watch(filtersOpen, v => { try { localStorage.setItem('spooler.filters', v ? '1' : '0'); } catch { /* per viewer */ } });
watch(() => m.plate, p => { if (!p && sortKey.value === 'plate') sortKey.value = lastSort.value; });
watch(sortKey, k => { if (k !== 'plate') lastSort.value = k; });

const uniq = (xs: (string | undefined)[]) => [...new Set(xs.filter(Boolean) as string[])].sort();
const materials = computed(() => uniq(m.spools.map(s => s.filament?.material)).map(v => ({ value: v, label: v })));
const vendors = computed(() => uniq(m.spools.map(s => s.filament?.vendor?.name)).map(v => ({ value: v, label: v })));
const colours = computed(() => {
  const counts = new Map<string, number>();
  for (const s of m.spools) { const f = colorFamily(s.filament || {}); if (f) counts.set(f, (counts.get(f) || 0) + 1); }
  return [{ value: '', label: t('filters.allColours'), dot: '', n: m.spools.length },
    ...COLOR_FAMILIES.filter(([k]) => counts.has(k)).map(([k, dot]) => ({ value: k, label: t(`colour.${k}` as any), dot, n: counts.get(k) as number }))];
});
watch(colours, cs => { if (colour.value && !cs.some(c => c.value === colour.value)) colour.value = ''; });
const groups = computed(() => (['none', 'location', 'material', 'vendor'] as const).map(v => ({ value: v, label: t(`filters.group.${v}`) })));
const sorts = computed(() => (['name', 'material', 'vendor', 'remaining', 'used', 'first_used', 'last_used', 'plate'] as const)
  .map(v => ({ value: v, label: t(`filters.sort.${v}`), disabled: v === 'plate' && !m.plate })));
const activeFilters = computed(() => (material.value ? 1 : 0) + (vendor.value ? 1 : 0) + (group.value !== 'none' ? 1 : 0) + (matchHex.value ? 1 : 0));
const anyFilter = computed(() => !!(query.value.trim() || material.value || vendor.value || colour.value || matchHex.value));
function clearFilters() { query.value = ''; material.value = null; vendor.value = null; colour.value = ''; matchHex.value = ''; }

const filtered = computed<Spool[]>(() => {
  const q = query.value.trim().toLowerCase();
  let list = m.spools.filter(s => {
    const f = s.filament || {};
    if (material.value && f.material !== material.value) return false;
    if (vendor.value && f.vendor?.name !== vendor.value) return false;
    if (colour.value && colorFamily(f) !== colour.value) return false;
    return !q || spoolMatches(s, q);
  });
  if (matchHex.value) return closestSpools(list, matchHex.value);
  const order = new Map<number, number>();
  for (const row of m.plate?.rows ?? []) for (const id of row.ids) if (!order.has(id) || row.first < (order.get(id) as number)) order.set(id, row.first);
  list = [...list].sort((a, b) => compareSpools(a, b, sortKey.value, sortDir.value, order)
    || (sortKey.value === 'plate' ? compareSpools(a, b, 'remaining', 'asc', order) : 0));
  return list;
});
const loaded = (s: Spool) => shown(m.disp, 'in_use') && inUse.value.has(String(s.id));
const unknownLabels = computed(() => ({ location: t('group.noLocation'), material: t('group.unknownMaterial'), vendor: t('group.unknownVendor') }));
const grouped = computed(() => (group.value === 'none' || matchHex.value ? null : groupSpools(filtered.value, group.value, unknownLabels.value)));
const entries = computed(() => stackEntries(filtered.value, shown(m.disp, 'group_same'), loaded));
function toggle(key: string) { const next = new Set(collapsed.value); next.has(key) ? next.delete(key) : next.add(key); collapsed.value = next; }
const groupWeight = (items: Spool[]) => {
  const tt = totals(items), ex = shown(m.disp, 'exact_weight');
  const w = tt.remaining === null ? '?' : formatWeight(tt.remaining, ex, locale.value) + (tt.original === null ? '' : ' ' + t('weight.of', { total: formatWeight(tt.original, ex, locale.value) }));
  return { ...tt, label: m.wMode === 'grams' ? w : m.wMode === 'percent' ? (tt.percent === null ? w : `${tt.percent}%`) : `${w} · ${tt.percent === null ? '?' : tt.percent + '%'}` };
};

// Status line (count, presets) and the list state: first use, no address, read error, empty, filters (S01/S02).
const countLine = computed(() => {
  const base = tn('list.count', m.spools.length, { shown: filtered.value.length });
  return m.profiles.error ? `${base} · ${t('list.presetsFailed', { error: m.profiles.error })}`
    : m.profiles.count ? `${base} · ${tn('list.presets', m.profiles.count)}` : base;
});
const listState = computed(() => {
  if (!m.received) return 'loading';
  if (m.errorCode === 'no_url') return 'no_url';
  if (m.loadError && !m.spools.length) return 'error';
  if (!m.spools.length) return 'empty';
  if (!filtered.value.length) return 'no_match';
  return 'list';
});
const staleAt = computed(() => (m.loadError && m.spools.length ? fmt.time(m.loadedAt / 1000) : ''));
const refresh = () => { bridge.postMain({ type: 'refresh' }); note('pending', t('list.refreshing'), 'refresh'); };
watch(() => m.loadedAt, () => { if (pending('refresh')) note('success', t('list.refreshed'), 'refresh'); });
watch(() => m.loadError, e => { if (e && pending('refresh')) note('error', t('list.readFailedAt', { error: e }), 'refresh'); });
const openSettings = () => bridge.postMain({ type: 'settings' });
function sync() { note('pending', t('list.syncing'), 'send'); bridge.postMain({ type: 'sync_presets' }); }
function send() { note('pending', t('list.sending'), 'send'); bridge.postMain({ type: 'send' }); }
const setArchived = (on: boolean) => bridge.postMain({ type: 'spool_action', action: 'show_archived', on });
</script>

<template>
  <div class="sv">
    <PeerNote where="spools" />
    <section class="sp-card" aria-labelledby="sv-h">
      <h2 id="sv-h" class="sp-sr">{{ t('nav.spools') }}</h2>
      <div class="sp-row sv-bar">
        <span class="sv-count" :class="{ 'sp-err': !!m.profiles.error }" data-test="count">{{ listState === 'list' || listState === 'no_match' ? countLine : '' }}</span>
        <span class="sp-grow" />
        <Button severity="secondary" outlined :label="t('list.refresh')" :loading="pending('refresh')" data-test="refresh" @click="refresh" />
        <Button severity="secondary" outlined :label="t('list.sync')" :disabled="!!sourceOff || pending('send')" :title="t('list.syncHelp')"
                aria-describedby="sv-why" data-test="sync" @click="sync" />
        <Button severity="secondary" outlined :label="t('list.send')" :disabled="!!sourceOff || pending('send')" :title="t('list.sendHelp')"
                aria-describedby="sv-why" data-test="send" @click="send" />
        <Button severity="secondary" text :aria-expanded="filtersOpen" aria-controls="sv-panel" data-test="filters-toggle" @click="filtersOpen = !filtersOpen">
          {{ activeFilters ? t('filters.toggleN', { n: activeFilters }) : t('filters.toggle') }} {{ filtersOpen ? '▴' : '▾' }}</Button>
      </div>
      <p id="sv-why" class="sp-why">{{ sourceOff ? t('list.actionsOff', { reason: sourceOff }) : t('list.sendHelp') }}</p>
      <div class="sp-row sv-filters">
        <InputText v-model="query" type="search" class="sv-q" :placeholder="t('filters.search')" :aria-label="t('filters.searchLabel')" data-test="search" />
        <Select v-model="colour" :options="colours" option-label="label" option-value="value" :aria-label="t('filters.colour')" class="sv-col" data-test="colour">
          <template #value="{ value }"><span class="sv-copt"><span class="sv-cdot" :class="{ all: !value }" :style="value ? { background: colours.find(c => c.value === value)?.dot } : undefined" />
            {{ colours.find(c => c.value === value)?.label ?? t('filters.allColours') }}</span></template>
          <template #option="{ option }"><span class="sv-copt"><span class="sv-cdot" :class="{ all: !option.value }" :style="option.value ? { background: option.dot } : undefined" />
            {{ option.label }}<span class="oui-meta sv-n">{{ option.n }}</span></span></template>
        </Select>
      </div>
      <div v-show="filtersOpen" id="sv-panel" class="sv-panel">
        <div class="sp-row">
          <Select v-model="material" :options="materials" option-label="label" option-value="value" show-clear :placeholder="t('filters.allMaterials')" :aria-label="t('filters.material')" data-test="material" />
          <Select v-model="vendor" :options="vendors" option-label="label" option-value="value" show-clear :placeholder="t('filters.allVendors')" :aria-label="t('filters.vendor')" data-test="vendor" />
        </div>
        <div class="sp-row">
          <Select v-model="group" :options="groups" option-label="label" option-value="value" :aria-label="t('filters.groupLabel')" data-test="group" />
          <Select v-model="sortKey" :options="sorts" option-label="label" option-value="value" option-disabled="disabled" :aria-label="t('filters.sortLabel')" data-test="sort" />
          <Button severity="secondary" outlined :aria-label="sortDir === 'asc' ? t('filters.asc') : t('filters.desc')" :title="t('filters.dirHelp')"
                  :label="sortDir === 'asc' ? '▲' : '▼'" data-test="sort-dir" @click="sortDir = sortDir === 'asc' ? 'desc' : 'asc'" />
          <span v-if="m.source === 'spoolman'" class="sp-row"><Checkbox input-id="sv-arch" binary :model-value="m.disp.archived === true" @update:model-value="setArchived" />
            <label for="sv-arch">{{ t('filters.archived') }}</label></span>
        </div>
        <div class="sp-row">
          <label for="sv-match">{{ t('filters.closest') }}</label>
          <input id="sv-match" type="color" class="sv-match" :value="matchHex || '#888888'" :aria-describedby="'sv-match-h'" @input="e => (matchHex = (e.target as HTMLInputElement).value)">
          <Button v-if="matchHex" severity="secondary" text :label="t('filters.clearColour')" @click="matchHex = ''" />
          <span id="sv-match-h" class="sp-why">{{ t('filters.closestHelp', { n: 12 }) }}</span>
        </div>
      </div>
    </section>

    <PlatePanel v-if="!m.showPrinterTab" />

    <section class="sv-list-wrap" :aria-label="t('list.label')" aria-live="polite" :aria-busy="listState === 'loading'">
      <Message v-if="staleAt" severity="warn" data-test="stale">{{ t('list.stale', { error: m.loadError, time: staleAt }) }}
        <Button size="small" text :label="t('common.retry')" @click="refresh" /></Message>
      <div v-if="listState === 'loading'" class="sp-card sv-empty" role="status">{{ t('list.loading') }}</div>
      <div v-else-if="listState === 'no_url'" class="sp-card sv-empty" data-test="empty-no-url">
        <h3>{{ t('list.noUrl.title') }}</h3><p>{{ t('list.noUrl.body') }}</p>
        <Button :label="t('nav.openSettings')" @click="openSettings" /></div>
      <div v-else-if="listState === 'error'" class="sp-card sv-empty" data-test="empty-error">
        <h3>{{ t('list.readFailed.title') }}</h3><p class="oui-error-detail">{{ m.loadError }}</p>
        <div class="sp-row"><Button :label="t('common.retry')" @click="refresh" /><Button severity="secondary" outlined :label="t('nav.openSettings')" @click="openSettings" /></div></div>
      <div v-else-if="listState === 'empty'" class="sp-card sv-empty" data-test="empty-none">
        <h3>{{ t('list.empty.title') }}</h3><p>{{ m.source === 'bambu' ? t('list.empty.bambu') : t('list.empty.body') }}</p>
        <Button :label="t('list.refresh')" @click="refresh" /></div>
      <div v-else-if="listState === 'no_match'" class="sp-card sv-empty" data-test="empty-filter">
        <h3>{{ t('list.noMatch.title') }}</h3><p>{{ t('list.noMatch.body') }}</p>
        <Button :label="t('filters.clear')" :disabled="!anyFilter" @click="clearFilters" /></div>
      <template v-else-if="grouped">
        <section v-for="g in grouped" :key="g.key" class="sv-group" :class="{ collapsed: collapsed.has(g.key) }">
          <button type="button" class="sv-ghead" :aria-expanded="!collapsed.has(g.key)" @click="toggle(g.key)">
            <span aria-hidden="true">{{ collapsed.has(g.key) ? '▸' : '▾' }}</span>
            <span class="sv-gname"><strong>{{ g.label }}</strong><span class="oui-meta">{{ tn('group.count', g.items.length) }}</span></span>
            <span class="sv-gbar"><span class="oui-meta">{{ groupWeight(g.items).label }}</span>
              <span class="sv-gtrack"><i :class="groupWeight(g.items).percent === null ? 'mid' : (groupWeight(g.items).percent as number) >= 50 ? 'high' : (groupWeight(g.items).percent as number) >= 20 ? 'mid' : 'low'"
                :style="{ width: (groupWeight(g.items).percent ?? 0) + '%' }" /></span></span>
          </button>
          <div v-show="!collapsed.has(g.key)" class="sv-list" :class="{ two: m.columns === 2 }">
            <template v-for="e in stackEntries(g.items, shown(m.disp, 'group_same'), loaded)" :key="e.key">
              <SpoolCard v-if="e.kind === 'spool'" :spool="e.spool" />
              <StackCard v-else :items="e.items" :used="e.used" :stack-key="e.key" />
            </template>
          </div>
        </section>
      </template>
      <div v-else class="sv-list" :class="{ two: m.columns === 2 }" data-test="list">
        <template v-for="e in entries" :key="e.key">
          <SpoolCard v-if="e.kind === 'spool'" :spool="e.spool" />
          <StackCard v-else :items="e.items" :used="e.used" :stack-key="e.key" />
        </template>
      </div>
    </section>
  </div>
</template>

<style scoped>
.sv { display: grid; gap: 16px; }
.sv-bar { margin-bottom: 4px; }
.sv-count { font-weight: 600; }
.sv-filters { margin-top: 8px; }
.sv-q { flex: 1 1 280px; min-width: 0; }
.sv-col { min-width: 180px; }
.sv-copt { display: inline-flex; align-items: center; gap: 8px; width: 100%; }
.sv-n { margin-left: auto; }
.sv-cdot { width: 14px; height: 14px; border-radius: 50%; border: 1px solid var(--oui-control-border, var(--oui-border)); flex: none; }
.sv-cdot.all { background: conic-gradient(#e5484d, #f5d90a, #46a758, #3e63dd, #e5484d); }
.sv-panel { display: grid; gap: 8px; margin-top: 8px; }
.sv-match { width: 44px; height: 32px; padding: 0; border: 1px solid var(--oui-control-border, var(--oui-border)); border-radius: 6px; background: none; }
.sv-list-wrap { display: grid; gap: 12px; }
.sv-list { display: grid; gap: 8px; }
.sv-list.two { grid-template-columns: repeat(2, minmax(0, 1fr)); align-items: start; }
@media (max-width: 760px) { .sv-list.two { grid-template-columns: minmax(0, 1fr); } }
.sv-empty { display: grid; gap: 8px; justify-items: start; }
.sv-empty h3, .sv-empty p { margin: 0; }
.sv-group { display: grid; gap: 8px; }
.sv-ghead { display: flex; align-items: center; gap: 12px; width: 100%; padding: 12px; border: 1px solid var(--oui-border); border-radius: 12px;
  background: var(--oui-surface); color: var(--oui-text); font: inherit; text-align: left; cursor: pointer; }
.sv-gname { display: grid; flex: 1; min-width: 0; overflow-wrap: anywhere; }
.sv-gbar { display: grid; gap: 4px; min-width: 90px; white-space: nowrap; text-align: right; }
.sv-gtrack { display: block; height: 6px; border-radius: 3px; background: var(--oui-border); overflow: hidden; }
.sv-gtrack i { display: block; height: 100%; }
.sv-gtrack i.high { background: var(--oui-success); } .sv-gtrack i.mid { background: var(--oui-warning); } .sv-gtrack i.low { background: var(--oui-danger); }
</style>
