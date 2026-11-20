<script setup lang="ts">
import { computed, nextTick, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import { OuiBanner, OuiEmpty, OuiHint, OuiIcon, OuiPageHeader, OuiPanel, OuiSwatch, OuiToolbar } from '@orca-plugins/ui-foundation/src/components';
import { download, filter, plus, refresh as refreshIcon, search, settings, type OuiIconData } from '@orca-plugins/ui-foundation/src/icons';
import shelf from '../assets/spooler-shelf.webp';
import SpoolTable, { type GroupInfo, type Row } from './SpoolTable.vue';
import SpoolDetail from './SpoolDetail.vue';
import StackDetail from './StackDetail.vue';
import SpoolEditor from './SpoolEditor.vue';
import PlatePanel from './PlatePanel.vue';
import PeerNote from './PeerNote.vue';
import * as bridge from '../core/bridge';
import { m, inUse, sourceOff, pending, refresh, syncPresets, openSettings, setListView } from '../state/main';
import { menu, shownSpool, openEditor } from '../state/menu';
import { t, tn, fmt, locale } from '../core/i18n';
import { COLOR_FAMILIES, colorFamily, closestSpools, compareSpools, formatWeight, groupSpools, lowLevel, spoolMatches, stackEntries, stackLead, shown, totals, type SortKey, type Spool } from '../logic/spools';

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
const openStacks = ref(new Set<string>());
function readFlag(k: string) { try { return localStorage.getItem(k) === '1'; } catch { return false; } }
watch(filtersOpen, v => { try { localStorage.setItem('spooler.filters', v ? '1' : '0'); } catch { /* per viewer */ } });
watch(() => m.plate, p => { if (!p && sortKey.value === 'plate') sortKey.value = lastSort.value; });
watch(sortKey, k => { if (k !== 'plate') lastSort.value = k; });

// Table or cards: this viewer's pick, else the Settings default. Both draw the same rows.
const view = computed(() => m.viewPick ?? m.listView ?? 'table');
const VIEWS: ['table' | 'cards', OuiIconData][] = [['table', [['path', { d: 'M3 5h18M3 12h18M3 19h18' }]]],
  ['cards', [['rect', { x: 3, y: 3, width: 7, height: 7, rx: 1 }], ['rect', { x: 14, y: 3, width: 7, height: 7, rx: 1 }], ['rect', { x: 3, y: 14, width: 7, height: 7, rx: 1 }], ['rect', { x: 14, y: 14, width: 7, height: 7, rx: 1 }]]]];

const uniq = (xs: (string | undefined)[]) => [...new Set(xs.filter(Boolean) as string[])].sort();
const materials = computed(() => uniq(m.spools.map(s => s.filament?.material)).map(v => ({ value: v, label: v })));
const vendors = computed(() => uniq(m.spools.map(s => s.filament?.vendor?.name)).map(v => ({ value: v, label: v })));
const ALL_COLOURS = COLOR_FAMILIES.find(([k]) => k === 'multi')![1];
const colours = computed(() => {
  const counts = new Map<string, number>();
  for (const s of m.spools) { const f = colorFamily(s.filament || {}); if (f) counts.set(f, (counts.get(f) || 0) + 1); }
  return [{ value: '', label: t('filters.allColours'), dot: ALL_COLOURS, n: m.spools.length },
    ...COLOR_FAMILIES.filter(([k]) => counts.has(k)).map(([k, dot]) => ({ value: k, label: t(`colour.${k}` as any), dot, n: counts.get(k) as number }))];
});
watch(colours, cs => { if (colour.value && !cs.some(c => c.value === colour.value)) colour.value = ''; });
const groups = computed(() => (['none', 'location', 'material', 'vendor'] as const).map(v => ({ value: v, label: t(`filters.group.${v}`) })));
const sorts = computed(() => (['name', 'material', 'vendor', 'remaining', 'used', 'first_used', 'last_used', 'plate'] as const)
  .map(v => ({ value: v, label: t(`filters.sort.${v}`), disabled: v === 'plate' && !m.plate })));
const activeFilters = computed(() => (vendor.value ? 1 : 0) + (group.value !== 'none' ? 1 : 0) + (matchHex.value ? 1 : 0));
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
const flip = (set: Set<string>, key: string) => { const next = new Set(set); next.has(key) ? next.delete(key) : next.add(key); return next; };

// Rows of the table: a stack is one row followed, when open, by its spools; a closed group keeps one hidden row
// so its header still shows.
function rowsOf(list: Spool[], groupKey?: string): Row[] {
  const out: Row[] = [];
  for (const e of stackEntries(list, shown(m.disp, 'group_same'), loaded)) {
    if (e.kind === 'spool') { out.push({ key: e.key, kind: 'spool', spool: e.spool, group: groupKey }); continue; }
    const key = (groupKey ?? '') + '|' + e.key, open = openStacks.value.has(key);
    out.push({ key, kind: 'stack', items: e.items, used: e.used, open, group: groupKey });
    if (open) for (const s of e.items) out.push({ key: 's:' + s.id, kind: 'spool', spool: s, child: true, group: groupKey });
  }
  return out;
}
const rows = computed<Row[]>(() => (grouped.value
  ? grouped.value.flatMap(g => { const rs = rowsOf(g.items, g.key); return collapsed.value.has(g.key) ? [{ ...rs[0], hidden: true }] : rs; })
  : rowsOf(filtered.value)));
const groupInfo = computed<Record<string, GroupInfo> | null>(() => (grouped.value
  ? Object.fromEntries(grouped.value.map(g => [g.key, { label: g.label, count: g.items.length, totals: totals(g.items), open: !collapsed.value.has(g.key) }])) : null));
// Settings > Spool list > Two columns: the list splits in two where it has the room, never inside a stack or a group.
const columns = computed<Row[][]>(() => {
  const all = rows.value;
  const heads = all.map((_, i) => i).filter(i => !(all[i].kind === 'spool' && all[i].child));
  if (m.columns !== 2 || view.value === 'cards' || heads.length < 2) return [all];
  let cut = -1;
  for (let j = 1; j < heads.length; j++) {
    if (grouped.value && all[heads[j]].group === all[heads[j] - 1].group) continue;
    if (cut < 0 || Math.abs(j - heads.length / 2) < Math.abs(cut - heads.length / 2)) cut = j;
  }
  return cut < 0 ? [all] : [all.slice(0, heads[cut]), all.slice(heads[cut])];
});

// The spool whose detail is open: the one picked, else the first of the list until the detail is closed.
const selected = computed<Spool | null>(() => {
  const picked = menu.id == null ? null : m.spools.find(s => s.id === menu.id) ?? null;
  if (picked || !menu.auto || !rows.value.length) return picked;
  const top = rows.value[0];
  return top.kind === 'stack' ? stackLead(top.items, loaded) : top.spool;
});
// A stack's list in the detail (its row or card was opened), until one of its spools is picked.
const stackSpools = computed<Spool[] | null>(() => {
  if (!menu.stack || menu.id != null) return null;
  const list = menu.stack.map(id => m.spools.find(s => s.id === id)).filter(Boolean) as Spool[];
  return list.length ? list : null;
});
const backN = computed(() => (menu.stack && selected.value && menu.stack.includes(selected.value.id) ? menu.stack.length : 0));
// Keyed on the source too: the same id from another source is another spool, shown afresh.
watch(() => [selected.value?.id ?? null, m.source] as const, ([id]) => shownSpool(id), { immediate: true });
// Where the detail sits under the list (narrow), an explicit pick takes the keyboard and the eye to its heading.
watch(() => menu.picks, async () => {
  await nextTick();
  const detail = document.getElementById('sp-detail'), list = detail?.previousElementSibling;
  if (!detail || !list || detail.getBoundingClientRect().top < list.getBoundingClientRect().bottom - 1) return;
  const head = detail.querySelector<HTMLElement>('.oui-panel-title');
  if (!head) return;
  head.tabIndex = -1;
  head.focus({ preventScroll: true });
  detail.scrollIntoView({ block: 'nearest' });
});

// The page header's line of facts: how many spools, what they hold together, how many are low, and the presets made from them.
const headMeta = computed(() => {
  const stock = m.spools.filter(s => !s.archived);
  if (!m.received || !stock.length) return '';
  const grams = stock.reduce((a, s) => a + (typeof s.remaining_weight === 'number' ? s.remaining_weight : 0), 0);
  const low = stock.filter(s => lowLevel(s.remaining_weight, m.low)).length;
  return [tn('group.count', stock.length), t('weight.left', { w: formatWeight(grams, shown(m.disp, 'exact_weight'), locale.value) }), low ? `${t('stats.low')}: ${low}` : '',
    m.profiles.count && !m.profiles.error ? tn('list.presets', m.profiles.count) : ''].filter(Boolean).join(' · ');
});
// Summary (count, presets) and the list state: first use, no address, read error, empty, filters (S01/S02).
const countLine = computed(() => {
  const base = tn('list.count', m.spools.length, { shown: filtered.value.length });
  return m.profiles.error ? `${base} · ${t('list.presetsFailed', { error: m.profiles.error })}` : base;
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
const setArchived = (on: boolean) => bridge.postMain({ type: 'spool_action', action: 'show_archived', on });
</script>

<template>
  <div class="oui-stack sv">
    <OuiPageHeader :title="t('nav.spools')" :meta="headMeta">
      <template #actions>
        <OuiHint v-if="m.peers.u1control" end :label="t('peer.whyTitle')"><PeerNote where="spools" /></OuiHint>
        <Button severity="secondary" :label="t('list.sync')" :disabled="!!sourceOff || pending('send')" :title="t('list.syncHelp')" aria-describedby="sv-why" data-test="sync" @click="syncPresets">
          <template #icon><OuiIcon :icon="download" :size="14" /></template></Button>
        <Button v-if="m.source === 'spoolman'" :label="t('editor.add')" :disabled="!!sourceOff" data-test="add-spool" @click="openEditor(null)"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
      </template>
    </OuiPageHeader>
    <OuiBanner :show="!!staleAt" tone="warn" :title="t('list.stale', { error: m.loadError, time: staleAt })" data-test="stale"
               dismissible :dismiss-key="`stale:${m.source}:${m.loadError}`" :close-label="t('common.close')">
      <template #actions><Button severity="secondary" size="small" :label="t('common.retry')" @click="refresh"><template #icon><OuiIcon :icon="refreshIcon" :size="14" /></template></Button></template>
    </OuiBanner>
    <PlatePanel v-if="!m.showPrinterTab" />

    <div class="oui-split sp-grid" :data-detail="!!selected || !!stackSpools || undefined">
      <OuiPanel flush class="sp-list">
        <OuiToolbar :label="t('filters.searchLabel')">
          <InputText v-model="query" type="search" size="small" :placeholder="t('filters.search')" :aria-label="t('filters.searchLabel')" data-test="search" />
          <Select v-model="material" size="small" :options="materials" option-label="label" option-value="value" show-clear :placeholder="t('filters.allMaterials')" :aria-label="t('filters.material')" data-test="material" />
          <Select v-model="colour" size="small" :options="colours" option-label="label" option-value="value" :aria-label="t('filters.colour')" data-test="colour">
            <template #value="{ value }"><span class="sv-copt"><OuiSwatch :color="colours.find(c => c.value === value)?.dot ?? ALL_COLOURS" />{{ colours.find(c => c.value === value)?.label ?? t('filters.allColours') }}</span></template>
            <template #option="{ option }"><span class="sv-copt"><OuiSwatch :color="option.dot" />{{ option.label }}<span class="oui-meta oui-num sv-n">{{ option.n }}</span></span></template>
          </Select>
          <Button severity="secondary" text size="small" :label="activeFilters ? t('filters.toggleN', { n: activeFilters }) : t('filters.toggle')" :aria-expanded="filtersOpen" aria-controls="sv-panel"
                  data-test="filters-toggle" @click="filtersOpen = !filtersOpen"><template #icon><OuiIcon :icon="filter" :size="14" /></template></Button>
          <span class="oui-toolbar-summary oui-meta oui-num" :class="{ 'sv-bad': !!m.profiles.error }" aria-live="polite" data-test="count">{{ listState === 'list' || listState === 'no_match' ? countLine : '' }}</span>
          <template #end>
            <span class="oui-row sv-views" role="group" :aria-label="t('list.view')">
              <Button v-for="[v, icon] in VIEWS" :key="v" severity="secondary" :text="view !== v" size="small" :aria-label="t(`list.${v}`)" :title="t(`list.${v}`)" :aria-pressed="view === v"
                      :data-test="`view-${v}`" @click="setListView(v)"><template #icon><OuiIcon :icon="icon" :size="14" /></template></Button>
            </span>
          </template>
        </OuiToolbar>
        <div v-show="filtersOpen" id="sv-panel" class="oui-toolbar sv-panel" role="group" :aria-label="t('filters.toggle')">
          <Select v-model="vendor" size="small" :options="vendors" option-label="label" option-value="value" show-clear :placeholder="t('filters.allVendors')" :aria-label="t('filters.vendor')" data-test="vendor" />
          <Select v-model="group" size="small" :options="groups" option-label="label" option-value="value" :aria-label="t('filters.groupLabel')" data-test="group" />
          <Select v-model="sortKey" size="small" :options="sorts" option-label="label" option-value="value" option-disabled="disabled" :aria-label="t('filters.sortLabel')" data-test="sort" />
          <Button severity="secondary" size="small" :aria-label="sortDir === 'asc' ? t('filters.asc') : t('filters.desc')" :title="t('filters.dirHelp')"
                  :label="sortDir === 'asc' ? '↑' : '↓'" data-test="sort-dir" @click="sortDir = sortDir === 'asc' ? 'desc' : 'asc'" />
          <span v-if="m.source === 'spoolman'" class="oui-row"><Checkbox input-id="sv-arch" binary :model-value="m.disp.archived === true" @update:model-value="setArchived" />
            <label for="sv-arch">{{ t('filters.archived') }}</label></span>
          <span class="oui-row"><label for="sv-match">{{ t('filters.closest') }}</label>
            <input id="sv-match" type="color" class="sv-match" :value="matchHex || '#888888'" :title="t('filters.closestHelp', { n: 12 })" aria-describedby="sv-match-h" @input="e => (matchHex = (e.target as HTMLInputElement).value)">
            <Button v-if="matchHex" severity="secondary" text size="small" :label="t('filters.clearColour')" @click="matchHex = ''" />
            <span id="sv-match-h" class="oui-sr">{{ t('filters.closestHelp', { n: 12 }) }}</span></span>
        </div>

        <section class="sp-scroll" :class="{ 'sp-two': columns.length > 1 }" :aria-label="t('list.label')" aria-live="polite" :aria-busy="listState === 'loading'">
          <OuiEmpty v-if="listState === 'loading'" state="loading" :title="t('list.loading')" role="status" />
          <OuiEmpty v-else-if="listState === 'no_url'" :image="shelf" :title="t('list.noUrl.title')" :text="t('list.noUrl.body')" data-test="empty-no-url">
            <template #actions><Button :label="t('nav.openSettings')" @click="openSettings('s-src')"><template #icon><OuiIcon :icon="settings" :size="14" /></template></Button></template></OuiEmpty>
          <OuiEmpty v-else-if="listState === 'error'" state="error" :title="t('list.readFailed.title')" data-test="empty-error">
            <span class="oui-error-detail">{{ m.loadError }}</span>
            <template #actions><Button severity="secondary" :label="t('common.retry')" @click="refresh"><template #icon><OuiIcon :icon="refreshIcon" :size="14" /></template></Button>
              <Button severity="secondary" :label="t('nav.openSettings')" @click="openSettings('s-src')" /></template></OuiEmpty>
          <OuiEmpty v-else-if="listState === 'empty'" :image="shelf" :title="t('list.empty.title')" :text="m.source === 'bambu' ? t('list.empty.bambu') : t('list.empty.body')" data-test="empty-none">
            <template #actions><Button v-if="m.source === 'spoolman'" severity="secondary" :label="t('editor.add')" @click="openEditor(null)"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button><Button severity="secondary" :label="t('list.refresh')" @click="refresh"><template #icon><OuiIcon :icon="refreshIcon" :size="14" /></template></Button></template></OuiEmpty>
          <OuiEmpty v-else-if="listState === 'no_match'" :icon="search" tone="neutral" :title="t('list.noMatch.title')" :text="t('list.noMatch.body')" data-test="empty-filter">
            <template #actions><Button severity="secondary" :label="t('filters.clear')" :disabled="!anyFilter" @click="clearFilters" /></template></OuiEmpty>
          <div v-else class="sp-cols" data-test="list">
            <div v-for="(part, i) in columns" :key="i" class="sp-col">
              <SpoolTable :cards="view === 'cards'" :rows="part" :groups="groupInfo" :selected="selected?.id ?? null" @stack="k => (openStacks = flip(openStacks, k))" @group="k => (collapsed = flip(collapsed, k))" />
            </div>
          </div>
        </section>
        <!-- Why Sync and Send are off: the list's own state above (loading, no address, read error) or the banner says it to the eye. -->
        <p v-if="sourceOff" id="sv-why" class="oui-sr">{{ t('list.actionsOff', { reason: sourceOff }) }}</p>
      </OuiPanel>
      <StackDetail v-if="stackSpools" id="sp-detail" :spools="stackSpools" class="sp-detail" />
      <SpoolDetail v-else-if="selected" id="sp-detail" :spool="selected" :back="backN" class="sp-detail" />
    </div>
    <SpoolEditor v-if="m.source === 'spoolman'" />
  </div>
</template>

<style>
/* .oui-split: list and detail side by side from 900 px (the detail is 320 px, 400 from 1160 px: it holds a table);
   the detail under the list below that. The list scrolls inside its panel, so the detail stays in view. */
.sp-scroll { container: sp-list / inline-size; max-height: calc(100vh - 180px); min-height: 200px; overflow: auto; border-top: 1px solid var(--oui-border); }
.sp-grid[data-detail] .sp-scroll { max-height: 380px; }
@container oui-page (min-width: 900px) {
  .sp-grid[data-detail] .sp-scroll { max-height: calc(100vh - 180px); }
  .sp-detail { position: sticky; top: 56px; }
}
@container oui-page (min-width: 1160px) { .sp-grid[data-detail] { grid-template-columns: minmax(0, 1fr) 400px; } }
.sp-col { container: sp-col / inline-size; min-width: 0; }
@container sp-list (min-width: 1040px) { .sp-two > .sp-cols { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); align-items: start; } .sp-col + .sp-col { border-inline-start: 1px solid var(--oui-border); } }
@container sp-list (max-width: 1039.9px) { .orca-ui .sp-col + .sp-col thead { display: none; } .sp-col + .sp-col { border-top: 1px solid var(--oui-border); } }
.sv-views { gap: 2px; }
.sv-panel { border-top: 1px solid var(--oui-border); }
.sv-copt { display: inline-flex; align-items: center; gap: var(--oui-s2); width: 100%; }
.sv-n { margin-inline-start: auto; padding-inline-start: var(--oui-s3); }
.sv-bad { color: var(--oui-danger); }
.sv-match { width: 36px; height: var(--oui-control-sm); padding: 0; border: 1px solid var(--oui-control-border); border-radius: var(--oui-radius); background: none; }
</style>
