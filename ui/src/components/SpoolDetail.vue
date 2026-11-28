<script setup lang="ts">
import { computed, nextTick, ref, watch } from 'vue';
import Button from 'primevue/button';
import Column from 'primevue/column';
import DataTable from 'primevue/datatable';
import InputText from 'primevue/inputtext';
import Select from 'primevue/select';
import SelectButton from 'primevue/selectbutton';
import { longList, OuiHint, OuiIcon, OuiKeyValue, OuiLevel, OuiMenu, OuiPanel, OuiSpark, OuiSpool, OuiSwatch, type OuiFact, type OuiMenuItem } from '@orca-plugins/ui-foundation/src/components';
import { archive as archiveIcon, chevronDown, download, edit, external, scale, spool as spoolIcon, store, upload, x } from '@orca-plugins/ui-foundation/src/icons';
import SpoolChips from './SpoolChips.vue';
import { boot } from '../core/boot';
import * as bridge from '../core/bridge';
import { m, dupes, sourceOff, pending, sendEdits, syncPresets } from '../state/main';
import { menu, closeDetail, pickStack, setMode, sendAction, openEditor, type MenuMode } from '../state/menu';
import { ask, prompt } from '../core/dialog';
import { note } from '../state/main';
import { t, tn, fmt, locale } from '../core/i18n';
import { presetLabel } from '../logic/presets';
import { driedDays, gramsValid, formatWeight, levelTone, lowLevel, noteText, originalWeight, percentLeft, shown, spoolDirection, spoolPaint, tagUids, type Spool } from '../logic/spools';

// The selected spool, beside the list: its picture, what it is and how much is left (the big figure with its level),
// what you can do to it (Spoolman only), its facts, its weekly use and the prints that used it. The plugin sends the print history
// (spool_detail) when the spool is picked.
interface Detail { prints: { time: number; name?: string; grams: number; cost?: number | null }[]; grams: number; cost: number | null; sign: string; rate: number | null; weeks: number | null;
  presets?: { name: string; label: string; linked: boolean; own?: boolean }[] }
const props = defineProps<{ spool: Spool; /** Opened from a stack of this many spools: a link back to its list. */ back?: number }>();
const s = computed(() => props.spool);
const f = computed(() => s.value.filament || {});
const detail = computed<Detail | null>(() => menu.detail);
const ex = computed(() => shown(m.disp, 'exact_weight'));
const w = (g: unknown) => formatWeight(g, ex.value, locale.value);
const name = computed(() => f.value.name || t('spool.numbered', { id: s.value.id }));
const pct = computed(() => percentLeft(s.value));
const original = computed(() => originalWeight(s.value));
const level = computed(() => lowLevel(s.value.remaining_weight, m.low));
const stale = computed(() => !!m.loadError);
const canAct = computed(() => m.source === 'spoolman');
const money = (v: unknown) => (typeof v === 'number' ? fmt.money(detail.value?.sign ?? '', v) : '—');

// The amount, big: grams (or the percentage, when Settings asks for it), with the rest as its sub line.
const amount = computed(() => {
  const known = typeof s.value.remaining_weight === 'number';
  if (!known) return { value: pct.value === null ? null : pct.value, unit: '%', sub: '' };
  const [value, unit] = w(s.value.remaining_weight).split(' ');
  const of = typeof original.value === 'number' ? t('weight.of', { total: w(original.value) }) : '';
  if (m.wMode === 'percent' && pct.value !== null) return { value: pct.value, unit: '%', sub: `· ${value} ${unit} ${of}`.trim() };
  return { value, unit, sub: [of, m.wMode === 'both' && pct.value !== null ? `${pct.value}%` : ''].filter(Boolean).join(' · ') };
});
// How long the spool lasts ("5 weeks"); the rate it is worked out from is under Used per week. Null while unknown.
const lasts = computed(() => {
  const d = detail.value;
  if (!d || d.rate === null || d.weeks === null) return null;
  if (d.weeks < 1) return `< 1 ${tn('detail.weeks', 1)}`;
  const digits = d.weeks < 10 && Math.round(d.weeks * 10) % 10 ? 1 : 0;
  // A number shown with a decimal takes the plural (pt-BR's rules would make 1,6 singular).
  return `${fmt.number(d.weeks, digits)} ${digits ? t('detail.weeks_other') : tn('detail.weeks', Math.round(d.weeks))}`;
});
// Grams booked to this spool in each of the last 8 weeks (oldest first), from the prints the plugin sent.
const weeks = computed(() => {
  const out = new Array<number>(8).fill(0), now = m.now / 1000;
  for (const p of detail.value?.prints ?? []) { const i = 7 - Math.floor((now - p.time) / 604800); if (i >= 0 && i < 8) out[i] += p.grams; }
  return out.map(v => Math.round(v));
});
const dried = computed(() => driedDays(s.value));
const price = computed(() => {
  const raw = (s.value as { price?: unknown }).price ?? (f.value as { price?: unknown }).price;
  return typeof raw === 'number' && typeof original.value === 'number' && original.value > 0 ? (raw / original.value) * 1000 : null;
});
const dupe = computed(() => { const d = dupes.value.get(f.value.id as number); return d && d.count > 1 ? d : null; });
// A fact with nothing to say is left out (a column of dashes says nothing); the location stays, as the place to see it is unset.
const facts = computed<OuiFact[]>(() => ([
  // Location, Dried and RFID follow their Display switches; price and use have none.
  ...(shown(m.disp, 'location') ? [{ label: t('menu.location'), value: s.value.location || '—' }] : []),
  ...(canAct.value ? [{ label: t('detail.lasts'), value: lasts.value }] : []),
  ...(shown(m.disp, 'dried') ? [{ label: t('detail.dried'), value: dried.value === null ? null : dried.value === 0 ? t('detail.today') : tn('detail.daysAgo', dried.value) }] : []),
  { label: t('detail.price'), value: price.value === null ? null : `${money(price.value)} / kg` },
  { label: t('detail.used'), value: typeof s.value.used_weight === 'number' ? [w(s.value.used_weight), detail.value && detail.value.cost !== null ? money(detail.value.cost) : ''].filter(Boolean).join(' · ') : null },
  ...(shown(m.disp, 'rfid') ? [{ label: t('detail.rfid'), value: tagUids(s.value).join(', '), mono: true }] : []),
  ...(dupe.value ? [{ label: t('detail.sameFilament'), value: t('spool.together', { n: dupe.value.count, w: w(dupe.value.total) }) }] : []),
] as OuiFact[]).filter(x => x.value != null && x.value !== ''));
// Low stock, with Settings > Reorder on: a web search for this filament.
const cartQuery = computed(() => [f.value.vendor?.name, s.value.lot_nr || f.value.name || t('spool.numbered', { id: s.value.id })].filter(Boolean).join(' '));
const cart = computed(() => m.cart && typeof s.value.remaining_weight === 'number' && s.value.remaining_weight < m.low);
const noteLine = computed(() => noteText(s.value, { ...m.disp, comment: true }, boot.own_fields, v => t('spool.lot', { lot: v })));
// Send to Spoolman acts on the preset picked here: your own linked one, else Spooler's preset of this spool for each printer.
// Spooler's presets are named by the printer they are for (the plugin's label); two of one printer add the preset's own name.
const presets = computed(() => { const list = detail.value?.presets ?? [];
  const twice = (label: string) => list.filter(p => !p.linked && p.label === label).length > 1;
  return list.map(p => ({ value: p.name, label: p.linked ? t('detail.presetLinked', { name: presetLabel(p.name) })
    : !p.label ? presetLabel(p.name) : twice(p.label) ? `${p.label} · ${presetLabel(p.name)}` : p.label })); });
const presetPick = ref('');
// A link of this spool alone: Spoolman keeps settings on the filament every spool of it shares, so the plugin won't send it.
const ownLink = computed(() => !!detail.value?.presets?.find(p => p.name === presetPick.value)?.own);
watch(presets, list => { if (!list.some(o => o.value === presetPick.value)) presetPick.value = list[0]?.value ?? ''; }, { immediate: true });
// Day and month; the year only when it isn't this one (the column is narrow).
const date = (unix: number) => { const d = new Date(unix * 1000);
  return new Intl.DateTimeFormat(locale.value, { day: 'numeric', month: 'short', ...(d.getFullYear() !== new Date(m.now).getFullYear() ? { year: '2-digit' } : {}) }).format(d); };

// ------------------------------------------------------------------ actions
// Three ways to say how much is left share one form (Update weight): the spool on the scale, the grams left, the grams used.
const KINDS = ['weigh', 'remain', 'use'] as const;
const kinds = computed(() => KINDS.map(v => ({ value: v, label: t(`menu.kind.${v}`) })));
const isWeight = computed(() => (KINDS as readonly string[]).includes(menu.mode));
const actKey = (mode: MenuMode) => (mode === 'move' || mode === 'note' ? mode : 'weight');
const HINTS = { move: 'menu.location', weigh: 'menu.scale', use: 'menu.used', remain: 'menu.remainLabel', note: 'menu.noteLabel' } as const;
const hint = computed(() => t(HINTS[menu.mode as keyof typeof HINTS] ?? 'menu.used'));
const isText = computed(() => menu.mode === 'move' || menu.mode === 'note');
const locations = computed(() => [...new Set([...m.locations, ...m.spools.map(x => x.location)])].filter(Boolean).sort() as string[]);
// The plugin takes 0 < grams <= 100,000 for a weight or a use (MAX_GRAMS): refuse the rest here, with the reason.
// Grams left may be 0 (an empty spool).
const gramsOk = computed(() => isText.value || gramsValid(menu.val, menu.mode === 'remain'));
const help = computed(() => (menu.mode === 'note' ? t('menu.noteHelp')
  : menu.mode === 'move' ? (s.value.u1_bound ? t('menu.u1Bound', { location: s.value.location }) : '')
  : menu.val !== '' && !gramsOk.value ? t(menu.mode === 'remain' ? 'menu.remainInvalid' : 'menu.gramsInvalid')
  : t(menu.mode === 'remain' ? 'menu.remainHelp' : 'menu.gramsHelp')));
const panel = ref<HTMLElement | null>(null);
let opener: MenuMode = '';
watch(() => menu.mode, async (mode, was) => {   // the keyboard goes to the form's field, and back to the action that opened it
  await nextTick();
  if (mode) { opener = mode; (panel.value?.querySelector('input') as HTMLElement | null)?.focus(); }
  else if (was && panel.value?.contains(document.activeElement) === false) (panel.value?.querySelector(`[data-focus-key="act:${actKey(opener)}"]`) as HTMLElement | null)?.focus();
});
function cancel() { const from = menu.mode; setMode(''); void nextTick(() => (panel.value?.querySelector(`[data-focus-key="act:${actKey(from)}"]`) as HTMLElement | null)?.focus()); }

async function archive() {
  if (!await ask({ title: t('menu.archive'), text: t('confirm.archive', { name: name.value, id: s.value.id }), yes: t('menu.archive'), no: t('common.goBack') })) return;
  sendAction('archive', { filament: f.value.id });
}
// One or several (a multi-pack): the count is asked in the same confirmation.
async function addSpool() {
  const answer = await prompt({ title: t('menu.add'), text: t('confirm.add', { name: name.value }), yes: t('menu.addYes'), no: t('common.goBack'),
    input: { label: t('menu.addCount'), value: '1' } });
  if (answer === null) return;
  const count = Number(answer.trim());
  if (!Number.isInteger(count) || count < 1 || count > 20) { note('error', t('menu.addCountInvalid')); return; }
  sendAction('add', { filament: f.value.id, ...(count > 1 ? { count } : {}) });
}
// The actions used now and then, behind More. An empty spool's Archive is the hint above the actions, so it isn't here too.
const more = ref<InstanceType<typeof OuiMenu>>();
const emptyHint = computed(() => canAct.value && level.value === 'empty' && !s.value.archived);
const moreItems = computed<OuiMenuItem[]>(() => [
  { id: 'dried', label: t('menu.dried'), run: () => sendAction('dried') },
  ...(dried.value !== null ? [{ id: 'clear-dried', label: t('menu.clearDried'), run: () => sendAction('clear_dried') }] : []),
  ...(f.value.id != null ? [{ id: 'add', label: t('menu.add'), run: () => void addSpool() }] : []),
  ...(s.value.archived ? [{ id: 'unarchive', label: t('menu.unarchive'), icon: archiveIcon, separator: true, run: () => sendAction('unarchive') }]
    : emptyHint.value ? [] : [{ id: 'archive', label: t('menu.archive'), icon: archiveIcon, danger: true, separator: true, run: () => void archive() }]),
]);
async function save() {
  if (!gramsOk.value || sourceOff.value) return;
  if (menu.mode === 'note') { sendAction('comment', { comment: menu.val }); return; }
  if (menu.mode === 'remain') { sendAction('remaining', { grams: menu.val.replace(',', '.') }); return; }
  if (menu.mode !== 'move') { sendAction(menu.mode, { grams: menu.val.replace(',', '.') }); return; }
  if (s.value.u1_bound && !await ask({ title: t('menu.move'), text: t('confirm.unlink', { location: s.value.location }), yes: t('confirm.unlinkYes'), no: t('common.goBack'), danger: true })) return;
  sendAction('move', { location: menu.val });
}
</script>

<template>
  <OuiPanel :title="t('spool.numbered', { id: s.id })" :icon="spoolIcon" tone="magenta" :data-detail="s.id">
    <template #actions>
      <Button v-if="canAct" severity="secondary" text size="small" :label="t('detail.edit')" :aria-label="t('editor.editTitle', { id: s.id })" data-test="detail-edit" data-focus-key="edit" @click="openEditor(s.id)">
        <template #icon><OuiIcon :icon="edit" :size="14" /></template></Button>
      <Button v-if="canAct" severity="secondary" text size="small" :aria-label="t('menu.open')" :title="t('menu.open')" @click="sendAction('open')"><template #icon><OuiIcon :icon="external" :size="14" /></template></Button>
      <Button severity="secondary" text size="small" :aria-label="t('detail.close')" :title="t('detail.close')" data-test="detail-close" @click="closeDetail"><template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
    </template>

    <Button v-if="back" text size="small" class="sd-back" :label="'← ' + t('detail.backStack', { n: back })" data-test="stack-back" @click="pickStack(menu.stack!)" />
    <div class="sd-top"><div class="sd-top-grid">
    <div class="sd-well oui-well"><OuiSpool v-bind="spoolPaint(f)" :direction="spoolDirection(f)" :fraction="pct === null ? null : pct / 100" :size="128" /></div>
    <div class="sd-what">
    <div class="sd-id">
      <SpoolChips :spool="s" band />
      <p class="sd-name">{{ name }}</p>
      <p class="oui-meta sd-sub"><OuiSwatch v-bind="spoolPaint(f)" />{{ [f.vendor?.name, f.material, typeof f.diameter === 'number' ? `${f.diameter} mm` : '', f.color_hex && shown(m.disp, 'colour_code') ? '#' + f.color_hex.replace(/^#/, '').toUpperCase() : ''].filter(Boolean).join(' · ') }}</p>
    </div>
    <!-- The amount: the one big figure of the panel, with its level. Kept from an earlier read (stale), it is grey. -->
    <div class="sd-amount" :data-stale="stale || undefined">
      <p class="oui-num" data-test="weight"><span class="oui-sr">{{ t('list.col.left') }}: </span><template v-if="amount.value === null"><strong class="sd-figure" aria-hidden="true">—</strong> <span class="oui-muted">{{ t('spool.unknownLeft') }}</span></template>
        <template v-else><strong class="sd-figure">{{ amount.value }}</strong>{{ amount.unit === '%' ? '%' : ' ' + amount.unit }}<span v-if="amount.sub" class="oui-muted">{{ ' ' + amount.sub }}</span></template></p>
      <OuiLevel :fraction="pct === null ? null : pct / 100" :tone="levelTone(level)" :label="pct === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct })" />
      <Button v-if="cart" severity="secondary" text size="small" class="sd-reorder" :label="t('detail.reorder')" :title="t('spool.reorder', { q: cartQuery })" data-test="cart"
              @click="bridge.postMain({ type: 'order', query: cartQuery })"><template #icon><OuiIcon :icon="store" :size="14" /></template></Button>
    </div>
    </div>
    </div></div>

    <p v-if="emptyHint" class="sd-empty oui-row" data-test="empty-hint">{{ t('detail.emptyHint') }}
      <Button severity="danger" outlined size="small" :label="t('menu.archive')" :disabled="!!sourceOff" data-test="archive-empty" @click="archive"><template #icon><OuiIcon :icon="archiveIcon" :size="14" /></template></Button></p>
    <div v-if="canAct" :id="`sc-panel-${s.id}`" ref="panel" class="sd-act" role="group" :aria-label="t('menu.label', { id: s.id })" @keydown.escape.prevent="menu.mode && cancel()">
      <form v-if="menu.mode" class="sd-form oui-well" @submit.prevent="save">
        <SelectButton v-if="isWeight" :model-value="menu.mode" :options="kinds" option-label="label" option-value="value" :allow-empty="false" size="small" class="sd-kind"
                      :aria-label="t('menu.kind')" data-test="weight-kind" @update:model-value="v => setMode(v)" />
        <div class="oui-field"><label :for="`sc-in-${s.id}`">{{ hint }}</label>
          <InputText v-if="menu.mode === 'move'" :id="`sc-in-${s.id}`" v-model="menu.val" maxlength="64" :list="`sc-locs-${s.id}`" aria-describedby="sc-help" />
          <InputText v-else-if="menu.mode === 'note'" :id="`sc-in-${s.id}`" v-model="menu.val" maxlength="1024" aria-describedby="sc-help" />
          <InputText v-else :id="`sc-in-${s.id}`" v-model="menu.val" inputmode="decimal" :invalid="menu.val !== '' && !gramsOk" aria-describedby="sc-help" /></div>
        <datalist v-if="menu.mode === 'move'" :id="`sc-locs-${s.id}`"><option v-for="l in locations" :key="l" :value="l" /></datalist>
        <Button type="submit" :label="t('common.save')" :disabled="!gramsOk || !!sourceOff" data-act="sp-go" />
        <Button severity="secondary" text :label="t('common.cancel')" @click="cancel" />
        <p id="sc-help" class="oui-meta sd-help" :class="{ 'sd-bad': menu.val !== '' && !gramsOk }">{{ help }}</p>
      </form>
      <fieldset v-else class="sd-actions" :disabled="!!sourceOff" :aria-describedby="sourceOff ? 'sd-off' : undefined" data-test="spool-actions">
        <Button severity="secondary" :label="t('menu.weight')" data-focus-key="act:weight" data-act="weight" @click="setMode('weigh')"><template #icon><OuiIcon :icon="scale" :size="14" /></template></Button>
        <Button severity="secondary" :label="t('menu.move')" data-focus-key="act:move" data-act="move" @click="setMode('move', s.location || '')" />
        <Button severity="secondary" :label="t('menu.noteLabel')" data-focus-key="act:note" data-act="note" @click="setMode('note', s.comment || '')" />
        <Button severity="secondary" :label="t('menu.more')" aria-haspopup="menu" data-act="more" @click="e => more?.open(e, moreItems)"><template #icon><OuiIcon :icon="chevronDown" :size="14" /></template></Button>
      </fieldset>
      <OuiMenu ref="more" />
      <p v-if="sourceOff && !menu.mode" id="sd-off" class="oui-sr" data-test="actions-off">{{ t('detail.actionsOff', { reason: sourceOff }) }}</p>
    </div>
    <div v-if="canAct && detail" class="sd-preset" data-test="detail-preset">
      <template v-if="presets.length">
        <div class="oui-field"><label :for="`sd-preset-${s.id}`">{{ t('detail.preset') }}</label>
          <Select v-model="presetPick" :input-id="`sd-preset-${s.id}`" :options="presets" option-label="label" option-value="value" :virtual-scroller-options="longList(presets.length, 32)" size="small" fluid aria-describedby="sd-send-h" data-test="preset-pick" /></div>
        <Button severity="secondary" size="small" :label="t('list.send')" :disabled="!!sourceOff || pending('send') || !presetPick || ownLink" aria-describedby="sd-send-h" data-test="send"
                @click="sendEdits(s.id, presetPick)"><template #icon><OuiIcon :icon="upload" :size="14" /></template></Button>
        <OuiHint :label="t('list.send')" :text="ownLink ? t('detail.ownLink') : t('list.sendHelp')" data-test="send-help" />
        <!-- What the picker and Send are described by: the (i)'s own bubble is hidden while closed, and so not read from here. -->
        <span id="sd-send-h" class="oui-sr">{{ ownLink ? t('detail.ownLink') : t('list.sendHelp') }}</span>
      </template>
      <p v-else class="oui-meta oui-row" data-test="no-presets">{{ t('detail.noPresets') }}
        <Button severity="secondary" text size="small" :label="t('list.sync')" :disabled="!!sourceOff || pending('send')" @click="syncPresets"><template #icon><OuiIcon :icon="download" :size="14" /></template></Button></p>
    </div>
    <hr class="oui-divider sd-rule">

    <OuiKeyValue :items="facts" />
    <p v-if="noteLine" class="sd-note"><span class="oui-label">{{ t('menu.noteLabel') }}</span>{{ noteLine }}</p>

    <template v-if="canAct">
      <div class="sd-usage">
        <div><h3 class="oui-label">{{ t('detail.usedPerWeek') }}</h3>
          <p v-if="!detail" class="oui-muted" role="status">{{ t('common.loading') }}</p>
          <p v-else-if="detail.rate === null" class="oui-muted">{{ t('detail.noRate') }}</p>
          <p v-else class="oui-num"><strong>{{ Math.round(detail.rate) }} g</strong> <span class="oui-muted">{{ t('detail.rateNote') }}</span></p></div>
        <OuiSpark v-if="detail" type="bars" :values="weeks" :width="176" :height="40" :label="t('detail.weeksAria', { values: weeks.join(', ') })" />
      </div>
      <h3 class="oui-label sd-h">{{ t('detail.lastPrints') }}</h3>
      <div class="sd" role="status" aria-live="polite">
        <p v-if="!detail" class="oui-meta">{{ t('common.loading') }}</p>
        <p v-else-if="!detail.prints.length" class="oui-meta">{{ t('detail.none') }}</p>
        <template v-else>
          <p class="oui-meta">{{ tn('detail.prints', detail.prints.length) }} · {{ fmt.number(detail.grams, 1) }} g · {{ money(detail.cost) }}</p>
          <DataTable :value="detail.prints.slice(0, 20)" size="small" class="sd-history">
            <Column :header="t('stats.col.date')" style="width: 68px"><template #body="{ data }">{{ date(data.time) }}</template></Column>
            <Column :header="t('stats.col.print')"><template #body="{ data }"><span class="oui-truncate sd-print" :title="data.name || undefined">{{ data.name || t('stats.print') }}</span></template></Column>
            <Column :header="t('stats.col.weight')" class="oui-num" style="width: 70px"><template #body="{ data }">{{ fmt.number(data.grams, 1) }} g</template></Column>
            <Column :header="t('stats.col.cost')" class="oui-num sd-c-cost" style="width: 68px"><template #body="{ data }">{{ money(data.cost) }}</template></Column>
          </DataTable>
          <p v-if="detail.prints.length > 20" class="oui-meta">{{ t('detail.latest', { n: detail.prints.length }) }}</p>
        </template>
      </div>
    </template>
  </OuiPanel>
</template>

<style>
.orca-ui .sd-back.p-button { margin: calc(-1 * var(--oui-s2)) 0 var(--oui-s2); padding-inline: 0; }
.sd-empty { justify-content: space-between; flex-wrap: wrap; margin-top: var(--oui-s3); padding: var(--oui-s2) var(--oui-s3); border-radius: var(--oui-radius); background: var(--oui-raised); }
/* The picture is the spool itself, on a neutral well; nothing in the panel is filled with a hue. */
.sd-well { display: grid; place-items: center; padding: var(--oui-s4); }
/* Under the list (a wide panel) the picture sits beside what it is and how much is left, instead of spanning the panel. */
.sd-top { container: sd-top / inline-size; }
.sd-top-grid { display: grid; gap: var(--oui-s3); }
.sd-what { display: grid; gap: var(--oui-s3); align-content: center; min-width: 0; }
@container sd-top (min-width: 560px) { .sd-top-grid { grid-template-columns: 176px minmax(0, 1fr); gap: var(--oui-s4); } }
.sd-id { display: grid; gap: var(--oui-s1); min-width: 0; }
.sd-name { font-size: var(--oui-text-lg); font-weight: 700; line-height: 1.3; overflow-wrap: anywhere; }
.sd-sub { display: flex; align-items: center; gap: 6px; }
.sd-amount { display: grid; gap: 6px; }
.orca-ui .sd-reorder.p-button { justify-self: start; padding-inline: 0; }
.sd-figure { font-size: var(--oui-text-2xl); font-weight: 700; letter-spacing: -.015em; line-height: 1.1; }
.sd-amount[data-stale] { color: var(--oui-muted); }
.sd-act { margin-top: var(--oui-s4); }
.sd-actions { display: flex; flex-wrap: wrap; gap: var(--oui-s2); margin: 0; padding: 0; border: 0; min-width: 0; }
.sd-form { display: flex; flex-wrap: wrap; align-items: flex-end; gap: var(--oui-s2); padding: var(--oui-s3); }
.sd-form > .oui-field { flex: 1 1 200px; }
.sd-kind { flex: 1 0 100%; }
.sd-help { flex: 1 0 100%; }
.sd-help:empty { display: none; }
.sd-bad { color: var(--oui-danger); }
.sd-rule { margin-block: var(--oui-s4); }
/* Send to Spoolman: the label, the preset across the panel, then the button with its (i). */
.sd-preset { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); margin-top: var(--oui-s4); }
.sd-preset > .oui-field { flex: 1 0 100%; min-width: 0; }
.sd-note { display: grid; gap: 2px; margin-top: var(--oui-s3); overflow-wrap: anywhere; }
.sd-usage { display: flex; flex-wrap: wrap; align-items: flex-end; justify-content: space-between; gap: var(--oui-s3); margin-top: var(--oui-s4); padding: var(--oui-s3);
  border-radius: var(--oui-radius); background: var(--oui-raised); }
.sd-usage strong { font-size: var(--oui-text-xl); font-weight: 700; }
.sd-h { margin-block: var(--oui-s4) var(--oui-s1); }
.sd { container: sd / inline-size; display: grid; gap: var(--oui-s2); }
/* The 320 px detail: the cost column goes; the total above the table still has it. */
@container sd (max-width: 340px) { .orca-ui .sd-c-cost { display: none; } }
.sd-history { margin-inline: calc(-1 * var(--oui-s3)); }
.sd-history table { table-layout: fixed; width: 100%; }
.sd-print { display: block; }
</style>
