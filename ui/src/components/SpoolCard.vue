<script setup lang="ts">
import { computed, nextTick, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import SpoolDetail from './SpoolDetail.vue';
import SpoolFigure from './SpoolFigure.vue';
import LevelBar from './LevelBar.vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { m, inUse, dupes, plateSlots, pending } from '../state/main';
import { menu, openMenu, closeMenu, setMode, sendAction } from '../state/menu';
import { ask } from '../core/dialog';
import { t, locale } from '../core/i18n';
import { barFill, driedDays, driedOld, formatWeight, lowLevel, noteText, originalWeight, percentLeft, shown, swatch, swatchCols, swatchMain,
  tagUids, type Spool } from '../logic/spools';

const props = defineProps<{ spool: Spool; inStack?: boolean }>();
const s = computed(() => props.spool);
const f = computed(() => s.value.filament || {});
const disp = computed(() => m.disp);
const ex = computed(() => shown(disp.value, 'exact_weight'));
const w = (g: unknown) => formatWeight(g, ex.value, locale.value);
const name = computed(() => f.value.name || t('spool.numbered', { id: s.value.id }));
const vendor = computed(() => f.value.vendor?.name || '');
const pct = computed(() => percentLeft(s.value));
const remaining = computed(() => w(s.value.remaining_weight));
const original = computed(() => originalWeight(s.value));
const level = computed(() => lowLevel(s.value.remaining_weight, m.low));
const subtitle = computed(() => [
  vendor.value && shown(disp.value, 'vendor') ? vendor.value : '',
  f.value.material && shown(disp.value, 'material') ? f.value.material : '',
  f.value.color_hex && shown(disp.value, 'colour_code') ? '#' + f.value.color_hex.replace(/^#/, '').toUpperCase() : '',
  typeof f.value.diameter === 'number' && shown(disp.value, 'diameter') ? `${f.value.diameter} mm` : '',
  s.value.location && shown(disp.value, 'location') ? s.value.location : '',
  shown(disp.value, 'spool_id') && s.value.id != null ? `#${s.value.id}` : '',
].filter(Boolean));
const noteLine = computed(() => noteText(s.value, disp.value, boot.own_fields, v => t('spool.lot', { lot: v })));
const tags = computed(() => tagUids(s.value));
const dupe = computed(() => { const d = dupes.value.get(f.value.id as number); return !props.inStack && d && d.count > 1 ? d : null; });
const where = computed(() => (shown(disp.value, 'in_use') ? inUse.value.get(String(s.value.id)) : ''));
const plateLabel = computed(() => plateSlots.value.slots.get(s.value.id));
const dried = computed(() => (shown(disp.value, 'dried') ? driedDays(s.value) : null));
const ring = computed(() => (swatchCols(f.value).length > 1 ? swatchMain(f.value) : undefined));
const lowPct = computed(() => (typeof original.value === 'number' && original.value > 0 && m.low > 0 ? (m.low / original.value) * 100 : null));
const big = computed(() => (pct.value !== null && m.wMode === 'percent' ? `${pct.value}%` : remaining.value));
const ofTotal = computed(() => (m.wMode !== 'percent' && typeof original.value === 'number' ? t('weight.of', { total: w(original.value) }) : ''));
const pctSide = computed(() => (pct.value !== null && m.wMode === 'both' ? `${pct.value}%` : ''));
const actions = computed(() => m.source === 'spoolman' && s.value.id != null);
const open = computed(() => actions.value && menu.id === s.value.id);
const cartQuery = computed(() => [vendor.value, s.value.lot_nr || name.value].filter(Boolean).join(' '));
const showCart = computed(() => m.cart && typeof s.value.remaining_weight === 'number' && s.value.remaining_weight < m.low);
const tip = computed(() => [name.value, vendor.value, t('weight.left', { w: remaining.value + (typeof original.value === 'number' ? ' ' + t('weight.of', { total: w(original.value) }) : '') })]
  .filter(Boolean).join(' · '));

const panel = ref<HTMLElement | null>(null);
const more = ref<{ $el: HTMLElement } | null>(null);
watch(() => [open.value, menu.mode], async ([o]) => {   // the keyboard goes to the panel's first control
  if (!o) return;
  await nextTick();
  (panel.value?.querySelector('input, button') as HTMLElement | null)?.focus();
});
function close() { closeMenu(); void nextTick(() => more.value?.$el.focus()); }
const hint = computed(() => (menu.mode === 'move' ? t('menu.location') : menu.mode === 'weigh' ? t('menu.scale') : t('menu.used')));
const locations = computed(() => [...new Set([...m.locations, ...m.spools.map(x => x.location)])].filter(Boolean).sort() as string[]);
const gramsOk = computed(() => menu.mode === 'move' || (menu.val.trim() !== '' && Number.isFinite(Number(menu.val.replace(',', '.'))) && Number(menu.val.replace(',', '.')) >= 0));

async function archive() {
  if (!await ask({ title: t('menu.archive'), text: t('confirm.archive', { name: name.value, id: s.value.id }), yes: t('menu.archive'), no: t('common.goBack') })) return;
  sendAction('archive', { filament: f.value.id });
}
async function addSpool() {
  if (!await ask({ title: t('menu.add'), text: t('confirm.add', { name: name.value }), yes: t('menu.add'), no: t('common.goBack') })) return;
  sendAction('add', { filament: f.value.id });
}
async function save() {
  if (!gramsOk.value) return;
  if (menu.mode !== 'move') { sendAction(menu.mode, { grams: menu.val.replace(',', '.') }); return; }
  if (s.value.u1_bound && !await ask({ title: t('menu.move'), text: t('confirm.unlink', { location: s.value.location }), yes: t('confirm.unlinkYes'), no: t('common.goBack'), danger: true })) return;
  sendAction('move', { location: menu.val });
}
function onKey(e: KeyboardEvent) {
  if (e.key === 'Escape') { e.preventDefault(); close(); }
}
</script>

<template>
  <article class="sc" :class="{ archived: s.archived }" :title="tip" :data-spool="s.id">
    <div class="sc-body">
      <div class="sc-swcol">
        <SpoolFigure :paint="swatch(f)" :fraction="pct === null ? null : pct / 100" :size="84" />
        <span v-if="tags.length && shown(disp, 'rfid')" class="sp-chip sc-rfid" :title="t('spool.rfid', { tags: tags.join(', ') })">RFID</span>
      </div>
      <div class="sc-main">
        <div class="sc-top">
          <h3 class="sc-title"><span class="sc-dot" :style="{ background: swatch(f), borderColor: ring }" aria-hidden="true" />{{ name }}<span v-if="dupe" class="oui-meta sc-dup">{{ t('spool.together', { n: dupe.count, w: w(dupe.total) }) }}</span></h3>
          <Button v-if="showCart" text size="small" class="sc-icon" :aria-label="t('spool.reorder', { q: cartQuery })" :title="t('spool.reorder', { q: cartQuery })"
                  data-test="cart" @click="bridge.postMain({ type: 'order', query: cartQuery })">
            <svg viewBox="0 0 24 24" width="18" height="18" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><circle cx="9" cy="20" r="1.4"/><circle cx="18" cy="20" r="1.4"/><path d="M2 3h3l2.4 12.2a1.5 1.5 0 0 0 1.5 1.2h8.6a1.5 1.5 0 0 0 1.5-1.1L21 8H6"/></svg></Button>
          <Button v-if="actions" ref="more" text size="small" class="sc-icon" :aria-expanded="open" :aria-controls="`sc-panel-${s.id}`"
                  :aria-label="t('spool.actionsFor', { name })" data-act="sp-menu" @click="openMenu(s.id)">⋯</Button>
        </div>
        <div class="sc-weight sp-num" :class="level" data-test="weight">
          <strong class="sc-big">{{ big }}</strong> <span v-if="ofTotal" class="sc-of">{{ ofTotal }}</span> <span v-if="pctSide" class="sc-pct">{{ pctSide }}</span>
          <span v-if="level" class="sc-flag">{{ t(level === 'out' ? 'spool.out' : 'spool.low') }}</span>
        </div>
        <LevelBar v-if="shown(disp, 'bar')" class="sc-track" :pct="pct" :paint="barFill(f)" :low-pct="lowPct" :level="level"
                  :title="pct === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct })" />
        <div class="sc-sub">
          <span class="sc-subtext">{{ subtitle.join(' · ') }}</span>
          <span v-if="plateLabel" class="sp-chip accent">{{ t('spool.onPlate', { slots: plateLabel }) }}</span>
          <span v-if="where" class="sp-chip" :title="t('spool.loadedIn', { where })">{{ t('spool.inUse', { where }) }}</span>
          <span v-if="s.use_first && shown(disp, 'use_first') && !s.archived" class="sp-chip accent" :title="t('spool.useFirstHelp')">{{ t('spool.useFirst') }}</span>
          <span v-if="dried !== null" class="sp-chip" :class="{ warn: driedOld(s, dried) }" data-test="dried"
                :title="driedOld(s, dried) ? t('spool.driedOld', { days: s.dry_days }) : t('spool.driedHelp')">
            {{ dried === 0 ? t('spool.driedToday') : t('spool.driedAgo', { n: dried }) }}</span>
          <span v-if="s.archived" class="sp-chip">{{ t('spool.archived') }}</span>
        </div>
        <p v-if="noteLine" class="sc-note" :title="noteLine">{{ noteLine }}</p>
      </div>
    </div>
    <div v-if="open" :id="`sc-panel-${s.id}`" ref="panel" class="sc-panel" role="group" :aria-label="t('menu.label', { id: s.id })" @keydown="onKey">
      <template v-if="menu.mode === 'detail'">
        <SpoolDetail :detail="menu.detail" />
        <Button severity="secondary" outlined :label="t('common.close')" @click="setMode('')" />
      </template>
      <form v-else-if="menu.mode" class="sp-row" @submit.prevent="save">
        <label :for="`sc-in-${s.id}`" class="sp-sr">{{ hint }}</label>
        <InputText v-if="menu.mode === 'move'" :id="`sc-in-${s.id}`" v-model="menu.val" maxlength="64" :list="`sc-locs-${s.id}`" :placeholder="hint" class="sc-in" />
        <InputText v-else :id="`sc-in-${s.id}`" v-model="menu.val" inputmode="decimal" :placeholder="hint" class="sc-in" :invalid="menu.val !== '' && !gramsOk" />
        <datalist v-if="menu.mode === 'move'" :id="`sc-locs-${s.id}`"><option v-for="l in locations" :key="l" :value="l" /></datalist>
        <Button type="submit" :label="t('common.save')" :disabled="!gramsOk" data-act="sp-go" />
        <Button severity="secondary" outlined :label="t('common.cancel')" @click="setMode('')" />
        <p v-if="menu.mode === 'move' && s.u1_bound" class="sp-why sc-full">{{ t('menu.u1Bound', { location: s.location }) }}</p>
        <p v-if="menu.mode !== 'move'" class="sp-why sc-full">{{ menu.val !== '' && !gramsOk ? t('menu.gramsInvalid') : t('menu.gramsHelp') }}</p>
      </form>
      <div v-else class="sc-actions">
        <Button severity="secondary" outlined :label="t('menu.weigh')" @click="setMode('weigh')" />
        <Button severity="secondary" outlined :label="t('menu.use')" @click="setMode('use')" />
        <Button severity="secondary" outlined :label="t('menu.move')" @click="setMode('move', s.location || '')" />
        <Button severity="secondary" outlined :label="t('menu.details')" @click="setMode('detail')" />
        <Button v-if="s.archived" severity="secondary" outlined :label="t('menu.unarchive')" @click="sendAction('unarchive')" />
        <Button v-else severity="secondary" outlined :label="t('menu.archive')" @click="archive" />
        <Button v-if="f.id != null" severity="secondary" outlined :label="t('menu.add')" @click="addSpool" />
        <Button severity="secondary" outlined :label="t('menu.dried')" @click="sendAction('dried')" />
        <Button v-if="driedDays(s) !== null" severity="secondary" outlined :label="t('menu.clearDried')" @click="sendAction('clear_dried')" />
        <Button severity="secondary" outlined :label="t('menu.open')" @click="sendAction('open')" />
        <Button severity="secondary" text :label="t('common.close')" @click="close" />
      </div>
      <p v-if="pending('spool-action')" class="sp-why" role="status">{{ t('action.sending') }}</p>
    </div>
  </article>
</template>

<style scoped>
.sc { container: sc / inline-size; border: 1px solid var(--oui-border); border-radius: 14px; background: var(--oui-surface); padding: 10px 14px 10px 8px; min-width: 0;
  transition: border-color 140ms ease, box-shadow 140ms ease; }
.sc:hover { border-color: color-mix(in srgb, var(--oui-text) 22%, var(--oui-border)); box-shadow: 0 2px 10px rgb(0 0 0 / 0.06); }
.sc.archived { opacity: 1; border-style: dashed; }
.sc-body { display: flex; gap: 10px; min-width: 0; align-items: center; }
.sc-swcol { display: grid; gap: 4px; justify-items: center; align-content: center; }
.sc-swcol :deep(.sf) { transition: transform 180ms ease; transform-origin: 50% 92%; }
.sc:hover .sc-swcol :deep(.sf) { transform: rotate(-4deg) scale(1.04); }
.sc-dot { display: inline-block; width: 10px; height: 10px; margin-right: 6px; border-radius: 50%; vertical-align: 0;
  border: 1px solid color-mix(in srgb, var(--oui-text) 25%, transparent); }
.sc-rfid { font-size: 12px; padding: 0 4px; line-height: 16px; }
.sc-main { flex: 1; min-width: 0; display: grid; gap: 5px; }
.sc-top { display: flex; align-items: center; gap: 8px; min-width: 0; }
.sc-title { flex: 1; margin: 0; font-size: 14px; font-weight: 600; min-width: 0; overflow-wrap: anywhere; }
.sc-dup { margin-left: 6px; font-weight: 400; }
.sc-weight { display: flex; flex-wrap: wrap; align-items: baseline; gap: 2px 6px; }
.sc-big { font-size: 20px; font-weight: 700; line-height: 1.1; letter-spacing: -0.01em; }
.sc-of, .sc-pct { color: var(--oui-muted); font-size: 12px; }
.sc-pct { margin-left: auto; font-weight: 600; }
.sc-flag { font-size: 11px; font-weight: 700; text-transform: uppercase; letter-spacing: 0.04em; padding: 1px 6px; border-radius: 999px;
  background: color-mix(in srgb, currentColor 14%, transparent); }
.sc-weight.low .sc-big, .sc-weight.low .sc-flag { color: var(--oui-warning); }
.sc-weight.out .sc-big, .sc-weight.out .sc-flag { color: var(--oui-danger); }
.sc-icon { width: 32px; height: 32px; padding: 0; justify-content: center; }
/* narrow places (a printer slot, two columns on a small window): smaller spool, number on its own line */
@container sc (max-width: 360px) {
  .sc-swcol { --sf-w: 52px; }
  .sc-big { font-size: 17px; }
  .sc-pct { margin-left: 0; }
}
@media (prefers-reduced-motion: reduce) { .sc, .sc-swcol :deep(.sf) { transition: none; } .sc:hover .sc-swcol :deep(.sf) { transform: none; } }
.sc-sub { display: flex; flex-wrap: wrap; gap: 6px; align-items: center; color: var(--oui-muted); font-size: 12px; min-width: 0; }
.sc-subtext { overflow-wrap: anywhere; }
.sc-note { margin: 0; color: var(--oui-muted); font-size: 12px; white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.sc-panel { margin-top: 10px; padding-top: 10px; border-top: 1px solid var(--oui-border); display: grid; gap: 8px; }
.sc-actions { display: flex; flex-wrap: wrap; gap: 6px; }
.sc-in { flex: 1 1 200px; min-width: 0; }
.sc-full { flex-basis: 100%; margin: 0; }
</style>
