<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, ref } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import RadioButton from 'primevue/radiobutton';
import Logo from '../components/Logo.vue';
import SourceBlock from './SourceBlock.vue';
import SetupWizard from './SetupWizard.vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { m } from '../state/main';
import { ask } from '../core/dialog';
import { t, tn, langPref, setLangPref, autoLocale, onLangPref } from '../core/i18n';
import type { LangPref } from '../core/i18n-core';
import { form, saving, dirty, ready, saveWhy, update, cancel, save, checkUpdate, startSettings, openWizard, wizard } from './state';

const stop = startSettings();
onBeforeUnmount(stop);
onLangPref(v => bridge.postSettings({ type: 'ui_language', value: v }));

const SPOOL_KEYS = ['group_same', 'in_use', 'vendor', 'material', 'colour_code', 'diameter', 'rfid', 'bar', 'location', 'spool_id', 'comment', 'lot_nr',
  'extra_fields', 'exact_weight', 'archived', 'use_first', 'dried', 'low_notice'];
const HEAD_KEYS = ['head_vendor', 'head_material', 'head_colour_code', 'head_weight', 'head_bar', 'head_spool', 'head_preset', 'head_rfid'];
const weights = computed(() => (['grams', 'percent', 'both'] as const).map(v => ({ v, label: t(`set.weight.${v}`) })));
const sample = computed(() => (form.weight_display === 'grams' ? '640 g' : form.weight_display === 'percent' ? '64%' : '64% · 640 g'));
const curSign = computed(() => { const code = form.stats.cur === 'spoolman' ? form.cur_code : form.stats.cur.toUpperCase();
  return ({ GBP: '£', EUR: '€', USD: '$' } as Record<string, string>)[code] ?? code + ' '; });

// Reorder preview: which spools would show the cart at this weight (from the list the tab already has).
const lowPreview = computed(() => {
  if (boot.mode === 'settings' || !m.received || m.loadError) return null;
  const g = form.low_stock;
  if (typeof g !== 'number' || !(g >= 0)) return { invalid: true, list: [] as { id: number; name: string; w: number }[], n: 0 };
  const list = m.spools.filter(s => typeof s.remaining_weight === 'number' && (s.remaining_weight as number) < g)
    .sort((a, b) => (a.remaining_weight as number) - (b.remaining_weight as number))
    .map(s => ({ id: s.id, name: s.filament?.name || t('spool.numbered', { id: s.id }), w: s.remaining_weight as number }));
  return { invalid: false, list, n: list.length };
});

// Drying reminders: days per material, 0 = no reminder; materials normalised to upper case.
const newMat = ref('');
const dryRows = computed(() => Object.entries(form.drying));
function addMat() {
  const name = newMat.value.trim().replace(/\s+/g, ' ').toUpperCase();
  if (!name) return;
  if (!(name in form.drying)) form.drying = { ...form.drying, [name]: 0 };
  newMat.value = '';
  void nextTick(() => (document.getElementById(`dry-${name}`) as HTMLInputElement | null)?.focus());
}
function removeMat(name: string) { const { [name]: _gone, ...rest } = form.drying; form.drying = rest; }
const setDays = (name: string, v: number | null) => { form.drying = { ...form.drying, [name]: v && v > 0 ? Math.min(3650, Math.round(v)) : 0 }; };

const currencies = computed(() => [{ v: 'spoolman', label: t('set.cur.spoolman', { code: form.cur_code }) }, { v: 'gbp', label: '£ GBP' }, { v: 'eur', label: '€ EUR' }, { v: 'usd', label: '$ USD' }]);
const langOptions = computed(() => [{ value: 'auto', label: t('lang.auto', { current: t(`lang.${autoLocale.value}` as any) }) },
  { value: 'en', label: t('lang.en') }, { value: 'pt-BR', label: t('lang.pt-BR') }]);

// Data loss: leaving with unsaved edits asks first.
async function leave() {
  if (dirty.value && !await ask({ title: t('set.discardTitle'), text: t('set.discardText'), yes: t('set.discard'), no: t('set.keepEditing'), danger: true })) return;
  cancel();
}
</script>

<template>
  <div class="set">
    <header class="oui-header set-head">
      <span class="sp-brand"><Logo /><h1>{{ t('set.title') }}</h1></span><span class="sp-grow" />
      <Button severity="secondary" text :aria-label="t('set.feedback')" :title="t('set.feedback')" @click="bridge.postSettings({ type: 'feedback' })">
        <svg width="20" height="20" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" aria-hidden="true"><path d="M21 11.5a8.4 8.4 0 0 1-9 8.5 8.4 8.4 0 0 1-3.8-.9L3 21l1.9-5.7a8.4 8.4 0 0 1-.9-3.8 8.5 8.5 0 0 1 8.5-8.5h.5a8.5 8.5 0 0 1 8 8z"/></svg></Button>
    </header>
    <div class="set-body">
      <section class="sp-card set-sec" aria-labelledby="s-src">
        <div><h2 id="s-src">{{ t('set.source') }}</h2><SourceBlock v-if="!wizard.open" /><p v-else class="oui-meta">{{ t('set.inGuide') }}</p></div>
        <aside class="set-aside"><h3>{{ t('set.guide') }}</h3><p class="oui-meta">{{ t('set.guideText') }}</p>
          <Button severity="secondary" outlined :label="t('set.openGuide')" data-test="open-guide" data-focus-key="open-guide" @click="openWizard" /></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-reorder">
        <div><h2 id="s-reorder">{{ t('set.reorder') }}</h2>
          <span class="sp-row"><Checkbox v-model="form.show_cart" input-id="show-cart" binary /><label for="show-cart">{{ t('set.cart') }}</label></span>
          <div class="oui-field"><label for="low-stock">{{ t('set.lowStock') }}</label>
            <InputNumber v-model="form.low_stock" input-id="low-stock" :min="0" :step="10" :use-grouping="false" suffix=" g" aria-describedby="low-help" /></div>
          <p id="low-help" class="oui-meta">{{ t('set.lowHelp') }}</p></div>
        <aside class="set-aside" aria-live="polite"><h3>{{ t('set.preview') }}</h3>
          <p v-if="!lowPreview" class="oui-meta">{{ t('set.previewNoSource') }}</p>
          <p v-else-if="lowPreview.invalid" class="oui-meta">{{ t('set.previewEnter') }}</p>
          <template v-else><p>{{ lowPreview.n ? tn('set.previewCount', lowPreview.n, { g: form.low_stock }) : t('set.previewNone', { g: form.low_stock }) }}</p>
            <ul class="set-list"><li v-for="s in lowPreview.list.slice(0, 5)" :key="s.id"><span>{{ s.name }}</span><span class="sp-num">{{ Math.round(s.w) }} g</span></li></ul>
            <p v-if="lowPreview.n > 5" class="oui-meta">{{ t('set.previewMore', { n: lowPreview.n - 5 }) }}</p></template></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-weights">
        <div><h2 id="s-weights">{{ t('set.weights') }}</h2><p class="oui-meta" id="w-l">{{ t('set.weightsLabel') }}</p>
          <div class="sp-row" role="radiogroup" aria-labelledby="w-l"><span v-for="o in weights" :key="o.v" class="sp-row">
            <RadioButton v-model="form.weight_display" :input-id="`w-${o.v}`" name="weight-display" :value="o.v" /><label :for="`w-${o.v}`">{{ o.label }}</label></span></div></div>
        <aside class="set-aside"><h3>{{ t('set.preview') }}</h3><div class="set-sample"><span class="set-sw" /><span>PLA Matte - Black</span><span class="sp-num">{{ sample }}</span></div></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-layout">
        <div><h2 id="s-layout">{{ t('set.layout') }}</h2><p class="oui-meta" id="c-l">{{ t('set.layoutLabel') }}</p>
          <div class="sp-row" role="radiogroup" aria-labelledby="c-l"><span v-for="c in [1, 2]" :key="c" class="sp-row">
            <RadioButton v-model="form.spool_columns" :input-id="`cols-${c}`" name="spool-cols" :value="c" /><label :for="`cols-${c}`">{{ c === 1 ? t('set.one') : t('set.two') }}</label></span></div>
          <p class="oui-meta">{{ t('set.layoutHelp') }}</p></div>
        <aside class="set-aside"><h3>{{ t('set.preview') }}</h3><div class="set-cols" :class="{ two: form.spool_columns === 2 }"><span v-for="c in ['#1a1a1a', '#C12E1F', '#2850A8', '#3F8E43']" :key="c" :style="{ borderColor: c }" /></div></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-display">
        <div><h2 id="s-display">{{ t('set.display') }}</h2><p class="oui-meta">{{ t('set.displayHelp') }}</p>
          <h3>{{ t('set.displaySpools') }}</h3><div class="set-checks">
            <span v-for="k in SPOOL_KEYS" :key="k" class="sp-row"><Checkbox :input-id="`d-${k}`" binary :model-value="form.display[k] !== false" :data-disp="k"
              @update:model-value="v => (form.display = { ...form.display, [k]: !!v })" /><label :for="`d-${k}`">{{ t(`disp.${k}` as any) }}</label></span></div>
          <h3>{{ t('set.displayHeads') }}</h3><div class="set-checks">
            <span v-for="k in HEAD_KEYS" :key="k" class="sp-row"><Checkbox :input-id="`d-${k}`" binary :model-value="form.display[k] !== false" :data-disp="k"
              @update:model-value="v => (form.display = { ...form.display, [k]: !!v })" /><label :for="`d-${k}`">{{ t(`disp.${k}` as any) }}</label></span></div></div>
        <aside class="set-aside"><p class="oui-meta">{{ t('set.displayNote') }}</p></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-dry">
        <div><h2 id="s-dry">{{ t('set.drying') }}</h2><p class="oui-meta">{{ t('set.dryingHelp') }}</p>
          <table v-if="dryRows.length" class="sp-table set-dry"><tbody><tr v-for="[name, days] in dryRows" :key="name">
            <th scope="row">{{ name }}</th>
            <td><InputNumber :model-value="days > 0 ? days : null" :input-id="`dry-${name}`" :min="0" :max="3650" :use-grouping="false" :suffix="' ' + t('set.days')"
              :aria-label="t('set.daysFor', { m: name })" :placeholder="t('set.noReminder')" @update:model-value="v => setDays(name, v)" @input="e => setDays(name, typeof e.value === 'number' ? e.value : null)" /></td>
            <td><Button text severity="secondary" :aria-label="t('set.removeMat', { m: name })" :title="t('set.removeMat', { m: name })" @click="removeMat(name)">✕</Button></td></tr></tbody></table>
          <p v-else class="oui-meta">{{ t('set.dryNone') }}</p>
          <form class="sp-row" @submit.prevent="addMat"><InputText v-model="newMat" maxlength="24" :placeholder="t('set.matPh')" :aria-label="t('set.matLabel')" />
            <Button type="submit" severity="secondary" outlined :label="t('set.addMat')" :disabled="!newMat.trim()" /></form></div>
        <aside class="set-aside"><p class="oui-meta">{{ t('set.dryNote') }}</p></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-check">
        <div><h2 id="s-check">{{ t('set.check') }}</h2>
          <span class="sp-row"><Checkbox v-model="form.plate_check" input-id="plate-check" binary /><label for="plate-check">{{ t('set.checkOn') }}</label></span>
          <div class="oui-field"><label for="plate-margin">{{ t('set.margin') }}</label>
            <InputNumber v-model="form.plate_margin" input-id="plate-margin" :min="0" :max="50" :step="5" suffix=" %" :use-grouping="false" aria-describedby="m-help" /></div>
          <p id="m-help" class="oui-meta">{{ t('set.marginHelp') }}</p></div>
        <aside class="set-aside"><h3>{{ t('set.beforeStart') }}</h3><p class="oui-meta">{{ t('set.checkHint') }}</p></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-printer">
        <div><h2 id="s-printer">{{ t('set.printer') }}</h2>
          <span class="sp-row"><Checkbox v-model="form.progress.on" input-id="show-progress" binary /><label for="show-progress">{{ t('set.progressOn') }}</label></span>
          <fieldset :disabled="!form.progress.on" class="set-fs">
            <span class="sp-row"><Checkbox v-model="form.progress.finish" input-id="prog-finish" binary :disabled="!form.progress.on" /><label for="prog-finish">{{ t('set.finish') }}</label></span>
            <span class="sp-row"><Checkbox v-model="form.progress.slot" input-id="prog-slot" binary :disabled="!form.progress.on" /><label for="prog-slot">{{ t('set.slot') }}</label></span>
            <p class="oui-meta" id="idle-l">{{ t('set.idle') }}</p>
            <div class="sp-row" role="radiogroup" aria-labelledby="idle-l"><span v-for="v in ['line', 'hide'] as const" :key="v" class="sp-row">
              <RadioButton v-model="form.progress.idle" :input-id="`idle-${v}`" name="progress-idle" :value="v" :disabled="!form.progress.on" /><label :for="`idle-${v}`">{{ t(`set.idle.${v}`) }}</label></span></div>
          </fieldset>
          <p class="oui-meta">{{ t('set.liveNeeded') }}</p></div>
        <aside class="set-aside"><h3>{{ t('set.preview') }}</h3>
          <p v-if="!form.progress.on" class="oui-meta">{{ t('set.progressHidden') }}</p>
          <div v-else class="set-pp"><strong>Desk_Organiser_Plate_1</strong> <span class="sp-chip">{{ t('progress.state.RUNNING') }}</span> <span class="sp-num">37%</span>
            <p class="oui-meta">{{ t('progress.layer', { n: 142, total: 380 }) }} · {{ t('progress.left', { d: t('progress.hm', { h: 2, m: '04' }) }) }}<template
              v-if="form.progress.finish"> · {{ t('progress.done', { time: '11:24' }) }}</template><template v-if="form.progress.slot"> · {{ t('printer.slotOf', { unit: 'AMS 1', n: 2 }) }}</template></p></div></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-stats">
        <div><h2 id="s-stats">{{ t('set.stats') }}</h2>
          <span class="sp-row"><Checkbox v-model="form.stats.on" input-id="show-stats" binary /><label for="show-stats">{{ t('set.statsOn') }}</label></span>
          <p class="oui-meta" id="cur-l">{{ t('set.currency') }}</p>
          <div class="sp-row" role="radiogroup" aria-labelledby="cur-l"><span v-for="c in currencies" :key="c.v" class="sp-row">
            <RadioButton v-model="form.stats.cur" :input-id="`cur-${c.v}`" name="stats-cur" :value="c.v" :disabled="!form.stats.on" /><label :for="`cur-${c.v}`">{{ c.label }}</label></span></div>
          <p class="oui-meta">{{ t('set.currencyHelp') }}</p><p class="oui-meta">{{ t('set.statsKeep') }}</p></div>
        <aside class="set-aside"><h3>{{ t('set.preview') }}</h3>
          <p v-if="!form.stats.on" class="oui-meta">{{ t('set.statsHidden') }}</p>
          <p v-else>{{ t('stats.cost') }}: <strong class="sp-num">{{ curSign }}24.10</strong><br><span class="oui-meta">Headphone_Stand.3mf · 94.3 g · {{ curSign }}2.08</span></p></aside>
      </section>

      <section class="sp-card set-sec" aria-labelledby="s-lang">
        <div><h2 id="s-lang">{{ t('lang.title') }}</h2>
          <div class="sp-row"><label id="lang-l">{{ t('lang.label') }}</label>
            <Select :model-value="langPref" :options="langOptions" option-label="label" option-value="value" aria-labelledby="lang-l" data-test="lang"
                    @update:model-value="setLangPref($event as LangPref)" /></div>
          <p class="oui-meta">{{ t('lang.help') }}</p></div>
        <aside class="set-aside"><p class="oui-meta">{{ t('set.version', { v: boot.version }) }}</p>
          <div class="sp-row"><Button severity="secondary" text :label="t('set.checkUpdate')" :loading="update.busy" @click="checkUpdate" />
            <Button v-if="update.newer" text :label="t('set.newer', { v: update.newer })" @click="bridge.postSettings({ type: 'release' })" />
            <span v-else class="oui-meta" role="status">{{ update.text }}</span></div>
          <p class="oui-meta set-log">{{ t('set.log', { path: boot.settings.log_path }) }}</p></aside>
      </section>
    </div>
    <footer class="set-foot">
      <span v-if="dirty" class="sp-warn" role="status">{{ t('set.unsaved') }}</span>
      <span v-if="saveWhy" class="sp-why" id="save-why">{{ saveWhy }}</span>
      <span class="sp-grow" />
      <Button severity="secondary" outlined :label="t('common.cancel')" data-test="cancel" @click="leave" />
      <Button :label="t('set.save')" :disabled="!ready" :loading="saving" aria-describedby="save-why" data-test="save" @click="save" />
    </footer>
    <SetupWizard />
  </div>
</template>

<style scoped>
.set { min-height: 100vh; background: var(--oui-background); display: flex; flex-direction: column; }
.set-head { position: sticky; top: 0; z-index: 5; }
.set-body { padding: 16px; display: grid; gap: 16px; max-width: 1100px; width: 100%; }
.set-sec { display: grid; grid-template-columns: minmax(0, 1.5fr) minmax(220px, 1fr); gap: 16px; }
.set-sec h2 { margin: 0 0 8px; } .set-sec h3 { font-size: 14px; margin: 12px 0 6px; }
.set-sec > div { display: grid; gap: 8px; align-content: start; min-width: 0; }
.set-aside { border-left: 1px solid var(--oui-border); padding-left: 16px; display: grid; gap: 6px; align-content: start; min-width: 0; }
.set-aside h3 { margin: 0; font-size: 12px; text-transform: uppercase; letter-spacing: .04em; color: var(--oui-muted); }
.set-aside p { margin: 0; }
.set-list { list-style: none; padding: 0; margin: 0; display: grid; gap: 2px; } .set-list li { display: flex; justify-content: space-between; gap: 8px; }
.set-sample { display: flex; gap: 8px; align-items: center; } .set-sample > span:nth-child(2) { flex: 1; }
.set-sw { width: 20px; height: 20px; border-radius: 50%; background: #1a1a1a; }
.set-cols { display: grid; gap: 6px; } .set-cols.two { grid-template-columns: 1fr 1fr; }
.set-cols span { height: 18px; border: 1px solid var(--oui-border); border-left-width: 6px; border-radius: 6px; }
.set-checks { display: grid; grid-template-columns: repeat(auto-fill, minmax(240px, 1fr)); gap: 6px 16px; }
.set-dry th { font-weight: 600; } .set-dry :deep(input) { width: 140px; }
.set-fs { border: 0; padding: 0; margin: 0; display: grid; gap: 8px; min-width: 0; }
.set-pp p { margin: 4px 0 0; }
.set-log { overflow-wrap: anywhere; }
.set-foot { position: sticky; bottom: 0; display: flex; flex-wrap: wrap; gap: 8px; align-items: center; padding: 12px 16px; background: var(--oui-surface); border-top: 1px solid var(--oui-border); }
@media (max-width: 760px) { .set-sec { grid-template-columns: minmax(0, 1fr); } .set-aside { border-left: 0; padding-left: 0; border-top: 1px solid var(--oui-border); padding-top: 12px; } }
</style>
