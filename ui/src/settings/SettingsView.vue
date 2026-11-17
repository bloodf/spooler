<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, ref } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import RadioButton from 'primevue/radiobutton';
import { OuiFormRow, OuiFormSection, OuiIcon, OuiSettings, OuiStatus, OuiSwatch, type OuiSettingsSection } from '../../shared/src/components';
import { chart, check, drop, eye, info, languages, layers, plus, printer, save as saveIcon, scale, spoolman, store, x } from '../../shared/src/icons';
import SourceBlock from './SourceBlock.vue';
import SetupWizard from './SetupWizard.vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { m } from '../state/main';
import { t, tn, langPref, setLangPref, autoLocale, onLangPref } from '../core/i18n';
import { LOCALES } from '../core/i18n-core';
import type { LangPref } from '../core/i18n-core';
import { form, saving, dirty, ready, saveWhy, update, save, checkUpdate, startSettings, openWizard, wizard, leave, rfidSkipped, unskipRfid } from './state';

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
const langOptions = computed(() => [{ value: 'auto', label: t('lang.auto', { current: t(`lang.${autoLocale.value}`) }) },
  ...LOCALES.map(value => ({ value, label: t(`lang.${value}`) }))]);
const setDisp = (k: string, v: unknown) => { form.display = { ...form.display, [k]: !!v }; };

// The index beside the sections; the source flags itself until it passed a test (Save waits for it).
const sections = computed<OuiSettingsSection[]>(() => [
  { id: 's-src', label: t('set.source'), icon: spoolman, ...(ready.value ? {} : { state: 'warn' as const }) },
  { id: 's-reorder', label: t('set.reorder'), icon: store },
  { id: 's-weights', label: t('set.weights'), icon: scale },
  { id: 's-layout', label: t('set.layout'), icon: layers },
  { id: 's-check', label: t('set.check'), icon: check },
  { id: 's-display', label: t('set.display'), icon: eye },
  { id: 's-dry', label: t('set.drying'), icon: drop },
  { id: 's-printer', label: t('set.printer'), icon: printer },
  { id: 's-stats', label: t('set.stats'), icon: chart },
  { id: 's-lang', label: t('lang.title'), icon: languages },
]);
</script>

<template>
  <!-- One root: the tab hides this view with v-show and names it as a tab panel. -->
  <div class="set">
  <OuiSettings :sections="sections" :nav-label="t('set.title')">
    <div class="oui-stack">
      <OuiFormSection id="s-src" :icon="spoolman" tone="magenta" :title="t('set.source')" :description="t('set.guideText')">
        <template #actions><Button severity="secondary" size="small" :label="t('set.openGuide')" data-test="open-guide" data-focus-key="open-guide" @click="openWizard" /></template>
        <div class="set-pad"><SourceBlock v-if="!wizard.open" /><p v-else class="oui-meta">{{ t('set.inGuide') }}</p></div>
      </OuiFormSection>

      <OuiFormSection id="s-reorder" :icon="store" tone="lime" :title="t('set.reorder')">
        <OuiFormRow :label="t('set.cart')" for="show-cart"><Checkbox v-model="form.show_cart" input-id="show-cart" binary /></OuiFormRow>
        <OuiFormRow :label="t('set.lowStock')" for="low-stock" :hint="t('set.lowHelp')">
          <InputNumber v-model="form.low_stock" input-id="low-stock" :min="0" :step="10" :use-grouping="false" suffix=" g" aria-describedby="low-help" /><span id="low-help" class="oui-sr">{{ t('set.lowHelp') }}</span></OuiFormRow>
        <div class="set-pad" aria-live="polite"><div class="set-pv oui-well">
          <p class="oui-label">{{ t('set.preview') }}</p>
          <p v-if="!lowPreview" class="oui-meta">{{ t('set.previewNoSource') }}</p>
          <p v-else-if="lowPreview.invalid" class="oui-meta">{{ t('set.previewEnter') }}</p>
          <template v-else><p>{{ lowPreview.n ? tn('set.previewCount', lowPreview.n, { g: form.low_stock }) : t('set.previewNone', { g: form.low_stock }) }}</p>
            <ul class="set-list"><li v-for="s in lowPreview.list.slice(0, 5)" :key="s.id"><span class="oui-truncate">{{ s.name }}</span><span class="oui-num">{{ Math.round(s.w) }} g</span></li></ul>
            <p v-if="lowPreview.n > 5" class="oui-meta">{{ t('set.previewMore', { n: lowPreview.n - 5 }) }}</p></template>
        </div></div>
      </OuiFormSection>

      <OuiFormSection id="s-weights" :icon="scale" :title="t('set.weights')">
        <OuiFormRow :label="t('set.weightsLabel')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.weightsLabel')"><span v-for="o in weights" :key="o.v" class="oui-row set-opt">
            <RadioButton v-model="form.weight_display" :input-id="`w-${o.v}`" name="weight-display" :value="o.v" /><label :for="`w-${o.v}`">{{ o.label }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.preview')"><span class="set-sample"><OuiSwatch color="#1a1a1a" /><span>PLA Matte - Black</span><strong class="oui-num">{{ sample }}</strong></span></OuiFormRow>
      </OuiFormSection>

      <OuiFormSection id="s-layout" :icon="layers" tone="sky" :title="t('set.layout')" :description="t('set.layoutHelp')">
        <OuiFormRow :label="t('set.layoutLabel')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.layoutLabel')"><span v-for="c in [1, 2]" :key="c" class="oui-row set-opt">
            <RadioButton v-model="form.spool_columns" :input-id="`cols-${c}`" name="spool-cols" :value="c" /><label :for="`cols-${c}`">{{ c === 1 ? t('set.one') : t('set.two') }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.preview')"><div class="set-cols" :class="{ two: form.spool_columns === 2 }" aria-hidden="true">
          <span v-for="c in ['accent', 'teal', 'sky', 'lime']" :key="c" :data-tone="c" /></div></OuiFormRow>
      </OuiFormSection>

      <OuiFormSection id="s-check" :icon="check" tone="teal" :title="t('set.check')" :description="t('set.checkHint')">
        <OuiFormRow :label="t('set.checkOn')" for="plate-check"><Checkbox v-model="form.plate_check" input-id="plate-check" binary /></OuiFormRow>
        <OuiFormRow :label="t('set.margin')" for="plate-margin" :hint="t('set.marginHelp')">
          <InputNumber v-model="form.plate_margin" input-id="plate-margin" :min="0" :max="50" :step="5" suffix=" %" :use-grouping="false" aria-describedby="m-help" /><span id="m-help" class="oui-sr">{{ t('set.marginHelp') }}</span></OuiFormRow>
      </OuiFormSection>
    </div>

    <div class="oui-stack">
      <OuiFormSection id="s-display" :icon="eye" tone="violet" :title="t('set.display')" :description="t('set.displayHelp')">
        <div class="set-pad">
          <h3 class="oui-label">{{ t('set.displaySpools') }}</h3>
          <div class="set-checks"><span v-for="k in SPOOL_KEYS" :key="k" class="oui-row set-opt"><Checkbox :input-id="`d-${k}`" binary :model-value="form.display[k] !== false" :data-disp="k"
            @update:model-value="v => setDisp(k, v)" /><label :for="`d-${k}`">{{ t(`disp.${k}` as any) }}</label></span></div>
          <h3 class="oui-label">{{ t('set.displayHeads') }}</h3>
          <div class="set-checks"><span v-for="k in HEAD_KEYS" :key="k" class="oui-row set-opt"><Checkbox :input-id="`d-${k}`" binary :model-value="form.display[k] !== false" :data-disp="k"
            @update:model-value="v => setDisp(k, v)" /><label :for="`d-${k}`">{{ t(`disp.${k}` as any) }}</label></span></div>
          <p class="oui-meta">{{ t('set.displayNote') }}</p>
        </div>
      </OuiFormSection>

      <OuiFormSection id="s-dry" :icon="drop" tone="sky" :title="t('set.drying')" :description="t('set.dryingHelp')">
        <OuiFormRow v-for="[name, days] in dryRows" :key="name" :label="name" :for="`dry-${name}`">
          <InputNumber :model-value="days > 0 ? days : null" :input-id="`dry-${name}`" :min="0" :max="3650" :use-grouping="false" :suffix="' ' + t('set.days')"
            :aria-label="t('set.daysFor', { m: name })" :placeholder="t('set.noReminder')" @update:model-value="v => setDays(name, v)" @input="e => setDays(name, typeof e.value === 'number' ? e.value : null)" />
          <Button text severity="secondary" size="small" :aria-label="t('set.removeMat', { m: name })" :title="t('set.removeMat', { m: name })" @click="removeMat(name)">
            <template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
        </OuiFormRow>
        <p v-if="!dryRows.length" class="oui-meta set-pad">{{ t('set.dryNone') }}</p>
        <form class="oui-row set-pad" @submit.prevent="addMat"><InputText v-model="newMat" maxlength="24" class="set-grow" :placeholder="t('set.matPh')" :aria-label="t('set.matLabel')" />
          <Button type="submit" severity="secondary" :label="t('set.addMat')" :disabled="!newMat.trim()"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></form>
        <template #footer><p class="oui-meta">{{ t('set.dryNote') }}</p></template>
      </OuiFormSection>

      <OuiFormSection id="s-printer" :icon="printer" tone="cobalt" :title="t('set.printer')" :description="t('set.liveNeeded')">
        <OuiFormRow :label="t('set.progressOn')" for="show-progress"><Checkbox v-model="form.progress.on" input-id="show-progress" binary /></OuiFormRow>
        <OuiFormRow :label="t('set.finish')" for="prog-finish"><Checkbox v-model="form.progress.finish" input-id="prog-finish" binary :disabled="!form.progress.on" /></OuiFormRow>
        <OuiFormRow :label="t('set.slot')" for="prog-slot"><Checkbox v-model="form.progress.slot" input-id="prog-slot" binary :disabled="!form.progress.on" /></OuiFormRow>
        <OuiFormRow :label="t('set.idle')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.idle')"><span v-for="v in ['line', 'hide'] as const" :key="v" class="oui-row set-opt">
            <RadioButton v-model="form.progress.idle" :input-id="`idle-${v}`" name="progress-idle" :value="v" :disabled="!form.progress.on" /><label :for="`idle-${v}`">{{ t(`set.idle.${v}`) }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.autoKeep')" for="auto-keep" :hint="t('set.autoKeepHelp')"><Checkbox v-model="form.auto_keep_slots" input-id="auto-keep" binary aria-describedby="auto-keep-help" /><span id="auto-keep-help" class="oui-sr">{{ t('set.autoKeepHelp') }}</span></OuiFormRow>
        <OuiFormRow :label="t('rfid.skippedLabel')" :hint="t('rfid.skippedHelp')">
          <div class="oui-row"><span class="oui-meta" data-test="rfid-skipped">{{ rfidSkipped ? tn('rfid.skipped', rfidSkipped) : t('rfid.skippedNone') }}</span>
            <Button v-if="rfidSkipped" severity="secondary" size="small" :label="t('rfid.unskip')" data-test="rfid-unskip" @click="unskipRfid" /></div></OuiFormRow>
        <div class="set-pad"><div class="set-pv oui-well">
          <p class="oui-label">{{ t('set.preview') }}</p>
          <p v-if="!form.progress.on" class="oui-meta">{{ t('set.progressHidden') }}</p>
          <template v-else><p class="oui-row"><strong>Desk_Organiser_Plate_1</strong><OuiStatus state="busy">{{ t('progress.state.RUNNING') }}</OuiStatus><span class="oui-num">37%</span></p>
            <p class="oui-meta">{{ t('progress.layer', { n: 142, total: 380 }) }} · {{ t('progress.left', { d: t('progress.hm', { h: 2, m: '04' }) }) }}<template
              v-if="form.progress.finish"> · {{ t('progress.done', { time: '11:24' }) }}</template><template v-if="form.progress.slot"> · {{ t('printer.slotOf', { unit: 'AMS 1', n: 2 }) }}</template></p></template>
        </div></div>
      </OuiFormSection>

      <OuiFormSection id="s-stats" :icon="chart" tone="orange" :title="t('set.stats')" :description="t('set.statsKeep')">
        <OuiFormRow :label="t('set.statsOn')" for="show-stats"><Checkbox v-model="form.stats.on" input-id="show-stats" binary /></OuiFormRow>
        <OuiFormRow :label="t('set.currency')" :hint="t('set.currencyHelp')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.currency')"><span v-for="c in currencies" :key="c.v" class="oui-row set-opt">
            <RadioButton v-model="form.stats.cur" :input-id="`cur-${c.v}`" name="stats-cur" :value="c.v" :disabled="!form.stats.on" /><label :for="`cur-${c.v}`">{{ c.label }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.preview')">
          <p v-if="!form.stats.on" class="oui-meta">{{ t('set.statsHidden') }}</p>
          <p v-else class="set-end">{{ t('stats.cost') }}: <strong class="oui-num">{{ curSign }}24.10</strong><br><span class="oui-meta">Headphone_Stand.3mf · 94.3 g · {{ curSign }}2.08</span></p>
        </OuiFormRow>
      </OuiFormSection>

      <OuiFormSection id="s-lang" :icon="languages" tone="neutral" :title="t('lang.title')">
        <OuiFormRow :label="t('lang.label')" :hint="t('lang.help')">
          <Select :model-value="langPref" :options="langOptions" option-label="label" option-value="value" :aria-label="t('lang.label')" data-test="lang"
                  @update:model-value="setLangPref($event as LangPref)" /></OuiFormRow>
        <OuiFormRow :label="t('set.version', { v: boot.version })">
          <span v-if="!update.newer" class="oui-meta" role="status">{{ update.text }}</span>
          <Button v-else size="small" :label="t('set.newer', { v: update.newer })" @click="bridge.postSettings({ type: 'release' })" />
          <Button severity="secondary" size="small" :label="t('set.checkUpdate')" :loading="update.busy" @click="checkUpdate"><template #icon><OuiIcon :icon="info" :size="14" /></template></Button>
        </OuiFormRow>
        <p class="oui-meta set-pad set-log">{{ t('set.log', { path: boot.settings.log_path }) }}</p>
      </OuiFormSection>
    </div>

    <template #footer>
      <OuiStatus v-if="dirty" state="pending" role="status">{{ t('set.unsaved') }}</OuiStatus>
      <span v-if="saveWhy" id="save-why" class="oui-meta">{{ saveWhy }}</span>
      <span class="oui-spacer" />
      <Button severity="secondary" text :label="t('common.cancel')" data-test="cancel" @click="leave" />
      <Button :label="t('set.save')" :disabled="!ready" :loading="saving" aria-describedby="save-why" data-test="save" @click="save"><template #icon><OuiIcon :icon="saveIcon" :size="14" /></template></Button>
    </template>
  </OuiSettings>
  <SetupWizard />
  </div>
</template>

<style>
.set-pad { padding: var(--oui-s3) var(--oui-s4); }
.set-pad > * + * { margin-top: var(--oui-s2); }
.set-pv { display: grid; gap: var(--oui-s1); padding: var(--oui-s3); }
.set-list { list-style: none; margin: 0; padding: 0; display: grid; gap: 2px; }
.set-list li { display: flex; justify-content: space-between; gap: var(--oui-s2); }
.set-opt { gap: 6px; }
.set-sample { display: inline-flex; align-items: center; gap: var(--oui-s2); }
.set-cols { display: grid; gap: 4px; width: min(220px, 100%); }
.set-cols.two { grid-template-columns: 1fr 1fr; }
.set-cols span { height: 14px; border-radius: var(--oui-radius-sm); background: var(--oui-tone-soft); box-shadow: inset 4px 0 0 var(--oui-tone); }
.set-checks { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 6px var(--oui-s4); }
.set-checks > .set-opt { flex-wrap: nowrap; align-items: flex-start; }
.set-checks label { min-width: 0; padding-top: 1px; }
.set-grow { flex: 1 1 160px; min-width: 0; }
.set-end { text-align: end; }
.set-log { overflow-wrap: anywhere; }
</style>
