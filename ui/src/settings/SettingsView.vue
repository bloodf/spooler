<script setup lang="ts">
import { computed, nextTick, onBeforeUnmount, onMounted, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import InputNumber from 'primevue/inputnumber';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import RadioButton from 'primevue/radiobutton';
import { OuiFormRow, OuiFormSection, OuiHint, OuiIcon, OuiRequirement, OuiStatus, OuiSwatch, type OuiSettingsSection } from '@orca-plugins/ui-foundation/src/components';
import { chart, check, drop, eye, files, info, languages, layers, note, plug, plus, printer, save as saveIcon, scale, settings as settingsIcon, spoolman, store, x } from '@orca-plugins/ui-foundation/src/icons';
import SourceBlock from './SourceBlock.vue';
import PresetsBlock from './PresetsBlock.vue';
import SetupWizard from './SetupWizard.vue';
import SettingsPages from '../components/SettingsPages.vue';
import * as bridge from '../core/bridge';
import { boot } from '../core/boot';
import { m, settingsPage } from '../state/main';
import { REFRESH_DEFAULT_S } from '../core/autorefresh';
import { t, tn, langPref, setLangPref, autoLocale, onLangPref } from '../core/i18n';
import { LOCALES } from '../core/i18n-core';
import type { LangPref } from '../core/i18n-core';
import { conn, bambu, form, saving, dirty, ready, saveWhy, update, save, checkUpdate, startSettings, openWizard, wizard, leave, rfidSkipped, unskipRfid, req, checkRequirements, type Requirement } from './state';

const stop = startSettings();
onBeforeUnmount(stop);
onLangPref(v => bridge.postSettings({ type: 'ui_language', value: v }));

// Display: what each spool shows, the state badges, and how the list behaves; then what a printer slot shows. Each group
// fills its columns top to bottom, so related switches sit under one another. Archived spools are shown from the list's
// own Filters, not from here.
const DISPLAY_GROUPS = [
  ['set.displayShown', ['vendor', 'material', 'colour_code', 'diameter', 'bar', 'location', 'spool_id', 'comment', 'lot_nr', 'extra_fields', 'exact_weight']],
  ['set.displayBadges', ['in_use', 'use_first', 'dried', 'rfid']],
  ['set.displayBehaviour', ['group_same', 'low_notice']],
  ['set.displayHeads', ['head_vendor', 'head_material', 'head_colour_code', 'head_weight', 'head_bar', 'head_spool', 'head_preset', 'head_rfid']],
] as const;
const logShown = ref(false);
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

// Requirements: the saved spool source. Spoolman installs with Docker on every desktop system.
const SPOOLMAN_DOCKER = 'docker run -d --name spoolman -p 7912:8000 -v spoolman-data:/home/app/.local/share/spoolman ghcr.io/donkie/spoolman:latest';
const SPOOLMAN_SITE = 'https://github.com/Donkie/Spoolman';
const reqSteps = (r: Requirement) => (r.id === 'bambu' ? [] : [t('req.os.mac'), t('req.os.win'), t('req.os.linux'), t('req.then')]);
// Our states on OuiRequirement's: unreachable (it answered earlier this session) is a missing row without the install line.
const reqRow = (r: Requirement) => {
  if (req.checking) return { status: 'checking' as const, label: t('req.checking'), detail: undefined };
  const label = r.status === 'ok' ? t('req.connected') : r.status === 'unreachable' ? t('req.unreachable') : r.status === 'unknown' ? t('req.untested')
    : r.signin ? t('req.signedOut') : t('req.status.missing');
  const status = r.status === 'ok' ? 'found' as const : r.status === 'unknown' ? 'unknown' as const : 'missing' as const;
  return { status, label, detail: r.details || undefined };
};
const reqMissing = computed(() => req.list.some(r => r.status === 'missing' || r.status === 'unreachable'));

// Six pages, each a few related sections. The source page flags itself until the source passed a test (Save waits for
// it), in red when the test failed, and while the source is missing (its Requirements section).
const srcState = computed(() => ((form.source === 'bambu' ? bambu.kind : conn.kind) === 'error' ? 'error' as const : ready.value && !reqMissing.value ? undefined : 'warn' as const));
const sections = computed<OuiSettingsSection[]>(() => [
  { id: 's-src', label: t('set.page.source'), icon: spoolman, ...(srcState.value ? { state: srcState.value } : {}) },
  { id: 's-list', label: t('set.layout'), icon: layers },
  { id: 's-printer', label: t('set.printer'), icon: printer },
  { id: 's-dry', label: t('set.drying'), icon: drop },
  { id: 's-presets', label: t('presets.title'), icon: files },
  { id: 's-general', label: t('set.page.general'), icon: settingsIcon },
]);
// A "Settings" link that names a page (the window's boot, or openSettings(page) in the tab) opens it once Settings shows.
const pages = ref<InstanceType<typeof SettingsPages>>();
function follow() {
  const id = settingsPage.value || (boot.mode === 'settings' ? boot.page ?? '' : '');
  if (!id || (boot.mode === 'tab' && m.view !== 'settings')) return;
  settingsPage.value = ''; boot.page = '';
  void nextTick(() => pages.value?.select(id));
}
watch([settingsPage, () => m.view], follow);
onMounted(follow);
</script>

<template>
  <!-- One root: the tab hides this view with v-show and names it as a tab panel. -->
  <div class="set">
  <SettingsPages ref="pages" :sections="sections" :nav-label="t('set.title')" :back-label="t('wiz.back')" :error-label="t('set.hasError')">
    <div id="s-src" class="set-page">
      <OuiFormSection id="s-source" :icon="spoolman" tone="magenta" :title="t('set.source')" :description="t('set.guideText')">
        <template #actions><Button severity="secondary" size="small" :label="t('set.openGuide')" data-test="open-guide" data-focus-key="open-guide" @click="openWizard" /></template>
        <div class="set-pad"><SourceBlock v-if="!wizard.open" /><p v-else class="oui-meta">{{ t('set.inGuide') }}</p></div>
        <OuiFormRow v-if="form.source === 'spoolman'" :label="t('set.calibration')" :hint="t('set.calibrationHelp')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.calibration')" data-test="save-calibration"><span v-for="v in ['ask', 'auto', 'never'] as const" :key="v" class="oui-row set-opt">
            <RadioButton v-model="form.save_calibration" :input-id="`cal-${v}`" name="save-calibration" :value="v" /><label :for="`cal-${v}`">{{ t(`set.calibration.${v}`) }}</label></span></div>
          <OuiHint :label="t('set.calibration')" :text="t('set.calibrationMore')" />
        </OuiFormRow>
        <OuiFormRow v-if="form.source === 'spoolman'" :label="t('set.refresh')" :hint="t('set.refreshHelp')">
          <Select :model-value="form.refresh_s ?? REFRESH_DEFAULT_S" :options="[0, 10, 15, 30, 60, 120, 300].map(n => ({ value: n, label: n ? t('set.refreshOption', { n }) : t('set.refreshOff') }))"
                  option-label="label" option-value="value" :aria-label="t('set.refresh')" data-test="refresh-every" @update:model-value="form.refresh_s = $event" />
          <OuiHint :label="t('set.refresh')" :text="t('set.refreshMore')" />
        </OuiFormRow>
      </OuiFormSection>
      <OuiFormSection id="s-req" :icon="plug" tone="neutral" :title="t('req.title')" :description="t('req.help')">
        <div aria-live="polite" data-test="requirements">
          <template v-for="r in req.list" :key="r.id">
            <OuiRequirement :name="r.id === 'bambu' ? 'Bambu Cloud' : 'Spoolman'" :why="t(r.id === 'bambu' ? 'req.why.bambu' : 'req.why.spoolman')"
                            :status="reqRow(r).status" :status-label="reqRow(r).label" :detail="reqRow(r).detail" :check-label="t('req.check')" data-test="req-row"
                            :install-text="r.status !== 'missing' ? undefined : t(r.id === 'bambu' ? 'req.bambuHow' : 'req.spoolmanInstall')"
                            :install-url="r.id === 'bambu' || r.status !== 'missing' ? undefined : SPOOLMAN_SITE" :install-label="t('req.install')"
                            @check="checkRequirements" @open="bridge.postSettings({ type: 'spoolman_help' })" />
            <div v-if="r.id !== 'bambu' && r.status === 'missing' && !req.checking" class="set-req-how" data-test="req-how">
              <pre class="oui-mono oui-well set-req-code">{{ SPOOLMAN_DOCKER }}</pre>
              <ul class="set-req-steps"><li v-for="line in reqSteps(r)" :key="line" class="oui-meta">{{ line }}</li></ul>
            </div>
          </template>
          <p v-if="!req.list.length" class="oui-meta set-pad">{{ t('req.checking') }}</p>
        </div>
      </OuiFormSection>
    </div>
    <div id="s-list" class="set-page">
      <OuiFormSection id="s-weights" :icon="scale" :title="t('set.weights')">
        <OuiFormRow :label="t('set.weightsLabel')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.weightsLabel')"><span v-for="o in weights" :key="o.v" class="oui-row set-opt">
            <RadioButton v-model="form.weight_display" :input-id="`w-${o.v}`" name="weight-display" :value="o.v" /><label :for="`w-${o.v}`">{{ o.label }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.preview')"><span class="set-sample"><OuiSwatch color="#1a1a1a" /><span>PLA Matte - Black</span><strong class="oui-num">{{ sample }}</strong></span></OuiFormRow>
      </OuiFormSection>
      <OuiFormSection id="s-layout" :icon="layers" :title="t('set.layout')" :description="t('set.layoutHelp')">
        <OuiFormRow :label="t('set.layoutLabel')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.layoutLabel')"><span v-for="c in [1, 2]" :key="c" class="oui-row set-opt">
            <RadioButton v-model="form.spool_columns" :input-id="`cols-${c}`" name="spool-cols" :value="c" /><label :for="`cols-${c}`">{{ c === 1 ? t('set.one') : t('set.two') }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.viewLabel')">
          <div class="oui-row" role="radiogroup" :aria-label="t('set.viewLabel')"><span v-for="v in (['table', 'cards'] as const)" :key="v" class="oui-row set-opt">
            <RadioButton v-model="form.spool_view" :input-id="`view-${v}`" name="spool-view" :value="v" /><label :for="`view-${v}`">{{ t(`list.${v}`) }}</label></span></div>
        </OuiFormRow>
        <OuiFormRow :label="t('set.preview')"><div class="set-cols" :class="{ two: form.spool_columns === 2 }" aria-hidden="true">
          <span v-for="c in 4" :key="c" /></div></OuiFormRow>
      </OuiFormSection>
      <OuiFormSection id="s-display" :icon="eye" :title="t('set.display')" :description="`${t('set.displayHelp')} ${t('set.displayNote')}`">
        <div class="set-pad">
          <template v-for="[title, keys] in DISPLAY_GROUPS" :key="title">
            <h3 class="oui-label">{{ t(title) }}</h3>
            <div class="set-checks" role="group" :aria-label="t(title)"><span v-for="k in keys" :key="k" class="oui-row set-opt"><Checkbox :input-id="`d-${k}`" binary :model-value="form.display[k] !== false" :data-disp="k"
              @update:model-value="v => setDisp(k, v)" /><label :for="`d-${k}`">{{ t(`disp.${k}` as any) }}</label></span></div>
          </template>
        </div>
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
    </div>
    <div id="s-printer" class="set-page">
      <OuiFormSection id="s-printer-panel" :icon="printer" tone="cobalt" :title="t('set.printer')" :description="t('set.liveNeeded')">
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
      <OuiFormSection id="s-check" :icon="check" tone="teal" :title="t('set.check')" :description="t('set.checkHint')">
        <OuiFormRow :label="t('set.checkOn')" for="plate-check"><Checkbox v-model="form.plate_check" input-id="plate-check" binary /></OuiFormRow>
        <OuiFormRow :label="t('set.margin')" for="plate-margin" :hint="t('set.marginHelp')">
          <InputNumber v-model="form.plate_margin" input-id="plate-margin" :min="0" :max="50" :step="5" suffix=" %" :use-grouping="false" aria-describedby="m-help" /><span id="m-help" class="oui-sr">{{ t('set.marginHelp') }}</span></OuiFormRow>
      </OuiFormSection>
    </div>
    <OuiFormSection id="s-dry" :icon="drop" tone="sky" :title="t('set.drying')" :description="`${t('set.dryingHelp')} ${t('set.dryNote')}`">
        <OuiFormRow v-for="[name, days] in dryRows" :key="name" :label="name" :for="`dry-${name}`">
          <InputNumber :model-value="days > 0 ? days : null" :input-id="`dry-${name}`" :min="0" :max="3650" :use-grouping="false" :suffix="' ' + t('set.days')"
            :aria-label="t('set.daysFor', { m: name })" :placeholder="t('set.noReminder')" @update:model-value="v => setDays(name, v)" @input="e => setDays(name, typeof e.value === 'number' ? e.value : null)" />
          <Button text severity="secondary" size="small" :aria-label="t('set.removeMat', { m: name })" :title="t('set.removeMat', { m: name })" @click="removeMat(name)">
            <template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
        </OuiFormRow>
        <p v-if="!dryRows.length" class="oui-meta set-pad">{{ t('set.dryNone') }}</p>
        <form class="oui-row set-pad" @submit.prevent="addMat"><InputText v-model="newMat" maxlength="24" class="set-grow" :placeholder="t('set.matPh')" :aria-label="t('set.matLabel')" />
          <Button type="submit" severity="secondary" :label="t('set.addMat')" :disabled="!newMat.trim()"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></form>
      </OuiFormSection>
    <PresetsBlock />
    <div id="s-general" class="set-page">
      <OuiFormSection id="s-stats" :icon="chart" tone="lime" :title="t('set.stats')" :description="t('set.statsKeep')">
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
      </OuiFormSection>
      <OuiFormSection id="s-about" :icon="info" tone="neutral" :title="t('set.about')">
        <OuiFormRow :label="t('set.version', { v: boot.version })">
          <Button v-if="update.newer" size="small" :label="t('set.newer', { v: update.newer })" @click="bridge.postSettings({ type: 'release' })" />
          <Button severity="secondary" size="small" :label="t('set.checkUpdate')" :loading="update.busy" @click="checkUpdate"><template #icon><OuiIcon :icon="info" :size="14" /></template></Button>
        </OuiFormRow>
        <!-- For a bug report: the log's path is shown when asked for, not as a line of the page. -->
        <OuiFormRow :label="t('set.logLabel')">
          <Button severity="secondary" size="small" :label="t('set.showLog')" :aria-expanded="logShown" aria-controls="set-log" data-test="show-log" @click="logShown = !logShown" />
          <Button severity="secondary" size="small" :label="t('set.feedback')" data-test="feedback" @click="bridge.postSettings({ type: 'feedback' })"><template #icon><OuiIcon :icon="note" :size="14" /></template></Button>
        </OuiFormRow>
        <p v-if="logShown" id="set-log" class="oui-mono set-pad set-log" data-test="log-path">{{ boot.settings.log_path }}</p>
      </OuiFormSection>
    </div>

    <template #footer>
      <OuiStatus v-if="dirty" state="pending" role="status">{{ t('set.unsaved') }}</OuiStatus>
      <span v-if="saveWhy" id="save-why" class="oui-meta">{{ saveWhy }}</span>
      <span class="oui-spacer" />
      <Button severity="secondary" text :label="t('common.cancel')" data-test="cancel" @click="leave" />
      <Button :label="t('set.save')" :disabled="!ready" :loading="saving" aria-describedby="save-why" data-test="save" @click="save"><template #icon><OuiIcon :icon="saveIcon" :size="14" /></template></Button>
    </template>
  </SettingsPages>
  <SetupWizard />
  </div>
</template>

<style>
/* A page of several sections; OuiSettings shows the open one (it sets `hidden` on the others). */
.set-page { display: grid; gap: var(--oui-s3); min-width: 0; }
.set-page[hidden] { display: none; }
.set-pad { padding: var(--oui-s3) var(--oui-s4); }
.set-pad > * + * { margin-top: var(--oui-s2); }
.set-pv { display: grid; gap: var(--oui-s1); padding: var(--oui-s3); }
.set-list { list-style: none; margin: 0; padding: 0; display: grid; gap: 2px; }
.set-list li { display: flex; justify-content: space-between; gap: var(--oui-s2); }
.set-opt { gap: 6px; }
.set-sample { display: inline-flex; align-items: center; gap: var(--oui-s2); }
.set-cols { display: grid; gap: 4px; width: min(220px, 100%); }
.set-cols.two { grid-template-columns: 1fr 1fr; }
.set-cols span { height: 14px; border-radius: var(--oui-radius-sm); background: var(--oui-raised); box-shadow: inset 0 0 0 1px var(--oui-border); }
.set-checks { columns: 2 200px; column-gap: var(--oui-s4); }
.set-checks > .set-opt { display: flex; flex-wrap: nowrap; align-items: flex-start; break-inside: avoid; padding-block: 3px; }
.set-pad > .oui-label:not(:first-child) { margin-top: var(--oui-s4); }
.set-checks label { min-width: 0; padding-top: 1px; }
.set-grow { flex: 1 1 160px; min-width: 0; }
.set-end { text-align: end; }
.set-log { overflow-wrap: anywhere; user-select: all; }
.set-req-how { display: grid; gap: var(--oui-s1); padding: 0 var(--oui-s4) var(--oui-s3); }
.set-req-code { margin: 0; padding: var(--oui-s2); white-space: pre-wrap; overflow-wrap: anywhere; user-select: all; }
.set-req-steps { margin: 0; padding-inline-start: 1.2em; display: grid; gap: 2px; }
</style>
