<script setup lang="ts">
import { computed, ref, watch } from 'vue';
import Dialog from 'primevue/dialog';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Select from 'primevue/select';
import SelectButton from 'primevue/selectbutton';
import Textarea from 'primevue/textarea';
import ToggleSwitch from 'primevue/toggleswitch';
import { OuiBanner, OuiFormRow, OuiIcon, OuiLevel, OuiSpool, OuiSwatch } from '../../shared/src/components';
import { plus, x } from '../../shared/src/icons';
import EditorNumber from './EditorNumber.vue';
import EditorExtra from './EditorExtra.vue';
import { boot } from '../core/boot';
import { m, note } from '../state/main';
import { editor, submitEditor } from '../state/menu';
import { ask } from '../core/dialog';
import { t, tn, locale } from '../core/i18n';
import { formatWeight, spoolPaint, swatchHex, type Filament } from '../logic/spools';
import { changed, densityFor, editable, filamentForm, filamentPayload, filled, previewFilament, problems, spoolForm, spoolPayload, wasOf,
  type FilamentForm, type Raw, type SpoolForm } from '../logic/editor';

// Add Spool (pick a Spoolman filament to restock, or make a new one, then the spool) and Edit Spool (the spool's fields
// and its filament's, which every spool of that filament shares), with a live preview drawn like the list's reels.
const adding = computed(() => editor.id == null);
const data = computed(() => editor.data);
const defs = computed(() => ({ spool: editable(data.value?.fields?.spool, boot.own_fields), filament: editable(data.value?.fields?.filament, boot.own_fields) }));
const raw = computed<Raw | undefined>(() => data.value?.spool ?? undefined);
const rawFil = computed<Raw | undefined>(() => raw.value?.filament ?? undefined);
const step = ref<1 | 2>(1);
const source = ref<'existing' | 'new'>('existing');
const pickId = ref<number | null>(null);
const sf = ref<SpoolForm>(spoolForm(undefined, []));
const ff = ref<FilamentForm>(filamentForm(undefined, []));
const tried = ref(false);
let suggested: number | null = null;

watch(data, d => {
  if (!d) return;
  sf.value = spoolForm(raw.value, defs.value.spool);
  ff.value = filamentForm(rawFil.value, defs.value.filament);
  step.value = 1;
  source.value = (d.filaments ?? []).length ? 'existing' : 'new';
  pickId.value = null; tried.value = false; suggested = null;
}, { immediate: true });
// The new filament was made but Spoolman refused the spool: it is an existing filament now, picked for the retry.
watch(() => editor.made, id => {
  if (id == null || !editor.data) return;
  editor.data.filaments = [...(editor.data.filaments ?? []), { ...previewFilament(ff.value), id }];
  source.value = 'existing'; pickId.value = id;
});
// A new filament gets the usual density of its material until the user types another.
watch(() => ff.value.material, mat => {
  const d = densityFor(mat);
  if (adding.value && d !== null && (ff.value.density === null || ff.value.density === suggested)) { ff.value.density = d; suggested = d; }
});

const sources = computed(() => [{ value: 'existing', label: t('editor.existing') }, { value: 'new', label: t('editor.new') }]);
const filaments = computed(() => ((data.value?.filaments ?? []) as Raw[])
  .map(f => ({ value: f.id as number, label: [f.vendor?.name, f.name || `#${f.id}`, f.material].filter(Boolean).join(' · '), f: f as Filament }))
  .sort((a, b) => a.label.localeCompare(b.label, locale.value)));
const picked = computed(() => filaments.value.find(o => o.value === pickId.value)?.f ?? null);
const withFilament = computed(() => !adding.value || source.value === 'new');
const baseSpool = computed(() => (raw.value ? spoolForm(raw.value, defs.value.spool) : undefined));
const issues = computed(() => problems(sf.value, withFilament.value ? ff.value : null, defs.value, adding.value, baseSpool.value));
const err = (key: string) => (tried.value || key === 'remaining_weight' || key === 'initial_weight') && issues.value[key] ? t(`editor.problem.${issues.value[key]}` as any) : undefined;
const shared = computed(() => m.spools.filter(s => rawFil.value?.id != null && s.filament?.id === rawFil.value.id && s.id !== editor.id).length);
const title = computed(() => (adding.value ? t('editor.addTitle') : t('editor.editTitle', { id: editor.id })));

// ------------------------------------------------------------------ preview
const pf = computed<Filament>(() => (adding.value && source.value === 'existing' ? picked.value ?? {} : previewFilament(ff.value)));
const start = computed(() => sf.value.initial_weight ?? pf.value.weight ?? null);
const left = computed(() => sf.value.remaining_weight ?? (adding.value ? start.value : null));
const fraction = computed(() => (typeof start.value === 'number' && start.value > 0 && typeof left.value === 'number' ? Math.max(0, Math.min(1, left.value / start.value)) : null));
const w = (g: number | null) => formatWeight(g, true, locale.value);
const weightLine = computed(() => (left.value === null ? t('spool.unknownLeft')
  : start.value === null ? w(left.value) : `${w(left.value)} ${t('weight.of', { total: w(start.value) })}`));
const sub = computed(() => [pf.value.vendor?.name, pf.value.material, typeof pf.value.diameter === 'number' ? `${new Intl.NumberFormat(locale.value).format(pf.value.diameter)} mm` : ''].filter(Boolean).join(' · '));

// ------------------------------------------------------------------ colours
// A colour left unset becomes grey once there are several: a multi-colour filament names every one.
const addColour = () => { ff.value.colors = [...ff.value.colors.map(c => c || '#888888'), ff.value.colors.at(-1) || '#888888']; };
const removeColour = (i: number) => { ff.value.colors = ff.value.colors.filter((_, j) => j !== i); };
const setColour = (i: number, v: string) => { ff.value.colors = ff.value.colors.map((c, j) => (j === i ? v : c)); };
const directions = computed(() => (['coaxial', 'longitudinal'] as const).map(v => ({ value: v, label: t(`editor.${v}`) })));

// ------------------------------------------------------------------ steps and save
const stepOk = computed(() => (source.value === 'existing' ? pickId.value !== null
  : !Object.keys(issues.value).some(k => k === 'density' || k === 'diameter' || k.startsWith('filament.'))));
function next() { tried.value = true; if (stepOk.value) { step.value = 2; tried.value = false; } }
async function save() {
  tried.value = true;
  if (adding.value && step.value === 1) { next(); return; }
  if (Object.keys(issues.value).length || editor.busy) return;
  const spool = spoolPayload(sf.value, defs.value.spool);
  if (adding.value) {
    submitEditor(source.value === 'existing' ? { action: 'create', filament_id: pickId.value, spool: filled(spool) }
      : { action: 'create', spool: filled(spool), filament: filled(filamentPayload(ff.value, defs.value.filament)) });
    return;
  }
  const sCh = changed(spool, spoolPayload(spoolForm(raw.value, defs.value.spool), defs.value.spool));
  // Spoolman keeps the used grams: a new starting weight alone would move the grams left, so those go with it.
  if ('initial_weight' in sCh && spool.remaining_weight !== null) sCh.remaining_weight = spool.remaining_weight;
  const fCh = changed(filamentPayload(ff.value, defs.value.filament), filamentPayload(filamentForm(rawFil.value, defs.value.filament), defs.value.filament));
  if (!Object.keys(sCh).length && !Object.keys(fCh).length) { editor.open = false; note('info', t('editor.noChanges'), 'spool-action'); return; }
  // A new location unlinks a U1 toolhead bound by its location: asked first, as the detail's Move does.
  const listed = m.spools.find(s => s.id === editor.id);
  if ('location' in sCh && listed?.u1_bound && !await ask({ title: t('menu.move'), text: t('confirm.unlink', { location: listed.location }),
    yes: t('confirm.unlinkYes'), no: t('common.goBack'), danger: true })) return;
  submitEditor({ action: 'save', spool: sCh, filament: fCh, was: { spool: wasOf(raw.value, sCh), filament: { ...wasOf(rawFil.value, fCh), id: rawFil.value?.id ?? null } } });
}
</script>

<template>
  <Dialog v-model:visible="editor.open" modal :header="title" :draggable="false" class="se-dialog" data-test="editor"
          :style="{ width: 'min(940px, calc(100vw - 32px))' }" :close-button-props="{ severity: 'secondary', text: true, rounded: true, 'aria-label': t('common.close') }">
    <div class="se">
      <OuiBanner v-if="editor.error" tone="error" :title="editor.error" role="alert" data-test="editor-error" />
      <p v-if="!data && !editor.error" class="oui-meta" role="status">{{ t('common.loading') }}</p>
      <div v-if="data" class="se-grid">
        <form id="se-form" class="se-form" novalidate @submit.prevent="save">
          <p v-if="adding" class="oui-label se-step" aria-live="polite">{{ t('editor.step', { n: step, name: step === 1 ? t('editor.stepFilament') : t('editor.stepSpool') }) }}</p>

          <template v-if="adding && step === 1">
            <SelectButton v-model="source" :options="sources" option-label="label" option-value="value" :allow-empty="false" :aria-label="t('editor.sourceLabel')" data-test="editor-source" />
            <div v-if="source === 'existing'" class="oui-field se-pick">
              <label for="se-pick">{{ t('editor.pick') }}</label>
              <Select v-model="pickId" input-id="se-pick" :options="filaments" option-label="label" option-value="value" filter :placeholder="t('editor.pickPh')"
                      :invalid="tried && pickId === null" :empty-message="t('editor.noFilaments')" aria-describedby="se-pick-h" data-test="editor-pick">
                <template #option="{ option }"><span class="se-opt"><OuiSwatch v-bind="spoolPaint(option.f)" />{{ option.label }}</span></template>
              </Select>
              <p id="se-pick-h" class="oui-meta" :class="{ 'se-bad': tried && pickId === null }">{{ tried && pickId === null ? t('editor.pickPh') : t('editor.pickHelp') }}</p>
            </div>
          </template>

          <section v-if="!adding || step === 2" class="se-sec" :aria-label="t('editor.stepSpool')">
            <h3 v-if="!adding" class="oui-label se-h">{{ t('editor.stepSpool') }}</h3>
            <OuiFormRow :label="t('editor.initial')" for="se-initial" :hint="t('editor.initialHelp')" :error="err('initial_weight')">
              <EditorNumber id="se-initial" v-model="sf.initial_weight" :min="0" :max="100000" :digits="1" unit="g" :invalid="!!err('initial_weight')" /></OuiFormRow>
            <OuiFormRow :label="t('editor.remaining')" for="se-left" :error="err('remaining_weight')">
              <EditorNumber id="se-left" v-model="sf.remaining_weight" :min="0" :max="100000" :digits="1" unit="g" :invalid="!!err('remaining_weight')" /></OuiFormRow>
            <OuiFormRow :label="t('menu.location')" for="se-loc">
              <InputText id="se-loc" v-model="sf.location" maxlength="64" list="se-locs" /></OuiFormRow>
            <datalist id="se-locs"><option v-for="l in [...new Set(m.spools.map(s => s.location).filter(Boolean))]" :key="l" :value="l" /></datalist>
            <OuiFormRow :label="t('editor.lot')" for="se-lot"><InputText id="se-lot" v-model="sf.lot_nr" maxlength="64" /></OuiFormRow>
            <OuiFormRow :label="t('detail.price')" for="se-price"><EditorNumber id="se-price" v-model="sf.price" :min="0" :max="10000000" :digits="2" /></OuiFormRow>
            <OuiFormRow :label="t('menu.noteLabel')" for="se-note" stacked><Textarea id="se-note" v-model="sf.comment" maxlength="1024" rows="2" auto-resize fluid /></OuiFormRow>
            <OuiFormRow :label="t('editor.archived')" for="se-arch"><ToggleSwitch v-model="sf.archived" input-id="se-arch" /></OuiFormRow>
            <OuiFormRow v-for="d in defs.spool" :key="d.key" :label="d.name || d.key" :for="`se-sx-${d.key}`" :error="err('spool.' + d.key)">
              <EditorExtra v-model="sf.extra[d.key]" :def="d" :id="`se-sx-${d.key}`" :invalid="!!err('spool.' + d.key)" /></OuiFormRow>
          </section>

          <section v-if="withFilament && (!adding || step === 1)" class="se-sec" :aria-label="t('editor.filament')" data-test="editor-filament">
            <h3 class="oui-label se-h">{{ adding ? t('editor.new') : t('editor.filament') }}</h3>
            <OuiBanner v-if="!adding" tone="info" :title="shared ? tn('editor.shared', shared) : t('editor.sharedNone')" data-test="editor-shared" />
            <datalist id="se-vendors"><option v-for="v in data.vendors" :key="v" :value="v" /></datalist>
            <OuiFormRow :label="t('disp.head_vendor')" for="se-vendor"><InputText id="se-vendor" v-model="ff.vendor" maxlength="64" list="se-vendors" /></OuiFormRow>
            <OuiFormRow :label="t('editor.name')" for="se-name"><InputText id="se-name" v-model="ff.name" maxlength="64" /></OuiFormRow>
            <OuiFormRow :label="t('filters.material')" for="se-mat"><InputText id="se-mat" v-model="ff.material" maxlength="64" /></OuiFormRow>
            <OuiFormRow :label="t('editor.colour')" for="se-col-0">
              <span class="se-cols">
                <span v-for="(c, i) in ff.colors" :key="i" class="se-col">
                  <input :id="`se-col-${i}`" type="color" :value="swatchHex(c) || '#888888'" :aria-label="t('editor.colourN', { n: i + 1 })" @input="e => setColour(i, (e.target as HTMLInputElement).value)">
                  <Button v-if="ff.colors.length > 1" severity="secondary" text size="small" :aria-label="t('editor.removeColour', { n: i + 1 })" :title="t('editor.removeColour', { n: i + 1 })"
                          @click="removeColour(i)"><template #icon><OuiIcon :icon="x" :size="12" /></template></Button>
                </span>
                <Button v-if="ff.colors.length < 8" severity="secondary" text size="small" :label="t('editor.addColour')" data-test="editor-add-colour" @click="addColour">
                  <template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
              </span></OuiFormRow>
            <OuiFormRow v-if="ff.colors.length > 1" :label="t('editor.direction')" for="se-dir">
              <Select v-model="ff.direction" input-id="se-dir" :options="directions" option-label="label" option-value="value" /></OuiFormRow>
            <OuiFormRow :label="t('disp.diameter')" for="se-dia" :error="err('diameter')">
              <EditorNumber id="se-dia" v-model="ff.diameter" :min="0" :max="10" :digits="2" unit="mm" :invalid="!!err('diameter')" /></OuiFormRow>
            <OuiFormRow :label="t('editor.density')" for="se-den" :error="err('density')">
              <EditorNumber id="se-den" v-model="ff.density" :min="0" :max="100" :digits="3" unit="g/cm³" :invalid="!!err('density')" /></OuiFormRow>
            <OuiFormRow :label="t('editor.nozzle')" for="se-noz"><EditorNumber id="se-noz" v-model="ff.settings_extruder_temp" :min="0" :max="600" unit="°C" /></OuiFormRow>
            <OuiFormRow :label="t('editor.bed')" for="se-bed"><EditorNumber id="se-bed" v-model="ff.settings_bed_temp" :min="0" :max="300" unit="°C" /></OuiFormRow>
            <OuiFormRow :label="t('editor.weight')" for="se-fw"><EditorNumber id="se-fw" v-model="ff.weight" :min="0" :max="100000" :digits="1" unit="g" /></OuiFormRow>
            <OuiFormRow :label="t('editor.spoolWeight')" for="se-sw"><EditorNumber id="se-sw" v-model="ff.spool_weight" :min="0" :max="100000" :digits="1" unit="g" /></OuiFormRow>
            <OuiFormRow v-for="d in defs.filament" :key="d.key" :label="d.name || d.key" :for="`se-fx-${d.key}`" :error="err('filament.' + d.key)">
              <EditorExtra v-model="ff.extra[d.key]" :def="d" :id="`se-fx-${d.key}`" :invalid="!!err('filament.' + d.key)" /></OuiFormRow>
          </section>
        </form>

        <aside class="se-preview" :aria-label="t('editor.preview')" data-test="editor-preview">
          <p class="oui-label">{{ t('editor.preview') }}</p>
          <div class="se-card oui-hero oui-on-band">
            <OuiSpool v-bind="spoolPaint(pf)" :fraction="fraction" :size="120" />
            <div class="se-id">
              <p class="oui-meta">{{ adding ? t('editor.newSpool') : t('spool.numbered', { id: editor.id }) }}</p>
              <p class="se-name" data-test="preview-name">{{ pf.name || t('editor.unnamed') }}</p>
              <p v-if="sub" class="oui-meta se-sub"><OuiSwatch v-bind="spoolPaint(pf)" />{{ sub }}</p>
              <p class="oui-num se-w" data-test="preview-weight">{{ weightLine }}</p>
              <OuiLevel :fraction="fraction" />
              <p v-if="sf.location.trim()" class="oui-meta">{{ sf.location.trim() }}</p>
            </div>
          </div>
        </aside>
      </div>
    </div>
    <template #footer>
      <Button severity="secondary" :label="t('common.cancel')" data-test="editor-cancel" @click="editor.open = false" />
      <Button v-if="adding && step === 2" severity="secondary" :label="t('editor.back')" data-test="editor-back" @click="step = 1" />
      <Button v-if="data && adding && step === 1" :label="t('editor.next')" data-test="editor-next" @click="next" />
      <Button v-else-if="data" type="submit" form="se-form" :label="adding ? t('editor.addTitle') : t('common.save')" :loading="editor.busy" data-test="editor-save" />
    </template>
  </Dialog>
</template>

<style>
.se { display: grid; gap: var(--oui-s3); container: se / inline-size; }
.se-grid { display: grid; gap: var(--oui-s4); grid-template-columns: minmax(0, 1fr); align-items: start; }
@container se (min-width: 720px) { .se-grid { grid-template-columns: minmax(0, 1fr) 280px; } .se-preview { position: sticky; top: 0; } }
.se-form { display: grid; gap: var(--oui-s3); container: oui-form / inline-size; min-width: 0; }
.se-sec { display: grid; border: 1px solid var(--oui-border); border-radius: var(--oui-radius); }
.se-sec > * + * { border-top: 1px solid var(--oui-border); }
.se-sec > datalist { display: none; }
.se-h { padding: var(--oui-s2) var(--oui-s4); }
.se-step { margin: 0; }
.se-pick { gap: var(--oui-s1); }
.se-opt { display: inline-flex; align-items: center; gap: var(--oui-s2); }
.se-bad { color: var(--oui-danger); }
.se-cols { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); }
.se-col { display: inline-flex; align-items: center; }
.se-col input[type=color] { width: 40px; height: var(--oui-control-sm, 32px); padding: 0; border: 1px solid var(--oui-control-border); border-radius: var(--oui-radius); background: none; }
.se-preview { display: grid; gap: var(--oui-s2); }
.se-card { display: grid; justify-items: center; gap: var(--oui-s3); padding: var(--oui-s4); border-radius: var(--oui-radius); }
.se-id { display: grid; gap: var(--oui-s1); width: 100%; min-width: 0; }
.se-name { font-size: var(--oui-text-lg, 1.125rem); font-weight: 700; overflow-wrap: anywhere; }
.se-sub { display: flex; align-items: center; gap: 6px; }
.se-w { font-weight: 600; }
</style>
