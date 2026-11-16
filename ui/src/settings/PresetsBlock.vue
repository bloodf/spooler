<script setup lang="ts">
import { computed, ref } from 'vue';
import Checkbox from 'primevue/checkbox';
import RadioButton from 'primevue/radiobutton';
import Select from 'primevue/select';
import { OuiBanner, OuiFormRow, OuiFormSection } from '../../shared/src/components';
import { files } from '../../shared/src/icons';
import EditorNumber from '../components/EditorNumber.vue';
import { form } from './state';
import { t } from '../core/i18n';
import { TUNE_FIELDS, basesFor, matName, setTune, tuneMaterials, type TuneKey } from '../logic/presets';

// Settings > Presets: one OrcaSlicer preset per filament or per spool, and Advanced tuning per material (off by default;
// off, the presets are made exactly as before).
const modes = ['filament', 'spool'] as const;
const mode = computed({ get: () => (form.presets.per_spool ? 'spool' : 'filament'), set: v => { form.presets = { ...form.presets, per_spool: v === 'spool' }; } });
const tuning = computed({ get: () => form.presets.tuning, set: v => { form.presets = { ...form.presets, tuning: !!v }; } });

const mat = ref('PLA');
const mats = computed(() => tuneMaterials(form.presets.materials).map(name => ({ name, label: form.presets.materials[name] ? `${name} ●` : name })));
const pickMat = (v: unknown) => { const name = matName(String(v ?? '')); if (name) mat.value = name; };
const row = computed(() => form.presets.materials[mat.value] ?? {});
const bases = computed(() => [{ name: '', label: t('presets.baseAuto') }, ...basesFor(form.parents ?? [], mat.value).map(p => ({ name: p.name, label: p.name }))]);
const value = (key: TuneKey) => (typeof row.value[key] === 'number' ? (row.value[key] as number) : null);
function set(key: TuneKey | 'parent', v: number | string | null): void {
  form.presets = { ...form.presets, materials: setTune(form.presets.materials, mat.value, key, v) };
}
</script>

<template>
  <OuiFormSection id="s-presets" :icon="files" tone="teal" :title="t('presets.title')" :description="t('presets.help')">
    <OuiFormRow :label="t('presets.mode')">
      <div class="oui-row" role="radiogroup" :aria-label="t('presets.mode')"><span v-for="v in modes" :key="v" class="oui-row set-opt">
        <RadioButton v-model="mode" :input-id="`pm-${v}`" name="preset-mode" :value="v" :data-test="`preset-mode-${v}`" /><label :for="`pm-${v}`">{{ t(`presets.mode.${v}`) }}</label></span></div>
    </OuiFormRow>
    <div class="set-pad">
      <p class="oui-meta" data-test="preset-mode-help">{{ form.presets.per_spool ? t('presets.spoolHelp') : t('presets.filamentHelp') }}</p>
      <OuiBanner tone="info" :title="t('presets.unsaved')" data-test="preset-unsaved" />
    </div>

    <OuiFormRow :label="t('presets.tuning')" for="tune-on" :hint="t('presets.tuningHelp')">
      <Checkbox v-model="tuning" input-id="tune-on" binary aria-describedby="tune-help" data-test="tune-on" /><span id="tune-help" class="oui-sr">{{ t('presets.tuningHelp') }}</span></OuiFormRow>
    <template v-if="tuning">
      <OuiFormRow :label="t('filters.material')" for="tune-mat" :hint="t('presets.materialHelp')">
        <Select :model-value="mat" input-id="tune-mat" :options="mats" option-label="label" option-value="name" editable data-test="tune-mat"
                @update:model-value="pickMat" @blur="e => pickMat((e.target as HTMLInputElement | null)?.value)" /></OuiFormRow>
      <OuiFormRow :label="t('presets.base')" for="tune-base" :hint="t('presets.baseHelp')">
        <Select :model-value="(row.parent as string) ?? ''" input-id="tune-base" :options="bases" option-label="label" option-value="name" filter data-test="tune-base"
                @update:model-value="v => set('parent', v || null)" /></OuiFormRow>
      <OuiFormRow v-for="f in TUNE_FIELDS" :key="f.key" :label="t(`presets.key.${f.key}`)" :for="`tune-${f.key}`">
        <EditorNumber :id="`tune-${f.key}`" :model-value="value(f.key)" :min="f.min" :max="f.max" :digits="f.digits" :unit="f.unit" :data-test="`tune-${f.key}`"
                      @update:model-value="v => set(f.key, v)" /></OuiFormRow>
      <p class="oui-meta set-pad">{{ t('presets.tuningNote') }}</p>
    </template>
  </OuiFormSection>
</template>
