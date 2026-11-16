<script setup lang="ts">
import { computed } from 'vue';
import InputText from 'primevue/inputtext';
import Select from 'primevue/select';
import MultiSelect from 'primevue/multiselect';
import ToggleSwitch from 'primevue/toggleswitch';
import EditorNumber from './EditorNumber.vue';
import type { FieldDef } from '../logic/editor';
import { t } from '../core/i18n';

// One Spoolman extra field, with the input its type calls for: a switch, a menu, a number box with its unit (two for a
// range), else text. Datetimes are written as ISO dates.
const props = defineProps<{ def: FieldDef; id: string; invalid?: boolean; describedby?: string }>();
const model = defineModel<unknown>();
const kind = computed(() => props.def.field_type || 'text');
const options = computed(() => (props.def.choices ?? []).map(c => ({ value: c, label: c })));
const whole = computed(() => kind.value.startsWith('integer'));
const range = computed<(number | null)[]>(() => (Array.isArray(model.value) ? model.value as (number | null)[] : [null, null]));
const setEnd = (i: number, v: number | null) => { const next = [...range.value]; next[i] = v; model.value = next; };
const label = computed(() => props.def.name || props.def.key);
</script>
<template>
  <ToggleSwitch v-if="kind === 'boolean'" :input-id="id" :model-value="model === true" :aria-describedby="describedby" @update:model-value="v => (model = v)" />
  <MultiSelect v-else-if="kind === 'choice' && def.multi_choice" :input-id="id" :model-value="(model as string[] | null) ?? []" :options="options" option-label="label" option-value="value"
               display="chip" :invalid="invalid" @update:model-value="v => (model = v)" />
  <Select v-else-if="kind === 'choice'" :input-id="id" :model-value="model ?? null" :options="options" option-label="label" option-value="value" show-clear
          :invalid="invalid" @update:model-value="v => (model = v ?? null)" />
  <EditorNumber v-else-if="kind === 'integer' || kind === 'float'" :id="id" :model-value="(model as number | null) ?? null" :unit="def.unit" :digits="whole ? 0 : 4"
                :invalid="invalid" :describedby="describedby" @update:model-value="v => (model = v)" />
  <span v-else-if="kind.endsWith('_range')" class="ex-range">
    <EditorNumber :id="id" :label="`${label}: ${t('editor.from')}`" :model-value="range[0]" :unit="def.unit" :digits="whole ? 0 : 4" @update:model-value="v => setEnd(0, v)" />
    <span aria-hidden="true">–</span>
    <EditorNumber :label="`${label}: ${t('editor.to')}`" :model-value="range[1]" :unit="def.unit" :digits="whole ? 0 : 4" @update:model-value="v => setEnd(1, v)" />
  </span>
  <InputText v-else :id="id" :model-value="(model as string | null) ?? ''" :placeholder="kind === 'datetime' ? '2026-11-16' : undefined" :maxlength="1024" :invalid="invalid"
             :aria-describedby="describedby" @update:model-value="v => (model = v)" />
</template>
<style>
.ex-range { flex: 1 1 220px; display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; }
</style>
