<script setup lang="ts">
import { computed, nextTick, onMounted, ref } from 'vue';
import { OuiSpoolPick, type OuiSpoolPickLabels } from '@orca-plugins/ui-foundation/src/components';
import { m } from '../state/main';
import { t, locale } from '../core/i18n';
import { formatWeight, pickSpools, shown } from '../logic/spools';
import { takenIds } from '../logic/printers';

// Pick a spool for a slot, colour first (the shared OuiSpoolPick): one swatch per colour, so 2000 spools in 15 colours
// draw 15 circles. A colour with one spool picks it at once; with several, a dialog lists them fullest first.
// The search is focused on open; Escape closes (F11). `selected`: the spool in the slot now, marked.
const props = defineProps<{ label: string; excludeTaken?: boolean; selected?: number | null }>();
const emit = defineEmits<{ pick: [id: number]; close: [] }>();
const root = ref<HTMLElement | null>(null);
const spools = computed(() => pickSpools(m.spools, props.excludeTaken ? takenIds(m.cfg) : undefined, m.low));
const labels = computed<OuiSpoolPickLabels>(() => ({ label: props.label, spools: t('picker.spools'), noColour: t('picker.noColour'), choose: t('picker.choose'),
  unknown: t('spool.unknownLeft'), empty: t('picker.none'), search: t('picker.search'), noMatch: t('picker.noMatch'), allMaterials: t('filters.allMaterials') }));
const grams = (g: number) => formatWeight(g, shown(m.disp, 'exact_weight'), locale.value);
const pick = (id: number | string | null) => { if (id != null) emit('pick', Number(id)); };
onMounted(() => nextTick(() => root.value?.querySelector<HTMLInputElement>('[data-spick="search"]')?.focus()));
</script>
<template>
  <div ref="root" class="pk oui-well" data-test="picker">
    <OuiSpoolPick :spools="spools" :labels="labels" :selected="selected ?? null" :grams="grams" @pick="pick" @close="emit('close')" />
    <p v-if="excludeTaken" class="oui-meta" data-test="picker-note">{{ t('picker.takenHint') }}</p>
  </div>
</template>
<style>
.pk { display: grid; gap: var(--oui-s2); padding: var(--oui-s2); box-shadow: inset 0 0 0 1px var(--oui-primary-mark); min-width: 0; }
</style>
