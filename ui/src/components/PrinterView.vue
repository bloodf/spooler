<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import ProgressPanel from './ProgressPanel.vue';
import PrinterPanel from './PrinterPanel.vue';
import LinkedPanel from './LinkedPanel.vue';
import PlatePanel from './PlatePanel.vue';
import UsagePanel from './UsagePanel.vue';
import PeerNote from './PeerNote.vue';
import { m } from '../state/main';
import { addPrinter } from '../state/printers';
import { t } from '../core/i18n';
const linkedAny = computed(() => m.spools.some(s => s.ams && !s.archived));
</script>
<template>
  <div class="pv">
    <PeerNote where="printer" />
    <ProgressPanel />
    <PrinterPanel v-for="p in m.cfg" :key="p.id" :p="p" />
    <LinkedPanel v-if="linkedAny" />
    <div v-if="!m.cfg.length && !linkedAny" class="sp-card pv-empty"><p>{{ t('printer.none') }}</p></div>
    <div><Button severity="secondary" outlined :label="t('printer.add')" data-test="add-printer" @click="addPrinter" /></div>
    <PlatePanel />
    <UsagePanel />
  </div>
</template>
<style scoped>.pv { display: grid; gap: 16px; } .pv-empty p { margin: 0; }</style>
