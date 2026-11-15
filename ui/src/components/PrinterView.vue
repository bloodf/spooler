<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiEmpty, OuiIcon, OuiPanel } from '../../shared/src/components';
import { plus, printer } from '../../shared/src/icons';
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
// The plate check and the bookings sit beside the printers when the tab is wide, under them when it is not.
const side = computed(() => !!m.plate || (m.usage.enabled && (m.liveOn || m.usage.prints.length > 0)));
</script>
<template>
  <div class="oui-stack pv">
    <PeerNote where="printer" />
    <div class="pv-grid" :class="{ 'pv-side': side }">
      <div class="oui-stack">
        <ProgressPanel />
        <PrinterPanel v-for="p in m.cfg" :key="p.id" :p="p" />
        <LinkedPanel v-if="linkedAny" />
        <OuiPanel v-if="!m.cfg.length && !linkedAny"><OuiEmpty compact :icon="printer" tone="magenta" :title="t('printer.none')">
          <template #actions><Button :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></template></OuiEmpty></OuiPanel>
        <div v-else><Button severity="secondary" :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></div>
      </div>
      <div v-if="side" class="oui-stack">
        <PlatePanel />
        <UsagePanel />
      </div>
    </div>
  </div>
</template>
<style>
.pv-grid { display: grid; gap: var(--oui-s3); grid-template-columns: minmax(0, 1fr); align-items: start; }
@container oui-page (min-width: 1160px) { .pv-side { grid-template-columns: minmax(0, 7fr) minmax(420px, 5fr); } }
</style>
