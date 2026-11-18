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
import RfidPanel from './RfidPanel.vue';
import { m } from '../state/main';
import { addPrinter } from '../state/printers';
import { t } from '../core/i18n';
import { isNet } from '../logic/printers';
const linkedAny = computed(() => m.spools.some(s => s.ams && !s.archived));
const liveOf = (id: string) => (m.live.links?.[id] === 'live' ? m.live.printers.find(x => x.link === id) : undefined);
// How booking and linking work, said once for the tab: only the parts true for one of the printers shown.
const how = computed(() => {
  const out: string[] = [];
  if (m.cfg.some(p => p.auto)) out.push(t('printer.autoNote'), t('printer.klipperNote'));
  if (m.cfg.some(p => { const b = liveOf(p.id)?.bind; return b === 'T' || b === 'S'; })) out.push(t('printer.bindNote'));
  if (m.cfg.some(p => { const l = liveOf(p.id); return !!l?.hh && l.units.length > 0; })) out.push(t('printer.hhNote'));
  if (m.cfg.some(isNet)) out.push(t('printer.netNote'));
  if (m.cfg.some(p => !p.auto && !isNet(p) && !liveOf(p.id))) out.push(t('printer.manualNote'));
  return out;
});
</script>
<template>
  <div class="oui-stack pv">
    <PeerNote where="printer" />
    <details v-if="how.length" class="pv-how oui-well" data-test="how-booking">
      <summary>{{ t('printer.howTitle') }}</summary>
      <p v-for="(line, i) in how" :key="i" class="oui-meta">{{ line }}</p>
    </details>
    <RfidPanel />
    <ProgressPanel />
    <!-- Printers and the plate check and bookings share one grid: two columns from 1160 px, three from 1800 px. -->
    <div class="pv-grid" data-test="printer-grid">
      <PlatePanel />
      <UsagePanel />
      <PrinterPanel v-for="p in m.cfg" :key="p.id" :p="p" />
      <LinkedPanel v-if="linkedAny" />
    </div>
    <OuiPanel v-if="!m.cfg.length && !linkedAny"><OuiEmpty compact :icon="printer" tone="magenta" :title="t('printer.none')">
      <template #actions><Button :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></template></OuiEmpty></OuiPanel>
    <div v-else><Button severity="secondary" :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></div>
  </div>
</template>
<style>
.pv-grid { display: grid; gap: var(--oui-s3); grid-template-columns: minmax(0, 1fr); align-items: start; }
.pv-grid:empty { display: none; }
@container oui-page (min-width: 1160px) { .pv-grid { grid-template-columns: repeat(2, minmax(0, 1fr)); } }
@container oui-page (min-width: 1800px) { .pv-grid { grid-template-columns: repeat(3, minmax(0, 1fr)); } }
.pv-how { padding: var(--oui-s2) var(--oui-s3); }
.pv-how summary { cursor: pointer; color: var(--oui-primary); font-weight: 600; }
.pv-how p { max-width: 96ch; margin-top: var(--oui-s2); }
</style>
