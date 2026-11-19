<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiEmpty, OuiHint, OuiIcon, OuiPageHeader, OuiPanel } from '../../shared/src/components';
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
// How booking and linking work, said once for the tab, behind the page header's (i): only the parts true for one of the printers shown.
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
    <OuiPageHeader :title="t('nav.printer')">
      <template #actions>
        <OuiHint v-if="how.length || m.peers.u1control" end :label="t('printer.howTitle')">
          <PeerNote where="printer" />
          <span v-if="how.length" class="sp-hint-p" data-test="how-booking"><strong class="sp-hint-p">{{ t('printer.howTitle') }}</strong><span v-for="(line, i) in how" :key="i" class="sp-hint-p">{{ line }}</span></span>
        </OuiHint>
        <Button v-if="m.cfg.length || linkedAny" severity="secondary" :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
      </template>
    </OuiPageHeader>
    <RfidPanel />
    <ProgressPanel />
    <!-- The plate check, the bookings and the printers pack into columns (two from 1160 px, three from 1800 px), each
         panel under the one before it in its column, so a short panel never leaves a gap beside a tall one. -->
    <div class="pv-grid" data-test="printer-grid">
      <PlatePanel />
      <UsagePanel />
      <PrinterPanel v-for="p in m.cfg" :key="p.id" :p="p" />
      <LinkedPanel v-if="linkedAny" />
    </div>
    <OuiPanel v-if="!m.cfg.length && !linkedAny"><OuiEmpty compact :icon="printer" :title="t('printer.none')">
      <template #actions><Button :label="t('printer.add')" data-test="add-printer" @click="addPrinter"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button></template></OuiEmpty></OuiPanel>
  </div>
</template>
<style>
.pv-grid { columns: 1; column-gap: var(--oui-s3); }
.pv-grid > * { break-inside: avoid; margin-block-end: var(--oui-s3); }
.pv-grid:empty { display: none; }
@container oui-page (min-width: 1160px) { .pv-grid { columns: 2; } }
@container oui-page (min-width: 1800px) { .pv-grid { columns: 3; } }
</style>
