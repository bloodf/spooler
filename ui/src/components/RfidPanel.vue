<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiIcon, OuiPanel, OuiSpool } from '@orca-plugins/ui-foundation/src/components';
import { plus, rfid } from '@orca-plugins/ui-foundation/src/icons';
import * as bridge from '../core/bridge';
import { m, sourceOff, words } from '../state/main';
import { openEditor } from '../state/menu';
import { t, tn, locale } from '../core/i18n';
import { slotName } from '../logic/printers';
import { formatWeight, spoolFraction } from '../logic/spools';
import { BAMBU, leftGrams, type RfidOffer } from '../logic/rfid';

// Bambu RFID spools in a printer slot that no Spoolman spool carries: Add opens Add Spool filled in from the printer (the
// tag is stored with the spool, so it is known from then on); Skip stops asking about that spool in that printer.
const offers = computed(() => (m.source === 'spoolman' ? m.rfid : []));
function where(o: RfidOffer): string {
  const lv = m.live.printers.find(p => p.id === o.printer);
  if (!lv) return '';
  const u = o.unit === 'ext' ? null : lv.units.find(x => x.id === o.unit) ?? null;
  return `${lv.name} · ${slotName(lv, u, o.slot, o.unit === 'ext', words.value)}`;
}
function line(o: RfidOffer): string {
  const grams = leftGrams(o);
  const left = o.remain === null ? '' : grams === null ? t('rfid.left', { pct: Math.round(o.remain) })
    : t('rfid.leftGrams', { pct: Math.round(o.remain), grams: formatWeight(grams, true, locale.value) });
  return [`${BAMBU} ${o.name}`, o.name.toUpperCase().startsWith(o.type.toUpperCase()) ? '' : o.type, left].filter(Boolean).join(' · ');
}
const paint = (o: RfidOffer) => ({ color: o.colours[0] ? '#' + o.colours[0] : null, colors: o.colours.length > 1 ? o.colours.map(c => '#' + c) : null });
function skip(o: RfidOffer) {
  m.rfid = m.rfid.filter(x => x.tag !== o.tag);
  bridge.postMain({ type: 'rfid_skip', printer: o.printer, tag: o.tag });
}
</script>
<template>
  <!-- Always rendered, so a screen reader hears the first offer appear (a live region added with its content isn't read). -->
  <p class="oui-sr" aria-live="polite" data-test="rfid-live">{{ offers.length ? tn('rfid.title', offers.length) : '' }}</p>
  <OuiPanel v-if="offers.length" :title="tn('rfid.title', offers.length)" :icon="rfid" tone="magenta" :hint="t('rfid.skipHelp')" :hint-label="t('rfid.skip')" data-test="rfid">
    <ul class="rf-rows">
      <li v-for="o in offers" :key="o.printer + ':' + o.tag" class="rf-row" data-test="rfid-offer">
        <OuiSpool v-bind="paint(o)" :fraction="spoolFraction(null, o.remain)" :size="36" />
        <span class="rf-what"><strong>{{ t('rfid.offer', { where: where(o) }) }}</strong><span class="oui-meta">{{ line(o) }}</span></span>
        <span class="rf-act">
          <Button severity="secondary" size="small" :label="t('rfid.add')" :disabled="!!sourceOff" data-test="rfid-add" :aria-label="`${t('rfid.add')}: ${where(o)}`" @click="openEditor(null, { offer: o, where: where(o) })">
            <template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
          <Button severity="secondary" text size="small" :label="t('rfid.skip')" :aria-label="`${t('rfid.skip')}: ${where(o)}`" aria-describedby="rf-skip-help" data-test="rfid-skip" @click="skip(o)" />
        </span>
      </li>
    </ul>
    <p id="rf-skip-help" class="oui-sr">{{ t('rfid.skipHelp') }}</p>
  </OuiPanel>
</template>
<style>
.rf-rows { list-style: none; padding: 0; display: grid; gap: var(--oui-s3); }
.rf-row { display: grid; grid-template-columns: 36px minmax(0, 1fr) auto; gap: var(--oui-s3); align-items: center; }
.rf-what { display: grid; gap: 1px; min-width: 0; overflow-wrap: anywhere; }
.rf-act { display: flex; flex-wrap: wrap; gap: var(--oui-s1); justify-content: end; }
@container oui-page (max-width: 520px) { .rf-act { grid-column: 2 / -1; justify-content: start; } }
</style>
