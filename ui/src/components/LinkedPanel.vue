<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiPanel } from '../../shared/src/components';
import { printer } from '../../shared/src/icons';
import SpoolSlot from './SpoolSlot.vue';
import { m } from '../state/main';
import { showSpool } from '../state/menu';
import { t, tn } from '../core/i18n';
import type { Spool } from '../logic/spools';

// Bambu Cloud: a representative view built from the spools the cloud links to AMS slots.
const printers = computed(() => {
  const byName = new Map<string, Map<string | number, Map<number, Spool>>>();
  for (const s of m.spools) {
    const a = s.ams;
    if (!a || s.archived) continue;
    const name = a.printer || t('printer.defaultName');
    const units = byName.get(name) ?? new Map();
    const unit = Number(a.unit);
    const key = unit >= 128 ? 'ext' : Number.isFinite(unit) ? unit : 0;
    const slots = units.get(key) ?? new Map();
    slots.set(key === 'ext' ? 0 : Number(a.slot), s);
    units.set(key, slots);
    byName.set(name, units);
  }
  return [...byName.entries()].map(([name, units]) => ({ name, units: [...units.entries()].sort((x, y) => (x[0] === 'ext' ? 999 : +x[0]) - (y[0] === 'ext' ? 999 : +y[0])) }));
});
const slotsOf = (key: string | number, slots: Map<number, Spool>) => (key === 'ext' ? [0]
  : Array.from({ length: Math.max(3, ...[...slots.keys()].filter(Number.isFinite)) + 1 }, (_, i) => i));
const count = (units: [string | number, Map<number, Spool>][]) => units.reduce((a, u) => a + u[1].size, 0);
</script>
<template>
  <OuiPanel v-for="p in printers" :key="p.name" class="lp" :title="p.name" :icon="printer" tone="magenta" :meta="tn('linked.count', count(p.units))">
    <div class="oui-stack">
      <template v-for="[key, slots] in p.units" :key="String(key)">
        <h3 class="oui-label">{{ key === 'ext' ? t('printer.external') : `${t('printer.ams')} ${+key + 1}` }}</h3>
        <div class="oui-cards">
          <SpoolSlot v-for="i in slotsOf(key, slots)" :key="i" :label="key === 'ext' ? 'E' : String(i + 1)" :spool="slots.get(i)">
            <p v-if="!slots.get(i)" class="oui-meta">{{ t('linked.noSpool') }}</p>
            <template v-if="slots.get(i)" #actions><Button severity="secondary" text size="small" :label="t('printer.openSpool')" @click="showSpool(slots.get(i)!.id)" /></template>
          </SpoolSlot>
        </div>
      </template>
      <p class="oui-meta">{{ t('linked.note') }}</p>
    </div>
  </OuiPanel>
</template>
