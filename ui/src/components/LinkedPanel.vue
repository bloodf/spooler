<script setup lang="ts">
import { computed } from 'vue';
import SpoolCard from './SpoolCard.vue';
import { m } from '../state/main';
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
  <section v-for="p in printers" :key="p.name" class="sp-card lp" :aria-label="p.name">
    <h2>{{ p.name }} <span class="oui-meta">{{ tn('linked.count', count(p.units)) }}</span></h2>
    <template v-for="[key, slots] in p.units" :key="String(key)">
      <strong>{{ key === 'ext' ? t('printer.external') : `${t('printer.ams')} ${+key + 1}` }}</strong>
      <div class="lp-grid"><div v-for="i in slotsOf(key, slots)" :key="i" class="lp-cell"><span class="oui-meta">{{ key === 'ext' ? 'E' : i + 1 }}</span>
        <SpoolCard v-if="slots.get(i)" :spool="slots.get(i)!" />
        <div v-else class="lp-empty"><strong>{{ t('tray.empty') }}</strong><span class="oui-meta">{{ t('linked.noSpool') }}</span></div></div></div>
    </template>
    <p class="oui-meta">{{ t('linked.note') }}</p>
  </section>
</template>
<style scoped>
.lp { display: grid; gap: 8px; }
.lp-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(220px, 1fr)); gap: 8px; }
.lp-cell { display: grid; gap: 4px; }
.lp-empty { display: grid; padding: 10px; border: 1px dashed var(--oui-border); border-radius: 12px; }
</style>
