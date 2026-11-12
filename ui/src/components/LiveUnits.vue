<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import TrayCard from './TrayCard.vue';
import SpoolPicker from './SpoolPicker.vue';
import { m } from '../state/main';
import { ui, moonSet } from '../state/printers';
import { ask } from '../core/dialog';
import { t } from '../core/i18n';
import { PROG_LIVE, type LivePrinter, type LiveUnit } from '../logic/printers';

// What a live printer reports: toolheads, AMS units, external spool — or, for a single-extruder Klipper printer
// with Spoolman, the active spool Moonraker books usage to (Change Spool / Clear).
const props = defineProps<{ lv: LivePrinter; link: string }>();
const act = computed(() => {
  const j = props.lv.job;
  return m.progress.on && m.progress.slot && j && j.tray && PROG_LIVE.includes(j.state) ? j.tray : null;
});
const moon = computed(() => props.lv.spool_set && m.source === 'spoolman');
const units = computed(() => {
  let ams = 0;
  return props.lv.units.map((u: LiveUnit) => {
    if (props.lv.heads) return { u, label: t('printer.toolheads') };
    if (u.kind === 'ht') return { u, label: t('printer.ht') };
    ams += 1;
    const name = props.lv.unit_label || t('printer.ams');
    return { u, label: props.lv.unit_label && props.lv.units.length === 1 ? name : `${name} ${ams}` };
  });
});
const picking = computed(() => ui.picking?.moon && ui.picking.p === props.link);
async function clear() {
  if (!await ask({ title: t('moon.clearTitle'), text: t('moon.clearText', { printer: props.lv.name }), yes: t('moon.clear'), no: t('common.goBack') })) return;
  moonSet(props.link, null);
}
function pick(id: number) { ui.picking = null; moonSet(props.link, id); }
</script>
<template>
  <div class="lu">
    <template v-if="moon">
      <div class="sp-row lu-unit"><span>{{ t('moon.active') }}</span><span class="sp-grow" />
        <Button v-if="lv.ext" severity="secondary" outlined :label="t('moon.clear')" :data-focus-key="`moon-clear:${link}`" @click="clear" />
        <Button :label="t('moon.change')" :aria-expanded="!!picking" :data-focus-key="`moon-pick:${link}`" data-act="moon-pick"
                @click="ui.picking = picking ? null : { p: link, moon: true }" /></div>
      <div class="lu-grid"><div class="lu-cell"><span class="lu-n">E</span>
        <TrayCard v-if="lv.ext" :tray="lv.ext" />
        <div v-else class="lu-none"><strong>{{ t('moon.none') }}</strong><span class="oui-meta">{{ t('moon.noneHelp') }}</span></div>
        <SpoolPicker v-if="picking" :label="t('moon.change')" @pick="pick" @close="ui.picking = null" /></div></div>
      <p v-if="m.moonNote && m.moonNote.id === link" class="oui-meta" :class="{ 'sp-err': !m.moonNote.ok }" role="status">{{ m.moonNote.text }}</p>
    </template>
    <template v-else>
      <template v-for="(x, k) in units" :key="String(x.u.id) + ':' + k">
        <div class="lu-unit">{{ x.label }}</div>
        <div class="lu-grid">
          <div v-for="(tr, i) in x.u.trays" :key="i" class="lu-cell" :class="{ active: act && act.unit === x.u.id && act.slot === i }">
            <span class="lu-n">{{ lv.heads ? 'T' + (i + 1) : i + 1 }}</span><TrayCard :tray="tr" />
            <span v-if="act && act.unit === x.u.id && act.slot === i" class="sp-chip accent">{{ t('progress.inUseSlot') }}</span>
          </div>
        </div>
      </template>
      <template v-if="lv.ext && !lv.heads">
        <div class="lu-unit">{{ t('printer.external') }}</div>
        <div class="lu-grid"><div class="lu-cell" :class="{ active: act && act.unit === 'ext' }"><span class="lu-n">E</span><TrayCard :tray="lv.ext" /></div></div>
      </template>
      <p v-if="!units.length && !lv.ext" class="oui-meta" role="status">{{ lv.heads ? t('printer.waitingHeads') : t('printer.waitingSlots') }}</p>
    </template>
  </div>
</template>
<style scoped>
.lu { display: grid; gap: 8px; }
.lu-unit { font-weight: 600; margin-top: 4px; }
.lu-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(200px, 1fr)); gap: 8px; }
.lu-cell { display: grid; gap: 4px; align-content: start; }
.lu-cell.active :deep(.tc) { border-color: var(--p-primary-color); box-shadow: inset 0 0 0 1px var(--p-primary-color); }
.lu-cell > .sp-chip { justify-self: start; }
.lu-n { color: var(--oui-muted); font-size: 12px; font-weight: 600; }
.lu-none { display: grid; gap: 2px; padding: 10px; border: 1px dashed var(--oui-border); border-radius: 12px; }
</style>
