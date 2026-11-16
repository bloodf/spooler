<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiStatus } from '../../shared/src/components';
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
const tool = (i: number) => (props.lv.heads && i < 4 ? (i + 1) as 1 | 2 | 3 | 4 : undefined);
async function clear() {
  if (!await ask({ title: t('moon.clearTitle'), text: t('moon.clearText', { printer: props.lv.name }), yes: t('moon.clear'), no: t('common.goBack') })) return;
  moonSet(props.link, null);
}
function pick(id: number) { ui.picking = null; moonSet(props.link, id); }
</script>
<template>
  <div class="lu oui-stack">
    <template v-if="moon">
      <h3 class="oui-label">{{ t('moon.active') }}</h3>
      <div class="oui-cards">
        <TrayCard :tray="lv.ext" label="E" :empty-label="t('moon.none')" :empty-hint="t('moon.noneHelp')">
          <SpoolPicker v-if="picking" :label="t('moon.change')" @pick="pick" @close="ui.picking = null" />
          <template #actions>
            <Button severity="secondary" size="small" :label="t('moon.change')" :aria-expanded="!!picking" :data-focus-key="`moon-pick:${link}`" data-act="moon-pick"
                    @click="ui.picking = picking ? null : { p: link, moon: true }" />
            <Button v-if="lv.ext" severity="secondary" text size="small" :label="t('moon.clear')" :data-focus-key="`moon-clear:${link}`" @click="clear" />
          </template>
        </TrayCard>
      </div>
      <p v-if="m.moonNote && m.moonNote.id === link" role="status" data-test="moon-note"><OuiStatus :state="m.moonNote.ok ? 'ok' : 'error'" variant="plain">{{ m.moonNote.text }}</OuiStatus></p>
    </template>
    <template v-else>
      <template v-for="(x, k) in units" :key="String(x.u.id) + ':' + k">
        <h3 class="oui-label">{{ x.label }}</h3>
        <div class="oui-cards">
          <TrayCard v-for="(tr, i) in x.u.trays" :key="i" :tray="tr" :label="lv.heads ? 'T' + (i + 1) : String(i + 1)" :tool="tool(i)" :active="!!act && act.unit === x.u.id && act.slot === i" />
        </div>
      </template>
      <template v-if="lv.ext && !lv.heads">
        <h3 class="oui-label">{{ t('printer.external') }}</h3>
        <div class="oui-cards"><TrayCard :tray="lv.ext" label="E" :active="!!act && act.unit === 'ext'" /></div>
      </template>
      <p v-if="lv.hh" class="oui-meta" data-test="hh-note">{{ t('printer.hhNote') }}</p>
      <p v-if="!units.length && !lv.ext" class="oui-meta" role="status">{{ lv.heads ? t('printer.waitingHeads') : t('printer.waitingSlots') }}</p>
    </template>
  </div>
</template>
