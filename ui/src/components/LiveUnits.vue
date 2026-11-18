<script setup lang="ts">
import { computed, onBeforeUnmount, ref, watch } from 'vue';
import Button from 'primevue/button';
import { OuiStatus } from '../../shared/src/components';
import TrayCard from './TrayCard.vue';
import SpoolPicker from './SpoolPicker.vue';
import { m } from '../state/main';
import { ui, moonSet, bindSlot } from '../state/printers';
import { ask } from '../core/dialog';
import { t } from '../core/i18n';
import { PROG_LIVE, WAIT_SLOTS_MS, type LivePrinter, type LiveUnit, type Tray } from '../logic/printers';

// What a live printer reports: toolheads, AMS units, external spool — or, for a single-extruder Klipper printer
// with Spoolman, the active spool Moonraker books usage to (Change Spool / Clear). A U1 toolhead or an Anycubic
// ACE slot takes a spool from here too: the link is the Spoolman location U1 Control or Kobra Control reads.
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

// Linking a slot: the 0-based slot U1 Control (toolhead) or Kobra Control (box * 4 + slot) counts.
const bindable = computed(() => (props.lv.bind === 'T' || props.lv.bind === 'S') && m.source === 'spoolman');
const slotOf = (u: LiveUnit, i: number) => (props.lv.bind === 'S' ? Number(u.id) * 4 + i : i);
const canBind = (tr: Tray) => bindable.value && !tr.empty && tr.linked !== 'printer';
const bound = (tr: Tray) => tr.spool != null && (tr.linked === 'u1control' || tr.linked === 'kobracontrol');
const isBinding = (slot: number) => !!ui.picking?.bind && ui.picking.p === props.link && ui.picking.s === slot;
const printing = computed(() => !!props.lv.job && PROG_LIVE.includes(props.lv.job.state));
async function busyOk(): Promise<boolean> {
  return !printing.value || ask({ title: t('bind.busyTitle', { printer: props.lv.name }), text: t('bind.busyText', { printer: props.lv.name }),
    yes: t('bind.busyYes'), no: t('common.goBack'), danger: true });
}
async function bindPick(slot: number, id: number) { ui.picking = null; if (await busyOk()) bindSlot(props.link, slot, id, true); }
async function unbind(slot: number, tr: Tray) {
  if (!await ask({ title: t('bind.clearTitle'), text: t('bind.clearText', { id: String(tr.spool) }), yes: t('bind.clear'), no: t('common.goBack') })) return;
  if (await busyOk()) bindSlot(props.link, slot, Number(tr.spool), false);
}

// A printer that hasn't reported a slot yet: a turning mark while it may still come, then why it may not.
const waiting = computed(() => !moon.value && !units.value.length && !props.lv.ext);
const late = ref(false);
let timer: ReturnType<typeof setTimeout> | undefined;
watch(waiting, on => { clearTimeout(timer); late.value = false; if (on) timer = setTimeout(() => { late.value = true; }, WAIT_SLOTS_MS); }, { immediate: true });
onBeforeUnmount(() => clearTimeout(timer));
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
    </template>
    <template v-else>
      <template v-for="(x, k) in units" :key="String(x.u.id) + ':' + k">
        <h3 class="oui-label">{{ x.label }}</h3>
        <div class="oui-cards">
          <TrayCard v-for="(tr, i) in x.u.trays" :key="i" :tray="tr" :label="lv.heads ? 'T' + (i + 1) : String(i + 1)" :tool="tool(i)" :active="!!act && act.unit === x.u.id && act.slot === i">
            <SpoolPicker v-if="canBind(tr) && isBinding(slotOf(x.u, i))" :label="t(bound(tr) ? 'bind.change' : 'bind.assign')" @pick="id => bindPick(slotOf(x.u, i), id)" @close="ui.picking = null" />
            <template v-if="canBind(tr)" #actions>
              <Button severity="secondary" size="small" :label="t(bound(tr) ? 'bind.change' : 'bind.assign')" :aria-expanded="isBinding(slotOf(x.u, i))"
                      :aria-label="t(bound(tr) ? 'bind.changeLabel' : 'bind.assignLabel', { slot: lv.heads ? 'T' + (i + 1) : x.label + ' ' + (i + 1), printer: lv.name })"
                      data-act="bind" @click="ui.picking = isBinding(slotOf(x.u, i)) ? null : { p: link, s: slotOf(x.u, i), bind: true }" />
              <Button v-if="bound(tr)" severity="secondary" text size="small" :label="t('bind.clear')" data-act="unbind" @click="unbind(slotOf(x.u, i), tr)" />
            </template>
          </TrayCard>
        </div>
      </template>
      <template v-if="lv.ext && !lv.heads">
        <h3 class="oui-label">{{ t('printer.external') }}</h3>
        <div class="oui-cards"><TrayCard :tray="lv.ext" label="E" :active="!!act && act.unit === 'ext'" /></div>
      </template>
      <div v-if="waiting" class="lu-wait oui-well" role="status" data-test="waiting">
        <OuiStatus :state="late ? 'warn' : 'connecting'">{{ late ? t('printer.waitLate') : lv.heads ? t('printer.waitingHeads') : t('printer.waitingSlots') }}</OuiStatus>
        <p v-if="late" class="oui-meta">{{ t('printer.waitLateHelp') }}</p>
      </div>
    </template>
  </div>
</template>
<style>
.lu-wait { display: grid; gap: var(--oui-s2); justify-items: start; padding: var(--oui-s3); }
.lu-wait .oui-status { white-space: normal; height: auto; min-height: 22px; padding-block: 3px; }
</style>
