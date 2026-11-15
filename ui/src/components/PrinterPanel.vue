<script setup lang="ts">
import { computed, nextTick, reactive, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Password from 'primevue/password';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import { OuiIcon, OuiPanel, OuiStatus, type OuiState } from '../../shared/src/components';
import { edit, link as linkIcon, plus, printer as printerIcon, trash, x } from '../../shared/src/icons';
import LiveUnits from './LiveUnits.vue';
import SpoolSlot from './SpoolSlot.vue';
import SpoolPicker from './SpoolPicker.vue';
import { m, words } from '../state/main';
import { showSpool } from '../state/menu';
import { ui, rename, addUnitTo, removeUnit, removePrinter, setSlot, saveLink } from '../state/printers';
import { ask } from '../core/dialog';
import { t } from '../core/i18n';
import { LIVE_STALE, MAX_UNITS, isNet, unitLabel, type ManualPrinter, type ManualUnit, type PrinterType } from '../logic/printers';

// A printer Spooler knows: found in OrcaSlicer's printer presets (auto) or added by hand with its AMS units and
// slots. With Live Link, a Bambu printer itself is read (read-only); otherwise the slots are the user's assignment.
// PrusaLink and OctoPrint printers report progress but not their spools, so their toolheads stay editable while linked.
const props = defineProps<{ p: ManualPrinter }>();
const p = computed(() => props.p);
const lv = computed(() => m.live.printers.find(x => x.link === p.value.id) ?? null);
const link = computed(() => m.live.links?.[p.value.id] ?? '');
const live = computed(() => !!lv.value && link.value === 'live');
const net = computed(() => isNet(p.value));
const editable = computed(() => !live.value || net.value);
const byId = computed(() => new Map(m.spools.filter(s => !s.archived).map(s => [String(s.id), s])));
// The link's state, as a chip; a printer with no link says how many of its slots are assigned instead.
const status = computed<{ state: OuiState; text: string } | null>(() => {
  if (!p.value.ip || (!p.value.has_code && !p.value.auto)) return null;
  if (live.value) return (lv.value?.age ?? 0) > LIVE_STALE ? { state: 'stale', text: t('link.stale') } : { state: 'ok', text: t('link.live') };
  const failed: Record<string, string> = { auth: net.value ? t('link.authNet') : t('link.auth'), serial: t('link.serial'),
    unreachable: net.value ? t('link.unreachableNet', { ip: p.value.ip }) : t('link.unreachable', { ip: p.value.ip }) };
  if (failed[link.value]) return { state: link.value === 'unreachable' ? 'offline' : 'error', text: failed[link.value] };
  return { state: 'connecting', text: link.value === 'waiting' ? t('link.waiting') : t('link.connecting', { ip: p.value.ip }) };
});
const total = computed(() => p.value.units.reduce((a, u) => a + u.slots.length, 0));
const used = computed(() => p.value.units.reduce((a, u) => a + u.slots.filter(Boolean).length, 0));
const sub = computed(() => (total.value ? t('printer.assigned', { used: used.value, total: total.value }) : p.value.auto ? '' : t('printer.addUnit')));
const hasExt = computed(() => p.value.units.some(u => u.kind === 'ext'));
const full = computed(() => p.value.units.length >= MAX_UNITS);
const noteText = computed(() => (p.value.auto ? t('printer.autoNote') + ' ' + t('printer.klipperNote') : net.value ? t('printer.netNote') : live.value ? '' : t('printer.manualNote')));

const nameInput = ref<{ $el: HTMLInputElement } | null>(null);
const draftName = ref(p.value.name);
watch(() => ui.renaming, async id => { if (id === p.value.id) { draftName.value = p.value.name; await nextTick(); nameInput.value?.$el.focus(); nameInput.value?.$el.select(); } }, { immediate: true });
function commitName(keep: boolean) { if (ui.renaming !== p.value.id) return; ui.renaming = ''; if (keep) rename(p.value.id, draftName.value); }

const form = reactive({ type: 'bambu' as PrinterType, ip: '', serial: '', user: '', code: '', slice_fill: true });
watch(() => ui.linkOpen, id => {
  if (id === p.value.id) Object.assign(form, { type: p.value.type || 'bambu', ip: p.value.ip || '', serial: p.value.serial || '', user: p.value.user || '',
    code: '', slice_fill: p.value.slice_fill !== false });
});
const types = computed(() => [{ value: 'bambu', label: t('link.typeBambu') }, { value: 'prusalink', label: 'PrusaLink' }, { value: 'octoprint', label: 'OctoPrint' }]);
const codeLabel = computed(() => t(form.type === 'prusalink' ? 'link.password' : form.type === 'octoprint' ? 'link.apiKey' : 'link.code'));
const codeHint = computed(() => (form.type === 'bambu' ? t('link.codePh') : form.type === 'prusalink' ? t('link.passwordPh') : t('link.apiKeyPh')));
const keepsCode = computed(() => p.value.has_code && (p.value.type || 'bambu') === form.type);
const linkHelp = computed(() => t(form.type === 'prusalink' ? 'link.helpPrusa' : form.type === 'octoprint' ? 'link.helpOcto' : 'link.help'));
function toggleLink() { ui.linkOpen = ui.linkOpen === p.value.id ? '' : p.value.id; }
function linkSave(remove: boolean) { saveLink(p.value.id, { ...form }, remove); ui.linkOpen = ''; }

async function dropUnit(i: number) {
  const label = unitLabel(p.value, p.value.units[i], words.value);
  if (!await ask({ title: t('printer.removeUnit', { unit: label }), text: t('confirm.removeUnit', { unit: label, printer: p.value.name }),
    yes: t('printer.removeUnit', { unit: label }), no: t('common.goBack'), danger: true })) return;
  ui.picking = null; removeUnit(p.value.id, i);
}
async function dropPrinter() {
  if (!await ask({ title: t('printer.remove'), text: t('confirm.removePrinter', { printer: p.value.name }), yes: t('printer.remove'), no: t('common.goBack'), danger: true })) return;
  ui.picking = null; removePrinter(p.value.id);
}
const isPicking = (u: number, s: number) => !!ui.picking && !ui.picking.moon && ui.picking.p === p.value.id && ui.picking.u === u && ui.picking.s === s;
function pick(u: number, s: number, id: number) {
  ui.picking = null; setSlot(p.value.id, u, s, String(id));
  void nextTick(() => (document.querySelector(`[data-focus-key="clear:${p.value.id}:${u}:${s}"]`) as HTMLElement | null)?.focus());
}
function closePicker(u: number, s: number) {
  ui.picking = null;
  void nextTick(() => (document.querySelector(`[data-focus-key="assign:${p.value.id}:${u}:${s}"]`) as HTMLElement | null)?.focus());
}
const slotLabel = (u: ManualUnit, si: number) => (u.kind === 'ext' ? 'E' : u.kind === 'tool' ? unitLabel(p.value, u, words.value) : String(si + 1));
const toolOf = (u: ManualUnit) => { const n = u.kind === 'tool' ? p.value.units.filter(x => x.kind === 'tool').indexOf(u) + 1 : 0; return n >= 1 && n <= 4 ? n as 1 | 2 | 3 | 4 : undefined; };
</script>

<template>
  <OuiPanel class="pp" :icon="printerIcon" tone="magenta" :aria-labelledby="`pp-${p.id}`">
    <template #title>
      <InputText v-if="ui.renaming === p.id" ref="nameInput" v-model="draftName" size="small" maxlength="40" :aria-label="t('printer.nameLabel')"
                 @keydown.enter.prevent="commitName(true)" @keydown.escape.prevent="commitName(false)" @blur="commitName(true)" />
      <span v-else :id="`pp-${p.id}`" class="pp-name">{{ p.name }}</span>
    </template>
    <template #meta><OuiStatus v-if="status" :state="status.state" role="status" :title="status.text">{{ status.text }}</OuiStatus><span v-else role="status">{{ sub }}</span></template>
    <template v-if="!p.auto" #actions>
      <Button v-if="ui.renaming !== p.id" severity="secondary" text size="small" :aria-label="t('printer.rename', { name: p.name })" :title="t('printer.rename', { name: p.name })" data-act="rename" @click="ui.renaming = p.id">
        <template #icon><OuiIcon :icon="edit" :size="14" /></template></Button>
      <Button v-if="editable" severity="secondary" size="small" :label="t('link.button')" :aria-expanded="ui.linkOpen === p.id" data-act="link" @click="toggleLink"><template #icon><OuiIcon :icon="linkIcon" :size="14" /></template></Button>
    </template>

    <div class="oui-stack">
      <form v-if="ui.linkOpen === p.id" class="pp-link oui-well" @submit.prevent="linkSave(false)">
        <div class="oui-field"><label :for="`type-${p.id}`">{{ t('link.type') }}</label>
          <Select v-model="form.type" :input-id="`type-${p.id}`" :options="types" option-label="label" option-value="value" data-test="link-type" /></div>
        <label class="oui-field"><span class="pp-lab">{{ form.type === 'bambu' ? t('link.ip') : t('link.address') }}</span>
          <InputText v-model="form.ip" :placeholder="form.type === 'octoprint' ? '192.168.1.50:5000' : '192.168.1.50'" autocomplete="off" /></label>
        <label v-if="form.type === 'bambu'" class="oui-field"><span class="pp-lab">{{ t('link.serialLabel') }}</span><InputText v-model="form.serial" :placeholder="t('link.serialPh')" autocomplete="off" /></label>
        <label v-if="form.type === 'prusalink'" class="oui-field"><span class="pp-lab">{{ t('link.user') }}</span><InputText v-model="form.user" placeholder="maker" maxlength="64" autocomplete="off" data-test="link-user" /></label>
        <div class="oui-field"><label :for="`code-${p.id}`">{{ codeLabel }}</label>
          <Password v-model="form.code" :input-id="`code-${p.id}`" :feedback="false" toggle-mask autocomplete="off" :placeholder="keepsCode ? t('link.codeSaved') : codeHint" fluid /></div>
        <span v-if="form.type !== 'bambu'" class="oui-row pp-full"><Checkbox v-model="form.slice_fill" binary :input-id="`fill-${p.id}`" />
          <label :for="`fill-${p.id}`">{{ t('link.sliceFill') }}</label></span>
        <div class="oui-row pp-full"><Button type="submit" :label="t('common.save')" />
          <Button severity="secondary" text :label="t('common.cancel')" @click="ui.linkOpen = ''" />
          <span class="oui-spacer" />
          <Button v-if="p.ip" severity="danger" text :label="t('link.remove')" @click="linkSave(true)" /></div>
        <p class="oui-meta pp-full">{{ linkHelp }}</p>
        <p v-if="form.type !== 'bambu'" class="oui-meta pp-full">{{ t('printer.netNote') }}</p>
      </form>

      <LiveUnits v-if="live && lv && !net" :lv="lv" :link="p.id" />
      <template v-else-if="!p.auto">
        <template v-for="(u, ui_) in p.units" :key="ui_">
          <div class="oui-row pp-unit"><h3 class="oui-label">{{ unitLabel(p, u, words) }}</h3><span class="oui-spacer" />
            <Button severity="secondary" text size="small" :label="t('printer.removeUnit', { unit: unitLabel(p, u, words) })" @click="dropUnit(ui_)" /></div>
          <div class="oui-cards">
            <SpoolSlot v-for="(id, si) in u.slots" :key="si" :label="slotLabel(u, si)" :tool="toolOf(u)" :spool="id ? byId.get(String(id)) : null" :missing="!!id && !byId.get(String(id))">
              <SpoolPicker v-if="isPicking(ui_, si)" exclude-taken :label="t('printer.assign')" @pick="id2 => pick(ui_, si, id2)" @close="closePicker(ui_, si)" />
              <template #actions>
                <template v-if="id">
                  <Button v-if="byId.get(String(id))" severity="secondary" text size="small" :label="t('printer.openSpool')" @click="showSpool(Number(id))" />
                  <Button severity="secondary" text size="small" :aria-label="t('printer.clearSlot', { n: si + 1 })" :title="t('printer.clearSlot', { n: si + 1 })"
                          :data-focus-key="`clear:${p.id}:${ui_}:${si}`" @click="setSlot(p.id, ui_, si, null)"><template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
                </template>
                <Button v-else severity="secondary" size="small" :label="t('printer.assign')" :aria-expanded="isPicking(ui_, si)" :data-focus-key="`assign:${p.id}:${ui_}:${si}`"
                        :aria-label="t('printer.assignLabel', { slot: u.kind === 'ext' ? t('printer.theExternal') : t('printer.slotN', { n: si + 1 }), printer: p.name })"
                        data-act="assign" @click="ui.picking = isPicking(ui_, si) ? null : { p: p.id, u: ui_, s: si }"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
              </template>
            </SpoolSlot>
          </div>
        </template>
      </template>
      <p v-if="noteText" class="oui-meta pp-note">{{ noteText }}</p>
    </div>

    <template v-if="!p.auto" #footer>
      <template v-if="editable && !full">
        <Button severity="secondary" text size="small" :label="t('printer.addTool')" data-act="add-tool" @click="addUnitTo(p.id, 'tool')" />
        <template v-if="!net">
          <Button severity="secondary" text size="small" :label="t('printer.addAms')" @click="addUnitTo(p.id, 'ams')" />
          <Button severity="secondary" text size="small" :label="t('printer.addHt')" @click="addUnitTo(p.id, 'ht')" />
        </template>
        <Button v-if="!hasExt" severity="secondary" text size="small" :label="t('printer.addExt')" @click="addUnitTo(p.id, 'ext')" />
      </template>
      <span class="oui-spacer" />
      <Button severity="danger" outlined size="small" :label="t('printer.remove')" @click="dropPrinter"><template #icon><OuiIcon :icon="trash" :size="14" /></template></Button>
    </template>
  </OuiPanel>
</template>
<style>
.pp-name { overflow-wrap: anywhere; }
.pp-link { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: var(--oui-s3); padding: var(--oui-s3); }
.pp-lab { font-size: var(--oui-text-sm); font-weight: 600; color: var(--oui-muted); }
.pp-full { grid-column: 1 / -1; }
.pp-note { max-width: 96ch; }
</style>
