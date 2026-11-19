<script setup lang="ts">
import { computed, nextTick, reactive, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Password from 'primevue/password';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import MultiSelect from 'primevue/multiselect';
import { OuiHint, OuiIcon, OuiPanel, OuiStatus, type OuiState } from '../../shared/src/components';
import { edit, link as linkIcon, plus, printer as printerIcon, trash, x } from '../../shared/src/icons';
import LiveUnits from './LiveUnits.vue';
import SpoolSlot from './SpoolSlot.vue';
import SpoolPicker from './SpoolPicker.vue';
import { m, words } from '../state/main';
import { showSpool } from '../state/menu';
import { ui, rename, addUnitTo, removeUnit, removePrinter, setSlot, saveLink, setGates, setSliceFill, setPresets } from '../state/printers';
import { ask } from '../core/dialog';
import { t } from '../core/i18n';
import { LIVE_STALE, MAX_GATES, MAX_UNITS, fillable, isKlipperManual, isNet, unitLabel, type ManualPrinter, type ManualUnit, type PrinterType } from '../logic/printers';

// A printer Spooler knows: found in OrcaSlicer's printer presets (auto) or added by hand with its AMS units and
// slots. With Live Link, a Bambu printer itself is read (read-only); otherwise the slots are the user's assignment.
// PrusaLink and OctoPrint printers report progress but not their spools, so their toolheads stay editable while linked.
const props = defineProps<{ p: ManualPrinter }>();
const p = computed(() => props.p);
const lv = computed(() => m.live.printers.find(x => x.link === p.value.id) ?? null);
const link = computed(() => m.live.links?.[p.value.id] ?? '');
const live = computed(() => !!lv.value && link.value === 'live');
const net = computed(() => isNet(p.value));
// A Klipper printer that reports neither its toolheads' spools nor MMU gates: the spools are set here, by hand.
const klipper = computed(() => isKlipperManual(p.value));
const handSet = computed(() => klipper.value && p.value.units.length > 0);
const tools = computed(() => p.value.units.filter(u => u.kind === 'tool').length);
const gates = computed(() => p.value.units.find(u => u.kind === 'gate')?.slots.length ?? 0);
const gateOptions = computed(() => Array.from({ length: MAX_GATES + 1 }, (_, n) => ({ value: n, label: n ? String(n) : t('printer.noGates') })));
// With two or more printers a slice can fill, each says which OrcaSlicer printer presets are its own.
const askPresets = computed(() => (net.value || klipper.value) && fillable(m.cfg).length > 1 && fillable(m.cfg).some(x => x.id === p.value.id));
// OrcaSlicer's presets now, plus this printer's own choices so one renamed or deleted since can still be removed.
const presetOptions = computed(() => [...new Set([...m.printerPresets, ...myPresets.value])]);
const myPresets = computed(() => Object.entries(m.sliceMap).filter(([, v]) => v === p.value.id).map(([k]) => k));
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
// One line that is true for this printer: who books its prints, or that its slots are set by hand. The longer
// explanations are said once, under "How booking works" at the top of the tab.
const chip = computed(() => {
  if (live.value && lv.value?.bind === 'T') return t('printer.chipU1');
  if (live.value && lv.value?.bind === 'S') return t('printer.chipKobra');
  if (live.value && lv.value?.hh && lv.value.units.length) return t('printer.chipHh');
  if (net.value) return t('printer.chipNet');
  if (!p.value.auto && !live.value) return t('printer.chipManual');
  return '';
});

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
// The slot cards in rows: one per unit; a Klipper printer's toolheads share one row, like a live printer's.
interface Cell { u: number; s: number; unit: ManualUnit; id: string | number | null }
const rows = computed(() => {
  const out: { key: string; label: string; remove: number; cells: Cell[] }[] = [];
  p.value.units.forEach((unit, u) => {
    const cells = unit.slots.map((id, s) => ({ u, s, unit, id }));
    const last = out[out.length - 1];
    if (p.value.auto && unit.kind === 'tool' && last?.key === 'tools') last.cells.push(...cells);
    else out.push({ key: p.value.auto && unit.kind === 'tool' ? 'tools' : String(u), label: p.value.auto && unit.kind === 'tool' ? t(tools.value === 1 ? 'printer.extruder' : 'printer.toolheads') : unitLabel(p.value, unit, words.value),
      remove: p.value.auto ? -1 : u, cells });
  });
  return out;
});
const slotName = (c: Cell) => (c.unit.kind === 'ext' ? t('printer.theExternal') : c.unit.kind === 'gate' ? t('printer.gateN', { n: c.s + 1 }) : c.unit.kind === 'tool' ? slotLabel(c.unit, c.s) : t('printer.slotN', { n: c.s + 1 }));
const slotLabel = (u: ManualUnit, si: number) => (u.kind === 'gate' ? String(si + 1) : u.kind === 'ext' ? 'E' : u.kind === 'tool' ? (p.value.auto && tools.value === 1 ? 'E' : unitLabel(p.value, u, words.value)) : String(si + 1));
const toolOf = (u: ManualUnit) => { const n = u.kind === 'tool' ? p.value.units.filter(x => x.kind === 'tool').indexOf(u) + 1 : 0; return n >= 1 && n <= 4 ? n as 1 | 2 | 3 | 4 : undefined; };
</script>

<template>
  <OuiPanel class="pp" :icon="printerIcon" :aria-labelledby="`pp-${p.id}`">
    <template #title>
      <InputText v-if="ui.renaming === p.id" ref="nameInput" v-model="draftName" size="small" maxlength="40" :aria-label="t('printer.nameLabel')"
                 @keydown.enter.prevent="commitName(true)" @keydown.escape.prevent="commitName(false)" @blur="commitName(true)" />
      <span v-else :id="`pp-${p.id}`" class="pp-name">{{ p.name }}</span>
    </template>
    <template #meta><OuiStatus v-if="status" :state="status.state" role="status" :title="status.text">{{ status.text }}</OuiStatus><span v-else role="status">{{ sub }}</span>
      <span v-if="chip" class="oui-chip pp-chip" data-test="printer-chip" :title="chip">{{ chip }}</span></template>
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
          <OuiHint :label="t('link.button')"><span class="sp-hint-p">{{ linkHelp }}</span><span v-if="form.type !== 'bambu'" class="sp-hint-p">{{ t('printer.netNote') }}</span></OuiHint>
          <span class="oui-spacer" />
          <Button v-if="p.ip" severity="danger" outlined :label="t('link.remove')" @click="linkSave(true)" /></div>
      </form>

      <LiveUnits v-if="live && lv && !net && !handSet" :lv="lv" :link="p.id" />
      <template v-else-if="!p.auto || handSet">
        <template v-for="r in rows" :key="r.key">
          <div class="oui-row pp-unit"><h3 class="oui-label">{{ r.label }}</h3><span class="oui-spacer" />
            <Button v-if="r.remove >= 0" severity="secondary" text size="small" :label="t('printer.removeUnit', { unit: r.label })" @click="dropUnit(r.remove)" /></div>
          <div class="oui-cards">
            <SpoolSlot v-for="c in r.cells" :key="c.u + ':' + c.s" :label="slotLabel(c.unit, c.s)" :tool="toolOf(c.unit)" :spool="c.id ? byId.get(String(c.id)) : null" :missing="!!c.id && !byId.get(String(c.id))">
              <SpoolPicker v-if="isPicking(c.u, c.s)" exclude-taken :label="t('printer.assign')" @pick="id2 => pick(c.u, c.s, id2)" @close="closePicker(c.u, c.s)" />
              <template #actions>
                <template v-if="c.id">
                  <Button severity="secondary" size="small" :label="t('bind.change')" :aria-expanded="isPicking(c.u, c.s)" :data-focus-key="`assign:${p.id}:${c.u}:${c.s}`"
                          :aria-label="t('bind.changeLabel', { slot: slotName(c), printer: p.name })" data-act="change"
                          @click="ui.picking = isPicking(c.u, c.s) ? null : { p: p.id, u: c.u, s: c.s }" />
                  <Button v-if="byId.get(String(c.id))" severity="secondary" text size="small" :label="t('printer.openSpool')" @click="showSpool(Number(c.id))" />
                  <Button severity="secondary" text size="small" :aria-label="t('printer.clearSlot', { n: c.s + 1 })" :title="t('printer.clearSlot', { n: c.s + 1 })"
                          :data-focus-key="`clear:${p.id}:${c.u}:${c.s}`" @click="setSlot(p.id, c.u, c.s, null)"><template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
                </template>
                <Button v-else severity="secondary" size="small" :label="t('printer.assign')" :aria-expanded="isPicking(c.u, c.s)" :data-focus-key="`assign:${p.id}:${c.u}:${c.s}`"
                        :aria-label="t('printer.assignLabel', { slot: slotName(c), printer: p.name })"
                        data-act="assign" @click="ui.picking = isPicking(c.u, c.s) ? null : { p: p.id, u: c.u, s: c.s }"><template #icon><OuiIcon :icon="plus" :size="14" /></template></Button>
              </template>
            </SpoolSlot>
          </div>
        </template>
      </template>
      <div v-if="klipper" class="pp-klipper oui-well" data-test="klipper-slots">
        <div v-if="tools < 2" class="oui-field"><label :for="`gates-${p.id}`">{{ t('printer.gateCount') }}</label>
          <Select :model-value="gates" :input-id="`gates-${p.id}`" :options="gateOptions" option-label="label" option-value="value" data-test="gate-count"
                  @update:model-value="n => setGates(p.id, n)" /></div>
        <span v-if="handSet" class="oui-row"><Checkbox :model-value="p.slice_fill !== false" binary :input-id="`kfill-${p.id}`" data-test="klipper-fill" @update:model-value="v => setSliceFill(p.id, v)" />
          <label :for="`kfill-${p.id}`">{{ t('printer.sliceFillSlots') }}</label></span>
        <OuiHint class="pp-khint" :label="t('printer.gateCount')" :text="tools >= 2 ? t('printer.klipperToolsNote') : t('printer.gatesNote')" />
      </div>
      <div v-if="askPresets" class="oui-field pp-presets" data-test="presets">
        <span class="oui-row"><label :for="`presets-${p.id}`">{{ t('printer.presets') }}</label><OuiHint :label="t('printer.presets')" :text="t('printer.presetsHelp')" /></span>
        <MultiSelect :model-value="myPresets" :input-id="`presets-${p.id}`" :options="presetOptions" :placeholder="t('printer.presetsAuto')" filter display="chip" :max-selected-labels="3"
                     :aria-label="t('printer.presetsLabel', { printer: p.name })" @update:model-value="v => setPresets(p.id, v)" />
      </div>
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
.pp-chip { margin-inline-start: var(--oui-s1); max-width: 100%; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.pp-klipper { display: flex; flex-wrap: wrap; align-items: flex-end; gap: var(--oui-s3); padding: var(--oui-s3); }
.pp-klipper > .oui-field { flex: 0 1 220px; }
.pp-klipper > .oui-row, .pp-khint { align-self: center; }
.pp-presets { max-width: 60ch; }
.pp-presets .p-multiselect { width: 100%; }
</style>
