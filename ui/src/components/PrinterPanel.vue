<script setup lang="ts">
import { computed, nextTick, reactive, ref, watch } from 'vue';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Password from 'primevue/password';
import Select from 'primevue/select';
import Checkbox from 'primevue/checkbox';
import LiveUnits from './LiveUnits.vue';
import SpoolCard from './SpoolCard.vue';
import SpoolPicker from './SpoolPicker.vue';
import { m } from '../state/main';
import { ui, rename, addUnitTo, removeUnit, removePrinter, setSlot, saveLink } from '../state/printers';
import { ask } from '../core/dialog';
import { t, tn } from '../core/i18n';
import { LIVE_STALE, MAX_UNITS, isNet, unitLabel, type ManualPrinter, type PrinterType } from '../logic/printers';
import { words } from '../state/main';

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
const status = computed(() => {
  if (!p.value.ip || (!p.value.has_code && !p.value.auto)) return '';
  if (live.value) return (lv.value?.age ?? 0) > LIVE_STALE ? t('link.stale') : t('link.live');
  return ({ auth: net.value ? t('link.authNet') : t('link.auth'), serial: t('link.serial'),
    unreachable: net.value ? t('link.unreachableNet', { ip: p.value.ip }) : t('link.unreachable', { ip: p.value.ip }),
    waiting: t('link.waiting') } as Record<string, string>)[link.value] ?? t('link.connecting', { ip: p.value.ip });
});
const total = computed(() => p.value.units.reduce((a, u) => a + u.slots.length, 0));
const used = computed(() => p.value.units.reduce((a, u) => a + u.slots.filter(Boolean).length, 0));
const sub = computed(() => status.value || (total.value ? t('printer.assigned', { used: used.value, total: total.value }) : t('printer.addUnit')));
const hasExt = computed(() => p.value.units.some(u => u.kind === 'ext'));
const full = computed(() => p.value.units.length >= MAX_UNITS);

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
</script>

<template>
  <section class="sp-card pp" :aria-labelledby="`pp-${p.id}`">
    <div class="sp-row pp-head">
      <InputText v-if="ui.renaming === p.id" ref="nameInput" v-model="draftName" maxlength="40" :aria-label="t('printer.nameLabel')"
                 @keydown.enter.prevent="commitName(true)" @keydown.escape.prevent="commitName(false)" @blur="commitName(true)" />
      <h2 v-else :id="`pp-${p.id}`" class="pp-name">
        <Button v-if="!p.auto" text :label="p.name + ' ✎'" :aria-label="t('printer.rename', { name: p.name })" @click="ui.renaming = p.id" />
        <template v-else>{{ p.name }}</template></h2>
      <span class="oui-meta" role="status">{{ sub }}</span>
      <span class="sp-grow" />
      <template v-if="!p.auto">
        <Button v-if="editable" :label="t('link.button')" :aria-expanded="ui.linkOpen === p.id" data-act="link" @click="toggleLink" />
        <template v-if="editable && !full">
          <Button severity="secondary" outlined :label="t('printer.addTool')" data-act="add-tool" @click="addUnitTo(p.id, 'tool')" />
          <template v-if="!net">
            <Button severity="secondary" outlined :label="t('printer.addAms')" @click="addUnitTo(p.id, 'ams')" />
            <Button severity="secondary" outlined :label="t('printer.addHt')" @click="addUnitTo(p.id, 'ht')" />
          </template>
          <Button v-if="!hasExt" severity="secondary" outlined :label="t('printer.addExt')" @click="addUnitTo(p.id, 'ext')" />
        </template>
        <Button severity="danger" outlined :label="t('printer.remove')" @click="dropPrinter" />
      </template>
    </div>
    <form v-if="ui.linkOpen === p.id" class="pp-link" @submit.prevent="linkSave(false)">
      <div class="oui-field"><label :for="`type-${p.id}`">{{ t('link.type') }}</label>
        <Select v-model="form.type" :input-id="`type-${p.id}`" :options="types" option-label="label" option-value="value" data-test="link-type" /></div>
      <label class="oui-field"><span>{{ form.type === 'bambu' ? t('link.ip') : t('link.address') }}</span>
        <InputText v-model="form.ip" :placeholder="form.type === 'octoprint' ? '192.168.1.50:5000' : '192.168.1.50'" autocomplete="off" /></label>
      <label v-if="form.type === 'bambu'" class="oui-field"><span>{{ t('link.serialLabel') }}</span><InputText v-model="form.serial" :placeholder="t('link.serialPh')" autocomplete="off" /></label>
      <label v-if="form.type === 'prusalink'" class="oui-field"><span>{{ t('link.user') }}</span><InputText v-model="form.user" placeholder="maker" maxlength="64" autocomplete="off" data-test="link-user" /></label>
      <div class="oui-field"><label :for="`code-${p.id}`">{{ codeLabel }}</label>
        <Password v-model="form.code" :input-id="`code-${p.id}`" :feedback="false" toggle-mask autocomplete="off" :placeholder="keepsCode ? t('link.codeSaved') : codeHint" /></div>
      <span v-if="form.type !== 'bambu'" class="sp-row pp-full"><Checkbox v-model="form.slice_fill" binary :input-id="`fill-${p.id}`" />
        <label :for="`fill-${p.id}`">{{ t('link.sliceFill') }}</label></span>
      <div class="sp-row pp-linkbar"><Button type="submit" :label="t('common.save')" />
        <Button severity="secondary" outlined :label="t('common.cancel')" @click="ui.linkOpen = ''" />
        <Button v-if="p.ip" severity="danger" text :label="t('link.remove')" @click="linkSave(true)" /></div>
      <p class="oui-meta pp-full">{{ linkHelp }}</p>
      <p v-if="form.type !== 'bambu'" class="oui-meta pp-full">{{ t('printer.netNote') }}</p>
    </form>
    <LiveUnits v-if="live && lv && !net" :lv="lv" :link="p.id" />
    <template v-else-if="!p.auto">
      <template v-for="(u, ui_) in p.units" :key="ui_">
        <div class="sp-row pp-unit"><strong>{{ unitLabel(p, u, words) }}</strong><span class="sp-grow" />
          <Button severity="secondary" text :label="t('printer.removeUnit', { unit: unitLabel(p, u, words) })" @click="dropUnit(ui_)" /></div>
        <div class="pp-grid">
          <div v-for="(id, si) in u.slots" :key="si" class="pp-cell">
            <div class="sp-row"><span class="pp-n">{{ u.kind === 'ext' ? 'E' : u.kind === 'tool' ? unitLabel(p, u, words) : si + 1 }}</span><span class="sp-grow" />
              <Button v-if="id" text size="small" :aria-label="t('printer.clearSlot', { n: si + 1 })" :title="t('printer.clearSlot', { n: si + 1 })"
                      :data-focus-key="`clear:${p.id}:${ui_}:${si}`" @click="setSlot(p.id, ui_, si, null)">✕</Button></div>
            <SpoolCard v-if="id && byId.get(String(id))" :spool="byId.get(String(id))!" />
            <div v-else-if="id" class="pp-missing"><strong>{{ t('printer.notFound') }}</strong><span class="oui-meta">{{ t('printer.notFoundHelp') }}</span></div>
            <Button v-else severity="secondary" outlined class="pp-assign" :aria-expanded="isPicking(ui_, si)" :data-focus-key="`assign:${p.id}:${ui_}:${si}`"
                    :aria-label="t('printer.assignLabel', { slot: u.kind === 'ext' ? t('printer.theExternal') : t('printer.slotN', { n: si + 1 }), printer: p.name })"
                    data-act="assign" @click="ui.picking = isPicking(ui_, si) ? null : { p: p.id, u: ui_, s: si }">{{ t('printer.assign') }}</Button>
            <SpoolPicker v-if="isPicking(ui_, si)" exclude-taken :label="t('printer.assign')" @pick="id2 => pick(ui_, si, id2)" @close="closePicker(ui_, si)" />
          </div>
        </div>
      </template>
    </template>
    <p class="oui-meta pp-note">{{ p.auto ? t('printer.autoNote') + ' ' + t('printer.klipperNote') : net ? t('printer.netNote') : live ? '' : t('printer.manualNote') }}</p>
  </section>
</template>
<style scoped>
.pp { display: grid; gap: 10px; }
.pp-head h2, .pp-name { margin: 0; font-size: 16px; }
.pp-link { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 12px; padding: 12px; border: 1px solid var(--oui-border); border-radius: 12px; }
.pp-linkbar, .pp-full { grid-column: 1 / -1; margin: 0; }
.pp-unit { margin-top: 4px; }
.pp-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(220px, 1fr)); gap: 8px; }
.pp-cell { display: grid; gap: 4px; align-content: start; }
.pp-n { color: var(--oui-muted); font-size: 12px; font-weight: 600; }
.pp-assign { width: 100%; min-height: 64px; border-style: dashed; justify-content: center; }
.pp-missing { display: grid; padding: 10px; border: 1px dashed var(--oui-border); border-radius: 12px; }
.pp-note { margin: 0; }
</style>
