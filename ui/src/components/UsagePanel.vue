<script setup lang="ts">
import { computed, reactive, ref, watch } from 'vue';
import Button from 'primevue/button';
import Select from 'primevue/select';
import Message from 'primevue/message';
import Dialog from 'primevue/dialog';
import InputNumber from 'primevue/inputnumber';
import * as bridge from '../core/bridge';
import { m, usageState, type UsagePrint } from '../state/main';
import { t, tn, fmt, locale } from '../core/i18n';
import { formatWeight, shown } from '../logic/spools';
import { rememberOpener, restoreFocus } from '../core/dialog';

// Filament usage booking: what each print used, booked to the spool in each slot (ask / auto / off).
// A row whose result is unknown is never sent again by itself: the user checks Spoolman and says what happened.
const open = ref(readOpen());
function readOpen() { try { return localStorage.getItem('spooler.bookings') === '1'; } catch { return false; } }
watch(open, v => { try { localStorage.setItem('spooler.bookings', v ? '1' : '0'); } catch { /* per viewer */ } });
const show = computed(() => m.usage.enabled && (m.liveOn || m.usage.prints.length > 0));
const list = computed(() => m.usage.prints.slice(0, 5));
const todo = computed(() => list.value.filter(p => p.state === 'pending').length);
const modes = computed(() => (['ask', 'auto', 'off'] as const).map(v => ({ value: v, label: t(`usage.mode.${v}`) })));
const busy = computed(() => !!usageState.booking || usageState.undoing);
const g = (v: number) => `${new Intl.NumberFormat(locale.value, { maximumFractionDigits: 1 }).format(Math.round(v * 10) / 10)} g`;
const hex = (c?: string) => (c ? '#' + String(c).replace(/^#/, '') : '#888');
const total = (p: UsagePrint, booked = false) => p.rows.filter(r => !booked || r.state === 'booked').reduce((a, r) => a + r.grams, 0);
function when(unix: number) {
  const d = new Date(unix * 1000), days = Math.round((+new Date(new Date().toDateString()) - +new Date(d.toDateString())) / 864e5);
  const hm = fmt.time(unix);
  return days === 0 ? t('when.today', { time: hm }) : days === 1 ? t('when.yesterday', { time: hm })
    : new Intl.DateTimeFormat(locale.value, { day: 'numeric', month: 'short' }).format(d) + ' ' + hm;
}
const result = (p: UsagePrint) => (p.result === 'finished' ? t('usage.finished') : p.result === 'unknown' ? t('usage.resultUnknown') : t('usage.stoppedAt', { pct: p.pct ?? 0 }));

// Edits to a pending print survive the refreshes that arrive while the user types.
const edits = reactive<Record<string, Record<number, { grams?: number | null; spool?: number | null }>>>({});
watch(() => m.usage.prints, ps => { for (const id of Object.keys(edits)) if (!ps.some(p => p.id === id && p.state === 'pending')) delete edits[id]; });
const edit = (p: UsagePrint, slot: number) => ((edits[p.id] ??= {})[slot] ??= {});
const gramsOf = (p: UsagePrint, r: { slot: number; grams: number }) => (edits[p.id]?.[r.slot]?.grams !== undefined ? edits[p.id][r.slot].grams : r.grams);
const spoolOptions = (material?: string) => {
  const mat = String(material || '').toLowerCase();
  return m.spools.filter(s => !s.archived).sort((x, y) => (String(x.filament?.material || '').toLowerCase() === mat ? 0 : 1) - (String(y.filament?.material || '').toLowerCase() === mat ? 0 : 1)
    || (x.filament?.name || '').localeCompare(y.filament?.name || '')).slice(0, 300)
    .map(s => ({ value: s.id, label: [s.filament?.vendor?.name, s.filament?.name || t('spool.numbered', { id: s.id }), '#' + s.id,
      formatWeight(s.remaining_weight, shown(m.disp, 'exact_weight'), locale.value)].filter(Boolean).join(' · ') }));
};
const bookable = (p: UsagePrint) => p.rows.filter(r => r.state !== 'booked').every(r => { const v = gramsOf(p, r); return typeof v === 'number' && v >= 0; });
function book(p: UsagePrint) {
  if (busy.value || !bookable(p)) return;
  const rows = p.rows.filter(r => r.state !== 'booked').map(r => {
    const e = edits[p.id]?.[r.slot] ?? {};
    return { slot: r.slot, grams: Number(gramsOf(p, r)), ...(e.spool ? { spool: String(e.spool) } : {}) };
  });
  usageState.booking = p.id; m.usageNotice = '';
  bridge.postMain({ type: 'usage_book', run: p.id, rows, origin: m.origin });
}
function resolve(p: UsagePrint, slot: number, outcome: 'applied' | 'not_applied') {
  if (busy.value) return;
  usageState.booking = p.id; m.usageNotice = '';
  bridge.postMain({ type: 'usage_resolve', run: p.id, slot, outcome });
}
function setMode(mode: string) { m.usage = { ...m.usage, mode: mode as any }; bridge.postMain({ type: 'usage_mode', mode }); }
const undoRun = ref<string | null>(null);
const undoPrint = computed(() => m.usage.prints.find(p => p.id === undoRun.value) ?? null);
function undo() { if (!undoRun.value || usageState.undoing) return; usageState.undoing = true; bridge.postMain({ type: 'usage_undo', run: undoRun.value }); }
watch(() => usageState.undoing, (now, was) => { if (was && !now) undoRun.value = null; });
const left = (id?: number | null) => m.spools.find(s => s.id === id)?.remaining_weight ?? 0;
</script>

<template>
  <section v-if="show" class="sp-card us" aria-labelledby="us-h" data-test="usage">
    <div class="sp-row"><h2 id="us-h">{{ t('usage.title') }}</h2><span class="sp-grow" />
      <label id="us-mode-l">{{ t('usage.whenDone') }}</label>
      <Select :model-value="m.usage.mode" :options="modes" option-label="label" option-value="value" aria-labelledby="us-mode-l" @update:model-value="setMode" /></div>
    <Message v-if="m.usageNotice" severity="error" role="alert">{{ m.usageNotice }}</Message>
    <button v-if="list.length" type="button" class="us-toggle" :aria-expanded="open" aria-controls="us-list" @click="open = !open">
      <span aria-hidden="true">{{ open ? '▾' : '▸' }}</span><strong>{{ t('usage.recent') }}</strong>
      <span class="oui-meta">{{ tn('usage.lastN', list.length) }}</span><span v-if="todo" class="sp-chip warn">{{ tn('usage.toBook', todo) }}</span></button>
    <div v-if="list.length && open" id="us-list" class="us-list">
      <article v-for="p in list" :key="p.id" class="us-card" :class="{ undone: p.state === 'undone' }" :data-run="p.id">
        <div class="sp-row"><strong class="us-name">{{ p.name }}</strong>
          <span class="oui-meta">{{ p.printer }} · {{ result(p) }} · {{ when(p.time) }}</span><span class="sp-grow" />
          <span v-if="p.state === 'booked'" class="sp-chip ok">{{ t('usage.booked', { g: g(total(p)) }) }}</span>
          <span v-else-if="p.state === 'undone'" class="sp-chip">{{ t('usage.undone') }}</span>
          <span v-else-if="p.state === 'unknown'" class="sp-chip warn">{{ t('usage.check') }}</span>
          <span v-else class="sp-chip warn">{{ t('usage.notBooked') }}</span>
          <Button v-if="p.state === 'booked'" severity="secondary" outlined :label="t('usage.undo')" :disabled="busy" data-usage="undo" :data-focus-key="`undo:${p.id}`" @click="rememberOpener(); undoRun = p.id" />
          <Button v-else-if="p.state !== 'unknown' && p.state !== 'undone'" :label="usageState.booking === p.id ? t('usage.booking') : t('usage.book')"
                  :loading="usageState.booking === p.id" :disabled="busy || !bookable(p)" data-usage="book" @click="book(p)" />
        </div>
        <div v-for="r in p.rows" :key="r.slot" class="us-row" :data-slot="r.slot">
          <span class="us-dot" :style="{ background: hex(r.colour) }" />
          <span class="us-slot">{{ t('usage.slot', { n: r.slot }) }}<template v-if="r.material"> · {{ r.material }}</template></span>
          <template v-if="p.state === 'pending'">
            <span class="us-spool">
              <template v-if="r.state === 'booked'">{{ r.label }} <span class="sp-chip ok">{{ t('usage.booked', { g: g(r.grams) }) }}</span></template>
              <template v-else-if="r.spool">{{ r.label }} <span v-if="r.how === 'rfid'" class="sp-chip">{{ t('usage.rfid') }}</span></template>
              <template v-else><Select :model-value="edit(p, r.slot).spool ?? null" :options="spoolOptions(r.material)" option-label="label" option-value="value" filter
                :placeholder="t('usage.choose')" :aria-label="t('usage.chooseFor', { n: r.slot })" class="us-sel" @update:model-value="v => (edit(p, r.slot).spool = v)" />
                <span class="sp-chip warn">{{ t('usage.notIdentified') }}</span></template>
            </span>
            <span v-if="r.state !== 'booked'" class="us-g"><InputNumber :model-value="gramsOf(p, r)" :min="0" :max-fraction-digits="1" :use-grouping="false" suffix=" g"
              :aria-label="t('usage.gramsFor', { n: r.slot })" :invalid="typeof gramsOf(p, r) !== 'number'"
              @input="e => (edit(p, r.slot).grams = typeof e.value === 'number' ? e.value : null)" @update:model-value="v => (edit(p, r.slot).grams = v)" /></span>
          </template>
          <template v-else><span class="us-spool">{{ r.label }}</span><span class="sp-num">{{ g(r.grams) }}</span></template>
          <p v-if="r.error" class="us-full sp-err" role="status">{{ r.error }}</p>
          <div v-if="r.state === 'unknown'" class="us-full sp-row">
            <span class="oui-meta">{{ r.op === 'undo' ? t('usage.askUndo') : t('usage.askBook') }}</span>
            <Button severity="secondary" outlined :disabled="busy" :label="r.op === 'undo' ? t('usage.wasAddedBack') : t('usage.wasBooked')" @click="resolve(p, r.slot, 'applied')" />
            <Button severity="secondary" outlined :disabled="busy" :label="r.op === 'undo' ? t('usage.wasntAddedBack') : t('usage.wasntBooked')" @click="resolve(p, r.slot, 'not_applied')" />
          </div>
        </div>
        <p v-if="p.state === 'pending' && (p.late || p.result !== 'finished')" class="oui-meta">{{ p.late ? t('usage.late') : t('usage.estimate') }}</p>
        <p v-if="p.state === 'pending' && !bookable(p)" class="sp-why">{{ t('usage.gramsNeeded') }}</p>
      </article>
    </div>
    <Dialog :visible="!!undoPrint" modal :header="t('usage.undoTitle')" :closable="!usageState.undoing" :draggable="false" :style="{ width: 'min(520px, calc(100vw - 32px))' }"
            @update:visible="v => { if (!v && !usageState.undoing) undoRun = null; }" @after-hide="restoreFocus">
      <template v-if="undoPrint">
        <p>{{ t('usage.undoText', { name: undoPrint.name, g: g(total(undoPrint, true)) }) }}</p>
        <table class="sp-table"><tbody><tr v-for="r in undoPrint.rows.filter(x => x.state === 'booked')" :key="r.slot">
          <td><span class="us-dot" :style="{ background: hex(r.colour) }" /> {{ r.label }}</td>
          <td class="r sp-num">{{ g(left(r.spool)) }} + {{ g(r.grams) }} = <strong>{{ g(left(r.spool) + r.grams) }}</strong></td></tr></tbody></table>
        <p class="oui-meta">{{ t('usage.undoKeep') }}</p>
      </template>
      <template #footer>
        <Button severity="secondary" outlined :label="t('common.goBack')" :disabled="usageState.undoing" autofocus @click="undoRun = null" />
        <Button :label="usageState.undoing ? t('usage.addingBack') : t('usage.addBack')" :loading="usageState.undoing" data-usage="unbook" @click="undo" />
      </template>
    </Dialog>
  </section>
</template>
<style scoped>
.us { display: grid; gap: 10px; }
.us h2 { margin: 0; }
.us-toggle { display: flex; align-items: center; gap: 8px; border: 0; background: none; color: var(--oui-text); font: inherit; cursor: pointer; padding: 4px 0; }
.us-list { display: grid; gap: 10px; }
.us-card { border: 1px solid var(--oui-border); border-radius: 12px; padding: 10px; display: grid; gap: 6px; }
.us-card.undone { border-style: dashed; }
.us-name { overflow-wrap: anywhere; }
.us-row { display: grid; grid-template-columns: 14px minmax(110px, auto) minmax(0, 1fr) auto; gap: 8px; align-items: center; }
.us-full { grid-column: 1 / -1; margin: 0; }
.us-dot { display: inline-block; width: 14px; height: 14px; border-radius: 50%; border: 1px solid var(--oui-border); }
.us-spool { min-width: 0; overflow-wrap: anywhere; display: flex; flex-wrap: wrap; gap: 6px; align-items: center; }
.us-sel { min-width: 200px; max-width: 100%; }
.us-g :deep(input) { width: 110px; }
@media (max-width: 600px) { .us-row { grid-template-columns: 14px minmax(0, 1fr); } .us-spool, .us-g { grid-column: 2; } }
</style>
