<script setup lang="ts">
import { computed, nextTick, onMounted, ref, watch } from 'vue';
import InputText from 'primevue/inputtext';
import { OuiHint, OuiSpool } from '@orca-plugins/ui-foundation/src/components';
import { m } from '../state/main';
import { t, locale } from '../core/i18n';
import { formatWeight, shown, spoolDirection, spoolFraction, spoolMatches, spoolPaint } from '../logic/spools';
import { takenIds } from '../logic/printers';

// Pick a spool for a slot: search, Enter takes the first, Down moves into the list, Escape closes (F11).
const props = defineProps<{ label: string; excludeTaken?: boolean }>();
const emit = defineEmits<{ pick: [id: number]; close: [] }>();
const q = ref('');
const input = ref<{ $el: HTMLInputElement } | null>(null);
const list = ref<HTMLElement | null>(null);
// Sorted once per spool list, not on every keystroke (thousands of spools); typing only filters it.
const byName = new Intl.Collator().compare;
const pickable = computed(() => {
  const taken = props.excludeTaken ? takenIds(m.cfg) : new Set<string>();
  return m.spools.filter(s => !s.archived && !taken.has(String(s.id))).sort((a, b) => byName(a.filament?.name || '', b.filament?.name || ''));
});
const items = computed(() => {
  const needle = q.value.trim();
  return needle ? pickable.value.filter(s => spoolMatches(s, needle)) : pickable.value;
});
// Only the rows in view (and a few around them) are drawn, each ROW px tall. The picker sits in a slot card inside nested
// grids, and the browser lays a card's content out several times per change: 200 drawn rows held the page for most of a
// second on every keystroke.
const ROW = 44, AROUND = 3;
const top = ref(0);
const first = computed(() => Math.max(0, Math.floor(top.value / ROW) - AROUND));
const drawn = computed(() => items.value.slice(first.value, first.value + Math.ceil(240 / ROW) + 2 * AROUND));
const pad = computed(() => ({ paddingTop: `${first.value * ROW}px`, paddingBottom: `${(items.value.length - first.value - drawn.value.length) * ROW}px` }));
watch(q, () => { top.value = 0; if (list.value) list.value.scrollTop = 0; });
onMounted(() => nextTick(() => input.value?.$el.focus()));
/** Focus the row of items[i], scrolling it into the list's view first so it is drawn. */
async function focusRow(i: number) {
  const el = list.value;
  if (!el) return;
  if (i * ROW < el.scrollTop) el.scrollTop = i * ROW;
  else if ((i + 1) * ROW > el.scrollTop + el.clientHeight) el.scrollTop = (i + 1) * ROW - el.clientHeight;
  top.value = el.scrollTop;
  await nextTick();
  el.querySelector<HTMLElement>(`[data-pick="${items.value[i].id}"]`)?.focus();
}
function key(e: KeyboardEvent) {
  if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); emit('close'); return; }
  if (e.target === input.value?.$el && (e.key === 'Enter' || e.key === 'ArrowDown') && items.value.length) {
    e.preventDefault();
    if (e.key === 'Enter') emit('pick', items.value[0].id); else void focusRow(0);
  }
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    const id = (document.activeElement as HTMLElement | null)?.closest('.pk-list') ? (document.activeElement as HTMLElement).dataset.pick : undefined;
    const i = id === undefined ? -1 : items.value.findIndex(s => String(s.id) === id);
    if (i < 0) return;
    e.preventDefault();
    if (e.key === 'ArrowUp' && i === 0) input.value?.$el.focus(); else void focusRow(Math.max(0, Math.min(items.value.length - 1, i + (e.key === 'ArrowDown' ? 1 : -1))));
  }
}
</script>
<template>
  <div class="pk oui-well" role="group" :aria-label="label" @keydown="key">
    <div class="pk-top"><InputText ref="input" v-model="q" type="search" size="small" :placeholder="t('picker.search')" :aria-label="t('picker.search')" class="pk-q" data-test="picker-search" />
      <OuiHint v-if="excludeTaken" :label="label" :text="t('picker.takenHint')" /></div>
    <div ref="list" class="pk-list" @scroll="top = list?.scrollTop ?? 0"><div :style="pad">
      <button v-for="s in drawn" :key="s.id" type="button" class="pk-item" :data-pick="s.id" @click="emit('pick', s.id)">
        <OuiSpool v-bind="spoolPaint(s.filament || {})" :direction="spoolDirection(s.filament || {})" :fraction="spoolFraction(s)" :size="32" />
        <span class="pk-t"><span class="oui-truncate">{{ s.filament?.name || t('spool.numbered', { id: s.id }) }}</span>
          <small class="oui-meta oui-truncate">{{ [s.filament?.vendor?.name, s.filament?.material, '#' + s.id, s.location].filter(Boolean).join(' · ') }}</small></span>
        <span class="oui-num">{{ formatWeight(s.remaining_weight, shown(m.disp, 'exact_weight'), locale) }}</span>
      </button>
      </div>
      <p v-if="!items.length" class="oui-meta pk-none">{{ q.trim() ? t('picker.noMatch') : t('picker.none') }}</p>
    </div>
  </div>
</template>
<style>
.pk { display: grid; gap: var(--oui-s2); padding: var(--oui-s2); box-shadow: inset 0 0 0 1px var(--oui-primary-mark); min-width: 0; }
.pk-top { display: flex; align-items: center; gap: var(--oui-s1); min-width: 0; }
.pk-q { flex: 1; min-width: 0; }
.pk-list { max-height: 240px; overflow: auto; }
.pk-list > div { display: grid; }
.orca-ui .pk-item { display: flex; align-items: center; gap: var(--oui-s2); padding: 6px var(--oui-s2); border: 0; border-radius: var(--oui-radius-sm); background: none; color: var(--oui-text);
  font: inherit; text-align: start; cursor: pointer; min-width: 0; height: 44px; box-sizing: border-box; }
.orca-ui .pk-item:hover, .orca-ui .pk-item:focus-visible { background: var(--oui-control); }
.pk-t { display: grid; flex: 1; min-width: 0; }
.pk-none { padding: var(--oui-s2); }
</style>
