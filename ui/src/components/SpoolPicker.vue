<script setup lang="ts">
import { computed, nextTick, onMounted, ref } from 'vue';
import InputText from 'primevue/inputtext';
import { m } from '../state/main';
import { t, locale } from '../core/i18n';
import { formatWeight, shown, swatch } from '../logic/spools';
import { takenIds } from '../logic/printers';

// Pick a spool for a slot: search, Enter takes the first, Down moves into the list, Escape closes (F11).
const props = defineProps<{ label: string; excludeTaken?: boolean }>();
const emit = defineEmits<{ pick: [id: number]; close: [] }>();
const q = ref('');
const input = ref<{ $el: HTMLInputElement } | null>(null);
const list = ref<HTMLElement | null>(null);
const items = computed(() => {
  const taken = props.excludeTaken ? takenIds(m.cfg) : new Set<string>();
  const needle = q.value.trim().toLowerCase();
  return m.spools.filter(s => !s.archived && !taken.has(String(s.id)) && (!needle || [s.filament?.name, s.filament?.material, s.filament?.vendor?.name, s.location,
    s.filament?.color_hex].join(' ').toLowerCase().includes(needle)))
    .sort((a, b) => (a.filament?.name || '').localeCompare(b.filament?.name || '')).slice(0, 200);
});
onMounted(() => nextTick(() => input.value?.$el.focus()));
function key(e: KeyboardEvent) {
  if (e.key === 'Escape') { e.preventDefault(); e.stopPropagation(); emit('close'); return; }
  if (e.target === input.value?.$el && (e.key === 'Enter' || e.key === 'ArrowDown') && items.value.length) {
    e.preventDefault();
    if (e.key === 'Enter') emit('pick', items.value[0].id); else (list.value?.querySelector('button') as HTMLElement | null)?.focus();
  }
  if (e.key === 'ArrowDown' || e.key === 'ArrowUp') {
    const buttons = [...(list.value?.querySelectorAll('button') ?? [])] as HTMLElement[];
    const i = buttons.indexOf(document.activeElement as HTMLElement);
    if (i < 0) return;
    e.preventDefault();
    if (e.key === 'ArrowUp' && i === 0) input.value?.$el.focus(); else buttons[Math.max(0, Math.min(buttons.length - 1, i + (e.key === 'ArrowDown' ? 1 : -1)))]?.focus();
  }
}
</script>
<template>
  <div class="pk" role="group" :aria-label="label" @keydown="key">
    <InputText ref="input" v-model="q" type="search" :placeholder="t('picker.search')" :aria-label="t('picker.search')" class="pk-q" data-test="picker-search" />
    <div ref="list" class="pk-list">
      <button v-for="s in items" :key="s.id" type="button" class="pk-item" :data-pick="s.id" @click="emit('pick', s.id)">
        <span class="pk-dot" :style="{ background: swatch(s.filament || {}) }" />
        <span class="pk-t"><span>{{ s.filament?.name || t('spool.numbered', { id: s.id }) }}</span>
          <small class="oui-meta">{{ [s.filament?.vendor?.name, '#' + s.id, s.location].filter(Boolean).join(' · ') }}</small></span>
        <span class="sp-num">{{ formatWeight(s.remaining_weight, shown(m.disp, 'exact_weight'), locale) }}</span>
      </button>
      <p v-if="!items.length" class="oui-meta pk-none">{{ q.trim() ? t('picker.noMatch') : t('picker.none') }}</p>
    </div>
    <p v-if="excludeTaken" class="oui-meta">{{ t('picker.takenHint') }}</p>
  </div>
</template>
<style scoped>
.pk { display: grid; gap: 6px; padding: 8px; border: 1px solid var(--p-primary-color); border-radius: 12px; background: var(--oui-surface); }
.pk-q { width: 100%; }
.pk-list { max-height: 260px; overflow: auto; display: grid; }
.pk-item { display: flex; align-items: center; gap: 8px; padding: 8px; border: 0; border-bottom: 1px solid var(--oui-border); background: none; color: var(--oui-text);
  font: inherit; text-align: left; cursor: pointer; }
.pk-item:hover { background: var(--oui-background); }
.pk-dot { width: 18px; height: 18px; border-radius: 50%; flex: none; border: 1px solid var(--oui-border); }
.pk-t { display: grid; flex: 1; min-width: 0; overflow-wrap: anywhere; }
.pk-none, .pk p { margin: 0; }
</style>
