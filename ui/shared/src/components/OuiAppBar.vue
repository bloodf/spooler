<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';

/*
 * The top bar of every plugin page: identity (the plugin's own mark and name), the page's one connection or
 * source state, the task tabs, then page-wide actions. The view for the selected tab is rendered by the app: give it
 * role="tabpanel" and aria-labelledby="oui-tab-<value>".
 */
export interface OuiTab { value: string; label: string; icon?: OuiIconData; count?: number | string;
  /** Shows a dot on the tab; the text is its accessible name and tooltip ("needs attention"). */ attention?: string;
  /** Extra attributes for the tab button (test hooks). The tab's own role, id, data-tab and aria attributes win. */ attrs?: Record<string, string> }
const props = defineProps<{ name: string; tabs?: OuiTab[]; modelValue?: string; tabsLabel?: string }>();
const emit = defineEmits<{ 'update:modelValue': [value: string] }>();

function onKey(event: KeyboardEvent) {
  const tabs = props.tabs ?? [];
  const at = tabs.findIndex(t => t.value === props.modelValue);
  const next = { ArrowRight: at + 1, ArrowLeft: at - 1, Home: 0, End: tabs.length - 1 }[event.key];
  if (next == null || !tabs.length) return;
  event.preventDefault();
  const tab = tabs[(next + tabs.length) % tabs.length];
  emit('update:modelValue', tab.value);
  const list = event.currentTarget as HTMLElement;
  requestAnimationFrame(() => list.querySelector<HTMLElement>(`[data-tab="${CSS.escape(tab.value)}"]`)?.focus());
}
</script>
<template>
  <header class="oui-appbar oui-on-band"><div class="oui-appbar-row">
    <div class="oui-appbar-id">
      <span v-if="$slots.mark" class="oui-appbar-mark" aria-hidden="true"><slot name="mark" /></span>
      <h1 class="oui-appbar-name">{{ name }}</h1>
    </div>
    <div v-if="$slots.status" class="oui-appbar-status"><slot name="status" /></div>
    <nav v-if="tabs?.length" class="oui-appbar-tabs" role="tablist" :aria-label="tabsLabel ?? name" @keydown="onKey">
      <button v-for="tab in tabs" :key="tab.value" v-bind="tab.attrs" type="button" role="tab" class="oui-appbar-tab" :data-tab="tab.value" :id="'oui-tab-' + tab.value"
        :aria-selected="tab.value === modelValue" :tabindex="tab.value === modelValue ? 0 : -1" @click="emit('update:modelValue', tab.value)">
        <OuiIcon v-if="tab.icon" :icon="tab.icon" :size="15" /><span>{{ tab.label }}</span>
        <!-- The leading space and comma keep the tab's accessible name readable ("Spools 24", "Printer, needs attention"). -->
        <span v-if="tab.count != null" class="oui-appbar-count oui-num"><span class="oui-sr">{{ ' ' }}</span>{{ tab.count }}</span>
        <span v-if="tab.attention" class="oui-appbar-attention" :title="tab.attention"><span class="oui-sr">, {{ tab.attention }}</span></span>
      </button>
    </nav>
    <div v-if="$slots.actions" class="oui-appbar-actions"><slot name="actions" /></div>
  </div></header>
</template>
<style>
/* A band in the plugin's accent, the same in both themes: the mark, the name, the page's state and the tabs sit on it. */
.oui-appbar { container: oui-appbar / inline-size; position: sticky; top: 0; z-index: 10; box-shadow: 0 1px 0 rgb(0 0 0 / .18), 0 4px 14px rgb(0 0 0 / .14); }
/* The row is a child of the container, so the narrow layout below can restyle it. Wide: one line, and the state text is
   what gives way. */
.oui-appbar-row { display: flex; align-items: center; gap: 0 var(--oui-s4); min-height: 52px; padding: 0 var(--oui-s4); }
.oui-appbar-id { display: flex; align-items: center; gap: 10px; min-height: 52px; }
.oui-appbar-mark { display: grid; place-items: center; width: 30px; height: 30px; border-radius: var(--oui-radius-lg); color: var(--oui-band); background: var(--oui-on-band); }
.oui-appbar-mark :is(svg, img) { display: block; width: 20px; height: 20px; }
.oui-appbar-name { font-size: 16px; font-weight: 700; letter-spacing: -.01em; white-space: nowrap; }
.oui-appbar-status { flex: 0 1 auto; display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; overflow: hidden; font-size: var(--oui-text-sm); font-weight: 500; }
.oui-appbar-status > .oui-status { flex: none; }
.oui-appbar-id, .oui-appbar-actions { flex: none; }
.oui-appbar-tabs { flex: none; display: flex; align-items: center; gap: 2px; margin-inline-start: var(--oui-s2); overflow-x: auto; scrollbar-width: none; }
.oui-appbar-tab { display: inline-flex; align-items: center; gap: 6px; height: 32px; padding: 0 12px; border: 0; border-radius: 16px; background: none; cursor: pointer;
  font-weight: 650; color: var(--oui-on-band); white-space: nowrap; transition: background var(--oui-fast), color var(--oui-fast); }
.oui-appbar-tab:hover { background: rgb(255 255 255 / .16); }
.oui-appbar-tab[aria-selected='true'] { color: var(--oui-band); background: var(--oui-on-band); }
.oui-appbar-count { min-width: 18px; padding: 0 5px; border-radius: 9px; font-size: var(--oui-text-xs); line-height: 18px; text-align: center; background: rgb(255 255 255 / .22); }
.oui-appbar-attention { flex: none; width: 8px; height: 8px; border-radius: 50%; background: currentColor; box-shadow: 0 0 0 3px color-mix(in srgb, currentColor 30%, transparent); }
.oui-appbar-tab[aria-selected='true'] .oui-appbar-count { color: var(--oui-on-band); background: var(--oui-band); }
.oui-appbar-actions { display: flex; align-items: center; gap: var(--oui-s2); margin-inline-start: auto; min-height: 52px; }
/* Narrow: identity and state on the first line, tabs on their own scrolling line. */
@container oui-appbar (max-width: 760px) {
  .oui-appbar-row { flex-wrap: wrap; }
  .oui-appbar-status { flex: 1 1 0; }
  .oui-appbar-tabs { order: 5; flex: 1 0 100%; margin-inline: -6px; padding-bottom: var(--oui-s2); }
  .oui-appbar-id, .oui-appbar-actions { min-height: 46px; }
}
</style>
