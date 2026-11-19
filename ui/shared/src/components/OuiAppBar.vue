<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';

/*
 * The top bar of every plugin page: identity (the plugin's own mark and name), the task tabs, then on the right the
 * page's one connection or source state and the page-wide actions. The view for the selected tab is rendered by the app: give it
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
  <header class="oui-appbar"><div class="oui-appbar-row">
    <div class="oui-appbar-id">
      <span v-if="$slots.mark" class="oui-appbar-mark" aria-hidden="true"><slot name="mark" /></span>
      <h1 class="oui-appbar-name">{{ name }}</h1>
    </div>
    <nav v-if="tabs?.length" class="oui-appbar-tabs" role="tablist" :aria-label="tabsLabel ?? name" @keydown="onKey">
      <button v-for="tab in tabs" :key="tab.value" v-bind="tab.attrs" type="button" role="tab" class="oui-appbar-tab" :data-tab="tab.value" :id="'oui-tab-' + tab.value"
        :aria-selected="tab.value === modelValue" :tabindex="tab.value === modelValue ? 0 : -1" @click="emit('update:modelValue', tab.value)">
        <OuiIcon v-if="tab.icon" :icon="tab.icon" :size="15" /><span>{{ tab.label }}</span>
        <!-- The leading space and comma keep the tab's accessible name readable ("Spools 24", "Printer, needs attention"). -->
        <span v-if="tab.count != null" class="oui-appbar-count oui-num"><span class="oui-sr">{{ ' ' }}</span>{{ tab.count }}</span>
        <span v-if="tab.attention" class="oui-appbar-attention" :title="tab.attention"><span class="oui-sr">, {{ tab.attention }}</span></span>
      </button>
    </nav>
    <span class="oui-spacer" />
    <div v-if="$slots.status" class="oui-appbar-status"><slot name="status" /></div>
    <div v-if="$slots.actions" class="oui-appbar-actions"><slot name="actions" /></div>
  </div></header>
</template>
<style>
/* A neutral bar, the colour of a panel, under OrcaSlicer's own tab bar. The plugin's hue is in two places only: its mark
   tile and the line under the open tab. Identity and tabs on the left; the page's one state and its actions on the right. */
.oui-appbar { container: oui-appbar / inline-size; position: sticky; top: 0; z-index: 10; background: var(--oui-surface); box-shadow: 0 1px 0 var(--oui-border); }
.oui-appbar-row { display: flex; align-items: stretch; gap: 0 var(--oui-s4); min-height: 44px; padding: 0 var(--oui-s4); }
.oui-appbar-id { flex: none; display: flex; align-items: center; gap: var(--oui-s2); }
.oui-appbar-mark { display: grid; place-items: center; width: 26px; height: 26px; border-radius: var(--oui-radius-lg); color: var(--oui-on-solid); background: var(--oui-accent-solid); }
.oui-appbar-mark :is(svg, img) { display: block; width: 17px; height: 17px; }
.oui-appbar-name { font-size: 14px; font-weight: 700; letter-spacing: -.005em; white-space: nowrap; }
.oui-appbar-tabs { flex: 0 1 auto; display: flex; align-items: stretch; min-width: 0; overflow-x: auto; scrollbar-width: none; }
.oui-appbar-tab { position: relative; display: inline-flex; align-items: center; gap: 6px; padding: 0 10px; border: 0; background: none; cursor: pointer;
  font-weight: 600; color: var(--oui-muted); white-space: nowrap; transition: color var(--oui-fast); }
.oui-appbar-tab:hover { color: var(--oui-text); }
.orca-ui .oui-appbar-tab:focus-visible { outline-offset: -3px; border-radius: var(--oui-radius); }
.oui-appbar-tab[aria-selected='true'] { color: var(--oui-text); }
.oui-appbar-tab[aria-selected='true']::after { content: ''; position: absolute; inset: auto 8px 0; height: 2px; border-radius: 2px 2px 0 0; background: var(--oui-accent); }
.oui-appbar-count { min-width: 18px; padding: 0 5px; border-radius: 9px; font-size: var(--oui-text-xs); line-height: 18px; text-align: center; color: var(--oui-muted); background: var(--oui-raised);
  box-shadow: inset 0 0 0 1px var(--oui-border); }
.oui-appbar-attention { flex: none; width: 7px; height: 7px; border-radius: 50%; background: var(--oui-warning); }
.oui-appbar-status { flex: 0 1 auto; display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; overflow: hidden; font-size: var(--oui-text-sm); color: var(--oui-muted); }
.oui-appbar-status > .oui-status { flex: none; }
.oui-appbar-actions { flex: none; display: flex; align-items: center; gap: var(--oui-s2); }
/* Narrow: identity, state and actions on the first line, tabs on their own scrolling line. */
@container oui-appbar (max-width: 760px) {
  .oui-appbar-row { flex-wrap: wrap; }
  .oui-appbar-id, .oui-appbar-status, .oui-appbar-actions { min-height: 40px; }
  .oui-appbar-tabs { order: 5; flex: 1 0 100%; min-height: 36px; margin-inline: -10px; box-shadow: inset 0 1px 0 var(--oui-border); }
}
</style>
