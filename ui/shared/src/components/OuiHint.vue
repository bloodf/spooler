<script setup lang="ts">
import { ref, useId } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { info } from '../icons';

/*
 * What a module or a control needs explained, behind an (i): the replacement for a helper paragraph under a module.
 * It opens on hover and on keyboard focus, stays while the pointer is on it, and Escape closes it. The text is the
 * button's description, so a screen reader hears it without opening anything. For more than two sentences, link to the
 * documentation from inside it ("Learn more").
 */
defineProps<{ /** Accessible name of the button: what the text is about ("About the camera"). */ label: string; text?: string; /** Open towards the start edge, for an (i) near the right edge of the page. */ end?: boolean }>();
const open = ref(false);
const id = useId();
</script>
<template>
  <span class="oui-hint" :data-end="end || undefined" @mouseenter="open = true" @mouseleave="open = false" @focusin="open = true" @focusout="open = false" @keydown.esc.stop="open = false">
    <button type="button" class="oui-hint-btn" :aria-label="label" :aria-describedby="id" :aria-expanded="open" @click="open = true"><OuiIcon :icon="info" :size="14" /></button>
    <!-- ponytail: an absolutely placed bubble; a scrolling ancestor can clip it. Move to PrimeVue Popover if a page needs that. -->
    <span :id="id" class="oui-hint-bubble" role="tooltip" :data-open="open || undefined"><slot>{{ text }}</slot></span>
  </span>
</template>
<style>
.oui-hint { position: relative; flex: none; display: inline-flex; }
.oui-hint-btn { display: inline-grid; place-items: center; width: 22px; height: 22px; padding: 0; border: 0; border-radius: 50%; color: var(--oui-muted); background: none; cursor: help; }
.oui-hint-btn:hover, .oui-hint-btn[aria-expanded='true'] { color: var(--oui-text); background: var(--oui-control); }
.oui-hint-bubble { position: absolute; z-index: 20; top: calc(100% + 4px); left: -8px; width: max-content; max-width: min(300px, 70vw); padding: var(--oui-s2) 10px; border-radius: var(--oui-radius-lg);
  font-size: var(--oui-text-sm); font-weight: 400; line-height: 1.45; text-align: start; white-space: normal; color: var(--oui-text); background: var(--oui-surface);
  box-shadow: inset 0 0 0 1px var(--oui-control-border), var(--oui-shadow-overlay); visibility: hidden; opacity: 0; transition: opacity var(--oui-fast); }
.oui-hint[data-end] > .oui-hint-bubble { left: auto; right: -8px; }
.oui-hint-bubble[data-open] { visibility: visible; opacity: 1; }
</style>
