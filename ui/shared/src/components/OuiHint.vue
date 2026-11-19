<script setup lang="ts">
import { computed, nextTick, ref, useId } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { info } from '../icons';

/*
 * What a module or a control needs explained, behind an (i): the replacement for a helper paragraph under a module.
 * It opens on hover and on keyboard focus, stays while the pointer is on it, and Escape closes it. The text is the
 * button's description, so a screen reader hears it without opening anything. For more than two sentences, link to the
 * documentation from inside it ("Learn more").
 *
 * Closed, the bubble takes no room at all (display: none; it is still the button's description). Each time it opens
 * it is placed against the window: under the button and starting at it when that fits, moved left as far as it must to
 * stay inside the right edge, and above the button when there is no room below. So it never widens the page and is
 * never cut off by the window, wherever the (i) is; no prop is needed for one near an edge.
 */
const props = defineProps<{ /** Accessible name of the button: what the text is about ("About the camera"). */ label: string; text?: string;
  /** The id of the text, so another control can point `aria-describedby` at it (it works while the bubble is closed). Default: a generated one. */ id?: string;
  /** Prefer opening towards the start edge (the bubble ends at the button). Only a preference since 5.0.2: the bubble stays inside the window either way. */ end?: boolean }>();
const open = ref(false);
const generated = useId();
const id = computed(() => props.id ?? generated);
const root = ref<HTMLElement>();
const bubble = ref<HTMLElement>();
const place = ref<{ left: string; top: string }>();
const EDGE = 8;   // the least distance kept from the window's edges
const GAP = 4;    // between the button and the bubble

function position() {
  const at = root.value?.getBoundingClientRect(); const b = bubble.value;
  if (!at || !b) return;
  const vw = document.documentElement.clientWidth; const vh = document.documentElement.clientHeight;
  const w = b.offsetWidth; const h = b.offsetHeight;
  // Across: the preferred side, then inside the window; the left edge wins if the window is narrower than the bubble.
  const left = Math.max(EDGE, Math.min(props.end ? at.right + EDGE - w : at.left - EDGE, vw - EDGE - w));
  // Down, unless it does not fit below and does fit above.
  const below = at.bottom + GAP + h <= vh - EDGE || at.top - GAP - h < EDGE;
  place.value = { left: left - at.left + 'px', top: (below ? at.height + GAP : -(h + GAP)) + 'px' };
}
// ponytail: placed when it opens, not while the page scrolls or resizes under an open bubble; it is open only while
// hovered or focused. An ancestor that scrolls can still clip it: move to PrimeVue Popover if a page needs that.
async function show() {
  if (open.value) return;
  open.value = true;
  await nextTick();   // the bubble has its size now, and nothing has been painted yet
  position();
}
function hide() { open.value = false; }
</script>
<template>
  <span ref="root" class="oui-hint" @mouseenter="show" @mouseleave="hide" @focusin="show" @focusout="hide" @keydown.esc.stop="hide">
    <button type="button" class="oui-hint-btn" :aria-label="label" :aria-describedby="id" :aria-expanded="open" @click="show"><OuiIcon :icon="info" :size="14" /></button>
    <span v-show="open" :id="id" ref="bubble" class="oui-hint-bubble" role="tooltip" :style="place"><slot>{{ text }}</slot></span>
  </span>
</template>
<style>
.oui-hint { position: relative; flex: none; display: inline-flex; }
.oui-hint-btn { display: inline-grid; place-items: center; width: 22px; height: 22px; padding: 0; border: 0; border-radius: 50%; color: var(--oui-muted); background: none; cursor: help; }
.oui-hint-btn:hover, .oui-hint-btn[aria-expanded='true'] { color: var(--oui-text); background: var(--oui-control); }
/* left and top are set from script each time it opens (see above); these are where it starts for its first measure. */
.oui-hint-bubble { position: absolute; z-index: 20; top: calc(100% + 4px); left: -8px; width: max-content; max-width: min(300px, calc(100vw - 16px)); padding: var(--oui-s2) 10px; border-radius: var(--oui-radius-lg);
  font-size: var(--oui-text-sm); font-weight: 400; line-height: 1.45; text-align: start; white-space: normal; color: var(--oui-text); background: var(--oui-surface);
  box-shadow: inset 0 0 0 1px var(--oui-control-border), var(--oui-shadow-overlay); }
</style>
