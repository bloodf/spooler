<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import OuiHint from './OuiHint.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/* A module of the page: a header (icon, title, one line of meta, an (i) for what needs explaining, actions) over its content.
   Every module has the same 40 px neutral header; only its icon may carry a colour. */
defineProps<{ title?: string; icon?: OuiIconData; /** Colour of the header icon: grey by default, a hue for a domain (see DESIGN.md). */ tone?: OuiTone; meta?: string;
  /** What the module needs explained, behind an (i) next to the title: replaces a helper paragraph under the module. */ hint?: string; /** Accessible name of the (i) button ("About the camera"). */ hintLabel?: string;
  /** The id of the hint's text: give it to a control's `aria-describedby` when the hint explains that control. */ hintId?: string;
  /** No body padding: for tables, lists and media that run edge to edge. */ flush?: boolean;
  /** Fill the grid cell and let the body scroll inside it. */ fill?: boolean }>();
</script>
<template>
  <section class="oui-panel" :data-flush="flush || undefined" :data-fill="fill || undefined">
    <header v-if="title || $slots.title || $slots.actions" class="oui-panel-head">
      <OuiIcon v-if="icon" :icon="icon" :size="16" :tone="tone ?? 'neutral'" class="oui-panel-icon" />
      <h2 class="oui-panel-title"><slot name="title">{{ title }}</slot></h2>
      <OuiHint v-if="hint || $slots.hint" :id="hintId" :label="hintLabel ?? title ?? ''"><slot name="hint">{{ hint }}</slot></OuiHint>
      <span v-if="meta || $slots.meta" class="oui-panel-meta oui-meta"><slot name="meta">{{ meta }}</slot></span>
      <div v-if="$slots.actions" class="oui-panel-actions"><slot name="actions" /></div>
    </header>
    <div class="oui-panel-body"><slot /></div>
    <footer v-if="$slots.footer" class="oui-panel-foot"><slot name="footer" /></footer>
  </section>
</template>
<style>
.oui-panel { display: flex; flex-direction: column; min-width: 0; background: var(--oui-surface); border-radius: var(--oui-radius-lg);
  box-shadow: inset 0 0 0 1px var(--oui-border), var(--oui-shadow-panel); }
.oui-panel[data-fill] { min-height: 0; height: 100%; }
/* The header: 40 px, neutral, a hairline under it. Title, meta and actions start on the same 12 px as the body.
   It is one line where there is room. Where there is not (a dock, a narrow column) it wraps inside the panel: first the
   meta gives way, then the actions go to a second line, then they wrap among themselves, and a long title breaks. A
   header never sets the least width of its column. */
.oui-panel-head { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s1) var(--oui-s2); min-height: 40px; padding: 4px var(--oui-s2) 4px var(--oui-s3); border-bottom: 1px solid var(--oui-border); }
.oui-panel-title { flex: none; max-width: 100%; font-weight: 700; overflow-wrap: anywhere; }
/* Beside its icon, never under it: the title's widest is the line less the icon. */
.oui-panel-icon + .oui-panel-title { max-width: calc(100% - 16px - var(--oui-s2)); }
.oui-panel-meta { flex: 1 1 0; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
/* A state chip in the meta keeps its word: the meta is then as wide as the chip instead of whatever is left over, so in a
   narrow header it is the actions that go to the next line, not the chip that shrinks to its mark. Text meta still
   shortens with an ellipsis. :has() is not in WebKit before 15.4: there the chip shrinks as it did in 5.0.4. */
.oui-panel-meta:has(> .oui-status) { flex: 0 1 auto; }
.oui-panel-actions { display: flex; flex-wrap: wrap; align-items: center; justify-content: flex-end; gap: var(--oui-s1); min-width: 0; max-width: 100%; margin-inline-start: auto; }
.oui-panel-head > :last-child:not(.oui-panel-actions) { margin-inline-end: var(--oui-s1); }
.oui-panel-body { flex: 1 1 auto; min-width: 0; padding: var(--oui-s3); }
.oui-panel[data-flush] > .oui-panel-body { padding: 0; }
.oui-panel[data-fill] > .oui-panel-body { min-height: 0; overflow: auto; }
.oui-panel-foot { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); padding: var(--oui-s2) var(--oui-s3); border-top: 1px solid var(--oui-border); }
</style>
