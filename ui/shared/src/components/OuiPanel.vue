<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import OuiHint from './OuiHint.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/* A module of the page: a header (icon, title, one line of meta, an (i) for what needs explaining, actions) over its content.
   Every module has the same 40 px neutral header; only its icon may carry a colour. */
defineProps<{ title?: string; icon?: OuiIconData; /** Colour of the header icon: grey by default, a hue for a domain (see DESIGN.md). */ tone?: OuiTone; meta?: string;
  /** What the module needs explained, behind an (i) next to the title: replaces a helper paragraph under the module. */ hint?: string; /** Accessible name of the (i) button ("About the camera"). */ hintLabel?: string;
  /** No body padding: for tables, lists and media that run edge to edge. */ flush?: boolean;
  /** Fill the grid cell and let the body scroll inside it. */ fill?: boolean }>();
</script>
<template>
  <section class="oui-panel" :data-flush="flush || undefined" :data-fill="fill || undefined">
    <header v-if="title || $slots.title || $slots.actions" class="oui-panel-head">
      <OuiIcon v-if="icon" :icon="icon" :size="16" :tone="tone ?? 'neutral'" class="oui-panel-icon" />
      <h2 class="oui-panel-title"><slot name="title">{{ title }}</slot></h2>
      <OuiHint v-if="hint || $slots.hint" :label="hintLabel ?? title ?? ''"><slot name="hint">{{ hint }}</slot></OuiHint>
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
/* The header: 40 px, neutral, a hairline under it. Title, meta and actions start on the same 12 px as the body. */
.oui-panel-head { display: flex; align-items: center; gap: var(--oui-s2); min-height: 40px; padding: 4px var(--oui-s2) 4px var(--oui-s3); border-bottom: 1px solid var(--oui-border); }
.oui-panel-title { flex: none; max-width: 100%; font-weight: 700; }
.oui-panel-meta { flex: 1 1 0; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.oui-panel-actions { display: flex; align-items: center; gap: var(--oui-s1); margin-inline-start: auto; }
.oui-panel-head > :last-child:not(.oui-panel-actions) { margin-inline-end: var(--oui-s1); }
.oui-panel-body { flex: 1 1 auto; min-width: 0; padding: var(--oui-s3); }
.oui-panel[data-flush] > .oui-panel-body { padding: 0; }
.oui-panel[data-fill] > .oui-panel-body { min-height: 0; overflow: auto; }
.oui-panel-foot { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); padding: var(--oui-s2) var(--oui-s3); border-top: 1px solid var(--oui-border); }
</style>
