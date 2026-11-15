<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/* A module of the page: a titled header strip (title, one line of meta, actions) over its content. */
defineProps<{ title?: string; icon?: OuiIconData; /** Colour of the header icon tile: the accent by default, a hue for a domain (see DESIGN.md). */ tone?: OuiTone; meta?: string; /** No body padding: for tables, lists and media that run edge to edge. */ flush?: boolean;
  /** Fill the grid cell and let the body scroll inside it. */ fill?: boolean }>();
</script>
<template>
  <section class="oui-panel" :data-flush="flush || undefined" :data-fill="fill || undefined">
    <header v-if="title || $slots.title || $slots.actions" class="oui-panel-head" :data-tone="tone ?? 'accent'">
      <OuiIcon v-if="icon" :icon="icon" :size="15" tile :tone="tone" class="oui-panel-icon" />
      <h2 class="oui-panel-title"><slot name="title">{{ title }}</slot></h2>
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
/* The header is a strip tinted with the module's hue; its icon is a solid tile of that hue. */
.oui-panel-head { display: flex; align-items: center; gap: var(--oui-s2); min-height: 44px; padding: 4px var(--oui-s2) 4px var(--oui-s3);
  border-radius: var(--oui-radius-lg) var(--oui-radius-lg) 0 0; background: var(--oui-tone-soft); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-tone) 26%, transparent); }
.oui-panel-title { flex: none; max-width: 100%; font-weight: 700; }
.oui-panel-meta { flex: 1 1 0; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.oui-panel-actions { display: flex; align-items: center; gap: var(--oui-s1); margin-inline-start: auto; }
.oui-panel-head > :last-child:not(.oui-panel-actions) { margin-inline-end: var(--oui-s2); }
.oui-panel-body { flex: 1 1 auto; min-width: 0; padding: var(--oui-s4); }
.oui-panel[data-flush] > .oui-panel-body { padding: 0; }
.oui-panel[data-fill] > .oui-panel-body { min-height: 0; overflow: auto; }
.oui-panel-foot { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); padding: var(--oui-s2) var(--oui-s4); border-top: 1px solid var(--oui-border); }
</style>
