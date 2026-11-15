<script setup lang="ts">
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/*
 * One icon, three treatments: mono (inherits the text colour), toned (its own colour from the palette) and tile
 * (toned, on its tint, in a rounded square: section headers, readouts, empty states, list objects).
 * Icons come from ../icons by name import, so only the ones a page uses are bundled.
 */
defineProps<{ icon: OuiIconData; /** Icon size in px: 14 in controls and tabs, 16 default, 20 in large tiles. */ size?: number; tone?: OuiTone; tile?: boolean; soft?: boolean }>();
</script>
<template>
  <span v-if="tile" class="oui-tile" :data-soft="soft || undefined" :data-tone="tone ?? 'accent'" :style="{ width: (size ?? 16) + 12 + 'px', height: (size ?? 16) + 12 + 'px' }" aria-hidden="true">
    <svg class="oui-icon" :width="size ?? 16" :height="size ?? 16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round" focusable="false">
      <component :is="tag" v-for="([tag, attrs], i) in icon" :key="i" v-bind="attrs" /></svg>
  </span>
  <svg v-else class="oui-icon" :data-tone="tone" :width="size ?? 16" :height="size ?? 16" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"
    stroke-linecap="round" stroke-linejoin="round" aria-hidden="true" focusable="false"><component :is="tag" v-for="([tag, attrs], i) in icon" :key="i" v-bind="attrs" /></svg>
</template>
<style>
.oui-icon { flex: none; display: block; }
.oui-icon[data-tone] { color: var(--oui-tone); }
/* The tile is a solid block of its tone with the icon in the on-colour; `soft` is the tinted version for dense lists. */
.oui-tile { flex: none; display: inline-grid; place-items: center; border-radius: var(--oui-radius); color: var(--oui-tone-on); background: var(--oui-tone); }
.oui-tile[data-soft] { color: var(--oui-tone); background: var(--oui-tone-soft); }
</style>
