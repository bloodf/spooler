<script setup lang="ts">
import { computed } from 'vue';
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/*
 * A measured or computed value with its label: label small, value large, in tabular figures.
 * An unknown value (null, undefined, '') is a dash, never 0. `incomplete` marks a value built from partial data.
 */
const props = defineProps<{ label: string; icon?: OuiIconData; tone?: OuiTone; value?: string | number | null; unit?: string; sub?: string;
  size?: 'sm' | 'md' | 'lg' | 'hero'; incomplete?: boolean; stale?: boolean; unknownLabel?: string }>();
const blank = computed(() => props.value == null || props.value === '');
</script>
<template>
  <div class="oui-readout" :data-size="size ?? 'md'" :data-incomplete="incomplete || undefined" :data-stale="stale || undefined" :data-icon="icon ? true : undefined">
    <OuiIcon v-if="icon" class="oui-readout-icon" :icon="icon" :size="size === 'sm' ? 14 : 16" tile :tone="stale ? 'neutral' : tone" />
    <div class="oui-label">{{ label }}</div>
    <div class="oui-readout-value oui-num" :data-tone="tone && !stale && !incomplete ? tone : undefined">
      <slot><span v-if="blank" :aria-label="unknownLabel ?? 'unknown'">—</span><template v-else>{{ value }}</template></slot>
      <span v-if="unit && !blank" class="oui-readout-unit">{{ unit }}</span>
    </div>
    <div v-if="sub || $slots.sub" class="oui-readout-sub oui-meta"><slot name="sub">{{ sub }}</slot></div>
  </div>
</template>
<style>
.oui-readout { display: grid; gap: 2px; min-width: 0; align-content: start; }
.oui-readout[data-icon] { grid-template-columns: auto minmax(0, 1fr); column-gap: var(--oui-s2); }
.oui-readout-icon { grid-row: 1 / span 2; align-self: center; }
.oui-readout[data-icon] > .oui-readout-sub { grid-column: 2; }
.oui-readout-value[data-tone] { color: var(--oui-tone); }
.oui-readout-value { font-size: var(--oui-text-xl); line-height: 1.15; font-weight: 700; letter-spacing: -.01em; overflow-wrap: anywhere; }
.oui-readout[data-size='sm'] .oui-readout-value { font-size: var(--oui-text-lg); line-height: 1.3; letter-spacing: 0; }
.oui-readout[data-size='lg'] .oui-readout-value { font-size: var(--oui-text-2xl); letter-spacing: -.015em; }
.oui-readout[data-size='hero'] { gap: 6px; }
.oui-readout[data-size='hero'] .oui-readout-value { font-size: var(--oui-text-3xl); line-height: 1.05; letter-spacing: -.02em; }
.oui-readout-unit { margin-inline-start: .18em; font-size: .6em; font-weight: 600; letter-spacing: 0; color: var(--oui-muted); }
.oui-readout-value[data-tone] .oui-readout-unit { color: inherit; }
.oui-readout[data-size='hero'] .oui-readout-value { font-weight: 700; }
.oui-readout[data-size='sm'] .oui-readout-unit { font-size: .8em; }
.oui-readout[data-incomplete] .oui-readout-value { color: var(--oui-muted); text-decoration: underline dashed 1px; text-underline-offset: .16em; padding-bottom: .12em; }
.oui-readout[data-stale] .oui-readout-value { color: var(--oui-muted); }
</style>
