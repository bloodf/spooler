<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import { check, error, info, warning, type OuiIconData } from '../icons';

/*
 * A page-level state, said once: why the page is offline, busy, stale or needs attention, with the one action
 * that resolves it. Controls that it disables point at it with aria-describedby instead of repeating it.
 */
const props = defineProps<{ tone?: 'info' | 'warn' | 'error' | 'success' | 'neutral'; title: string; icon?: OuiIconData; id?: string }>();
const TONE = { info: 'info', warn: 'warn', error: 'danger', success: 'success', neutral: 'neutral' } as const;
const ICON: Record<string, OuiIconData> = { info, warn: warning, error, success: check, neutral: info };
</script>
<template>
  <div :id="id" class="oui-banner" :data-tone="TONE[props.tone ?? 'info']" :role="props.tone === 'error' ? 'alert' : 'status'">
    <OuiIcon class="oui-banner-icon" :icon="icon ?? ICON[props.tone ?? 'info']" :size="16" tile :tone="TONE[props.tone ?? 'info']" />
    <p class="oui-banner-text"><strong>{{ title }}</strong> <span v-if="$slots.default"><slot /></span></p>
    <div v-if="$slots.actions" class="oui-banner-actions"><slot name="actions" /></div>
  </div>
</template>
<style>
.oui-banner { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 10px; min-height: 44px; padding: 6px 8px; border-radius: var(--oui-radius-lg);
  background: var(--oui-tone-soft); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-tone) 40%, transparent); }
.oui-banner-text { flex: 1 1 150px; min-width: 0; padding-block: 3px; }
.oui-banner-text > strong { font-weight: 700; margin-inline-end: 4px; }
.oui-banner-actions { display: flex; flex-wrap: wrap; gap: 6px; margin-inline-start: auto; }
</style>
