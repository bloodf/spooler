<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import { clock, error, offline, warning, type OuiIconData } from '../icons';

/*
 * The one way a state is shown anywhere in the family. Every state has its own mark as well as its colour,
 * so it reads without colour; `uncertain` outcomes use `warn` or `pending`, never `ok`.
 */
export type OuiState = 'ok' | 'busy' | 'warn' | 'error' | 'offline' | 'connecting' | 'stale' | 'pending' | 'idle';
defineProps<{ state: OuiState; label?: string; /** `badge` (default) is a tinted chip; `plain` is coloured text for a sentence. */ variant?: 'badge' | 'plain' }>();
const GLYPH: Partial<Record<OuiState, OuiIconData>> = { warn: warning, error, offline, stale: clock, pending: clock };
</script>
<template>
  <span class="oui-status" :data-state="state" :data-variant="variant ?? 'badge'">
    <OuiIcon v-if="GLYPH[state]" :icon="GLYPH[state]!" :size="13" />
    <span v-else class="oui-status-dot" aria-hidden="true" />
    <span class="oui-status-label"><slot>{{ label }}</slot></span>
  </span>
</template>
<style>
/* A chip tinted with the state's colour (the default), or `plain`: the mark and the word in that colour, for running text. */
.oui-status { --oui-status: var(--oui-muted); --oui-status-bg: var(--oui-raised); display: inline-flex; align-items: center; gap: 5px; min-width: 0; max-width: 100%; width: fit-content; height: 22px; padding: 0 9px 0 7px;
  border-radius: 11px; font-size: var(--oui-text-sm); font-weight: 650; line-height: 1; white-space: nowrap; color: var(--oui-status); background: var(--oui-status-bg);
  box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-status) 32%, transparent); }
.oui-status[data-variant='plain'] { height: auto; padding: 0; border-radius: 0; line-height: 1.3; background: none; box-shadow: none; }
.oui-status[data-state='ok'] { --oui-status: var(--oui-success); --oui-status-bg: var(--oui-success-bg); }
.oui-status:is([data-state='busy'], [data-state='pending']) { --oui-status: var(--oui-info); --oui-status-bg: var(--oui-info-bg); }
.oui-status:is([data-state='warn'], [data-state='stale']) { --oui-status: var(--oui-warning); --oui-status-bg: var(--oui-warning-bg); }
.oui-status[data-state='error'] { --oui-status: var(--oui-danger); --oui-status-bg: var(--oui-danger-bg); }
.oui-status-label { overflow: hidden; text-overflow: ellipsis; }
.oui-status-dot { flex: none; width: 8px; height: 8px; border-radius: 50%; background: currentColor; }
/* idle: a hollow ring. connecting: a turning arc. busy: a steady dot with a slow halo. */
.oui-status[data-state='idle'] .oui-status-dot { background: none; box-shadow: inset 0 0 0 1.5px currentColor; }
.oui-status[data-state='connecting'] .oui-status-dot { width: 10px; height: 10px; background: none; border: 1.5px solid currentColor; border-right-color: transparent;
  animation: oui-turn .9s linear infinite; }
.oui-status[data-state='busy'] .oui-status-dot { animation: oui-halo 2s var(--oui-ease) infinite; }
@keyframes oui-turn { to { transform: rotate(1turn); } }
@keyframes oui-halo { 0% { box-shadow: 0 0 0 0 color-mix(in srgb, currentColor 50%, transparent); } 70%, 100% { box-shadow: 0 0 0 5px transparent; } }
</style>
