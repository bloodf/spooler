<script setup lang="ts">
import OuiIcon from './OuiIcon.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/*
 * One line of a controls module (fan, speed, light, a mode): icon, label, what it reads now, then the control, on the
 * same columns as OuiSetpoint so heaters and the rest line up. Put the control in the default slot.
 * The module is an OuiPanel holding `.oui-controls` > `.oui-controls-group` (a `.oui-label`, then the rows).
 */
defineProps<{ label: string; icon?: OuiIconData; tone?: OuiTone; /** What it reads now, in words or figures ("79 %", "Not detected"). */ value?: string; for?: string }>();
</script>
<template>
  <div class="oui-control-row">
    <div class="oui-control-row-label"><OuiIcon v-if="icon" :icon="icon" :size="14" tile :tone="tone" />
      <label v-if="for" :for="for" class="oui-strong">{{ label }}</label><span v-else class="oui-strong">{{ label }}</span></div>
    <span class="oui-control-row-value oui-num oui-truncate"><slot name="value">{{ value }}</slot></span>
    <div class="oui-control-row-control"><slot /></div>
  </div>
</template>
<style>
.oui-control-row { display: grid; grid-template-columns: minmax(84px, 1fr) minmax(0, auto) auto; align-items: center; gap: var(--oui-s2) var(--oui-s3); min-height: 44px; }
.oui-control-row-label { display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; }
.oui-control-row-value { color: var(--oui-muted); text-align: end; }
.oui-control-row-control { display: flex; align-items: center; justify-content: flex-end; gap: var(--oui-s1); }
/* A controls module: groups (Temperature, Machine) side by side when the module is wide enough for two, stacked when not.
   Inside a group a small label, then rows (OuiSetpoint, OuiControlRow) separated by hairlines. */
.oui-controls { display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 340px), 1fr)); gap: var(--oui-s3) var(--oui-s8); align-items: start; }
.oui-controls-group { display: grid; min-width: 0; }
.oui-controls-group > .oui-label { display: flex; align-items: center; gap: var(--oui-s1); min-height: 22px; }
.oui-controls-group > :where(.oui-control-row, .oui-setpoint) + :where(.oui-control-row, .oui-setpoint) { border-top: 1px solid var(--oui-border); }
</style>
