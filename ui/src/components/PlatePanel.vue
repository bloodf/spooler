<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiIcon, OuiPanel, OuiStatus, OuiSwatch, type OuiState } from '../../shared/src/components';
import { plate, refresh } from '../../shared/src/icons';
import * as bridge from '../core/bridge';
import { m, plateAttention } from '../state/main';
import { t, tn } from '../core/i18n';

// The last slice's filament check: per plate slot, what it needs against what its spool has left.
const rows = computed(() => m.plate?.rows ?? []);
const fine = computed(() => rows.value.some(r => r.status === 'ok'));
const hex = (v: string) => (/^#?[0-9a-f]{6}/i.test(v || '') ? '#' + v.replace(/^#/, '').slice(0, 6) : null);
const STATE: Record<string, OuiState> = { ok: 'ok', barely: 'warn', mixed: 'warn', short: 'error', unknown: 'idle' };
function dismiss() { m.plate = null; bridge.postMain({ type: 'plate_dismiss' }); }
</script>
<template>
  <OuiPanel v-if="m.plate" :title="t('plate.title')" :icon="plate" tone="cobalt" data-test="plate">
    <template #meta><OuiStatus v-if="plateAttention" state="warn">{{ tn('plate.attention', plateAttention) }}</OuiStatus><OuiStatus v-else-if="fine" state="ok">{{ t('plate.ok') }}</OuiStatus></template>
    <template #actions>
      <Button severity="secondary" size="small" :label="t('plate.recheck')" :title="t('plate.recheckHelp')" @click="bridge.postMain({ type: 'plate_recheck' })"><template #icon><OuiIcon :icon="refresh" :size="14" /></template></Button>
      <Button severity="secondary" text size="small" :label="t('plate.dismiss')" :title="t('plate.dismissHelp')" @click="dismiss" />
    </template>
    <ul class="pl-rows">
      <li v-for="(r, i) in rows" :key="i" class="pl-row" :data-status="r.status">
        <OuiSwatch :color="hex(r.colour)" :size="14" />
        <span class="pl-who"><strong>{{ r.slots }} · {{ r.name }}</strong><span class="oui-meta">{{ r.meta }}</span></span>
        <span class="pl-bar" aria-hidden="true"><template v-if="r.status !== 'unknown'">
          <i class="have" :style="{ width: Math.round(r.fill * 100) + '%' }" /><i class="need" :style="{ width: Math.round(r.need_pct * 100) + '%' }" /></template></span>
        <span class="pl-res"><OuiStatus :state="STATE[r.status] ?? 'idle'" variant="plain">{{ r.headline }}</OuiStatus><span class="oui-meta">{{ r.detail }}</span></span>
      </li>
    </ul>
    <template #footer><p class="oui-meta">{{ t('plate.sub', { time: m.plate.time || '' }) }}</p></template>
  </OuiPanel>
</template>
<style>
/* Longer labels (German) wrap the actions under the title instead of pushing past a narrow dock. */
[data-test='plate'] > .oui-panel-head { flex-wrap: wrap; }
.pl-rows { list-style: none; padding: 0; display: grid; gap: var(--oui-s3); }
.pl-row { display: grid; grid-template-columns: 14px minmax(0, 1.4fr) minmax(64px, 1fr) minmax(0, 1.4fr); gap: var(--oui-s3); align-items: center; }
.pl-who, .pl-res { display: grid; gap: 1px; min-width: 0; overflow-wrap: anywhere; }
.pl-res > .oui-status { white-space: normal; }
/* solid = what the spool has left, striped = what the plate needs */
.pl-bar { position: relative; height: 8px; border-radius: 4px; background: var(--oui-border); overflow: hidden; }
.pl-bar i { position: absolute; inset-block: 0; inset-inline-start: 0; }
.pl-bar .have { background: var(--oui-success); }
.pl-row:is([data-status='barely'], [data-status='mixed']) .have { background: var(--oui-warning); }
.pl-row[data-status='short'] .have { background: var(--oui-danger); }
.pl-bar .need { background: repeating-linear-gradient(45deg, var(--oui-text) 0 2px, transparent 2px 6px); opacity: .6; }
@container oui-page (max-width: 620px) { .pl-row { grid-template-columns: 14px minmax(0, 1fr); } .pl-bar, .pl-res { grid-column: 2; } }
</style>
