<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import * as bridge from '../core/bridge';
import { m, plateAttention } from '../state/main';
import { t, tn } from '../core/i18n';

// The last slice's filament check: per plate slot, what it needs against what its spool has left.
const rows = computed(() => m.plate?.rows ?? []);
const fine = computed(() => rows.value.some(r => r.status === 'ok'));
const hex = (v: string) => (/^#?[0-9a-f]{6}/i.test(v || '') ? '#' + v.replace(/^#/, '').slice(0, 6) : '#888');
function dismiss() { m.plate = null; bridge.postMain({ type: 'plate_dismiss' }); }
</script>
<template>
  <section v-if="m.plate" class="sp-card pl" aria-labelledby="pl-h" data-test="plate">
    <div class="sp-row pl-head">
      <h2 id="pl-h">{{ t('plate.title') }}</h2>
      <span v-if="plateAttention" class="sp-chip warn">{{ tn('plate.attention', plateAttention) }}</span>
      <span v-else-if="fine" class="sp-chip ok">{{ t('plate.ok') }}</span>
      <span class="sp-grow" />
      <Button severity="secondary" outlined :label="t('plate.recheck')" :title="t('plate.recheckHelp')" @click="bridge.postMain({ type: 'plate_recheck' })" />
      <Button severity="secondary" text :label="t('plate.dismiss')" :title="t('plate.dismissHelp')" @click="dismiss" />
    </div>
    <p class="oui-meta">{{ t('plate.sub', { time: m.plate.time || '' }) }}</p>
    <ul class="pl-rows">
      <li v-for="(r, i) in rows" :key="i" class="pl-row" :class="'st-' + r.status">
        <span class="pl-dot" :style="{ background: hex(r.colour) }" />
        <span class="pl-who"><strong>{{ r.slots }} · {{ r.name }}</strong><span class="oui-meta">{{ r.meta }}</span></span>
        <span class="pl-bar" :aria-hidden="true"><template v-if="r.status !== 'unknown'">
          <i class="have" :style="{ width: Math.round(r.fill * 100) + '%', background: hex(r.spool_colour) }" />
          <i class="need" :style="{ width: Math.round(r.need_pct * 100) + '%' }" /></template></span>
        <span class="pl-res"><strong :class="{ 'sp-warn': ['barely', 'mixed'].includes(r.status), 'sp-err': r.status === 'short' }">{{ r.headline }}</strong>
          <span class="oui-meta">{{ r.detail }}</span></span>
      </li>
    </ul>
  </section>
</template>
<style scoped>
.pl-head h2 { margin: 0; }
.pl-rows { list-style: none; margin: 0; padding: 0; display: grid; gap: 8px; }
.pl-row { display: grid; grid-template-columns: 16px minmax(0, 1.4fr) minmax(80px, 1fr) minmax(0, 1.4fr); gap: 12px; align-items: center; }
.pl-dot { width: 16px; height: 16px; border-radius: 50%; border: 1px solid var(--oui-border); }
.pl-who, .pl-res { display: grid; min-width: 0; overflow-wrap: anywhere; }
.pl-bar { position: relative; height: 10px; border-radius: 5px; background: var(--oui-border); overflow: hidden; }
.pl-bar i { position: absolute; left: 0; top: 0; bottom: 0; }
.pl-bar .need { background: repeating-linear-gradient(45deg, var(--oui-text) 0 2px, transparent 2px 6px); opacity: .55; }
@media (max-width: 640px) { .pl-row { grid-template-columns: 16px minmax(0, 1fr); } .pl-bar, .pl-res { grid-column: 2; } }
</style>
