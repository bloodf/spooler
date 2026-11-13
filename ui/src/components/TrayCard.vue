<script setup lang="ts">
import { computed } from 'vue';
import { m } from '../state/main';
import SpoolFigure from './SpoolFigure.vue';
import LevelBar from './LevelBar.vue';
import { t, locale } from '../core/i18n';
import { formatWeight, originalWeight, shown } from '../logic/spools';
import type { Tray } from '../logic/printers';

// One live slot (AMS tray, toolhead, external spool) as the printer reports it, with the spool it holds.
const props = defineProps<{ tray: Tray }>();
const tr = computed(() => props.tray);
const colour = computed(() => (tr.value.colour ? '#' + tr.value.colour : '#888'));
const pct = computed(() => (tr.value.remain == null ? null : Math.round(tr.value.remain)));
const profile = computed(() => (tr.value.profile || '').split('/').pop() || '');
const spool = computed(() => (tr.value.spool != null ? m.spools.find(s => String(s.id) === String(tr.value.spool) && !s.archived) ?? null : null));
const d = computed(() => m.disp);
const ex = computed(() => shown(d.value, 'exact_weight'));
const sub = computed(() => [shown(d.value, 'head_vendor') ? spool.value?.filament?.vendor?.name || '' : '', shown(d.value, 'head_material') ? tr.value.type || '' : '',
  shown(d.value, 'head_colour_code') && tr.value.colour ? '#' + tr.value.colour : ''].filter(Boolean).join(' · '));
const weight = computed(() => {
  const s = spool.value;
  if (!shown(d.value, 'head_weight') || !s || typeof s.remaining_weight !== 'number') return '';
  const full = originalWeight(s);
  return t('weight.left', { w: formatWeight(s.remaining_weight, ex.value, locale.value) + (typeof full === 'number' ? ' ' + t('weight.of', { total: formatWeight(full, ex.value, locale.value) }) : '') });
});
const where = computed(() => (shown(d.value, 'head_spool') && spool.value
  ? [t('spool.numbered', { id: spool.value.id }), spool.value.location || '', tr.value.linked === 'u1control' ? t('tray.linkedU1') : ''].filter(Boolean).join(' · ') : ''));
const tip = computed(() => [profile.value ? t('tray.preset', { p: profile.value }) : '', tr.value.linked === 'u1control' ? t('tray.linkedU1Tip') : ''].filter(Boolean).join(' · '));
</script>
<template>
  <div v-if="tr.empty" class="tc empty"><strong>{{ t('tray.empty') }}</strong><span class="oui-meta">{{ t('tray.nothing') }}</span></div>
  <div v-else class="tc" :title="tip || undefined">
    <div class="tc-head">
      <div class="tc-swcol"><SpoolFigure :paint="colour" :fraction="pct === null ? (spool ? null : 1) : pct / 100" :size="56" /><span v-if="tr.rfid && shown(d, 'head_rfid')" class="sp-chip tc-rfid" :title="t('tray.rfid')">RFID</span></div>
      <div class="tc-top"><strong class="tc-name">{{ tr.name || tr.type }}</strong><span class="sp-num tc-pct">{{ pct === null ? '' : pct + '%' }}</span></div>
    </div>
    <LevelBar v-if="shown(d, 'head_bar')" class="tc-track" :pct="pct" :paint="colour" :title="pct === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct })" />
    <div class="tc-main">
      <span v-if="sub" class="tc-line">{{ sub }}</span>
      <span v-if="weight" class="tc-line">{{ weight }}</span>
      <span v-if="where" class="tc-line">{{ where }}</span>
      <span v-if="shown(d, 'head_preset') && profile" class="tc-line">{{ profile }}</span>
    </div>
  </div>
</template>
<style scoped>
.tc { display: grid; gap: 6px; padding: 8px 10px 10px; border: 1px solid var(--oui-border); border-radius: 14px; background: var(--oui-surface); min-width: 0; }
.tc.empty { display: grid; gap: 2px; border-style: dashed; padding: 10px; }
.tc-head { display: flex; align-items: center; gap: 8px; min-width: 0; }
.tc-swcol { display: grid; gap: 2px; justify-items: center; }
.tc-rfid { font-size: 12px; padding: 0 4px; line-height: 16px; }
.tc-top { flex: 1; display: grid; gap: 2px; min-width: 0; }
.tc-name { min-width: 0; overflow-wrap: anywhere; line-height: 1.25; }
.tc-pct { font-size: 18px; font-weight: 700; }
.tc-main { display: grid; gap: 2px; min-width: 0; }
.tc-line { color: var(--oui-muted); font-size: 12px; overflow-wrap: anywhere; }
</style>
