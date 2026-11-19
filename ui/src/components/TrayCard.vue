<script setup lang="ts">
import { computed } from 'vue';
import { OuiIcon, OuiLevel, OuiSlot, OuiStatus } from '../../shared/src/components';
import { rfid } from '../../shared/src/icons';
import { m } from '../state/main';
import { t, locale } from '../core/i18n';
import { LEVEL_KEY, formatWeight, lowLevel, originalWeight, shown, spoolFraction } from '../logic/spools';
import type { Tray } from '../logic/printers';

// One live slot (AMS tray, toolhead, external spool) as the printer reports it, with the spool it holds. Two sources,
// said apart: the percentage, the bar and the colour are the printer's; the grams line is Spoolman's.
const props = defineProps<{ tray?: Tray | null; label: string; tool?: 1 | 2 | 3 | 4; active?: boolean; emptyLabel?: string; emptyHint?: string }>();
const tr = computed<Tray>(() => props.tray ?? { empty: true });
const pct = computed(() => (tr.value.remain == null ? null : Math.round(tr.value.remain)));
const profile = computed(() => (tr.value.profile || '').split('/').pop() || '');
const spool = computed(() => (tr.value.spool != null ? m.spools.find(s => String(s.id) === String(tr.value.spool) && !s.archived) ?? null : null));
const d = computed(() => m.disp);
// The drawn spool: Spoolman's weight, else the printer's percentage; null when neither is known (the full reel in the
// slot's colour with the unknown badge), never a made-up level.
const fill = computed(() => spoolFraction(spool.value, tr.value.remain));
const ex = computed(() => shown(d.value, 'exact_weight'));
const level = computed(() => lowLevel(spool.value?.remaining_weight, m.low));
const sub = computed(() => [shown(d.value, 'head_vendor') ? spool.value?.filament?.vendor?.name || '' : '', shown(d.value, 'head_material') ? tr.value.type || '' : '',
  shown(d.value, 'head_colour_code') && tr.value.colour ? '#' + tr.value.colour : ''].filter(Boolean).join(' · '));
const weight = computed(() => {
  const s = spool.value;
  if (!shown(d.value, 'head_weight') || !s || typeof s.remaining_weight !== 'number') return '';
  const full = originalWeight(s);
  return t('weight.left', { w: formatWeight(s.remaining_weight, ex.value, locale.value) + (typeof full === 'number' ? ' ' + t('weight.of', { total: formatWeight(full, ex.value, locale.value) }) : '') });
});
// Linked through a Spoolman location that U1 Control or Kobra Control reads (the page can change it on these slots).
const by = computed(() => (tr.value.linked === 'u1control' ? ['tray.linkedU1', 'tray.linkedU1Tip'] as const
  : tr.value.linked === 'kobracontrol' ? ['tray.linkedKobra', 'tray.linkedKobraTip'] as const : null));
const where = computed(() => (shown(d.value, 'head_spool') && spool.value
  ? [t('spool.numbered', { id: spool.value.id }), spool.value.location || '', by.value ? t(by.value[0]) : ''].filter(Boolean).join(' · ') : ''));
const tip = computed(() => [profile.value ? t('tray.preset', { p: profile.value }) : '', by.value ? t(by.value[1]) : ''].filter(Boolean).join(' · '));
const empty = computed(() => !!tr.value.empty);
</script>
<template>
  <OuiSlot class="tc" :label="label" :tool="tool" :active="active && !empty" :empty-label="emptyLabel ?? t('tray.empty')" :title="(!empty && tip) || undefined"
           :name="empty ? null : tr.name || tr.type" :material="empty ? null : tr.type" :color="!empty && tr.colour ? '#' + tr.colour : null"
           :remaining="fill" :initial="1">
    <template v-if="!empty && (active || level)" #state>
      <OuiStatus v-if="active" state="busy">{{ t('progress.inUseSlot') }}</OuiStatus>
      <OuiStatus v-else :state="level === 'low' ? 'warn' : 'error'">{{ t(LEVEL_KEY[level]) }}</OuiStatus>
    </template>
    <template #meta>{{ sub }}</template>
    <template #amount>
      <div v-if="pct !== null || weight" class="oui-slot-amount" data-test="weight">
        <p v-if="pct !== null" class="oui-num" data-source="printer"><strong>{{ pct }}%</strong><span class="oui-muted">{{ ' ' + t('tray.fromPrinter') }}</span></p>
        <OuiLevel v-if="shown(d, 'head_bar') && pct !== null" :fraction="pct / 100" :label="t('spool.pctLeft', { pct }) + ' ' + t('tray.fromPrinter')" />
        <p v-if="weight" class="oui-num oui-meta" data-source="spoolman">{{ weight }} · Spoolman</p>
      </div>
    </template>
    <template v-if="empty">
      <p class="oui-meta">{{ emptyHint ?? t('tray.nothing') }}</p><slot />
    </template>
    <template v-else>
      <div v-if="where || (shown(d, 'head_preset') && profile) || (tr.rfid && shown(d, 'head_rfid'))" class="tc-lines">
        <p v-if="where" class="oui-meta oui-truncate" :title="where">{{ where }}</p>
        <p v-if="shown(d, 'head_preset') && profile" class="oui-meta oui-truncate" :title="profile">{{ profile }}</p>
        <span v-if="tr.rfid && shown(d, 'head_rfid')" class="oui-chip tc-chip" :title="t('tray.rfid')"><OuiIcon :icon="rfid" :size="12" />RFID</span>
      </div>
      <slot />
    </template>
    <template v-if="$slots.actions" #actions><slot name="actions" /></template>
  </OuiSlot>
</template>
<style>
/* Each line is as wide as the card and cut with an ellipsis (its full text in the title), never past the edge. */
.tc-lines { display: grid; gap: 2px; min-width: 0; }
.tc-chip { justify-self: start; }
</style>
