<script setup lang="ts">
import { computed } from 'vue';
import { OuiLevel, OuiSlot, OuiStatus } from '../../shared/src/components';
import { m } from '../state/main';
import { t, locale } from '../core/i18n';
import { formatWeight, leftLabel, levelTone, lowLevel, originalWeight, percentLeft, shown, spoolFraction, spoolPaint, type Spool } from '../logic/spools';

// A printer slot holding a spool from the stock (assigned by hand, or linked by Bambu Cloud): the same facts as the
// spool's row in the list. `missing` is a slot whose spool is no longer in the list.
const props = defineProps<{ label: string; tool?: 1 | 2 | 3 | 4; spool?: Spool | null; missing?: boolean; emptyLabel?: string }>();
const f = computed(() => props.spool?.filament || {});
const pct = computed(() => (props.spool ? percentLeft(props.spool) : null));
const level = computed(() => lowLevel(props.spool?.remaining_weight, m.low));
// The drawn spool: Spoolman's weight; null when unknown (the full reel with the unknown badge), never a made-up level.
const fill = computed(() => spoolFraction(props.spool));
const ex = computed(() => shown(m.disp, 'exact_weight'));
const original = computed(() => (props.spool ? originalWeight(props.spool) : null));
const meta = computed(() => [shown(m.disp, 'vendor') ? f.value.vendor?.name : '', shown(m.disp, 'material') ? f.value.material : '',
  props.spool?.location && shown(m.disp, 'location') ? props.spool.location : ''].filter(Boolean).join(' · '));
</script>
<template>
  <OuiSlot :label="label" :tool="tool" :empty-label="emptyLabel ?? t('tray.empty')" :data-spool="spool?.id"
           :name="missing ? t('printer.notFound') : spool ? f.name || t('spool.numbered', { id: spool.id }) : null" :material="spool ? f.material : null"
           v-bind="spool ? spoolPaint(f) : {}" :remaining="fill" :initial="1">
    <template v-if="level" #state><OuiStatus :state="level === 'out' ? 'error' : 'warn'">{{ t(level === 'out' ? 'spool.out' : 'spool.low') }}</OuiStatus></template>
    <template #meta>{{ missing ? t('printer.notFoundHelp') : meta }}</template>
    <template #amount>
      <div v-if="spool" class="oui-slot-amount" data-test="weight">
        <p class="oui-num"><strong>{{ leftLabel(spool.remaining_weight, pct, m.wMode, ex, locale) }}</strong>
          <span v-if="m.wMode !== 'percent' && typeof original === 'number' && typeof spool.remaining_weight === 'number'" class="oui-muted">{{ ' ' + t('weight.of', { total: formatWeight(original, ex, locale) }) }}</span>
          <span v-if="m.wMode === 'both' && pct !== null && typeof spool.remaining_weight === 'number'" class="oui-muted">{{ ` · ${pct}%` }}</span></p>
        <OuiLevel v-if="shown(m.disp, 'bar')" :fraction="pct === null ? null : pct / 100" :tone="levelTone(level)" :label="pct === null ? t('spool.unknownLeft') : t('spool.pctLeft', { pct })" />
      </div>
    </template>
    <slot />
    <template v-if="$slots.actions" #actions><slot name="actions" /></template>
  </OuiSlot>
</template>
