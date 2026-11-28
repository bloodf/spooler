<script setup lang="ts">
import { computed } from 'vue';
import { OuiIcon, OuiStatus } from '@orca-plugins/ui-foundation/src/components';
import { rfid } from '@orca-plugins/ui-foundation/src/icons';
import { m, inUse, plateSlots } from '../state/main';
import { t } from '../core/i18n';
import { LEVEL_KEY, driedDays, driedOld, lowLevel, shown, tagUids, type Spool } from '../logic/spools';

// What state a spool is in, as chips: its stock level, then the facts that follow the Display switches. In a card or
// the detail (`band`) every fact is a chip. In a table row they stay on one line: the level, the fact that matters most
// now, and "+n" for the rest, whose tooltip names them; the row leaves out a drying date that is not overdue.
const props = defineProps<{ spool: Spool; /** In a card or the detail: every fact, wrapping. */ band?: boolean }>();
const s = computed(() => props.spool);
const level = computed(() => lowLevel(s.value.remaining_weight, m.low));
interface Fact { key: string; text: string; title: string; tone?: string; icon?: boolean }
const facts = computed<Fact[]>(() => {
  const out: Fact[] = [];
  const plate = plateSlots.value.slots.get(s.value.id);
  // The row names the fact only; which slots, the unit and the slot are in the tooltip and in the detail.
  if (plate) out.push({ key: 'plate', text: props.band ? t('spool.onPlate', { slots: plate }) : t('spool.onPlateShort'), title: t('spool.onPlate', { slots: plate }), tone: 'cobalt' });
  const where = shown(m.disp, 'in_use') ? inUse.value.get(String(s.value.id)) : '';
  if (where) out.push({ key: 'in-use', text: t('spool.inUse', { where: props.band ? where : where.split(' · ')[0] }), title: t('spool.loadedIn', { where }) });
  if (s.value.use_first && shown(m.disp, 'use_first') && !s.value.archived && level.value !== 'empty') out.push({ key: 'use-first', text: t('spool.useFirst'), title: t('spool.useFirstHelp') });
  const dried = shown(m.disp, 'dried') ? driedDays(s.value) : null;
  if (dried !== null && (props.band || driedOld(s.value, dried))) out.push({ key: 'dried', text: dried === 0 ? t('spool.driedToday') : t('spool.driedAgo', { n: dried }),
    title: driedOld(s.value, dried) ? t('spool.driedOld', { days: s.value.dry_days }) : t('spool.driedHelp'), tone: driedOld(s.value, dried) ? 'warn' : undefined });
  if (s.value.archived) out.push({ key: 'archived', text: t('spool.archived'), title: t('spool.archived') });
  const tags = shown(m.disp, 'rfid') ? tagUids(s.value) : [];
  if (tags.length) out.push({ key: 'rfid', text: 'RFID', title: t('spool.rfid', { tags: tags.join(', ') }), icon: true });
  return out;
});
const drawn = computed(() => (props.band ? facts.value : facts.value.slice(0, 1)));
const rest = computed(() => (props.band ? [] : facts.value.slice(1)));
</script>
<template>
  <span class="sp-chips" :data-band="band || undefined">
    <OuiStatus v-if="level" :state="level === 'low' ? 'warn' : 'error'" :title="t(LEVEL_KEY[level])" :data-level="level">{{ t(LEVEL_KEY[level]) }}</OuiStatus>
    <span v-for="c in drawn" :key="c.key" class="oui-chip" :data-chip="c.key" :data-tone="c.tone" :data-test="c.key === 'dried' ? 'dried' : undefined" :title="c.title">
      <OuiIcon v-if="c.icon" :icon="rfid" :size="12" /><span class="oui-truncate">{{ c.text }}</span></span>
    <span v-if="rest.length" class="oui-chip oui-num sp-more" data-chip="more" tabindex="0" :title="rest.map(c => c.text).join(' · ')">+{{ rest.length }}<span class="oui-sr">: {{ rest.map(c => c.text).join(', ') }}</span></span>
  </span>
</template>
<style>
.sp-chips { display: flex; flex-wrap: nowrap; align-items: center; gap: var(--oui-s1); min-width: 0; }
.sp-chips[data-band] { flex-wrap: wrap; }
.sp-chips:empty { display: none; }
.sp-chips > .oui-chip { max-width: 100%; min-width: 0; }
.sp-chips > .oui-status, .sp-chips > .sp-more { flex: none; }
</style>
