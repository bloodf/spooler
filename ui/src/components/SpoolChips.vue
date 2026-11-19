<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiIcon, OuiStatus } from '../../shared/src/components';
import { rfid, store } from '../../shared/src/icons';
import * as bridge from '../core/bridge';
import { m, inUse, plateSlots } from '../state/main';
import { t } from '../core/i18n';
import { LEVEL_KEY, driedDays, driedOld, lowLevel, shown, tagUids, type Spool } from '../logic/spools';

// What state a spool is in, as chips: its stock level, then the facts that follow the Display switches.
const props = defineProps<{ spool: Spool; /** In the detail's accent block: facts only, no button. */ band?: boolean }>();
const s = computed(() => props.spool);
const level = computed(() => lowLevel(s.value.remaining_weight, m.low));
const where = computed(() => (shown(m.disp, 'in_use') ? inUse.value.get(String(s.value.id)) : ''));
const plate = computed(() => plateSlots.value.slots.get(s.value.id));
const dried = computed(() => (shown(m.disp, 'dried') ? driedDays(s.value) : null));
const tags = computed(() => (shown(m.disp, 'rfid') ? tagUids(s.value) : []));
const cartQuery = computed(() => [s.value.filament?.vendor?.name, s.value.lot_nr || s.value.filament?.name || t('spool.numbered', { id: s.value.id })].filter(Boolean).join(' '));
const cart = computed(() => !props.band && m.cart && typeof s.value.remaining_weight === 'number' && s.value.remaining_weight < m.low);
</script>
<template>
  <span class="sp-chips">
    <OuiStatus v-if="level" :state="level === 'low' ? 'warn' : 'error'" :title="t(LEVEL_KEY[level])" :data-level="level">{{ t(LEVEL_KEY[level]) }}</OuiStatus>
    <Button v-if="cart" severity="secondary" text size="small" class="sp-cart" :aria-label="t('spool.reorder', { q: cartQuery })" :title="t('spool.reorder', { q: cartQuery })"
            data-test="cart" @click.stop="bridge.postMain({ type: 'order', query: cartQuery })"><template #icon><OuiIcon :icon="store" :size="14" /></template></Button>
    <span v-if="s.use_first && shown(m.disp, 'use_first') && !s.archived && level !== 'empty'" class="oui-chip" data-tone="accent" data-solid data-chip="use-first" :title="t('spool.useFirstHelp')">{{ t('spool.useFirst') }}</span>
    <span v-if="plate" class="oui-chip" data-tone="accent" :title="t('spool.onPlate', { slots: plate })"><span class="oui-truncate">{{ t('spool.onPlate', { slots: plate }) }}</span></span>
    <span v-if="where" class="oui-chip" :title="t('spool.loadedIn', { where })"><span class="oui-truncate">{{ t('spool.inUse', { where }) }}</span></span>
    <span v-if="dried !== null" class="oui-chip" :data-tone="driedOld(s, dried) ? 'warn' : undefined" data-test="dried"
          :title="driedOld(s, dried) ? t('spool.driedOld', { days: s.dry_days }) : t('spool.driedHelp')">{{ dried === 0 ? t('spool.driedToday') : t('spool.driedAgo', { n: dried }) }}</span>
    <span v-if="tags.length" class="oui-chip" :title="t('spool.rfid', { tags: tags.join(', ') })"><OuiIcon :icon="rfid" :size="12" />RFID</span>
    <span v-if="s.archived" class="oui-chip">{{ t('spool.archived') }}</span>
  </span>
</template>
<style>
.sp-chips { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s1); min-width: 0; }
.sp-chips:empty { display: none; }
.sp-chips > .oui-chip { max-width: 100%; }
.sp-cart.p-button { width: 22px; height: 22px; padding: 0; }
</style>
