<script setup lang="ts">
import { computed } from 'vue';
import Dialog from 'primevue/dialog';
import Button from 'primevue/button';
import { OuiSwatch } from '../../shared/src/components';
import { m, words } from '../state/main';
import { answerPick } from '../state/printers';
import { dialog } from '../core/dialog';
import { t, locale } from '../core/i18n';
import { formatWeight, shown, spoolPaint, type Spool } from '../logic/spools';
import { unitLabel } from '../logic/printers';

// After a slice, a filament that matched several spools: the user says which one is loaded on the slot it goes on.
// One at a time, never over another dialog; "Leave it as it is" changes nothing.
const pick = computed(() => (dialog.visible ? null : m.slicePicks[0] ?? null));
const slot = computed(() => {
  const x = pick.value;
  const p = x && m.cfg.find(c => c.id === x.printer);
  const u = p?.units[x?.unit ?? -1];
  if (!x || !p || !u) return x ? `#${x.n}` : '';
  return u.kind === 'gate' ? words.value.gateN(x.slot + 1) : unitLabel(p, u, words.value);
});
const spools = computed(() => (pick.value?.spools ?? []).map(id => m.spools.find(s => s.id === id)).filter((s): s is Spool => !!s && !s.archived));
function answer(spool: number | null) { if (pick.value) answerPick(pick.value, spool); }
</script>
<template>
  <Dialog :visible="!!pick" modal :header="pick ? t('pick.title', { slot }) : ''" :draggable="false" data-test="slice-pick"
          :style="{ width: 'min(460px, calc(100vw - 32px))' }" :close-button-props="{ severity: 'secondary', text: true, rounded: true, 'aria-label': t('common.close') }"
          @update:visible="v => { if (!v) answer(null); }">
    <div v-if="pick" class="oui-stack">
      <p>{{ t('pick.text', { n: pick.n, material: pick.material || '?', printer: pick.name, slot }) }}</p>
      <div class="pk-list" role="group" :aria-label="t('pick.label', { n: pick.n })">
        <button v-for="s in spools" :key="s.id" type="button" class="pk-item" :data-pick="s.id" @click="answer(s.id)">
          <OuiSwatch v-bind="spoolPaint(s.filament || {})" :size="14" />
          <span class="pk-t"><span class="oui-truncate">{{ s.filament?.name || t('spool.numbered', { id: s.id }) }}</span>
            <small class="oui-meta oui-truncate">{{ [s.filament?.vendor?.name, '#' + s.id, s.location].filter(Boolean).join(' · ') }}</small></span>
          <span class="oui-num">{{ formatWeight(s.remaining_weight, shown(m.disp, 'exact_weight'), locale) }}</span>
        </button>
      </div>
    </div>
    <template #footer><Button severity="secondary" :label="t('pick.leave')" data-test="pick-leave" @click="answer(null)" /></template>
  </Dialog>
</template>
