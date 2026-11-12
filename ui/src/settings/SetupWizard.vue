<script setup lang="ts">
import { computed } from 'vue';
import Dialog from 'primevue/dialog';
import Button from 'primevue/button';
import SourceBlock from './SourceBlock.vue';
import { t } from '../core/i18n';
import { wizard, ready, closeWizard } from './state';
import { restoreFocus } from '../core/dialog';

// First-run guide: six steps; step 2 holds the real source controls and Next waits for a passing test.
const STEPS = 6;
const canNext = computed(() => wizard.step !== 1 || ready.value);
const last = computed(() => wizard.step === STEPS - 1);
function next() { if (!canNext.value) return; if (last.value) closeWizard(true); else wizard.step += 1; }
function back() { if (wizard.step > 0) wizard.step -= 1; }
</script>
<template>
  <Dialog :visible="wizard.open" modal :header="t(`wiz.title.${wizard.step}` as any)" :draggable="false" :closable="true" :close-button-props="{ severity: 'secondary', text: true, rounded: true, 'aria-label': t('wiz.skip') }"
          :style="{ width: 'min(620px, calc(100vw - 32px))' }" data-test="wizard" @update:visible="v => { if (!v) closeWizard(false); }" @after-hide="restoreFocus">
    <p class="oui-meta" data-test="wiz-count">{{ t('wiz.count', { n: wizard.step + 1, total: STEPS }) }}</p>
    <div v-if="wizard.step === 0" class="wz"><p>{{ t('wiz.0') }}</p></div>
    <div v-else-if="wizard.step === 1" class="wz"><SourceBlock /><p class="oui-meta">{{ t('wiz.1') }}</p></div>
    <div v-else-if="wizard.step === 2" class="wz"><p>{{ t('wiz.2') }}</p></div>
    <div v-else-if="wizard.step === 3" class="wz"><p>{{ t('wiz.3') }}</p></div>
    <div v-else-if="wizard.step === 4" class="wz"><p>{{ t('wiz.4a') }}</p><p>{{ t('wiz.4b') }}</p></div>
    <div v-else class="wz"><ul><li>{{ t('wiz.5a') }}</li><li>{{ t('wiz.5b') }}</li><li>{{ t('wiz.5c') }}</li></ul><p>{{ t('wiz.5') }}</p></div>
    <div class="wz-dots" aria-hidden="true"><i v-for="i in STEPS" :key="i" :class="{ on: i - 1 === wizard.step }" /></div>
    <template #footer>
      <Button v-if="!last" severity="secondary" text :label="t('wiz.skip')" data-test="wiz-skip" @click="closeWizard(false)" />
      <span class="sp-grow" />
      <Button severity="secondary" outlined :label="t('wiz.back')" :disabled="wizard.step === 0" data-test="wiz-back" @click="back" />
      <Button :label="last ? t('wiz.finish') : t('wiz.next')" :disabled="!canNext" data-test="wiz-next" autofocus @click="next" />
    </template>
    <p v-if="wizard.step === 1 && !ready" class="sp-why">{{ t('wiz.needTest') }}</p>
  </Dialog>
</template>
<style scoped>
.wz { display: grid; gap: 8px; } .wz p { margin: 0; }
.wz-dots { display: flex; gap: 6px; justify-content: center; margin-top: 12px; }
.wz-dots i { width: 8px; height: 8px; border-radius: 50%; background: var(--oui-border); } .wz-dots i.on { background: var(--p-primary-color); }
</style>
