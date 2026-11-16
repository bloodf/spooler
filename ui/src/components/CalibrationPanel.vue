<script setup lang="ts">
import Button from 'primevue/button';
import { OuiIcon, OuiPanel } from '../../shared/src/components';
import { save as saveIcon, spoolman } from '../../shared/src/icons';
import { m, answerCalibration, pending } from '../state/main';
import { t, tMaybe } from '../core/i18n';

// A saved copy of a Spooler preset changed calibrated values: nothing reaches Spoolman until Save here.
const label = (key: string) => tMaybe(`cal.key.${key}`, key);
</script>
<template>
  <OuiPanel v-for="a in m.calibration" :key="a.name" :title="t('cal.title')" :icon="spoolman" tone="magenta" data-test="calibration" :data-name="a.name">
    <p class="cal-text">{{ t('cal.text', { name: a.name }) }}</p>
    <table class="cal-table">
      <thead><tr><th scope="col">{{ t('cal.setting') }}</th><th scope="col">{{ t('cal.old') }}</th><th scope="col">{{ t('cal.new') }}</th></tr></thead>
      <tbody><tr v-for="c in a.changes" :key="c.key" :data-key="c.key">
        <th scope="row">{{ label(c.key) }}</th><td class="oui-num cal-old">{{ c.old || '—' }}</td><td class="oui-num cal-new">{{ c.new }}</td></tr></tbody>
    </table>
    <template #footer>
      <Button size="small" :label="t('cal.save')" :disabled="pending('send')" data-test="cal-save" @click="answerCalibration(a.name, true)">
        <template #icon><OuiIcon :icon="saveIcon" :size="14" /></template></Button>
      <Button severity="secondary" text size="small" :label="t('cal.skip')" :title="t('cal.skipHelp')" :disabled="pending('send')" data-test="cal-skip"
              @click="answerCalibration(a.name, false)" />
    </template>
  </OuiPanel>
</template>
<style>
.cal-text { margin-block-end: var(--oui-s3); overflow-wrap: anywhere; }
.cal-table { width: 100%; border-collapse: collapse; }
.cal-table :is(th, td) { padding: var(--oui-s1) var(--oui-s2); text-align: start; border-bottom: 1px solid var(--oui-border); }
.cal-table tr > :not(:first-child) { text-align: end; white-space: nowrap; }
.cal-table thead th { font-weight: 600; color: var(--oui-muted); }
.cal-table tbody th { font-weight: 500; overflow-wrap: anywhere; }
.cal-old { color: var(--oui-muted); text-decoration: line-through; }
.cal-new { font-weight: 700; }
</style>
