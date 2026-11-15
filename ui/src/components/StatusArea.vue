<script setup lang="ts">
import { computed } from 'vue';
import Button from 'primevue/button';
import { OuiBanner } from '../../shared/src/components';
import { m, dismiss } from '../state/main';
import { t, fmt } from '../core/i18n';

// B-20: results are announced; errors and unknown outcomes stay until dismissed (no 8 s expiry), each with time.
const tone = { error: 'error', unknown: 'warn', success: 'success', info: 'info', pending: 'neutral' } as const;
const lasting = computed(() => m.notes.filter(n => n.kind === 'error' || n.kind === 'unknown'));
const passing = computed(() => m.notes.filter(n => n.kind !== 'error' && n.kind !== 'unknown'));
</script>
<template>
  <section class="sa" :aria-label="t('status.region')">
    <!-- Both live regions stay rendered (an empty region announces what is added later); only filled ones take space. -->
    <div role="alert" class="sa-stack">
      <OuiBanner v-for="n in lasting" :key="n.id" :tone="tone[n.kind]" :title="n.kind === 'error' ? t('status.errorPrefix') : t('status.unknownPrefix')">
        {{ n.text }} <span class="oui-meta">{{ fmt.time(n.at / 1000) }}</span>
        <template #actions><Button severity="secondary" text size="small" :label="t('common.dismiss')" @click="dismiss(n.id)" /></template>
      </OuiBanner>
    </div>
    <div role="status" aria-live="polite" class="sa-stack">
      <OuiBanner v-for="n in passing" :key="n.id" :tone="tone[n.kind]" :title="n.text" />
    </div>
  </section>
</template>
<style>
.sa, .sa-stack { display: grid; gap: var(--oui-s2); }
.sa:not(:has(.oui-banner)) { display: none; }
.sa-stack:empty { display: none; }
</style>
