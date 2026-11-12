<script setup lang="ts">
import { computed } from 'vue';
import Message from 'primevue/message';
import Button from 'primevue/button';
import { m, dismiss } from '../state/main';
import { t, fmt } from '../core/i18n';

// B-20: results are announced; errors and unknown outcomes stay until dismissed (no 8 s expiry), each with time.
const sev = { error: 'error', unknown: 'warn', success: 'success', info: 'info', pending: 'secondary' } as const;
const lasting = computed(() => m.notes.filter(n => n.kind === 'error' || n.kind === 'unknown'));
const passing = computed(() => m.notes.filter(n => n.kind !== 'error' && n.kind !== 'unknown'));
</script>
<template>
  <section class="sa" :aria-label="t('status.region')">
    <div role="alert" class="sa-stack">
      <Message v-for="n in lasting" :key="n.id" :severity="sev[n.kind]">
        <div class="sa-row"><span><strong>{{ n.kind === 'error' ? t('status.errorPrefix') : t('status.unknownPrefix') }}</strong> {{ n.text }}
          <span class="oui-meta">{{ fmt.time(n.at / 1000) }}</span></span>
          <Button text size="small" :label="t('common.dismiss')" @click="dismiss(n.id)" /></div>
      </Message>
    </div>
    <div role="status" aria-live="polite" class="sa-stack">
      <Message v-for="n in passing" :key="n.id" :severity="sev[n.kind]">{{ n.text }}</Message>
    </div>
  </section>
</template>
<style scoped>
.sa { display: grid; }
/* Both live regions stay rendered (an empty region announces what is added later); only filled ones take space. */
.sa-stack { display: grid; gap: 8px; }
.sa-stack:not(:empty) { margin-bottom: 16px; }
.sa-row { display: flex; align-items: center; justify-content: space-between; gap: 12px; flex-wrap: wrap; }
</style>
