<script setup lang="ts">
import { OuiStatus, type OuiState } from '../../shared/src/components';

// One requirement: name, status, why it is needed and how to get it. Kept apart so ui-foundation's
// OuiRequirement can replace it later.
const props = defineProps<{ name: string; status: 'ok' | 'missing' | 'unknown'; label: string; details?: string; why: string; steps?: string[]; code?: string }>();
const STATE: Record<string, OuiState> = { ok: 'ok', missing: 'error', unknown: 'pending' };
</script>
<template>
  <div class="rq" :data-req-status="props.status">
    <p class="oui-row rq-head"><strong>{{ name }}</strong><OuiStatus :state="STATE[status]" data-test="req-status">{{ label }}</OuiStatus>
      <span v-if="details" class="oui-meta rq-details">{{ details }}</span></p>
    <p class="oui-meta">{{ why }}</p>
    <template v-if="status !== 'ok'">
      <pre v-if="code" class="oui-mono oui-well rq-code">{{ code }}</pre>
      <ul v-if="steps?.length" class="rq-steps"><li v-for="s in steps" :key="s" class="oui-meta">{{ s }}</li></ul>
    </template>
    <div class="oui-row"><slot /></div>
  </div>
</template>
<style scoped>
.rq { display: grid; gap: var(--oui-s1); }
.rq p { margin: 0; }
.rq-head { gap: var(--oui-s2); }
.rq-details { overflow-wrap: anywhere; }
.rq-code { margin: 0; padding: var(--oui-s2); white-space: pre-wrap; overflow-wrap: anywhere; user-select: all; }
.rq-steps { margin: 0; padding-inline-start: 1.2em; display: grid; gap: 2px; }
</style>
