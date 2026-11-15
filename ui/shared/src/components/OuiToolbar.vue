<script setup lang="ts">
/* The bar over a list or table: find and filter on the left, a short result summary, then the list's actions. */
defineProps<{ summary?: string; label?: string }>();
</script>
<template>
  <div class="oui-toolbar" role="group" :aria-label="label">
    <slot />
    <span v-if="summary" class="oui-toolbar-summary oui-meta oui-num" aria-live="polite">{{ summary }}</span>
    <div v-if="$slots.end" class="oui-toolbar-end"><slot name="end" /></div>
  </div>
</template>
<style>
.oui-toolbar { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); min-width: 0; padding: var(--oui-s2) var(--oui-s3); }
.oui-toolbar > :where(.p-inputtext, .p-iconfield) { flex: 1 1 180px; max-width: 320px; min-width: 0; }
.oui-toolbar-summary { margin-inline-start: var(--oui-s1); white-space: nowrap; }
.oui-toolbar-end { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); margin-inline-start: auto; }
</style>
