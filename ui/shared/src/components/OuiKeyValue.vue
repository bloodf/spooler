<script setup lang="ts">
/* Facts about one object as an aligned list. A missing value is a dash, never 0 or an empty cell. */
export interface OuiFact { label: string; value?: string | number | null; mono?: boolean }
defineProps<{ items: OuiFact[]; /** Label above value, in columns: for a row of a few facts. */ inline?: boolean }>();
</script>
<template>
  <dl class="oui-kv" :data-inline="inline || undefined">
    <div v-for="item in items" :key="item.label" class="oui-kv-row">
      <dt>{{ item.label }}</dt>
      <dd :class="{ 'oui-mono': item.mono }" class="oui-num">{{ item.value == null || item.value === '' ? '—' : item.value }}</dd>
    </div>
  </dl>
</template>
<style>
.oui-kv { display: grid; grid-template-columns: max-content minmax(0, 1fr); gap: 6px var(--oui-s4); }
.oui-kv-row { display: contents; }
.oui-kv dt { color: var(--oui-muted); }
.oui-kv dd { min-width: 0; overflow-wrap: anywhere; }
.oui-kv[data-inline] { display: flex; flex-wrap: wrap; gap: var(--oui-s3) var(--oui-s6); }
.oui-kv[data-inline] .oui-kv-row { display: grid; gap: 2px; }
.oui-kv[data-inline] dt { font-size: var(--oui-text-xs); font-weight: 600; letter-spacing: .05em; text-transform: uppercase; }
.oui-kv[data-inline] dd { font-weight: 600; }
</style>
