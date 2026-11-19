<script setup lang="ts">
/*
 * The first line of every main page, under the app bar: what this page is showing (a printer, a list, a quote), one line
 * of facts about it, and the page's own actions on the right, at most one of them primary. Not sticky, and never coloured.
 */
defineProps<{ title: string; meta?: string }>();
</script>
<template>
  <div class="oui-pagehead">
    <div v-if="$slots.lead" class="oui-pagehead-lead"><slot name="lead" /></div>
    <div class="oui-pagehead-id">
      <h2 class="oui-pagehead-title oui-truncate" :title="title">{{ title }}</h2>
      <p v-if="meta || $slots.meta" class="oui-pagehead-meta oui-meta oui-truncate"><slot name="meta">{{ meta }}</slot></p>
    </div>
    <div v-if="$slots.actions" class="oui-pagehead-actions"><slot name="actions" /></div>
  </div>
</template>
<style>
.oui-pagehead { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2) var(--oui-s3); min-height: 32px; min-width: 0; }
.oui-pagehead-lead { flex: none; display: flex; align-items: center; }
.oui-pagehead-id { flex: 1 1 200px; display: flex; flex-wrap: wrap; align-items: baseline; gap: 0 var(--oui-s3); min-width: 0; }
.orca-ui .oui-pagehead-title { font-size: var(--oui-text-lg); font-weight: 700; letter-spacing: -.005em; }
.oui-pagehead-meta { min-width: 0; }
.oui-pagehead-actions { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); margin-inline-start: auto; }
</style>
