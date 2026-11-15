<script setup lang="ts">
import OuiPanel from './OuiPanel.vue';
import type { OuiIconData } from '../icons';
import type { OuiTone } from './tones';

/* One topic of a settings page. The description says, once, what the rows below would otherwise each repeat. */
defineProps<{ id?: string; title: string; icon?: OuiIconData; tone?: OuiTone; description?: string }>();
</script>
<template>
  <OuiPanel :id="id" class="oui-formsection" :title="title" :icon="icon" :tone="tone" flush tabindex="-1">
    <template v-if="$slots.status" #meta><slot name="status" /></template>
    <template v-if="$slots.actions" #actions><slot name="actions" /></template>
    <p v-if="description" class="oui-formsection-desc oui-meta">{{ description }}</p>
    <div class="oui-formsection-rows"><slot /></div>
    <template v-if="$slots.footer" #footer><slot name="footer" /></template>
  </OuiPanel>
</template>
<style>
.oui-formsection { container: oui-form / inline-size; }
.orca-ui .oui-formsection:focus { outline: none; }
.oui-formsection-desc { padding: var(--oui-s3) var(--oui-s4) 0; max-width: 72ch; }
.oui-formsection-rows > * + * { border-top: 1px solid var(--oui-border); }
</style>
