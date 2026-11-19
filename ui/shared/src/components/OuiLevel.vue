<script setup lang="ts">
import { computed } from 'vue';

/*
 * How much is left (filament on a spool, space on a card): green when fine, amber when `low`, red when `critical`,
 * always with the amount in text beside it. The filament's own colour is never used here.
 * An unknown amount shows an empty hatched track, not an empty bar.
 */
const props = defineProps<{ fraction: number | null | undefined; tone?: 'normal' | 'low' | 'critical'; label?: string }>();
const known = computed(() => typeof props.fraction === 'number' && Number.isFinite(props.fraction));
const pct = computed(() => (known.value ? Math.max(0, Math.min(1, props.fraction as number)) * 100 : 0));
</script>
<template>
  <span class="oui-level" role="meter" :aria-label="label" aria-valuemin="0" aria-valuemax="100" :aria-valuenow="known ? Math.round(pct) : undefined"
    :data-tone="tone ?? 'normal'" :data-unknown="!known || undefined"><span :style="{ width: pct + '%' }" /></span>
</template>
<style>
.oui-level { display: block; height: 6px; min-width: 32px; border-radius: 3px; background: var(--oui-border); overflow: hidden; }
.oui-level > span { display: block; height: 100%; min-width: 3px; border-radius: 3px; background: var(--oui-success); }
.oui-level[data-tone='low'] > span { background: var(--oui-warning); }
.oui-level[data-tone='critical'] > span { background: var(--oui-danger); }
.oui-level[data-unknown] { background: repeating-linear-gradient(135deg, var(--oui-border) 0 3px, transparent 3px 6px); }
.oui-level[data-unknown] > span { display: none; }
</style>
