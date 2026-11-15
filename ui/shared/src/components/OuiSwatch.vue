<script setup lang="ts">
import { computed } from 'vue';

/* A filament colour. Always ringed, so black, white and transparent filaments stay visible on any surface. */
const props = defineProps<{ color?: string | null; /** Multi-colour filament: painted side by side. */ colors?: string[] | null; size?: number }>();
const paint = computed(() => {
  const list = props.colors && props.colors.length > 1 ? props.colors : null;
  if (list) return 'linear-gradient(90deg, ' + list.map((c, i) => `${c} ${(i * 100) / list.length}% ${((i + 1) * 100) / list.length}%`).join(', ') + ')';
  return props.color || '';
});
</script>
<template>
  <span class="oui-swatch" :data-unknown="!paint || undefined" :style="{ '--oui-swatch': paint || undefined, width: (size ?? 12) + 'px', height: (size ?? 12) + 'px' }" aria-hidden="true" />
</template>
<style>
.oui-swatch { flex: none; display: inline-block; border-radius: 50%; background: var(--oui-swatch); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-text) 38%, transparent); }
.oui-swatch[data-unknown] { background: repeating-linear-gradient(135deg, transparent 0 2px, color-mix(in srgb, var(--oui-muted) 60%, transparent) 2px 3px); }
</style>
