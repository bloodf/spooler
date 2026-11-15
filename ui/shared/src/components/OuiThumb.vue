<script setup lang="ts">
import { ref, watch } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { box, type OuiIconData } from '../icons';

/*
 * A picture in a list or table. The box has a fixed pixel size, whatever the picture's own proportions, so one
 * tall image cannot stretch a row; the picture is fitted inside it, never cropped or distorted.
 */
const props = defineProps<{ src?: string | null; alt?: string; size?: number; icon?: OuiIconData }>();
const failed = ref(false);
watch(() => props.src, () => { failed.value = false; });
</script>
<template>
  <span class="oui-thumb" :style="{ width: (size ?? 36) + 'px', height: (size ?? 36) + 'px' }">
    <img v-if="src && !failed" :src="src" :alt="alt ?? ''" :width="size ?? 36" :height="size ?? 36" :style="{ width: (size ?? 36) + 'px', height: (size ?? 36) + 'px' }"
      draggable="false" @error="failed = true">
    <slot v-else><OuiIcon :icon="icon ?? box" :size="Math.min(20, Math.round((size ?? 36) / 2))" /></slot>
  </span>
</template>
<style>
/* Box and image both get the same width and height in px. Not aspect-ratio and not height: 100%: a percentage height
   does not resolve against an auto-sized box or grid track (and, in WebKit, against an aspect-ratio box in a table cell),
   and the picture's own proportions then set the size of the row. */
.oui-thumb { flex: none; display: inline-flex; align-items: center; justify-content: center; overflow: hidden; border-radius: var(--oui-radius-sm); color: var(--oui-muted);
  background: var(--oui-inset); box-shadow: inset 0 0 0 1px var(--oui-border); vertical-align: middle; }
.oui-thumb > img { display: block; flex: none; object-fit: contain; }
</style>
