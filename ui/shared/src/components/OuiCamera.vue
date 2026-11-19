<script setup lang="ts">
import OuiEmpty from './OuiEmpty.vue';
import { cameraOff } from '../icons';

/*
 * The camera module's picture: a 16:9 box that keeps its size whatever the camera is doing, so the dashboard does not
 * jump when it turns on. Live: the picture, with what the page puts over it (`#overlay`: the rate, the time). Off,
 * loading and failed: one sentence and the way out, in the same box. The module's actions (rate, snapshot, on/off) go
 * in the OuiPanel header, not here.
 */
defineProps<{ src?: string | null; alt: string; state?: 'live' | 'off' | 'loading' | 'error'; /** One sentence for off, loading and error. */ title?: string; text?: string }>();
</script>
<template>
  <div class="oui-camera" :data-state="state ?? (src ? 'live' : 'off')">
    <img v-if="src && (state ?? 'live') === 'live'" class="oui-camera-picture" :src="src" :alt="alt" draggable="false">
    <OuiEmpty v-else :state="state === 'loading' ? 'loading' : state === 'error' ? 'error' : 'empty'" :icon="cameraOff" :title="title ?? alt" :text="text">
      <template v-if="$slots.actions" #actions><slot name="actions" /></template>
    </OuiEmpty>
    <div v-if="$slots.overlay && src && (state ?? 'live') === 'live'" class="oui-camera-overlay"><slot name="overlay" /></div>
  </div>
</template>
<style>
.oui-camera { position: relative; display: grid; aspect-ratio: 16 / 9; min-height: 120px; overflow: hidden; background: var(--oui-inset); border-radius: 0 0 var(--oui-radius-lg) var(--oui-radius-lg); }
.oui-camera-picture { display: block; width: 100%; height: 100%; object-fit: cover; }
.oui-camera > .oui-empty { min-height: 0; }
.oui-camera-overlay { position: absolute; inset: auto var(--oui-s2) var(--oui-s2); display: flex; flex-wrap: wrap; gap: var(--oui-s1); pointer-events: none; }
/* Chips over a picture need their own ground: the picture can be any colour. */
.oui-camera-overlay > .oui-chip { color: #fff; background: rgb(0 0 0 / .62); box-shadow: none; }
</style>
