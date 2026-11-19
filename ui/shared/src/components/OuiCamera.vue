<script setup lang="ts">
import { computed, useSlots } from 'vue';
import OuiEmpty from './OuiEmpty.vue';
import { cameraOff } from '../icons';

/*
 * The camera module's picture: a 16:9 box that keeps its size whatever the camera is doing, so the dashboard does not
 * jump when it turns on. Live: the picture, with what the page puts over it (`#overlay`: the rate, the time). Off,
 * loading and failed: one sentence and the way out, in the same box. The module's actions (rate, snapshot, on/off) go
 * in the OuiPanel header, not here. A page that plays the stream itself (a <video>, a canvas) puts its player in `#picture`
 * and says `state="live"`: give it the class `oui-camera-picture` and it fills the box like the built-in image.
 */
const emit = defineEmits<{ /** The built-in picture has loaded a frame (each time `src` changes and loads). Not fired for a player in `#picture`. */ frame: [picture: HTMLImageElement] }>();
const props = defineProps<{ /** `cover` (default) fills the 16:9 box and crops what does not fit; `contain` shows the whole picture, with bars when it is not 16:9. */ fit?: 'cover' | 'contain';
  src?: string | null; alt: string; state?: 'live' | 'off' | 'loading' | 'error'; /** One sentence for off, loading and error. */ title?: string; text?: string }>();
const slots = useSlots();
// Live only when there is something to show: a picture address, or the page's own player.
const shown = computed(() => { const state = props.state ?? (props.src ? 'live' : 'off'); return state === 'live' && !props.src && !slots.picture ? 'off' : state; });
</script>
<template>
  <div class="oui-camera" :data-state="shown" :data-fit="fit === 'contain' ? 'contain' : undefined">
    <template v-if="shown === 'live'"><slot name="picture"><img v-if="src" class="oui-camera-picture" :src="src" :alt="alt" draggable="false" @load="emit('frame', $event.target as HTMLImageElement)"></slot></template>
    <OuiEmpty v-else :state="shown === 'loading' ? 'loading' : shown === 'error' ? 'error' : 'empty'" :icon="cameraOff" :title="title ?? alt" :text="text">
      <template v-if="$slots.actions" #actions><slot name="actions" /></template>
    </OuiEmpty>
    <div v-if="$slots.overlay && shown === 'live'" class="oui-camera-overlay"><slot name="overlay" /></div>
  </div>
</template>
<style>
.oui-camera { position: relative; display: grid; aspect-ratio: 16 / 9; min-height: 120px; overflow: hidden; background: var(--oui-inset); border-radius: 0 0 var(--oui-radius-lg) var(--oui-radius-lg); }
.oui-camera-picture { display: block; width: 100%; height: 100%; min-height: 0; object-fit: cover; }
.oui-camera[data-fit='contain'] .oui-camera-picture { object-fit: contain; }
.oui-camera > .oui-empty { min-height: 0; }
.oui-camera-overlay { position: absolute; inset: auto var(--oui-s2) var(--oui-s2); display: flex; flex-wrap: wrap; gap: var(--oui-s1); pointer-events: none; }
/* Chips over a picture need their own ground: the picture can be any colour. */
.oui-camera-overlay > .oui-chip { color: #fff; background: rgb(0 0 0 / .62); box-shadow: none; }
</style>
