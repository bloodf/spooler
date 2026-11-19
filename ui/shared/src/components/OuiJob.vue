<script setup lang="ts">
import { computed } from 'vue';

/*
 * A running or finished job (a print, an arrange run) as one compact status block: a small picture, what it is, how far,
 * the times, and what you can do to it. One row when there is room, two under 1100 px, stacked under 640 px. It is a
 * neutral block: the only colour is the state chip and OrcaSlicer's teal in the bar. Unknown progress is an indeterminate
 * bar and a dash, not 0 %. A `stale` job (last known values) is drawn grey.
 */
const props = defineProps<{ name: string; /** 0..100, or null when the job reports no fraction. */ progress?: number | null;
  progressLabel?: string; /** Replaces the percentage (for counted work: "7 of 14"). */ count?: string; detail?: string;
  /** Always stacked and smaller: for the dock. */ compact?: boolean; /** @deprecated 5.0: there is no filled hero; the block is the same everywhere. */ hero?: boolean;
  /** Last known values of a job the page can no longer see. */ stale?: boolean }>();
const known = computed(() => typeof props.progress === 'number' && Number.isFinite(props.progress));
const pct = computed(() => (known.value ? Math.max(0, Math.min(100, props.progress as number)) : 0));
</script>
<template>
  <div class="oui-job" :data-compact="compact || undefined" :data-stale="stale || undefined"><div class="oui-job-block" :data-thumb="$slots.thumb ? true : undefined">
    <div v-if="$slots.thumb" class="oui-job-thumb"><slot name="thumb" /></div>
    <div class="oui-job-id">
      <div v-if="$slots.status" class="oui-job-status"><slot name="status" /></div>
      <p class="oui-job-name" :title="name">{{ name }}</p>
      <p v-if="detail" class="oui-job-detail oui-num oui-truncate">{{ detail }}</p>
    </div>
    <div class="oui-job-progress">
      <div class="oui-job-figure oui-num"><template v-if="count">{{ count }}</template><template v-else-if="known">{{ Math.round(pct) }}<span>%</span></template><span v-else aria-hidden="true">—</span></div>
      <div class="oui-job-bar" role="progressbar" :aria-label="progressLabel ?? name" aria-valuemin="0" aria-valuemax="100" :aria-valuenow="known ? Math.round(pct) : undefined"
        :data-indeterminate="!known || undefined"><span :style="known ? { width: pct + '%' } : undefined" /></div>
    </div>
    <div v-if="$slots.default" class="oui-job-stats"><slot /></div>
    <div v-if="$slots.actions" class="oui-job-actions"><slot name="actions" /></div>
  </div></div>
</template>
<style>
.oui-job { container: oui-job / inline-size; min-width: 0; }
/* Stacked (narrow, and always in the dock). */
.oui-job-block { display: grid; grid-template-columns: minmax(0, 1fr); align-items: center; gap: var(--oui-s3) var(--oui-s5); min-width: 0; }
.oui-job-block[data-thumb] { grid-template-columns: auto minmax(0, 1fr); }
.oui-job-block[data-thumb] > :not(.oui-job-thumb, .oui-job-id) { grid-column: 1 / -1; }
/* The picture is small and fixed: 72 px, whatever the image. It is never the tallest thing in the block. */
.oui-job-thumb { display: grid; place-items: center; width: 72px; height: 72px; overflow: hidden; border-radius: var(--oui-radius); background: var(--oui-inset); box-shadow: inset 0 0 0 1px var(--oui-border); }
.oui-job-thumb > :is(img, svg) { display: block; max-width: 100%; max-height: 100%; object-fit: contain; }
.oui-job-id { display: grid; gap: 2px; min-width: 0; }
.oui-job-status { margin-bottom: 2px; }
/* File names are long and their end matters (material, time): two lines, broken anywhere, before an ellipsis. */
.oui-job-name { font-size: var(--oui-text-lg); font-weight: 700; line-height: 1.3; overflow: hidden; overflow-wrap: anywhere; display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2; line-clamp: 2; }
.oui-job-detail { font-size: var(--oui-text-sm); color: var(--oui-muted); }
.oui-job-progress { display: flex; align-items: center; gap: var(--oui-s3); min-width: 0; }
.oui-job-figure { flex: none; min-width: 2.4ch; font-size: var(--oui-text-2xl); line-height: 1; font-weight: 700; letter-spacing: -.02em; }
.oui-job-figure > span { margin-inline-start: .08em; font-size: .5em; font-weight: 600; letter-spacing: 0; color: var(--oui-muted); }
.oui-job-bar { flex: 1 1 0; min-width: 60px; height: 8px; border-radius: 4px; background: var(--oui-border); overflow: hidden; }
.oui-job-bar > span { display: block; height: 100%; border-radius: inherit; background: var(--oui-primary-mark); transition: width .4s linear; }
.oui-job-bar[data-indeterminate] > span { width: 32%; animation: oui-slide 1.4s var(--oui-ease) infinite; }
.oui-job-stats { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2) var(--oui-s5); }
.oui-job-actions { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); }
@container oui-job (min-width: 640px) {
  .oui-job:not([data-compact]) > .oui-job-block { grid-template-columns: minmax(0, 1fr) minmax(0, 1fr); }
  .oui-job:not([data-compact]) > .oui-job-block[data-thumb] { grid-template-columns: auto minmax(0, 1fr) minmax(0, 1fr); }
  .oui-job:not([data-compact]) > .oui-job-block > :is(.oui-job-id, .oui-job-progress, .oui-job-stats, .oui-job-actions) { grid-column: auto; }
  .oui-job:not([data-compact]) > .oui-job-block[data-thumb] > .oui-job-thumb { grid-row: span 2; }
  .oui-job:not([data-compact]) > .oui-job-block > .oui-job-actions { justify-content: flex-end; }
}
@container oui-job (min-width: 1100px) {
  .oui-job:not([data-compact]) > .oui-job-block { grid-template-columns: minmax(180px, 1fr) minmax(220px, 1.1fr) auto auto; }
  .oui-job:not([data-compact]) > .oui-job-block[data-thumb] { grid-template-columns: auto minmax(180px, 1fr) minmax(220px, 1.1fr) auto auto; }
  .oui-job:not([data-compact]) > .oui-job-block[data-thumb] > .oui-job-thumb { grid-row: auto; }
}
.oui-job[data-compact] .oui-job-block { gap: var(--oui-s2); }
.oui-job[data-compact] .oui-job-name { font-size: var(--oui-text-md); -webkit-line-clamp: 1; line-clamp: 1; }
.oui-job[data-compact] .oui-job-figure { font-size: var(--oui-text-xl); }
.oui-job[data-compact] .oui-job-thumb { width: 44px; height: 44px; }
.oui-job[data-stale] .oui-job-bar > span { background: var(--oui-control-border); }
.oui-job[data-stale] .oui-job-figure { color: var(--oui-muted); }
@keyframes oui-slide { from { transform: translateX(-100%); } to { transform: translateX(320%); } }
</style>
