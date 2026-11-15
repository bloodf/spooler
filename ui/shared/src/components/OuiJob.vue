<script setup lang="ts">
import { computed } from 'vue';

/*
 * A running or finished job (a print, an arrange run): what it is, how far, and what you can do to it.
 * `hero` makes it the page's main block: filled with the plugin's accent, large figure, thick bar. Unknown progress is
 * an indeterminate bar and a dash, not 0 %. A `stale` job (last known values) is never filled: it is drawn grey.
 */
const props = defineProps<{ name: string; /** 0..100, or null when the job reports no fraction. */ progress?: number | null;
  progressLabel?: string; /** Replaces the percentage (for counted work: "7 of 14"). */ count?: string; detail?: string;
  compact?: boolean; hero?: boolean; /** Last known values of a job the page can no longer see. */ stale?: boolean }>();
const known = computed(() => typeof props.progress === 'number' && Number.isFinite(props.progress));
const pct = computed(() => (known.value ? Math.max(0, Math.min(100, props.progress as number)) : 0));
</script>
<template>
  <div class="oui-job" :data-compact="compact || undefined" :data-hero="hero || undefined" :data-stale="stale || undefined">
    <div class="oui-job-block" :class="{ 'oui-on-band': hero && !stale }">
      <div class="oui-job-head">
        <div v-if="$slots.thumb" class="oui-job-thumb"><slot name="thumb" /></div>
        <div class="oui-job-id">
          <div v-if="$slots.status" class="oui-job-status"><slot name="status" /></div>
          <p class="oui-job-name" :title="name">{{ name }}</p>
          <p v-if="detail" class="oui-job-detail oui-num">{{ detail }}</p>
        </div>
        <div class="oui-job-figure oui-num"><template v-if="count">{{ count }}</template><template v-else-if="known">{{ Math.round(pct) }}<span>%</span></template><span v-else aria-hidden="true">—</span></div>
      </div>
      <div class="oui-job-bar" role="progressbar" :aria-label="progressLabel ?? name" aria-valuemin="0" aria-valuemax="100" :aria-valuenow="known ? Math.round(pct) : undefined"
        :data-indeterminate="!known || undefined"><span :style="known ? { width: pct + '%' } : undefined" /></div>
      <div v-if="$slots.default" class="oui-job-stats"><slot /></div>
    </div>
    <div v-if="$slots.actions" class="oui-job-actions"><slot name="actions" /></div>
  </div>
</template>
<style>
.oui-job, .oui-job-block { display: grid; gap: var(--oui-s3); min-width: 0; }
.oui-job-head { display: flex; align-items: flex-end; gap: var(--oui-s3); min-width: 0; }
.oui-job-thumb { flex: none; align-self: center; }
.oui-job-id { flex: 1 1 0; display: grid; gap: 2px; min-width: 0; }
.oui-job-status { margin-bottom: 4px; }
.oui-job-name { font-size: var(--oui-text-lg); font-weight: 700; line-height: 1.3; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.oui-job-detail { font-size: var(--oui-text-sm); color: var(--oui-muted); }
.oui-job-figure { flex: none; font-size: var(--oui-text-3xl); line-height: .95; font-weight: 700; letter-spacing: -.02em; }
.oui-job-figure > span { margin-inline-start: .08em; font-size: .5em; font-weight: 600; letter-spacing: 0; }
.oui-job-bar { height: 8px; border-radius: 4px; background: var(--oui-border); overflow: hidden; }
.oui-job-bar > span { display: block; height: 100%; border-radius: inherit; background: var(--oui-primary); transition: width .4s linear; }
.oui-job-bar[data-indeterminate] > span { width: 32%; animation: oui-slide 1.4s var(--oui-ease) infinite; }
.oui-job-stats { display: flex; flex-wrap: wrap; gap: var(--oui-s3) var(--oui-s6); }
.oui-job-actions { display: flex; flex-wrap: wrap; gap: var(--oui-s2); }
.oui-job[data-compact] .oui-job-block { gap: var(--oui-s2); }
.oui-job[data-compact] .oui-job-name { font-size: var(--oui-text-md); }
.oui-job[data-compact] .oui-job-figure { font-size: var(--oui-text-xl); line-height: 1.1; }
/* Hero: the block is the accent; the bar is thick and white on it. */
.oui-job[data-hero] { gap: 0; }
.oui-job[data-hero] > .oui-job-block { padding: var(--oui-s4); border-radius: var(--oui-radius-lg) var(--oui-radius-lg) 0 0; }
.oui-job[data-hero]:not([data-compact]) .oui-job-figure { font-size: 56px; }
.oui-job[data-hero]:not([data-compact]) .oui-job-name { white-space: normal; overflow-wrap: anywhere; display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2; line-clamp: 2; }
.oui-job[data-hero] .oui-job-bar { height: 12px; border-radius: 6px; }
.oui-job[data-hero][data-compact] .oui-job-bar { height: 10px; }
.oui-job[data-hero] > .oui-job-actions { padding: var(--oui-s3) var(--oui-s4); }
.oui-job[data-stale] > .oui-job-block { background: var(--oui-raised); }
.oui-job[data-stale] .oui-job-bar > span { background: var(--oui-control-border); }
.oui-job[data-stale] .oui-job-figure { color: var(--oui-muted); }
@keyframes oui-slide { from { transform: translateX(-100%); } to { transform: translateX(320%); } }
</style>
