<script setup lang="ts">
import { computed } from 'vue';
import { OuiJob, OuiPanel, OuiReadout, OuiStatus, type OuiState } from '../../shared/src/components';
import { calendar, clock, hourglass, layers, printer } from '../../shared/src/icons';
import { m } from '../state/main';
import { t, tn, fmt } from '../core/i18n';
import { LIVE_STALE, PROG_LIVE, PROG_STATES, type LivePrinter } from '../logic/printers';

// Print progress from Live Link printers; idle printers stay as one line unless Settings hides them. The first print
// is the page's accent block; a printer that stopped reporting keeps its last values, in grey.
const list = computed(() => (m.liveOn && m.progress.on ? m.live.printers.filter(lv => m.live.links?.[lv.link as string] === 'live' && lv.job) : []));
const hide = computed(() => m.progress.idle === 'hide');
const busy = computed(() => list.value.filter(lv => (hide.value ? PROG_LIVE.includes(lv.job!.state) : !!PROG_STATES[lv.job!.state])));
const idle = computed(() => (hide.value ? [] : list.value.filter(lv => !PROG_STATES[lv.job!.state])));
const stale = (lv: LivePrinter) => (lv.age ?? 0) > LIVE_STALE;
const dur = (min: number) => { const h = Math.floor(min / 60); return h ? t('progress.hm', { h, m: String(min % 60).padStart(2, '0') }) : t('progress.m', { m: min }); };
const clockAt = (ms: number) => fmt.time(ms / 1000);
const STATE: Record<string, OuiState> = { RUNNING: 'busy', PREPARE: 'connecting', SLICING: 'connecting', PAUSE: 'warn', FINISH: 'ok', FAILED: 'error' };
const prep = (lv: LivePrinter) => PROG_STATES[lv.job!.state].fill === 'prep';
const pct = (lv: LivePrinter) => (prep(lv) ? null : lv.job!.state === 'FINISH' ? 100 : Math.max(0, Math.min(100, lv.job!.pct || 0)));
function line(lv: LivePrinter) {
  const j = lv.job!, out: string[] = [lv.name];
  if (j.stage && j.state !== 'FAILED') out.push(j.stage);
  if (j.layers) out.push(j.layer && !prep(lv) ? t('progress.layer', { n: j.layer, total: j.layers }) : tn('progress.layers', j.layers));
  if (j.state === 'FAILED' && j.layer) out.push(t('progress.stoppedAt', { n: j.layer }));
  return out.join(' · ');
}
function facts(lv: LivePrinter) {
  const j = lv.job!, out: { icon: typeof clock; label: string; value: string }[] = [];
  if (PROG_LIVE.includes(j.state) && j.left != null) {
    out.push({ icon: hourglass, label: t(prep(lv) ? 'progress.l.about' : 'progress.l.left'), value: dur(j.left) });
    if (m.progress.finish && !prep(lv)) out.push({ icon: calendar, label: t('progress.l.done'), value: clockAt(Date.now() + j.left * 60000) });
  }
  if (j.state === 'FINISH' && j.took) out.push({ icon: clock, label: t('progress.l.took'), value: dur(j.took) });
  if (j.state === 'FINISH' && j.end) out.push({ icon: calendar, label: t('progress.l.finished'), value: clockAt(j.end * 1000) });
  if (j.layers && j.layer && !prep(lv)) out.push({ icon: layers, label: t('progress.l.layer'), value: `${j.layer} / ${j.layers}` });
  return out;
}
</script>
<template>
  <OuiPanel v-if="busy.length || idle.length" flush class="pg" data-test="progress">
    <h2 class="oui-sr">{{ t('progress.title') }}</h2>
    <div v-for="(lv, i) in busy" :key="lv.link" class="pg-job" :class="{ 'pg-more': i > 0 }">
      <OuiJob :hero="i === 0" :compact="i > 0" :stale="stale(lv)" :name="lv.job!.name || t('stats.print')" :progress="pct(lv)" :progress-label="t('progress.bar', { name: lv.job!.name || '' })" :detail="line(lv)">
        <template #status><OuiStatus v-if="stale(lv)" state="stale">{{ t('link.stale') }}</OuiStatus><OuiStatus v-else :state="STATE[lv.job!.state]">{{ t(`progress.state.${lv.job!.state}` as any) }}</OuiStatus></template>
        <OuiReadout v-for="x in facts(lv)" :key="x.label" :icon="x.icon" :label="x.label" :value="x.value" size="sm" :stale="stale(lv)" />
      </OuiJob>
    </div>
    <div v-for="lv in idle" :key="'i' + lv.link" class="oui-row pg-idle"><OuiStatus state="idle">{{ t('progress.idle') }}</OuiStatus>
      <span class="oui-meta">{{ t('progress.noPrint') }} · {{ lv.name }}</span></div>
  </OuiPanel>
</template>
<style>
.pg-more { padding: var(--oui-s3) var(--oui-s4); border-top: 1px solid var(--oui-border); }
.pg-idle { padding: var(--oui-s2) var(--oui-s4); border-top: 1px solid var(--oui-border); }
.pg > .oui-panel-body > :first-child:not(.pg-job) { border-top: 0; }
.pg { overflow: hidden; }
</style>
