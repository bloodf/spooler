<script setup lang="ts">
import { computed, reactive } from 'vue';
import Button from 'primevue/button';
import { OuiIcon, OuiJob, OuiPanel, OuiReadout, OuiStatus, type OuiState } from '@orca-plugins/ui-foundation/src/components';
import { calendar, clock, hourglass, layers, x } from '@orca-plugins/ui-foundation/src/icons';
import { m } from '../state/main';
import { t, tn, fmt } from '../core/i18n';
import { LIVE_STALE, PROG_LIVE, PROG_STATES, type LivePrinter } from '../logic/printers';

// Print progress from Live Link printers; idle printers stay as one line unless Settings hides them. Each running print
// is the shared status block; a printer that stopped reporting keeps its last values, in grey.
const KEPT = ['live', 'unreachable'];
const list = computed(() => (m.liveOn && m.progress.on ? m.live.printers.filter(lv => KEPT.includes(m.live.links?.[lv.link as string] ?? '') && lv.job) : []));
const hide = computed(() => m.progress.idle === 'hide');
const busy = computed(() => list.value.filter(lv => (hide.value ? PROG_LIVE.includes(lv.job!.state) : !!PROG_STATES[lv.job!.state])));
const idle = computed(() => (hide.value ? [] : list.value.filter(lv => !PROG_STATES[lv.job!.state])));
// A print that is running gets the big block; one that finished or failed is one line, until dismissed (this session).
const running = computed(() => busy.value.filter(lv => PROG_LIVE.includes(lv.job!.state)));
const dismissed = reactive(new Set<string>());
const doneKey = (lv: LivePrinter) => `${lv.link}:${lv.job!.name || ''}:${lv.job!.end || ''}`;
const done = computed(() => busy.value.filter(lv => !PROG_LIVE.includes(lv.job!.state) && !dismissed.has(doneKey(lv))));
function doneLine(lv: LivePrinter) {
  const j = lv.job!;
  return [lv.name, j.end ? `${t('progress.l.finished')} ${clockAt(j.end * 1000)}` : '', j.state === 'FAILED' && j.layer ? t('progress.stoppedAt', { n: j.layer }) : ''].filter(Boolean).join(' · ');
}
// A printer whose link is down keeps its last job on screen (greyed, "Not reachable"); one that stopped reporting for a while says
// "Not updated for 3 min". A removed or never-working link (no entry, auth, serial, none) shows no job.
const aged = (lv: LivePrinter) => (lv.age ?? 0) > LIVE_STALE;
const down = (lv: LivePrinter) => m.live.links?.[lv.link as string] === 'unreachable';
const stale = (lv: LivePrinter) => aged(lv) || down(lv);
const staleText = (lv: LivePrinter) => (down(lv) ? t('req.unreachable') : t('link.stale'));
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
  <OuiPanel v-if="running.length || done.length || idle.length" flush class="pg" data-test="progress">
    <h2 class="oui-sr">{{ t('progress.title') }}</h2>
    <div v-for="lv in running" :key="lv.link" class="pg-job">
      <OuiJob :stale="stale(lv)" :name="lv.job!.name || t('stats.print')" :progress="pct(lv)" :progress-label="t('progress.bar', { name: lv.job!.name || '' })" :detail="line(lv)">
        <template #status><OuiStatus v-if="stale(lv)" state="stale">{{ staleText(lv) }}</OuiStatus><OuiStatus v-else :state="STATE[lv.job!.state]">{{ t(`progress.state.${lv.job!.state}` as any) }}</OuiStatus></template>
        <OuiReadout v-for="x in facts(lv)" :key="x.label" :icon="x.icon" :label="x.label" :value="x.value" size="sm" :stale="stale(lv)" />
      </OuiJob>
    </div>
    <div v-for="lv in done" :key="'d' + lv.link" class="oui-row pg-idle pg-done" data-test="job-done">
      <OuiStatus :state="stale(lv) ? 'stale' : STATE[lv.job!.state]">{{ stale(lv) ? staleText(lv) : t(`progress.state.${lv.job!.state}` as any) }}</OuiStatus>
      <span class="oui-truncate pg-done-t" :title="(lv.job!.name || t('stats.print')) + ' · ' + doneLine(lv)"><strong>{{ lv.job!.name || t('stats.print') }}</strong>
        <span class="oui-meta"> · {{ doneLine(lv) }}</span></span>
      <Button severity="secondary" text size="small" :aria-label="t('common.dismiss')" :title="t('common.dismiss')" data-act="dismiss-job" @click="dismissed.add(doneKey(lv))">
        <template #icon><OuiIcon :icon="x" :size="14" /></template></Button>
    </div>
    <div v-for="lv in idle" :key="'i' + lv.link" class="oui-row pg-idle"><OuiStatus state="idle">{{ t('progress.idle') }}</OuiStatus>
      <span class="oui-meta">{{ t('progress.noPrint') }} · {{ lv.name }}</span></div>
  </OuiPanel>
</template>
<style>
.pg-job { padding: var(--oui-s3); }
.pg-job + .pg-job { border-top: 1px solid var(--oui-border); }
.pg-idle { padding: var(--oui-s2) var(--oui-s3); border-top: 1px solid var(--oui-border); }
.pg > .oui-panel-body > :first-child:not(.pg-job) { border-top: 0; }
.pg { overflow: hidden; }
.pg-done { flex-wrap: nowrap; }
.pg-done-t { flex: 1; }
</style>
