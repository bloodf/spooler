<script setup lang="ts">
import { computed } from 'vue';
import ProgressBar from 'primevue/progressbar';
import { m } from '../state/main';
import { t, tn, fmt } from '../core/i18n';
import { LIVE_STALE, PROG_LIVE, PROG_STATES, type LivePrinter } from '../logic/printers';

// Print progress from Live Link printers; idle printers stay as one line unless Settings hides them.
const list = computed(() => (m.liveOn && m.progress.on ? m.live.printers.filter(lv => m.live.links?.[lv.link as string] === 'live' && lv.job) : []));
const hide = computed(() => m.progress.idle === 'hide');
const busy = computed(() => list.value.filter(lv => (hide.value ? PROG_LIVE.includes(lv.job!.state) : !!PROG_STATES[lv.job!.state])));
const idle = computed(() => (hide.value ? [] : list.value.filter(lv => !PROG_STATES[lv.job!.state])));
const stale = (lv: LivePrinter) => (lv.age ?? 0) > LIVE_STALE;
const dur = (min: number) => { const h = Math.floor(min / 60); return h ? t('progress.hm', { h, m: String(min % 60).padStart(2, '0') }) : t('progress.m', { m: min }); };
const clock = (ms: number) => fmt.time(ms / 1000);
function rows(lv: LivePrinter) {
  const j = lv.job!, s = PROG_STATES[j.state], live = PROG_LIVE.includes(j.state), prep = s.fill === 'prep';
  const out: string[] = [];
  if (j.stage && j.state !== 'FAILED') out.push(j.stage);
  if (j.layers) out.push(j.layer && !prep ? t('progress.layer', { n: j.layer, total: j.layers }) : tn('progress.layers', j.layers));
  if (live && j.left != null) {
    out.push(prep ? t('progress.about', { d: dur(j.left) }) : t('progress.left', { d: dur(j.left) }));
    if (m.progress.finish && !prep) out.push(t('progress.done', { time: clock(Date.now() + j.left * 60000) }));
  }
  if (j.state === 'FINISH' && j.took) out.push(t('progress.took', { d: dur(j.took) }));
  if (j.state === 'FINISH' && j.end) out.push(t('progress.finishedAt', { time: clock(j.end * 1000) }));
  if (j.state === 'FAILED' && j.layer) out.push(t('progress.stoppedAt', { n: j.layer }));
  return out;
}
const pct = (lv: LivePrinter) => (lv.job!.state === 'FINISH' ? 100 : Math.max(0, Math.min(100, lv.job!.pct || 0)));
const stateLabel = (s: string) => t(`progress.state.${s}` as any);
</script>
<template>
  <section v-if="busy.length || idle.length" class="sp-card pg" aria-labelledby="pg-h" data-test="progress">
    <h2 id="pg-h">{{ t('progress.title') }} <span v-if="busy.length" class="sp-chip" :class="busy.every(stale) ? 'warn' : 'ok'">{{ busy.every(stale) ? t('link.stale') : t('link.live') }}</span></h2>
    <div v-for="lv in busy" :key="lv.link" class="pg-job">
      <div class="sp-row"><strong class="pg-name">{{ lv.job!.name || t('stats.print') }}</strong>
        <span class="sp-chip" :class="PROG_STATES[lv.job!.state].cls">{{ stateLabel(lv.job!.state) }}</span>
        <span class="oui-meta">{{ lv.name }}<template v-if="stale(lv)"> · {{ t('link.stale') }}</template></span><span class="sp-grow" />
        <span v-if="PROG_STATES[lv.job!.state].fill !== 'prep'" class="sp-num">{{ pct(lv) }}%</span></div>
      <ProgressBar :value="pct(lv)" :show-value="false" :mode="PROG_STATES[lv.job!.state].fill === 'prep' ? 'indeterminate' : 'determinate'"
                   style="height: 8px" :aria-label="t('progress.bar', { name: lv.job!.name || '' })" />
      <p class="oui-meta pg-meta">{{ rows(lv).join(' · ') }}</p>
    </div>
    <div v-for="(lv, i) in idle" :key="'i' + lv.link" class="sp-row pg-idle"><span class="sp-chip">{{ t('progress.idle') }}</span>
      <span class="oui-meta">{{ t('progress.noPrint') }} · {{ lv.name }}</span><span v-if="i < 0" /></div>
  </section>
</template>
<style scoped>
.pg { display: grid; gap: 10px; }
.pg-job { display: grid; gap: 6px; }
.pg-name { overflow-wrap: anywhere; }
.pg-meta { margin: 0; }
</style>
