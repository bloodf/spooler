<script setup lang="ts">
import { computed, onBeforeUnmount, watch } from 'vue';
import Button from 'primevue/button';
import { OuiAppBar, OuiIcon, OuiStatus, type OuiState, type OuiTab } from '../shared/src/components';
import { chart, download, note, printer, refresh as refreshIcon, settings, spool } from '../shared/src/icons';
import Logo from './components/Logo.vue';
import StatusArea from './components/StatusArea.vue';
import SpoolsView from './components/SpoolsView.vue';
import PrinterView from './components/PrinterView.vue';
import StatsView from './components/StatsView.vue';
import ConfirmDialog from './components/ConfirmDialog.vue';
import SlicePick from './components/SlicePick.vue';
import SettingsView from './settings/SettingsView.vue';
import { leave, saved } from './settings/state';
import * as bridge from './core/bridge';
import { boot } from './core/boot';
import { m, start, setTab, statsOn, plateAttention, usageAttention, pollLive, sourceOff, pending, refresh, syncPresets, openSettings } from './state/main';
import { t, fmt } from './core/i18n';

// Three surfaces share this page: the native tab (spool views + Settings as its last tab), the separate spool window
// and the separate Settings window (hosts without native tabs). Settings never hides the spool views' functions.
const settingsOnly = boot.mode === 'settings';
const stop = settingsOnly ? () => {} : start();
onBeforeUnmount(stop);
watch(() => m.view, v => { if (v === 'main') pollLive(); });

type Tab = 'spools' | 'printer' | 'stats';
const tab = computed<Tab>(() => ((m.tab === 'stats' && !statsOn.value) || (m.tab === 'printer' && !m.showPrinterTab) ? 'spools' : m.tab));
const current = computed(() => (m.view === 'settings' ? 'settings' : tab.value));
// Each tab carries its name as a tooltip: in the 380 px dock the tabs show their icons only (the name stays their
// accessible name, visually hidden).
const named = (tab: OuiTab): OuiTab => ({ ...tab, attrs: { title: tab.label, ...tab.attrs } });
const tabs = computed<OuiTab[]>(() => [
  { value: 'spools', label: t('nav.spools'), icon: spool, ...(m.spools.length ? { count: m.spools.length } : {}) },
  ...(m.showPrinterTab ? [{ value: 'printer', label: t('nav.printer'), icon: printer,
    ...(plateAttention.value > 0 || usageAttention.value ? { attention: t('nav.attention') } : {}) }] : []),
  ...(statsOn.value ? [{ value: 'stats', label: t('nav.stats'), icon: chart }] : []),
  ...(boot.mode === 'tab' ? [{ value: 'settings', label: t('nav.settings'), icon: settings, attrs: { 'data-test': 'settings-btn' } }] : []),
].map(named));
// Settings is the plugin's to open and close (it sends show_view); leaving it with unsaved edits asks first.
async function go(value: string) {
  if (value === 'settings') { if (m.view !== 'settings') openSettings(); return; }
  if (m.view === 'settings' && !await leave()) return;
  setTab(value as Tab);
}

// The page's one source state. A list kept from an earlier read is stale, never "ok".
const sourceName = computed(() => (m.source === 'bambu' ? 'Bambu Cloud' : 'Spoolman'));
const state = computed<{ state: OuiState; label: string; text: string }>(() => {
  if (!m.received) return { state: 'connecting', label: sourceName.value, text: t('list.loading') };
  if (m.errorCode === 'no_url') return { state: 'idle', label: sourceName.value, text: t('list.noUrl.short') };
  if (m.loadError) return m.spools.length
    ? { state: 'stale', label: sourceName.value, text: t('app.readAt', { time: fmt.time(m.loadedAt / 1000) }) }
    : { state: 'error', label: sourceName.value, text: t('list.readFailed.short') };
  const host = m.source === 'spoolman' ? String(saved.value.url || '').replace(/^[a-z]+:\/\//i, '').replace(/\/+$/, '') : '';
  const read = t('app.read', { ago: fmt.ago(m.loadedAt / 1000, m.now / 1000) });
  return { state: 'ok', label: sourceName.value, text: host ? `${host} · ${read}` : read };
});
</script>

<template>
  <div class="sp-shell">
    <OuiAppBar name="Spooler" :tabs="settingsOnly ? undefined : tabs" :model-value="current" :tabs-label="t('nav.label')" @update:model-value="go">
      <template #mark><Logo /></template>
      <template #status>
        <span v-if="settingsOnly" class="oui-truncate">{{ t('nav.settings') }}</span>
        <template v-else><OuiStatus :state="state.state">{{ state.label }}</OuiStatus><span class="oui-truncate sp-state" data-test="source-state">{{ state.text }}</span></template>
      </template>
      <template #actions>
        <template v-if="!settingsOnly && m.view === 'main'">
          <Button severity="secondary" text size="small" :aria-label="t('list.refresh')" :title="t('list.refresh')" :loading="pending('refresh')" data-test="refresh" @click="refresh">
            <template #icon><OuiIcon :icon="refreshIcon" :size="14" /></template></Button>
          <Button severity="secondary" size="small" class="sp-sync" :label="t('list.sync')" :aria-label="t('list.sync')" :disabled="!!sourceOff || pending('send')" :title="t('list.syncHelp')"
                  aria-describedby="sv-why" data-test="sync" @click="syncPresets"><template #icon><OuiIcon :icon="download" :size="14" /></template></Button>
          <Button v-if="boot.mode === 'main'" severity="secondary" text size="small" :aria-label="t('nav.settings')" :title="t('nav.settings')" data-test="settings-btn" @click="openSettings">
            <template #icon><OuiIcon :icon="settings" :size="14" /></template></Button>
        </template>
        <Button v-else severity="secondary" text size="small" :aria-label="t('set.feedback')" :title="t('set.feedback')" @click="bridge.postSettings({ type: 'feedback' })">
          <template #icon><OuiIcon :icon="note" :size="14" /></template></Button>
      </template>
    </OuiAppBar>
    <SettingsView v-if="settingsOnly" />
    <template v-else>
      <main v-show="m.view === 'main'" class="oui-page">
        <StatusArea />
        <div v-show="tab === 'spools'" role="tabpanel" aria-labelledby="oui-tab-spools"><SpoolsView /></div>
        <div v-if="m.showPrinterTab" v-show="tab === 'printer'" role="tabpanel" aria-labelledby="oui-tab-printer"><PrinterView /></div>
        <div v-if="statsOn" v-show="tab === 'stats'" role="tabpanel" aria-labelledby="oui-tab-stats"><StatsView /></div>
      </main>
      <SettingsView v-if="boot.mode === 'tab'" v-show="m.view === 'settings'" role="tabpanel" aria-labelledby="oui-tab-settings" />
    </template>
    <ConfirmDialog />
    <SlicePick v-if="!settingsOnly" />
  </div>
</template>

<style>
html, body, #app { min-height: 100%; }
/* Manrope has Latin glyphs only. Chinese text takes the system's Simplified Chinese font, named here so a Japanese or
   Traditional Chinese one isn't picked first for the shared Han characters. */
html:lang(zh-CN) { --oui-font: 'Manrope', 'PingFang SC', 'Microsoft YaHei', 'Noto Sans CJK SC', 'Noto Sans SC', 'Source Han Sans SC', system-ui, -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; }
.sp-shell { min-height: 100vh; }
.oui-page > [role='tabpanel'] { min-width: 0; }
/* Narrow bar (the 380 px dock): the page actions keep their icons and drop their words; the state keeps its chip. */
@container oui-appbar (max-width: 520px) {
  .sp-sync .p-button-label, .sp-state { display: none; }
  .oui-appbar-tab > span:not([class]) { position: absolute; width: 1px; height: 1px; overflow: hidden; clip-path: inset(50%); white-space: nowrap; }
  .sp-sync.p-button { width: var(--oui-control-sm); padding-inline: 0; }
}
</style>
