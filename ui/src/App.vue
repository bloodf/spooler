<script setup lang="ts">
import { computed, onBeforeUnmount, watch } from 'vue';
import Tabs from 'primevue/tabs';
import TabList from 'primevue/tablist';
import Tab from 'primevue/tab';
import TabPanels from 'primevue/tabpanels';
import TabPanel from 'primevue/tabpanel';
import Button from 'primevue/button';
import Logo from './components/Logo.vue';
import StatusArea from './components/StatusArea.vue';
import SpoolsView from './components/SpoolsView.vue';
import PrinterView from './components/PrinterView.vue';
import StatsView from './components/StatsView.vue';
import ConfirmDialog from './components/ConfirmDialog.vue';
import SettingsView from './settings/SettingsView.vue';
import * as bridge from './core/bridge';
import { boot } from './core/boot';
import { m, start, setTab, statsOn, plateAttention, usageAttention, pollLive } from './state/main';
import { t } from './core/i18n';

// Three surfaces share this page: the native tab (spool views + Settings), the separate spool window and the
// separate Settings window (hosts without native tabs). Settings never hides the spool views' functions.
const settingsOnly = boot.mode === 'settings';
const stop = settingsOnly ? () => {} : start();
onBeforeUnmount(stop);

const tabValue = computed({
  get: () => (m.tab === 'stats' && !statsOn.value ? 'spools' : m.tab === 'printer' && !m.showPrinterTab ? 'spools' : m.tab),
  set: v => setTab(v as 'spools' | 'printer' | 'stats'),
});
const showTabs = computed(() => m.showPrinterTab || statsOn.value);
const dot = computed(() => plateAttention.value > 0 || usageAttention.value);
watch(() => m.view, v => { if (v === 'main') pollLive(); });

function openSettings() { bridge.postMain({ type: 'settings' }); }
</script>

<template>
  <div class="sp-shell">
    <SettingsView v-if="settingsOnly" />
    <template v-else>
      <Tabs v-model:value="tabValue" class="sp-tabs" :show-navigators="false">
        <header class="oui-header sp-head">
          <span class="sp-brand"><Logo /><h1>Spooler</h1></span>
          <TabList v-if="m.view === 'main' && showTabs" class="sp-nav" :aria-label="t('nav.label')">
            <Tab value="spools" data-tab="spools">{{ t('nav.spools') }}</Tab>
            <Tab v-if="m.showPrinterTab" value="printer" data-tab="printer">{{ t('nav.printer') }}
              <span v-if="dot" class="sp-dot" :title="t('nav.attention')"><span class="sp-sr">{{ t('nav.attention') }}</span></span></Tab>
            <Tab v-if="statsOn" value="stats" data-tab="stats">{{ t('nav.stats') }}</Tab>
          </TabList>
          <span class="sp-grow" />
          <Button v-if="m.view === 'main'" severity="secondary" outlined :label="t('nav.settings')" data-test="settings-btn" @click="openSettings" />
        </header>
        <main v-show="m.view === 'main'" class="sp-main">
          <StatusArea />
          <TabPanels class="sp-panels">
            <TabPanel value="spools"><SpoolsView /></TabPanel>
            <TabPanel v-if="m.showPrinterTab" value="printer"><PrinterView /></TabPanel>
            <TabPanel v-if="statsOn" value="stats"><StatsView /></TabPanel>
          </TabPanels>
        </main>
      </Tabs>
      <SettingsView v-if="boot.mode === 'tab'" v-show="m.view === 'settings'" />
    </template>
    <ConfirmDialog />
  </div>
</template>

<style>
html, body, #app { min-height: 100%; }
body { background: var(--oui-background); }
.sp-shell { min-height: 100vh; background: var(--oui-background); }
.sp-head { position: sticky; top: 0; z-index: 5; }
.sp-brand { display: inline-flex; align-items: center; gap: 8px; }
.sp-brand h1 { margin: 0; }
.sp-nav { min-width: 0; }
.sp-nav .p-tab { display: inline-flex; align-items: center; gap: 6px; }
.sp-grow { flex: 1; }
.sp-dot { width: 8px; height: 8px; border-radius: 50%; background: var(--oui-warning); display: inline-block; }
.sp-sr, .sp-sr-only { position: absolute; width: 1px; height: 1px; overflow: hidden; clip: rect(0 0 0 0); white-space: nowrap; }
.sp-main { padding: 16px; display: flex; flex-direction: column; min-width: 0; }
.sp-panels.p-tabpanels { padding: 0; background: transparent; }
.sp-card { padding: 16px; background: var(--oui-surface); border: 1px solid var(--oui-border); border-radius: 12px; min-width: 0; }
.sp-card > h2 { margin: 0 0 12px; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
.sp-row { display: flex; flex-wrap: wrap; align-items: center; gap: 8px; }
.sp-why { color: var(--oui-muted); font-size: 12px; }
.sp-num { font-variant-numeric: tabular-nums; white-space: nowrap; }
.sp-warn { color: var(--oui-warning); }
.sp-err { color: var(--oui-danger); }
.sp-chip { display: inline-flex; align-items: center; gap: 4px; padding: 0 8px; border-radius: 999px; border: 1px solid var(--oui-border);
  font-size: 12px; line-height: 20px; white-space: nowrap; color: var(--oui-text); }
.sp-chip.accent { border-color: var(--p-primary-color); color: var(--p-primary-color); }
.sp-chip.warn { border-color: var(--oui-warning); color: var(--oui-warning); background: var(--oui-warning-bg); }
.sp-chip.bad { border-color: var(--oui-danger); color: var(--oui-danger); background: var(--oui-danger-bg); }
.sp-chip.ok { border-color: var(--oui-success); color: var(--oui-success); background: var(--oui-success-bg); }
.sp-table { width: 100%; border-collapse: collapse; }
.sp-table th, .sp-table td { padding: 8px; border-bottom: 1px solid var(--oui-border); text-align: left; vertical-align: middle; }
.sp-table th { color: var(--oui-muted); font-size: 12px; font-weight: 600; }
.sp-table .r { text-align: right; }
@media (max-width: 720px) { .sp-main { padding: 12px; } .sp-nav { order: 3; flex-basis: 100%; overflow-x: auto; } }
</style>
