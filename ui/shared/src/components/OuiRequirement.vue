<script setup lang="ts">
import { getCurrentInstance } from 'vue';
import OuiIcon from './OuiIcon.vue';
import OuiStatus from './OuiStatus.vue';
import { link, refresh } from '../icons';

/*
 * "This feature needs X": one row of a Settings section for a tool or file the plugin looks for on this computer
 * (ffmpeg, a certificate, Spoolman, the other plugin). It says what it is, what it is needed for, whether it was found
 * (and where), how to get it when it is missing, and lets the user look again after installing it.
 * All text comes from the plugin, in the page language. `check` is emitted by "Check again"; `open` by the install link
 * (the plugin opens the address in the system browser; without a listener the link opens as a normal link).
 */
const props = defineProps<{ name: string; /** What the plugin uses it for. */ why?: string;
  status: 'found' | 'missing' | 'checking' | 'unknown'; /** The status chip text ("Found", "Not found"). */ statusLabel: string;
  /** Where it was found, or what was found ("/usr/bin/ffmpeg · 7.1"). */ detail?: string;
  /** How to install it, one line. */ installText?: string; installUrl?: string; installLabel?: string;
  checkLabel: string; checking?: boolean }>();
const emit = defineEmits<{ check: []; open: [url: string] }>();
const STATE = { found: 'ok', missing: 'warn', checking: 'busy', unknown: 'idle' } as const;
const listens = !!getCurrentInstance()?.vnode.props?.onOpen;
function onLink(event: MouseEvent) {
  if (!props.installUrl || !listens) return;
  event.preventDefault();
  emit('open', props.installUrl);
}
</script>
<template>
  <div class="oui-req" :data-status="status">
    <div class="oui-req-id">
      <p class="oui-req-name">{{ name }}</p>
      <p v-if="why" class="oui-meta">{{ why }}</p>
      <p v-if="detail" class="oui-meta oui-req-detail">{{ detail }}</p>
      <p v-if="status === 'missing' && (installText || installUrl)" class="oui-req-install">
        <span v-if="installText">{{ installText }}</span>
        <a v-if="installUrl" :href="installUrl" target="_blank" rel="noopener noreferrer" class="oui-req-link" @click="onLink"><OuiIcon :icon="link" :size="13" />{{ installLabel ?? installUrl }}</a>
      </p>
    </div>
    <div class="oui-req-side">
      <OuiStatus :state="STATE[status]">{{ statusLabel }}</OuiStatus>
      <button type="button" class="oui-req-check" :disabled="checking || status === 'checking'" @click="emit('check')">
        <OuiIcon :icon="refresh" :size="14" /><span>{{ checkLabel }}</span>
      </button>
    </div>
  </div>
</template>
<style>
.oui-req { container: oui-req / inline-size; display: flex; flex-wrap: wrap; align-items: flex-start; gap: var(--oui-s2) var(--oui-s4); padding: var(--oui-s3) var(--oui-s4); }
.oui-req-id { flex: 1 1 240px; display: grid; gap: 2px; min-width: 0; }
.oui-req-name { font-weight: 650; }
.oui-req-detail { font-family: var(--oui-mono); font-size: var(--oui-text-xs); overflow-wrap: anywhere; }
.oui-req-install { display: flex; flex-wrap: wrap; align-items: center; gap: 2px var(--oui-s2); margin-top: 2px; }
.oui-req-link { display: inline-flex; align-items: center; gap: 4px; font-weight: 600; overflow-wrap: anywhere; }
.oui-req-side { flex: none; display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); margin-inline-start: auto; }
.oui-req-check { display: inline-flex; align-items: center; gap: 6px; height: var(--oui-control-sm); padding: 0 10px; border: 1px solid var(--oui-control-border);
  border-radius: var(--oui-radius); font-weight: 600; color: var(--oui-text); background: var(--oui-surface); cursor: pointer; }
.oui-req-check:hover:not(:disabled) { background: var(--oui-raised); }
.oui-req-check:disabled { opacity: .55; cursor: not-allowed; }
</style>
