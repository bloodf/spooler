<script setup lang="ts">
import { ref, watch } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { check, error, info, warning, x as close, type OuiIconData } from '../icons';

/*
 * A page-level state, said once: why the page is offline, busy, stale or needs attention, with the one action
 * that resolves it. Controls that it disables point at it with aria-describedby instead of repeating it.
 *
 * Nothing stays on screen for good: with `dismissible` it has a close button. A `dismissKey` remembers the dismissal
 * for the session (a reload of the tab included) under that key; put what the banner is about in the key
 * ("spoolman-down:http://host:7912", "unconfirmed:3") and it comes back when that changes, not on every poll.
 * A banner is bound to its condition, never timed: pass the condition as `show` (instead of v-if) and when it clears
 * the dismissal is forgotten, so the same problem coming back later shows again. A key that changes forgets the old
 * one the same way.
 */
const props = withDefaults(defineProps<{ tone?: 'info' | 'warn' | 'error' | 'success' | 'neutral'; title: string; icon?: OuiIconData; id?: string;
  dismissible?: boolean; dismissKey?: string; /** Accessible name of the close button. */ closeLabel?: string;
  /** The banner's condition (default true). False hides it and forgets its dismissal. */ show?: boolean }>(), { show: true });
const emit = defineEmits<{ dismiss: [] }>();
const TONE = { info: 'info', warn: 'warn', error: 'danger', success: 'success', neutral: 'neutral' } as const;
const ICON: Record<string, OuiIconData> = { info, warn: warning, error, success: check, neutral: info };

const storeKey = (key: string) => 'oui-banner:' + key;
function remembered(key: string | undefined): boolean {
  if (!key) return false;
  try { return sessionStorage.getItem(storeKey(key)) === '1'; } catch { return false; }
}
function forget(key: string | undefined) {
  if (!key) return;
  try { sessionStorage.removeItem(storeKey(key)); } catch { /* nothing stored */ }
}
if (!props.show) forget(props.dismissKey);   // the condition is not there now: a later one starts afresh
const hidden = ref(props.show && remembered(props.dismissKey));
watch(() => props.dismissKey, (key, old) => { if (old && old !== key) forget(old); hidden.value = remembered(key); });
watch(() => props.show, (on) => { if (!on) { forget(props.dismissKey); hidden.value = false; } });
function dismiss() {
  hidden.value = true;
  if (props.dismissKey) { try { sessionStorage.setItem(storeKey(props.dismissKey), '1'); } catch { /* remembered until the page reloads */ } }
  emit('dismiss');
}
</script>
<template>
  <div v-if="show && !hidden" :id="id" class="oui-banner" :data-dismissible="dismissible || undefined" :data-tone="TONE[props.tone ?? 'info']" :role="props.tone === 'error' ? 'alert' : 'status'">
    <OuiIcon class="oui-banner-icon" :icon="icon ?? ICON[props.tone ?? 'info']" :size="16" tile :tone="TONE[props.tone ?? 'info']" />
    <p class="oui-banner-text"><strong>{{ title }}</strong> <span v-if="$slots.default"><slot /></span></p>
    <div v-if="$slots.actions" class="oui-banner-actions"><slot name="actions" /></div>
    <button v-if="dismissible" type="button" class="oui-banner-close" :aria-label="closeLabel ?? 'Close'" :title="closeLabel ?? 'Close'" @click="dismiss">
      <OuiIcon :icon="close" :size="14" />
    </button>
  </div>
</template>
<style>
.oui-banner { display: flex; flex-wrap: wrap; align-items: center; gap: 6px 10px; min-height: 44px; padding: 6px 8px; border-radius: var(--oui-radius-lg);
  background: var(--oui-tone-soft); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-tone) 40%, transparent); }
.oui-banner-text { flex: 1 1 150px; min-width: 0; padding-block: 3px; }
.oui-banner-text > strong { font-weight: 700; margin-inline-end: 4px; }
.oui-banner-actions { display: flex; flex-wrap: wrap; gap: 6px; margin-inline-start: auto; }
/* The close button keeps the top-right corner however the text and actions wrap. */
.oui-banner[data-dismissible] { position: relative; padding-inline-end: 40px; }
.oui-banner-close { position: absolute; top: 8px; right: 8px; display: inline-grid; place-items: center; width: 28px; height: 28px; border: 0; border-radius: var(--oui-radius);
  color: var(--oui-muted); background: none; cursor: pointer; }
.oui-banner-close:hover { color: var(--oui-text); background: color-mix(in srgb, var(--oui-tone) 14%, transparent); }
</style>
