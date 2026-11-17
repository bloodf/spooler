<script setup lang="ts">
import { watch } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { check, error, info, warning, x as close } from '../icons';
import { dismissToast, pauseToast, resumeToast, toastList, type OuiToastTone } from './toast';
import type { OuiTone } from './tones';

/*
 * Where toasts appear: bottom-left, stacked, newest at the bottom. Mount once, at the end of the app's root. Errors are
 * role="alert", the rest role="status". Closing a focused toast returns focus to where it came from.
 */
const props = defineProps<{ /** Accessible name of each close button. */ closeLabel?: string; /** Accessible name of the region. */ label?: string }>();
const TONE: Record<OuiToastTone, OuiTone> = { info: 'info', success: 'success', warn: 'warn', error: 'danger' };
const ICON = { info, success: check, warn: warning, error };

const cameFrom = new Map<number, HTMLElement>();
function onFocusIn(id: number, event: FocusEvent) {
  pauseToast(id);
  const from = event.relatedTarget;
  if (from instanceof HTMLElement && !(event.currentTarget as HTMLElement).contains(from)) cameFrom.set(id, from);
}
function onLeave(id: number, event: Event) {
  const card = event.currentTarget as HTMLElement;
  queueMicrotask(() => { if (!card.matches(':hover') && !card.contains(document.activeElement)) resumeToast(id); });
}
function run(id: number, action: () => void) { try { action(); } finally { dismissToast(id); } }
// The moment a toast that holds focus is closed (its X, its action, code, or the stack making room), focus goes back to
// where it came from: synchronously, while the card is still in the page, not after its leave animation.
watch(() => toastList.list.map(t => t.id), (ids) => {
  const focused = document.activeElement instanceof HTMLElement ? document.activeElement.closest<HTMLElement>('[data-toast-id]') : null;
  const id = Number(focused?.dataset.toastId);
  if (focused && !ids.includes(id)) {
    const back = cameFrom.get(id);
    const target = back?.isConnected ? back : document.querySelector<HTMLElement>('main, #app');
    if (target && !target.hasAttribute('tabindex') && !target.matches('a[href], button, input, select, textarea')) target.setAttribute('tabindex', '-1');
    target?.focus({ preventScroll: true });
  }
  for (const key of cameFrom.keys()) if (!ids.includes(key)) cameFrom.delete(key);
}, { flush: 'sync' });
</script>
<template>
  <section class="oui-toasts" :aria-label="props.label ?? 'Notifications'">
    <TransitionGroup name="oui-toast">
      <div v-for="t in toastList.list" :key="t.id" class="oui-toast" :data-toast-id="t.id" :data-tone="TONE[t.tone]" :data-toast-tone="t.tone"
        :role="t.tone === 'error' ? 'alert' : 'status'" :aria-live="t.tone === 'error' ? 'assertive' : 'polite'" aria-atomic="true"
        @mouseenter="pauseToast(t.id)" @mouseleave="onLeave(t.id, $event)" @focusin="onFocusIn(t.id, $event)" @focusout="onLeave(t.id, $event)">
        <OuiIcon :icon="ICON[t.tone]" :size="14" tile :tone="TONE[t.tone]" />
        <p class="oui-toast-text"><strong>{{ t.title }}</strong><span v-if="t.body" class="oui-toast-body">{{ ' ' + t.body }}</span></p>
        <button v-if="t.action" type="button" class="oui-toast-action" @click="run(t.id, t.action.run)">{{ t.action.label }}</button>
        <button type="button" class="oui-toast-close" :aria-label="props.closeLabel ?? 'Close'" :title="props.closeLabel ?? 'Close'" @click="dismissToast(t.id)">
          <OuiIcon :icon="close" :size="14" />
        </button>
      </div>
    </TransitionGroup>
  </section>
</template>
<style>
/* Bottom-left, over the page; the stack keeps a gutter on the narrow dock. A page with its own bar along the bottom edge
   lifts the stack above it with --oui-toast-bottom. */
.oui-toasts { position: fixed; left: 16px; bottom: var(--oui-toast-bottom, 16px); z-index: 1100; display: grid; gap: var(--oui-s2); width: min(380px, calc(100vw - 32px));
  pointer-events: none; }
.oui-toast { pointer-events: auto; display: flex; align-items: flex-start; gap: var(--oui-s2); min-height: 44px; padding: 8px 6px 8px 10px; border-radius: var(--oui-radius-lg);
  color: var(--oui-text); background: var(--oui-surface); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-tone) 50%, transparent), inset 3px 0 0 var(--oui-tone), var(--oui-shadow-overlay); }
.oui-toast > .oui-icon { margin-top: 1px; }
.oui-toast-text { flex: 1 1 auto; min-width: 0; padding-top: 2px; overflow-wrap: anywhere; }
.oui-toast-text > strong { font-weight: 700; }
.oui-toast-action, .oui-toast-close { flex: none; display: inline-grid; place-items: center; min-height: 28px; border: 0; border-radius: var(--oui-radius); background: none; cursor: pointer; }
.oui-toast-action { padding: 0 8px; font-weight: 650; color: var(--oui-primary); }
.oui-toast-close { width: 28px; color: var(--oui-muted); }
.oui-toast-action:hover, .oui-toast-close:hover { color: var(--oui-text); background: var(--oui-raised); }
.oui-toast-enter-active, .oui-toast-leave-active { transition: opacity var(--oui-base) var(--oui-ease), transform var(--oui-base) var(--oui-ease); }
.oui-toast-enter-from, .oui-toast-leave-to { opacity: 0; transform: translateX(-12px); }
.oui-toast-leave-active { position: absolute; width: 100%; }
.oui-toast-move { transition: transform var(--oui-base) var(--oui-ease); }
@media (prefers-reduced-motion: reduce) { .oui-toast-enter-active, .oui-toast-leave-active, .oui-toast-move { transition: none; } .oui-toast-enter-from, .oui-toast-leave-to { transform: none; } }
</style>
