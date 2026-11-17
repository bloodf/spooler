<script setup lang="ts">
import { nextTick, onBeforeUnmount, onMounted, ref, watch } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { error, warning, type OuiIconData } from '../icons';
import { toastList } from './toast';

/*
 * The settings page: one section at a time, picked from tabs (a side list when wide, a scrolling strip when narrow), and
 * one footer that owns saving (what changed, discard, save). Put OuiFormSection (with ids matching `sections`) in the
 * default slot; `.oui-stack` wrappers are allowed and flattened. Only the selected section shows.
 *
 * The page is as tall as the window under whatever sits above it, at every height: the selected section scrolls inside
 * and the footer is always on screen. The height follows the viewport in CSS (dvh); the offset above and below is
 * measured again on every resize of the window or of the page, never once at load.
 *
 * The last tab is remembered per page; #<section id> in the address opens that section; `select(id)` opens one from code.
 */
export interface OuiSettingsSection { id: string; label: string; icon?: OuiIconData; state?: 'warn' | 'error' }
const props = defineProps<{ sections: OuiSettingsSection[]; navLabel: string }>();
const root = ref<HTMLElement>();
const body = ref<HTMLElement>();
const tabs = ref<HTMLElement>();
const foot = ref<HTMLElement>();
// While the save bar is on screen the toast stack sits above it (--oui-toast-bottom on the root, read by OuiToastHost).
// A settings view kept mounted but hidden (v-show on another tab) has a bar of height 0 and gives the space back.
let footSet = false;
function liftToasts() {
  const r = foot.value?.getBoundingClientRect();
  const style = document.documentElement.style;
  // From the top of the bar to the bottom of the window, plus a gap: right whether the bar is at the very bottom or the
  // page has a little room under it.
  if (r && r.height > 0 && r.top < innerHeight) {
    const value = `${Math.ceil(innerHeight - r.top) + 12}px`;
    if (style.getPropertyValue('--oui-toast-bottom') !== value) style.setProperty('--oui-toast-bottom', value);
    footSet = true;
  } else if (footSet) { style.removeProperty('--oui-toast-bottom'); footSet = false; }
}
let liftFrame = 0;
const relift = () => { if (!liftFrame) liftFrame = requestAnimationFrame(() => { liftFrame = 0; liftToasts(); }); };
// Measured again whenever a toast comes, so the stack is placed against where the bar is now, whatever moved it.
watch(() => toastList.list.length, () => { liftToasts(); relift(); }, { flush: 'post' });
let footSizes: ResizeObserver | undefined;

const storeKey = () => 'oui-settings:' + location.pathname + ':' + props.sections.map(s => s.id).join(',');
const known = (id: string | null | undefined) => !!id && props.sections.some(s => s.id === id);
function initial(): string {
  const hash = typeof location !== 'undefined' ? decodeURIComponent(location.hash.slice(1)) : '';
  if (known(hash)) return hash;
  let saved: string | null = null;
  try { saved = localStorage.getItem(storeKey()); } catch { /* storage blocked: start at the first section */ }
  return known(saved) ? (saved as string) : props.sections[0]?.id ?? '';
}
const current = ref(initial());
watch(() => props.sections.map(s => s.id).join(','), () => { if (!known(current.value)) current.value = props.sections[0]?.id ?? ''; });

// Show only the selected section. The sections are the page's own elements, so this follows them as they come and go.
function sync() {
  if (!body.value) return;
  for (const s of props.sections) {
    const el = body.value.querySelector<HTMLElement>(`#${CSS.escape(s.id)}`);
    if (el) el.hidden = s.id !== current.value;
  }
}
watch(current, (id) => {
  sync();
  body.value?.scrollTo?.({ top: 0 });
  tabs.value?.querySelector<HTMLElement>(`[data-section="${CSS.escape(id)}"]`)?.scrollIntoView?.({ block: 'nearest', inline: 'nearest' });
  try { localStorage.setItem(storeKey(), id); } catch { /* not remembered */ }
}, { flush: 'post' });

function select(id: string, focusTab = false) {
  if (!known(id)) return;
  current.value = id;
  if (focusTab) nextTick(() => tabs.value?.querySelector<HTMLElement>(`[data-section="${CSS.escape(id)}"]`)?.focus());
}
defineExpose({ select });

function onKey(event: KeyboardEvent) {
  const at = props.sections.findIndex(s => s.id === current.value);
  const last = props.sections.length - 1;
  const next = { ArrowDown: at + 1, ArrowRight: at + 1, ArrowUp: at - 1, ArrowLeft: at - 1, Home: 0, End: last }[event.key];
  if (next == null || last < 0) return;
  event.preventDefault();
  select(props.sections[(next + last + 1) % (last + 1)].id, true);
}

// The room the page leaves for the settings: what sits above it (app bar, banners) and below it (page padding, anything
// after it). Below is added up from the content itself, not read off the document height, which a min-height shell
// would inflate in step with the settings.
function trailing(el: HTMLElement): number {
  let sum = 0;
  for (let node: HTMLElement | null = el; node && node !== document.documentElement; node = node.parentElement) {
    const own = getComputedStyle(node);
    const gap = node.parentElement ? parseFloat(getComputedStyle(node.parentElement).rowGap) || 0 : 0;
    sum += parseFloat(own.marginBottom) || 0;
    for (let next = node.nextElementSibling as HTMLElement | null; next; next = next.nextElementSibling as HTMLElement | null) {
      const cs = getComputedStyle(next);
      if (cs.position === 'absolute' || cs.position === 'fixed' || cs.display === 'none') continue;
      sum += gap + next.getBoundingClientRect().height + (parseFloat(cs.marginTop) || 0) + (parseFloat(cs.marginBottom) || 0);
    }
    const parent = node.parentElement;
    if (parent && parent !== document.documentElement) {
      const ps = getComputedStyle(parent);
      sum += (parseFloat(ps.paddingBottom) || 0) + (parseFloat(ps.borderBottomWidth) || 0);
    }
  }
  return sum;
}
function measure() {
  const el = root.value;
  if (!el) return;
  const box = el.getBoundingClientRect();
  const above = Math.max(0, box.top + window.scrollY);
  const below = trailing(el);
  const value = `${Math.round(above + below)}px`;
  if (el.style.getPropertyValue('--oui-settings-offset') !== value) el.style.setProperty('--oui-settings-offset', value);
  relift();   // the bar moves with the settings' height
}
// Measured on the next frame, not inside the observer's own callback: setting the height there would resize what it
// observes in the same frame (the browser reports that as a ResizeObserver loop).
let frame = 0;
const remeasure = () => { if (!frame) frame = requestAnimationFrame(() => { frame = 0; measure(); }); };
// Focus moving into a hidden section (a validation error, a link, a search) opens that section's tab.
function onFocusIn(event: FocusEvent) {
  const target = event.target as HTMLElement | null;
  const section = props.sections.find(s => target?.closest(`#${CSS.escape(s.id)}`));
  if (section && section.id !== current.value) current.value = section.id;
}
let mutations: MutationObserver | undefined; let sizes: ResizeObserver | undefined;
const onHash = () => { const id = decodeURIComponent(location.hash.slice(1)); if (known(id)) select(id); };
onMounted(() => {
  sync();
  if (body.value && typeof MutationObserver !== 'undefined') {
    mutations = new MutationObserver(sync);
    mutations.observe(body.value, { childList: true, subtree: true });
  }
  measure();
  window.addEventListener('resize', remeasure);
  window.addEventListener('resize', relift);
  window.addEventListener('scroll', relift, { passive: true });
  body.value?.addEventListener('focusin', onFocusIn);
  window.addEventListener('hashchange', onHash);
  if (typeof ResizeObserver !== 'undefined') {
    footSizes = new ResizeObserver(relift);
    if (foot.value) footSizes.observe(foot.value);
    footSizes.observe(document.body);
    if (root.value) footSizes.observe(root.value);
    sizes = new ResizeObserver(remeasure);
    sizes.observe(document.body);
    if (root.value?.parentElement) sizes.observe(root.value.parentElement);
  }
});
onBeforeUnmount(() => {
  mutations?.disconnect(); sizes?.disconnect(); footSizes?.disconnect(); cancelAnimationFrame(liftFrame);
  window.removeEventListener('resize', relift); window.removeEventListener('scroll', relift);
  if (footSet) document.documentElement.style.removeProperty('--oui-toast-bottom');
  cancelAnimationFrame(frame);
  window.removeEventListener('resize', remeasure); window.removeEventListener('hashchange', onHash);
});
</script>
<template>
  <div ref="root" class="oui-settings"><div class="oui-settings-grid">
    <nav class="oui-settings-nav" :aria-label="navLabel">
      <div ref="tabs" class="oui-settings-tabs" role="tablist" aria-orientation="vertical" :aria-label="navLabel" @keydown="onKey">
        <button v-for="s in sections" :key="s.id" type="button" role="tab" class="oui-settings-link" :id="'oui-settings-tab-' + s.id" :data-section="s.id"
          :aria-selected="current === s.id" :aria-current="current === s.id ? 'true' : undefined" aria-controls="oui-settings-panel"
          :tabindex="current === s.id ? 0 : -1" :data-state="s.state" @click="select(s.id)">
          <OuiIcon v-if="s.icon" :icon="s.icon" :size="15" /><span>{{ s.label }}</span>
          <OuiIcon v-if="s.state" :icon="s.state === 'error' ? error : warning" :size="13" class="oui-settings-flag" />
        </button>
      </div>
    </nav>
    <div id="oui-settings-panel" ref="body" class="oui-settings-body" role="tabpanel" :aria-labelledby="'oui-settings-tab-' + current" tabindex="-1"><slot /></div>
    <footer v-if="$slots.footer" ref="foot" class="oui-settings-foot"><slot name="footer" /></footer>
  </div></div>
</template>
<style>
/* The container is the outer element and the grid an inner one: a container query cannot restyle its own container.
   Its height is the viewport's (dvh where the web view has it) less what the page puts above and below it; the section
   scrolls inside, so the footer stays on screen whatever the window height. */
.oui-settings { container: oui-settings / inline-size; --oui-settings-offset: 52px;
  height: max(240px, calc(100vh - var(--oui-settings-offset))); height: max(240px, calc(100dvh - var(--oui-settings-offset))); }
.oui-settings-grid { display: grid; height: 100%; grid-template-columns: 208px minmax(0, 1fr); grid-template-rows: minmax(0, 1fr) auto;
  grid-template-areas: 'nav body' 'foot foot'; gap: 0 var(--oui-s4); padding: var(--oui-s3) var(--oui-s4) 0; }
.oui-settings-nav { grid-area: nav; min-height: 0; overflow-y: auto; }
.oui-settings-tabs { display: grid; gap: 1px; align-content: start; }
.oui-settings-link { display: flex; align-items: center; gap: var(--oui-s2); width: 100%; min-height: 34px; padding: 0 10px; border: 0; border-radius: var(--oui-radius);
  font-weight: 600; text-align: start; background: none; cursor: pointer; transition: background var(--oui-fast), color var(--oui-fast); }
.orca-ui .oui-settings-link { color: var(--oui-muted); }
.orca-ui .oui-settings-link:hover { color: var(--oui-text); background: var(--oui-raised); }
.orca-ui .oui-settings-link[aria-selected='true'] { color: var(--oui-on-primary); background: var(--oui-primary); }
.oui-settings-link[aria-selected='true'] .oui-settings-flag { color: inherit; }
.oui-settings-flag { margin-inline-start: auto; color: var(--oui-warning); }
.oui-settings-link[data-state='error'] .oui-settings-flag { color: var(--oui-danger); }
/* One column, one section: wrappers are flattened so no empty column or uneven second column is left behind. */
.oui-settings-body { grid-area: body; min-height: 0; overflow-y: auto; overscroll-behavior: contain; display: grid; grid-template-columns: minmax(0, 1fr);
  gap: var(--oui-s3); align-content: start; max-width: 960px; padding-bottom: var(--oui-s4); }
.orca-ui .oui-settings-body:focus { outline: none; }
.oui-settings-body > .oui-stack { display: contents; }
.oui-settings-foot { grid-area: foot; position: sticky; bottom: 0; z-index: 5; display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2) var(--oui-s3);
  margin-inline: calc(-1 * var(--oui-s4)); padding: var(--oui-s2) var(--oui-s4); background: var(--oui-surface); border-top: 1px solid var(--oui-border); box-shadow: 0 -6px 16px rgb(0 0 0 / .12); }
@container oui-settings (max-width: 820px) {
  .oui-settings-grid { grid-template-columns: minmax(0, 1fr); grid-template-rows: auto minmax(0, 1fr) auto; grid-template-areas: 'nav' 'body' 'foot'; }
  .oui-settings-nav { overflow: visible; }
  .oui-settings-tabs { display: flex; gap: var(--oui-s1); overflow-x: auto; padding-bottom: var(--oui-s2); scrollbar-width: none; }
  .oui-settings-link { flex: none; width: auto; }
}
</style>
