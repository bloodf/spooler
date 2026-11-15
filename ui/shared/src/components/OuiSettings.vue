<script setup lang="ts">
import { onBeforeUnmount, onMounted, ref } from 'vue';
import OuiIcon from './OuiIcon.vue';
import { error, warning, type OuiIconData } from '../icons';

/*
 * The settings page: a section index that follows the scroll, the sections in columns that use the width,
 * and one footer that owns saving (what changed, discard, save). Put OuiFormSection (with matching ids) in the
 * default slot, grouped in `.oui-stack` columns in the order they should be read.
 */
export interface OuiSettingsSection { id: string; label: string; icon?: OuiIconData; state?: 'warn' | 'error' }
const props = defineProps<{ sections: OuiSettingsSection[]; navLabel: string }>();
const current = ref(props.sections[0]?.id ?? '');
const body = ref<HTMLElement>();
let observer: IntersectionObserver | undefined;
onMounted(() => {
  if (!body.value || typeof IntersectionObserver === 'undefined') return;
  observer = new IntersectionObserver((entries) => {
    const top = entries.filter(e => e.isIntersecting).sort((a, b) => a.boundingClientRect.top - b.boundingClientRect.top)[0];
    if (top) current.value = top.target.id;
  }, { rootMargin: '-56px 0px -60% 0px' });
  for (const s of props.sections) { const el = body.value.querySelector(`#${CSS.escape(s.id)}`); if (el) observer.observe(el); }
});
onBeforeUnmount(() => observer?.disconnect());
function go(id: string) {
  current.value = id;
  const el = body.value?.querySelector<HTMLElement>(`#${CSS.escape(id)}`);
  el?.scrollIntoView({ block: 'start', behavior: 'smooth' });
  el?.focus({ preventScroll: true });
}
</script>
<template>
  <div class="oui-settings"><div class="oui-settings-grid">
    <nav class="oui-settings-nav" :aria-label="navLabel">
      <a v-for="s in sections" :key="s.id" :href="'#' + s.id" class="oui-settings-link" :aria-current="current === s.id ? 'true' : undefined"
        :data-state="s.state" @click.prevent="go(s.id)">
        <OuiIcon v-if="s.icon" :icon="s.icon" :size="15" /><span>{{ s.label }}</span>
        <OuiIcon v-if="s.state" :icon="s.state === 'error' ? error : warning" :size="13" class="oui-settings-flag" />
      </a>
    </nav>
    <div ref="body" class="oui-settings-body"><slot /></div>
    <footer v-if="$slots.footer" class="oui-settings-foot"><slot name="footer" /></footer>
  </div></div>
</template>
<style>
/* The container is the outer element and the grid an inner one: a container query cannot restyle its own container. */
.oui-settings { container: oui-settings / inline-size; }
.oui-settings-grid { display: grid; grid-template-columns: 208px minmax(0, 1fr); grid-template-areas: 'nav body' 'foot foot';
  gap: 0 var(--oui-s4); padding: var(--oui-s3) var(--oui-s4) 0; align-items: start; }
.oui-settings-nav { grid-area: nav; position: sticky; top: 60px; display: grid; gap: 1px; }
.oui-settings-link { display: flex; align-items: center; gap: var(--oui-s2); min-height: 34px; padding: 0 10px; border-radius: var(--oui-radius);
  font-weight: 600; text-decoration: none; transition: background var(--oui-fast), color var(--oui-fast); }
.orca-ui .oui-settings-link { color: var(--oui-muted); }
.orca-ui .oui-settings-link:hover { color: var(--oui-text); background: var(--oui-raised); }
.orca-ui .oui-settings-link[aria-current] { color: var(--oui-on-primary); background: var(--oui-primary); }
.oui-settings-link[aria-current] .oui-settings-flag { color: inherit; }
.oui-settings-flag { margin-inline-start: auto; color: var(--oui-warning); }
.oui-settings-link[data-state='error'] .oui-settings-flag { color: var(--oui-danger); }
.oui-settings-body { grid-area: body; display: grid; grid-template-columns: repeat(auto-fit, minmax(min(100%, 440px), 1fr)); gap: var(--oui-s3); align-items: start;
  max-width: 1480px; padding-bottom: var(--oui-s4); }
.oui-settings-body :where(section) { scroll-margin-top: 60px; }
.oui-settings-foot { grid-area: foot; position: sticky; bottom: 0; z-index: 5; display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2) var(--oui-s3);
  margin-inline: calc(-1 * var(--oui-s4)); padding: var(--oui-s2) var(--oui-s4); background: var(--oui-surface); border-top: 1px solid var(--oui-border); box-shadow: 0 -6px 16px rgb(0 0 0 / .12); }
@container oui-settings (max-width: 820px) {
  .oui-settings-grid { grid-template-columns: minmax(0, 1fr); grid-template-areas: 'nav' 'body' 'foot'; }
  .oui-settings-nav { position: static; display: flex; gap: var(--oui-s1); overflow-x: auto; padding-bottom: var(--oui-s2); scrollbar-width: none; }
  .oui-settings-link { flex: none; }
}
</style>
