<script setup lang="ts">
// Settings as pages, on top of the shared OuiSettings (one section shown, side list when wide, last page remembered,
// #<id> deep links). Added here: under 700 px the list and the page take turns (a page has a Back button), focus moves
// to the page's heading when a page is opened, and a page with an invalid field is flagged in the list.
import Button from "primevue/button";
import { computed, nextTick, onBeforeUnmount, onMounted, ref } from "vue";
import { OuiIcon, OuiSettings, type OuiSettingsSection } from "../../shared/src/components";
import { chevronRight } from "../../shared/src/icons";

const props = defineProps<{ sections: OuiSettingsSection[]; navLabel: string; backLabel: string; errorLabel: string }>();
const inner = ref<{ select: (id: string) => void }>();
const wrap = ref<HTMLElement>();
const current = ref("");
const open = ref(false); // narrow only: a page is showing instead of the list
const invalid = ref<string[]>([]);
const INVALID = '[aria-invalid="true"], .p-invalid, [role="alert"]';

const flagged = computed(() => props.sections.map((s) => (invalid.value.includes(s.id) && !s.state ? { ...s, state: "error" as const } : s)));

function read(): void {
  const el = wrap.value;
  if (!el) return;
  current.value = el.querySelector<HTMLElement>('.oui-settings-link[aria-selected="true"]')?.dataset.section ?? "";
  invalid.value = props.sections.filter((s) => el.querySelector(`#${CSS.escape(s.id)}`)?.querySelector(INVALID)).map((s) => s.id);
  // the flag icon is drawn only: say it in the tab's name too
  for (const s of flagged.value) {
    const link = el.querySelector<HTMLElement>(`.oui-settings-link[data-section="${CSS.escape(s.id)}"]`);
    if (s.state === "error") link?.setAttribute("aria-label", `${s.label}, ${props.errorLabel}`);
    else link?.removeAttribute("aria-label");
  }
}

function focusHeading(): void {
  const h = wrap.value?.querySelector<HTMLElement>(`#${CSS.escape(current.value)} .oui-panel-title`);
  if (!h) return;
  h.tabIndex = -1;
  h.focus();
}
const afterRender = (fn: () => void): void => void nextTick(() => requestAnimationFrame(() => { read(); fn(); }));

/** Open a page from code (a deep link): shown at once, also when narrow, with focus on its heading. */
function select(id: string): void {
  inner.value?.select(id);
  open.value = true;
  afterRender(focusHeading);
}
defineExpose({ select });

function onClick(event: MouseEvent): void {
  if (!(event.target as HTMLElement).closest(".oui-settings-link")) return;
  open.value = true;
  afterRender(focusHeading);
}
function back(): void {
  open.value = false;
  afterRender(() => wrap.value?.querySelector<HTMLElement>(`.oui-settings-link[data-section="${CSS.escape(current.value)}"]`)?.focus());
}

// #<page id> in the address (OuiSettings selects it): open that page, also when narrow.
function onHash(): void {
  const id = decodeURIComponent(location.hash.slice(1));
  if (props.sections.some((s) => s.id === id)) select(id);
}
let watcher: MutationObserver | undefined;
onMounted(() => {
  read();
  if (props.sections.some((s) => s.id === decodeURIComponent(location.hash.slice(1)))) open.value = true;
  window.addEventListener("hashchange", onHash);
  // ponytail: rescans on every DOM change under Settings; cheap at a few hundred nodes, debounce if a page grows large
  watcher = new MutationObserver(read);
  if (wrap.value) watcher.observe(wrap.value, { subtree: true, childList: true, attributes: true, attributeFilter: ["aria-selected", "aria-invalid", "class", "role"] });
});
onBeforeUnmount(() => { watcher?.disconnect(); window.removeEventListener("hashchange", onHash); });
</script>

<template>
  <div ref="wrap" class="spg" :data-open="open || undefined" @click="onClick">
    <OuiSettings ref="inner" :sections="flagged" :nav-label="navLabel">
      <div class="spg-bar">
        <Button type="button" text size="small" severity="secondary" class="spg-back" data-test="settings-back" @click.stop="back">
          <OuiIcon :icon="chevronRight" :size="14" class="spg-back-icon" /><span>{{ backLabel }}</span>
        </Button>
      </div>
      <slot />
      <template v-if="$slots.footer" #footer><slot name="footer" /></template>
    </OuiSettings>
  </div>
</template>

<style>
/* Wide (700 px and up): the side list beside the page, also between 700 and 820 px, where OuiSettings would use a strip. */
.spg-bar { display: none; }
@container oui-settings (min-width: 700px) and (max-width: 820px) {
  .spg .oui-settings-grid { grid-template-columns: 208px minmax(0, 1fr); grid-template-rows: minmax(0, 1fr) auto; grid-template-areas: 'nav body' 'foot foot'; }
  .spg .oui-settings-nav { overflow-y: auto; }
  .spg .oui-settings-tabs { display: grid; gap: 1px; overflow: visible; padding-bottom: 0; }
  .spg .oui-settings-link { width: 100%; }
}
/* Narrow: the list of pages, or one page with Back. */
@container oui-settings (max-width: 699.98px) {
  .spg .oui-settings-tabs { display: grid; gap: 1px; overflow: visible; padding-bottom: 0; }
  .spg .oui-settings-link { width: 100%; min-height: 44px; }
  .spg:not([data-open]) .oui-settings-grid { grid-template-rows: minmax(0, 1fr) auto; grid-template-areas: 'nav' 'foot'; }
  .spg:not([data-open]) .oui-settings-nav { overflow-y: auto; }
  .spg:not([data-open]) .oui-settings-body { display: none; }
  .spg[data-open] .oui-settings-grid { grid-template-rows: minmax(0, 1fr) auto; grid-template-areas: 'body' 'foot'; }
  .spg[data-open] .oui-settings-nav { display: none; }
  .spg-bar { display: flex; }
  .spg-back-icon { transform: scaleX(-1); }
}
</style>
