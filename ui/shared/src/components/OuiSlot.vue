<script setup lang="ts">
import { computed } from 'vue';
import OuiSpool from './OuiSpool.vue';
import OuiLevel from './OuiLevel.vue';

/*
 * Where a spool sits on a printer: a toolhead, an ACE or AMS slot, an external holder. A neutral card with a 4 px strip of
 * the filament's own colour across its top, ringed so black, white and clear still read; the drawn spool shows the same
 * colour at size. The badge is the slot's identity (its label and, for toolheads, its fixed colour). An empty slot has a
 * dashed frame and no strip.
 * The amount is grams left of grams total with a level bar; give `#amount` to show anything else, or nothing.
 * Per-slot reasons for disabled actions do not belong here: the page says the reason once (OuiBanner).
 */
const props = defineProps<{ label: string; /** Toolhead identity colour 1..4; omit for plain numbered slots. */ tool?: 1 | 2 | 3 | 4;
  name?: string | null; material?: string | null; color?: string | null; colors?: string[] | null;
  remaining?: number | null; initial?: number | null; unit?: string; emptyLabel: string; unknownLabel?: string;
  active?: boolean; low?: boolean }>();
const empty = computed(() => !props.name && !props.material);
const paint = computed(() => {
  const list = props.colors && props.colors.length > 1 ? props.colors : null;
  if (list) return 'linear-gradient(90deg, ' + list.map((c, i) => `${c} ${(i * 100) / list.length}% ${((i + 1) * 100) / list.length}%`).join(', ') + ')';
  return props.color || '';
});
const fraction = computed(() => (typeof props.remaining === 'number' && typeof props.initial === 'number' && props.initial > 0
  ? Math.max(0, Math.min(1, props.remaining / props.initial)) : null));
// The page language, not the browser's: a pt-BR page in an English browser still writes 1.380.
const grams = (n: number) => Math.round(n).toLocaleString(document.documentElement.lang || undefined);
</script>
<template>
  <article class="oui-slot" :data-active="active || undefined" :data-empty="empty || undefined">
    <span v-if="!empty" class="oui-slot-strip" :data-unknown="!paint || undefined" :style="paint ? { background: paint } : undefined" aria-hidden="true" />
    <header class="oui-slot-head">
      <span class="oui-slot-badge oui-num" :data-tool="tool">{{ label }}</span>
      <span v-if="$slots.state" class="oui-slot-state"><slot name="state" /></span>
    </header>
    <div class="oui-slot-main">
      <OuiSpool :color="empty ? null : color" :colors="empty ? null : colors" :fraction="empty ? null : fraction" :size="52" />
      <div class="oui-slot-id">
        <p class="oui-slot-name" :title="name ?? undefined">{{ empty ? emptyLabel : name || material }}</p>
        <p v-if="!empty" class="oui-meta oui-truncate"><slot name="meta">{{ material }}</slot></p>
      </div>
    </div>
    <!-- #amount replaces the weight line and level (percent-only trays, hidden weight or bar, other units). Wrap its content
         in .oui-slot-amount for the built-in look; rendering nothing in it leaves no gap. -->
    <template v-if="$slots.amount"><slot v-if="!empty" name="amount" :fraction="fraction" /></template>
    <div v-else-if="!empty" class="oui-slot-amount">
      <p v-if="remaining == null" class="oui-muted">{{ unknownLabel ?? '—' }}</p>
      <p v-else class="oui-num"><strong>{{ grams(remaining) }}</strong> {{ unit ?? 'g' }}<span v-if="initial != null" class="oui-muted"> / {{ grams(initial) }} {{ unit ?? 'g' }}</span></p>
      <OuiLevel :fraction="fraction" :tone="low ? 'low' : 'normal'" />
    </div>
    <div v-if="$slots.default" class="oui-slot-extra"><slot /></div>
    <footer v-if="$slots.actions" class="oui-slot-actions"><slot name="actions" /></footer>
  </article>
</template>
<style>
.oui-slot { display: flex; flex-direction: column; gap: var(--oui-s2); min-width: 0; padding: var(--oui-s2) var(--oui-s1) var(--oui-s2); border-radius: var(--oui-radius-lg);
  background: var(--oui-raised); box-shadow: inset 0 0 0 1px var(--oui-border); }
.oui-slot[data-active] { box-shadow: inset 0 0 0 2px var(--oui-primary-mark); }
.oui-slot[data-empty] { background: none; box-shadow: none; outline: 1.5px dashed var(--oui-control-border); outline-offset: -1.5px; }
.oui-slot > :not(.oui-slot-strip) { padding-inline: 6px; }
/* The strip: 4 px of the filament's colour inside a hairline ring. Hatched when the colour is not known. */
.oui-slot-strip { display: block; height: 6px; margin: -2px 2px 0; border: 1px solid color-mix(in srgb, var(--oui-text) 34%, transparent); border-radius: 3px; background-clip: padding-box; }
.oui-slot-strip[data-unknown] { background: repeating-linear-gradient(135deg, transparent 0 4px, color-mix(in srgb, var(--oui-control-border) 55%, transparent) 4px 5px); }
.oui-slot-head { display: flex; align-items: center; justify-content: space-between; gap: var(--oui-s2); min-height: 22px; }
.oui-slot-main { display: flex; align-items: center; gap: var(--oui-s3); min-width: 0; }
.oui-slot-id { display: grid; gap: 1px; min-width: 0; }
.oui-slot-name { font-weight: 700; display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2; line-clamp: 2; overflow: hidden; overflow-wrap: anywhere; }
.oui-slot[data-empty] .oui-slot-name { font-weight: 500; color: var(--oui-muted); }
.oui-slot-amount { display: grid; gap: 5px; line-height: 20px; }
.oui-slot-amount strong { font-size: var(--oui-text-lg); font-weight: 700; }
.oui-slot-extra { display: grid; gap: var(--oui-s2); }
.oui-slot-actions { display: flex; flex-wrap: wrap; gap: var(--oui-s1); margin-top: auto; padding-top: var(--oui-s1); }
</style>
