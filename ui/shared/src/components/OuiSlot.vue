<script setup lang="ts">
import { computed } from 'vue';
import OuiSpool from './OuiSpool.vue';
import OuiLevel from './OuiLevel.vue';

/*
 * Where a spool sits on a printer: a toolhead, an ACE or AMS slot, an external holder. The top of the card is a sample
 * of the filament's own colour, framed by the card so it reads as material, not as interface; the badge on it is the
 * slot's identity (its label and, for toolheads, its fixed colour). An empty slot has a hatched sample and a dashed frame.
 * The amount is grams left of grams total with a level bar; give `#amount` to show anything else, or nothing.
 * Per-slot reasons for disabled actions do not belong here: the page says the reason once (OuiBanner).
 */
const props = defineProps<{ label: string; /** Toolhead identity colour 1..4; omit for plain numbered slots. */ tool?: 1 | 2 | 3 | 4;
  name?: string | null; material?: string | null; color?: string | null; colors?: string[] | null;
  remaining?: number | null; initial?: number | null; unit?: string; emptyLabel: string; unknownLabel?: string;
  active?: boolean; low?: boolean }>();
const empty = computed(() => !props.name && !props.material);
const fraction = computed(() => (typeof props.remaining === 'number' && typeof props.initial === 'number' && props.initial > 0
  ? Math.max(0, Math.min(1, props.remaining / props.initial)) : null));
const paint = computed(() => {
  const list = props.colors && props.colors.length > 1 ? props.colors : null;
  if (list) return 'linear-gradient(90deg, ' + list.map((c, i) => `${c} ${(i * 100) / list.length}% ${((i + 1) * 100) / list.length}%`).join(', ') + ')';
  return props.color || '';
});
// The page language, not the browser's: a pt-BR page in an English browser still writes 1.380.
const grams = (n: number) => Math.round(n).toLocaleString(document.documentElement.lang || undefined);
</script>
<template>
  <article class="oui-slot" :data-active="active || undefined" :data-empty="empty || undefined">
    <header class="oui-slot-sample" :data-unknown="!paint || undefined" :style="paint ? { background: paint } : undefined">
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
.oui-slot { display: flex; flex-direction: column; gap: var(--oui-s2); min-width: 0; padding: 6px 6px var(--oui-s2); border-radius: var(--oui-radius-lg);
  background: var(--oui-raised); box-shadow: inset 0 0 0 1px var(--oui-border); }
.oui-slot[data-active] { box-shadow: inset 0 0 0 2px var(--oui-primary); }
.oui-slot[data-empty] { background: none; box-shadow: none; outline: 1.5px dashed var(--oui-control-border); outline-offset: -1.5px; }
.oui-slot > :not(.oui-slot-sample) { padding-inline: 6px; }
/* The sample: the filament's colour at size, with a hairline so black, white and clear still read. */
.oui-slot-sample { display: flex; align-items: center; justify-content: space-between; gap: var(--oui-s2); min-height: 40px; padding: 0 8px;
  border-radius: var(--oui-radius); box-shadow: inset 0 0 0 1px color-mix(in srgb, var(--oui-text) 30%, transparent); }
.oui-slot-sample[data-unknown] { background: repeating-linear-gradient(135deg, transparent 0 6px, color-mix(in srgb, var(--oui-control-border) 45%, transparent) 6px 7px); }
.oui-slot-badge { display: inline-grid; place-items: center; min-width: 28px; height: 24px; padding: 0 7px; border-radius: var(--oui-radius);
  font-size: var(--oui-text-md); font-weight: 700; color: var(--oui-text); background: var(--oui-surface); box-shadow: 0 0 0 1px color-mix(in srgb, var(--oui-text) 30%, transparent); }
.oui-slot-badge[data-tool] { color: var(--oui-on-tool); }
.oui-slot-badge[data-tool='1'] { background: var(--oui-tool1); }
.oui-slot-badge[data-tool='2'] { background: var(--oui-tool2); }
.oui-slot-badge[data-tool='3'] { background: var(--oui-tool3); }
.oui-slot-badge[data-tool='4'] { background: var(--oui-tool4); }
.oui-slot-state > .oui-status { box-shadow: 0 0 0 1px color-mix(in srgb, var(--oui-text) 30%, transparent); }
.oui-slot-main { display: flex; align-items: center; gap: var(--oui-s3); min-width: 0; }
.oui-slot-id { display: grid; gap: 1px; min-width: 0; }
.oui-slot-name { font-weight: 700; display: -webkit-box; -webkit-box-orient: vertical; -webkit-line-clamp: 2; line-clamp: 2; overflow: hidden; overflow-wrap: anywhere; }
.oui-slot[data-empty] .oui-slot-name { font-weight: 500; color: var(--oui-muted); }
.oui-slot-amount { display: grid; gap: 5px; line-height: 20px; }
.oui-slot-amount strong { font-size: var(--oui-text-lg); font-weight: 700; }
.oui-slot-extra { display: grid; gap: var(--oui-s2); }
.oui-slot-actions { display: flex; flex-wrap: wrap; gap: var(--oui-s1); margin-top: auto; padding-top: var(--oui-s1); }
</style>
