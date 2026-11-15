<script setup lang="ts">
import { OuiBanner } from '../../shared/src/components';
import { m } from '../state/main';
import { t } from '../core/i18n';
// X01/X05: with U1 Control running in this OrcaSlicer, say in one line where the U1 printer and its links live,
// and why there are two tabs. The host can't merge or hide tabs; nothing here claims it does.
defineProps<{ where: 'spools' | 'printer' }>();
</script>
<template>
  <OuiBanner v-if="m.peers.u1control" tone="info" :title="where === 'printer' ? t('peer.printer') : t('peer.spools')" data-test="peer-u1">
    <details class="pn"><summary>{{ t('peer.whyTitle') }}</summary><p>{{ t('peer.whyBody') }}</p></details>
  </OuiBanner>
</template>
<style>
.pn { display: inline; }
.pn summary { display: inline; cursor: pointer; color: var(--oui-primary); font-weight: 600; }
.pn[open] { display: block; margin-top: var(--oui-s1); }
</style>
