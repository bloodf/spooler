<script setup lang="ts">
import Message from 'primevue/message';
import { m } from '../state/main';
import { t } from '../core/i18n';
// X01/X05: with U1 Control running in this OrcaSlicer, say in one line where the U1 printer and its links live,
// and why there are two tabs. The host can't merge or hide tabs; nothing here claims it does.
defineProps<{ where: 'spools' | 'printer' }>();
</script>
<template>
  <Message v-if="m.peers.u1control" severity="info" data-test="peer-u1">
    <span>{{ where === 'printer' ? t('peer.printer') : t('peer.spools') }}</span>
    <details class="pn"><summary>{{ t('peer.whyTitle') }}</summary><p>{{ t('peer.whyBody') }}</p></details>
  </Message>
</template>
<style scoped>.pn summary { cursor: pointer; } .pn p { margin: 6px 0 0; }</style>
