<script setup lang="ts">
import { m } from '../state/main';
import { t } from '../core/i18n';
// X01/X05: with U1 Control running in this OrcaSlicer, the page header's (i) says where the U1 printer and its links
// live, and why there are two tabs. The host can't merge or hide tabs; nothing here claims it does.
defineProps<{ where: 'spools' | 'printer' }>();
</script>
<template>
  <span v-if="m.peers.u1control" class="sp-hint-p" data-test="peer-u1">
    <span class="sp-hint-p">{{ where === 'printer' ? t('peer.printer') : t('peer.spools') }}</span><span class="sp-hint-p"><strong>{{ t('peer.whyTitle') }}</strong> {{ t('peer.whyBody') }}</span>
  </span>
</template>
