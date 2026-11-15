<script setup lang="ts">
import Dialog from 'primevue/dialog';
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import { OuiConfirm } from '../../shared/src/components';
import { dialog, close, restoreFocus } from '../core/dialog';
import { t } from '../core/i18n';

// A yes/no decision is the shared confirmation; one that also asks for a value keeps a plain dialog with the same hooks.
function onVisible(v: boolean) { if (!v) close(dialog.cancelValue); }
</script>
<template>
  <Dialog v-if="dialog.input" :visible="dialog.visible" modal :header="dialog.title" :draggable="false" data-dlg
          :style="{ width: 'min(420px, calc(100vw - 32px))' }" :close-button-props="{ severity: 'secondary', text: true, rounded: true, 'aria-label': t('common.close') }"
          @update:visible="onVisible" @after-hide="restoreFocus">
    <form id="dlg-form" class="oui-stack" @submit.prevent="dialog.inputValue.trim() && close(dialog.inputValue)">
      <p class="dlg-text">{{ dialog.text }}</p>
      <div class="oui-field"><label for="dlg-input">{{ dialog.input.label }}</label>
        <InputText id="dlg-input" v-model="dialog.inputValue" :placeholder="dialog.input.placeholder" autofocus /></div>
    </form>
    <template #footer>
      <Button :label="dialog.no ?? t('common.goBack')" severity="secondary" data-dlg="cancel" @click="close(dialog.cancelValue)" />
      <Button type="submit" form="dlg-form" :label="dialog.yes ?? t('common.ok')" :severity="dialog.danger ? 'danger' : undefined" data-dlg="confirm" :disabled="!dialog.inputValue.trim()" />
    </template>
  </Dialog>
  <OuiConfirm v-else :visible="dialog.visible" :title="dialog.title" :confirm-label="dialog.yes ?? t('common.ok')" :cancel-label="dialog.no ?? t('common.goBack')"
              :danger="dialog.danger" @update:visible="onVisible" @confirm="close(true)" @after-hide="restoreFocus">
    <p class="dlg-text">{{ dialog.text }}</p>
  </OuiConfirm>
</template>
<style>
.dlg-text { white-space: pre-line; }
</style>
