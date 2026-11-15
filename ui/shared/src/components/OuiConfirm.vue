<script setup lang="ts">
import Button from 'primevue/button';
import Dialog from 'primevue/dialog';

/*
 * The protected-decision dialog: what will happen, in the user's terms, with the action named on its button.
 * For a destructive action focus starts on the way back, and the confirm button is the only solid red on the page.
 */
defineProps<{ visible: boolean; title: string; confirmLabel: string; cancelLabel: string; danger?: boolean; busy?: boolean }>();
const emit = defineEmits<{ 'update:visible': [value: boolean]; confirm: []; cancel: [] }>();
function cancel() { emit('cancel'); emit('update:visible', false); }
</script>
<template>
  <Dialog :visible="visible" modal :header="title" :closable="!busy" :close-on-escape="!busy" :style="{ width: '420px', maxWidth: 'calc(100vw - 32px)' }"
    data-dlg @update:visible="(v: boolean) => v || cancel()">
    <div class="oui-confirm-body"><slot /></div>
    <template #footer>
      <Button :label="cancelLabel" severity="secondary" :autofocus="danger" :disabled="busy" data-dlg="cancel" @click="cancel" />
      <Button :label="confirmLabel" :severity="danger ? 'danger' : undefined" :autofocus="!danger" :loading="busy" data-dlg="confirm" @click="emit('confirm')" />
    </template>
  </Dialog>
</template>
<style>
.oui-confirm-body { display: grid; gap: var(--oui-s2); color: var(--oui-text); }
</style>
