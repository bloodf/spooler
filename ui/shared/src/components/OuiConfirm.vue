<script setup lang="ts">
import { watch } from 'vue';
import Button from 'primevue/button';
import Dialog from 'primevue/dialog';

/*
 * The protected-decision dialog: what will happen, in the user's terms, with the action named on its button.
 * For a destructive action focus starts on the way back, and the confirm button is the only solid red on the page.
 * Once it has closed, focus goes back to what had it when it opened, if that is still on the page; then `closed` is
 * emitted, so a page whose action removed that element can put focus somewhere sensible itself.
 */
const props = defineProps<{ visible: boolean; title: string; confirmLabel: string; cancelLabel: string; danger?: boolean; busy?: boolean }>();
const emit = defineEmits<{ 'update:visible': [value: boolean]; confirm: []; cancel: []; closed: [] }>();
function cancel() { emit('cancel'); emit('update:visible', false); }
let opener: HTMLElement | null = null;
// Remembered before the dialog takes focus, and given back only after it has gone (PrimeVue keeps focus inside it until then).
watch(() => props.visible, (on) => { if (on) opener = document.activeElement instanceof HTMLElement && document.activeElement !== document.body ? document.activeElement : null; });
function afterHide() {
  const back = opener; opener = null;
  if (back?.isConnected && back.offsetParent !== null) back.focus();
  emit('closed');
}
</script>
<template>
  <Dialog :visible="visible" modal :header="title" :closable="!busy" :close-on-escape="!busy" :style="{ width: '420px', maxWidth: 'calc(100vw - 32px)' }"
    data-dlg @update:visible="(v: boolean) => v || cancel()" @after-hide="afterHide">
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
