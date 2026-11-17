<script setup lang="ts">
import Button from 'primevue/button';
import InputText from 'primevue/inputtext';
import Password from 'primevue/password';
import Select from 'primevue/select';
import RadioButton from 'primevue/radiobutton';
import { OuiBanner, OuiIcon } from '../../shared/src/components';
import { plug } from '../../shared/src/icons';
import { boot } from '../core/boot';
import { t } from '../core/i18n';
import { form, conn, bambu, test, checkBambu, bambuSend, setSource, onUrlInput } from './state';

// Where Spooler reads spools from. Spoolman: URL + Test (Save waits for a passing test). Bambu Cloud: sign in
// (experimental, unofficial service); the password is never stored and the field is cleared after sending.
const regions = [{ value: 'global', label: 'Global' }, { value: 'china', label: 'China' }];
function signIn() { bambuSend('password', { account: bambu.email, password: bambu.password, region: bambu.region }); bambu.password = ''; }
const tone = (k: string) => (k === 'ok' ? 'success' : k === 'error' ? 'error' : 'neutral');
// Whether the source is there at all, with how to get it, is the Requirements section (SettingsView).
</script>
<template>
  <div class="sb">
    <p class="oui-meta" id="src-l">{{ t('src.question') }}</p>
    <div class="oui-row sb-src" role="radiogroup" aria-labelledby="src-l">
      <span class="oui-row sb-opt"><RadioButton :model-value="form.source" input-id="src-spoolman" name="spool-source" value="spoolman" @update:model-value="setSource('spoolman', true)" /><label for="src-spoolman">Spoolman</label></span>
      <span class="oui-row sb-opt"><RadioButton :model-value="form.source" input-id="src-bambu" name="spool-source" value="bambu" @update:model-value="setSource('bambu', true)" /><label for="src-bambu">Bambu Cloud</label></span>
    </div>
    <template v-if="form.source === 'spoolman'">
      <label for="url">{{ t('src.url') }}</label>
      <form class="oui-row" @submit.prevent="test">
        <InputText id="url" v-model="form.url" class="sb-url oui-mono" :placeholder="boot.settings.default_url" autocomplete="off" aria-describedby="conn-status" @input="onUrlInput" />
        <Button type="submit" severity="secondary" :label="t('src.test')" data-test="test"><template #icon><OuiIcon :icon="plug" :size="14" /></template></Button></form>
      <div id="conn-status" aria-live="polite"><OuiBanner :tone="tone(conn.kind)" :title="conn.text" data-test="conn-status" /></div>
    </template>
    <template v-else>
      <div v-if="bambu.pane === 'in'" class="oui-row"><span class="oui-meta">{{ t('bambu.account') }}</span><strong>{{ bambu.account || t('bambu.signedOut') }}</strong>
        <Button severity="secondary" :label="t('bambu.test')" @click="checkBambu" />
        <Button severity="secondary" text :label="t('bambu.signOut')" @click="bambuSend('sign_out')" /></div>
      <form v-else-if="bambu.pane === 'login'" class="sb-login" @submit.prevent="signIn">
        <p class="oui-meta sb-full">{{ t('bambu.signInTitle') }}</p>
        <label class="oui-field"><span>{{ t('bambu.email') }}</span><InputText v-model="bambu.email" autocomplete="off" /></label>
        <div class="oui-field"><label for="bambu-pass">{{ t('bambu.password') }}</label><Password v-model="bambu.password" input-id="bambu-pass" :feedback="false" toggle-mask autocomplete="off" /></div>
        <div class="oui-field"><label id="bambu-region-l">{{ t('bambu.region') }}</label><Select v-model="bambu.region" :options="regions" option-label="label" option-value="value" aria-labelledby="bambu-region-l" /></div>
        <div class="sb-full"><Button type="submit" :label="t('bambu.signIn')" :disabled="!bambu.email.trim() || !bambu.password" /></div>
      </form>
      <form v-else class="sb-login" @submit.prevent="bambuSend(bambu.step, { code: bambu.code })">
        <label class="oui-field"><span>{{ t('bambu.enterCode') }}</span><InputText v-model="bambu.code" autocomplete="one-time-code" /></label>
        <div class="oui-row sb-full"><Button type="submit" :label="t('bambu.verify')" :disabled="!bambu.code.trim()" />
          <Button severity="secondary" :label="t('common.goBack')" @click="bambu.pane = 'login'" />
          <Button v-if="!bambu.tfa" text :label="t('bambu.resend')" @click="bambuSend('resend')" /></div>
      </form>
      <div aria-live="polite"><OuiBanner v-if="bambu.text" :tone="tone(bambu.kind)" :title="bambu.text" data-test="bambu-status" /></div>
    </template>
    <OuiBanner :show="form.source === 'bambu'" tone="warn" :title="t('bambu.experimental')" dismissible dismiss-key="bambu-experimental" :close-label="t('common.close')" data-test="bambu-experimental" />
  </div>
</template>
<style scoped>
.sb { display: grid; gap: var(--oui-s2); }
.sb-src { gap: var(--oui-s4); }
.sb-opt { gap: 6px; }
.sb-url { flex: 1 1 260px; min-width: 0; }
.sb-login { display: grid; grid-template-columns: repeat(auto-fit, minmax(180px, 1fr)); gap: var(--oui-s2); align-items: end; }
.sb-full { grid-column: 1 / -1; margin: 0; }
</style>
