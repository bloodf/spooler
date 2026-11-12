import { computed, reactive, ref } from 'vue';
import * as bridge from '../core/bridge';
import { boot, type SettingsBoot } from '../core/boot';
import { t } from '../core/i18n';
import { m } from '../state/main';
import { rememberOpener } from '../core/dialog';

// Settings form. It resets to the saved values each time Settings opens (show_view), so abandoned edits don't
// linger; Save stays off until the source passed a test, as the plugin also requires.
const clone = (x: SettingsBoot) => JSON.parse(JSON.stringify(x)) as SettingsBoot;
export const saved = ref<SettingsBoot>(clone(boot.settings));
export const form = reactive<SettingsBoot>(clone(boot.settings));
export const conn = reactive({ verifiedUrl: norm(boot.settings.verified_url), verifiedText: '', text: '', kind: 'pending' as 'ok' | 'pending' | 'error' });
export const bambu = reactive({ verified: false, account: '', pane: 'login' as 'in' | 'login' | 'code', step: 'password', tfa: false,
  text: '', kind: 'pending' as 'ok' | 'pending' | 'error', email: '', password: '', region: 'global', code: '' });
export const update = reactive({ busy: false, text: '', newer: '' });
export const saving = ref(false);
export const wizard = reactive({ open: false, step: 0 });

export function norm(u: string): string { return String(u || '').trim().replace(/\/+$/, ''); }
export const dirty = computed(() => JSON.stringify(form) !== JSON.stringify(saved.value));
export const ready = computed(() => (form.source === 'bambu' ? bambu.verified : !!norm(form.url) && norm(form.url) === conn.verifiedUrl));
export const saveWhy = computed(() => (ready.value ? '' : form.source === 'bambu' ? t('settings.needBambu') : t('settings.needTest')));

function reset(values: Partial<SettingsBoot>): void {
  const next = { ...clone(saved.value), ...values } as SettingsBoot;
  if (!next.url) next.url = '';
  saved.value = clone(next);
  Object.assign(form, clone(next));
  update.text = ''; update.newer = '';
  conn.text = conn.verifiedUrl && norm(form.url) === conn.verifiedUrl ? conn.verifiedText : t('settings.checking');
  conn.kind = conn.verifiedUrl && norm(form.url) === conn.verifiedUrl ? 'ok' : 'pending';
}

export function onUrlInput(): void {
  if (norm(form.url) === conn.verifiedUrl && conn.verifiedText) { conn.text = conn.verifiedText; conn.kind = 'ok'; }
  else { conn.text = t('settings.pressTest'); conn.kind = 'pending'; }
}
export function test(): void {
  conn.text = t('settings.testing'); conn.kind = 'pending';
  bridge.postSettings({ type: 'test', source: 'spoolman', url: form.url.trim() });
}
export function checkBambu(): void {
  bambu.text = t('bambu.connecting'); bambu.kind = 'pending';
  bridge.postSettings({ type: 'test', source: 'bambu' });
}
export function bambuSend(action: string, extra: Record<string, unknown> = {}): void {
  bambu.text = ({ password: t('bambu.signingIn'), sign_out: t('bambu.signingOut'), resend: t('bambu.resending') } as Record<string, string>)[action] ?? t('bambu.verifying');
  bambu.kind = 'pending';
  if (action === 'sign_out') bambu.verified = false;
  bridge.postSettings({ type: 'bambu_auth', action, ...extra });
}
export function setSource(v: 'spoolman' | 'bambu', byUser: boolean): void {
  form.source = v;
  if (v === 'bambu' && !bambu.verified && byUser) checkBambu();
}
export function checkUpdate(): void { update.busy = true; update.text = t('settings.checkingUpdate'); update.newer = ''; bridge.postSettings({ type: 'check_update' }); }

export function save(): void {
  if (!ready.value || saving.value) return;
  saving.value = true;
  bridge.postSettings({
    type: 'save', source: form.source, url: form.url.trim(), low_stock: form.low_stock, plate_check: form.plate_check, plate_margin: form.plate_margin,
    weight_display: form.weight_display, show_cart: form.show_cart, spool_columns: form.spool_columns, progress: { ...form.progress },
    stats: { ...form.stats }, display: { ...form.display }, drying: { ...form.drying },
  });
  // The plugin answers by closing Settings (show_view main / window close) or with a test_result refusal.
  window.setTimeout(() => { saving.value = false; }, 4000);
}
export function cancel(): void { bridge.postSettings({ type: 'cancel' }); }

function onMessage(d: any): void {
  if (d.type === 'show_view') {
    m.view = d.view === 'settings' ? 'settings' : 'main';
    if (d.view !== 'settings') { saving.value = false; return; }
    reset({ url: d.url || '', source: d.source || 'spoolman', low_stock: d.low_stock, plate_check: d.plate_check !== false,
      ...(d.plate_margin !== undefined ? { plate_margin: d.plate_margin } : {}), weight_display: d.weight_display || 'both', show_cart: d.show_cart === true,
      spool_columns: d.spool_columns === 2 ? 2 : 1, progress: { on: true, finish: true, slot: true, idle: 'line', ...(d.progress || {}) },
      stats: { on: true, cur: 'spoolman', ...(d.stats || {}) }, ...(d.display ? { display: d.display } : {}), ...(d.drying ? { drying: d.drying } : {}),
      ...(d.cur_code ? { cur_code: d.cur_code } : {}), wizard: !!d.wizard });
    if (d.wizard) openWizard();
    return;
  }
  if (boot.mode === 'tab' && d.view !== 'settings') return;
  if (d.type === 'update_result') {
    update.busy = false;
    update.text = !d.ok ? d.error || t('common.unknownError') : d.newer ? '' : t('settings.upToDate');
    update.newer = d.ok && d.newer ? d.version : '';
  } else if (d.type === 'bambu_auth_result') {
    if (!d.ok) { bambu.text = d.error || t('bambu.signInFailed'); bambu.kind = 'error'; }
    else if (d.step === 'done') { bambu.code = ''; checkBambu(); }
    else if (d.step === 'out') { bambu.pane = 'login'; bambu.account = ''; bambu.text = t('bambu.signedOut'); bambu.kind = 'pending'; }
    else { bambu.step = d.step; bambu.tfa = d.step === 'tfa'; bambu.pane = 'code'; bambu.text = t('bambu.enterCode'); bambu.kind = 'pending'; }
  } else if (d.type === 'test_result') {
    saving.value = false;
    if (d.source === 'bambu') {
      bambu.account = d.account || '';
      bambu.verified = !!d.ok;
      bambu.pane = d.ok || !d.signin ? 'in' : 'login';
      bambu.text = d.ok ? t('bambu.connected') : t('bambu.notConnected', { why: d.error || t('bambu.failed') });
      bambu.kind = d.ok ? 'ok' : 'error';
      return;
    }
    if (d.ok) {
      conn.verifiedUrl = norm(d.url || '');
      conn.verifiedText = t('settings.connected', { version: d.version });
      if (norm(form.url) === conn.verifiedUrl) { conn.text = conn.verifiedText; conn.kind = 'ok'; }
    } else { conn.text = d.error || t('settings.failed'); conn.kind = 'error'; }
  }
}

export function openWizard(): void { if (wizard.open) return; rememberOpener('open-guide'); Object.assign(wizard, { open: true, step: 0 }); }
export function closeWizard(finish: boolean): void {
  if (!wizard.open) return;
  wizard.open = false;
  bridge.postSettings({ type: 'wizard', done: true });
  if (finish && ready.value) save();
}

export function startSettings(): () => void {
  bridge.attach();
  const off = bridge.onMessage(onMessage);
  // Confirms the listener is registered before the plugin sends anything unprompted (its "ready" handler).
  bridge.postSettings({ type: 'ready' });
  conn.text = conn.verifiedUrl && norm(form.url) === conn.verifiedUrl ? t('settings.checking') : t('settings.pressTest');
  if (form.source === 'bambu') checkBambu();
  if (boot.settings.wizard && (boot.mode === 'settings' || boot.view === 'settings')) openWizard();
  return () => { off(); };
}
