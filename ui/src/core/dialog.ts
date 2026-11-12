import { reactive, nextTick } from 'vue';

// One in-page dialog at a time (native confirm()/prompt() may be missing in Orca's WebView). Every protected
// decision names both answers explicitly (U01). Closing returns focus to the control that opened it, or to the
// control that now stands for it after a re-render (data-focus-key), never to <body> (B-01).
export interface ChoiceItem { value: string; label: string }
export interface DialogRequest {
  title: string;
  text: string;
  yes?: string;
  no?: string;
  danger?: boolean;
  input?: { label: string; value: string; placeholder?: string };
  choices?: ChoiceItem[];
}
interface Open extends DialogRequest { visible: boolean; resolve: ((v: any) => void) | null; cancelValue: unknown; inputValue: string }

export const dialog = reactive<Open>({ visible: false, title: '', text: '', resolve: null, cancelValue: false, inputValue: '' });
let opener: { el: Element | null; key: string | null } = { el: null, key: null };
// A dialog opened right after another (e.g. an input, then a confirmation) waits for the first one's leave
// transition; the focus goes back to the control that opened the first one.
let hidden: Promise<void> = Promise.resolve();
let markHidden: () => void = () => {};

async function open<T>(req: DialogRequest, cancelValue: T): Promise<T | any> {
  if (dialog.resolve) close(dialog.cancelValue);
  if (!opener.el) {
    const active = document.activeElement;
    opener = { el: active, key: active?.closest('[data-focus-key]')?.getAttribute('data-focus-key') ?? null };
  }
  await hidden;
  return new Promise(resolve => {
    Object.assign(dialog, { yes: undefined, no: undefined, danger: false, input: undefined, choices: undefined },
      req, { visible: true, resolve, cancelValue, inputValue: req.input?.value ?? '' });
  });
}

export function close(value: unknown): void {
  const resolve = dialog.resolve;
  dialog.resolve = null;
  dialog.visible = false;
  hidden = new Promise(r => { markHidden = r; setTimeout(r, 600); });
  resolve?.(value);
}

/** Called after the dialog's leave transition. */
export async function restoreFocus(): Promise<void> {
  markHidden();
  await nextTick();
  await nextTick();
  if (dialog.visible || dialog.resolve) return;   // another dialog follows; it restores focus when it closes
  const { el, key } = opener;
  opener = { el: null, key: null };
  const target = el && el.isConnected ? el : key ? document.querySelector(`[data-focus-key="${CSS.escape(key)}"]`) : null;
  const focusable = target?.matches('button, input, select, a, [tabindex]') ? target : target?.querySelector('button, input, select, a, [tabindex]');
  (focusable as HTMLElement | null)?.focus?.();
}

/** For dialogs that don't go through open(): record the opener now, synchronously, before any await. */
export function rememberOpener(fallbackKey: string | null = null): void {
  const active = document.activeElement && document.activeElement !== document.body ? document.activeElement : null;
  opener = { el: active, key: active?.closest('[data-focus-key]')?.getAttribute('data-focus-key') ?? fallbackKey };
}

export const ask = (req: DialogRequest): Promise<boolean> => open(req, false);
export const prompt = (req: DialogRequest & { input: NonNullable<DialogRequest['input']> }): Promise<string | null> => open(req, null);
export const choose = (req: DialogRequest & { choices: ChoiceItem[] }): Promise<string | null> => open(req, null);
/** The printer selection changed: no pending answer may apply to the next printer. */
export const cancelDialog = (): void => { if (dialog.resolve) close(dialog.cancelValue); };
