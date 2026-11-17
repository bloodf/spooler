import { reactive, readonly } from 'vue';

/*
 * The page's toasts: short news about something that just happened ("Saved", "Spool linked", "Could not reach the
 * printer"). One host (OuiToastHost) draws them bottom-left, stacked, newest at the bottom. Every toast has a close
 * button; info and success leave after 5 s, warnings after 8 s, errors stay until closed. Hovering or focusing a toast
 * holds its timer. A state that lasts (offline, a missing tool) is an OuiBanner on the page, not a toast.
 */
export type OuiToastTone = 'info' | 'success' | 'warn' | 'error';
export interface OuiToastAction { label: string; run: () => void }
export interface OuiToastInput {
  tone?: OuiToastTone; title: string; body?: string; action?: OuiToastAction;
  /** Milliseconds on screen; 0 keeps it until closed. Defaults: info/success 5000, warn 8000, error 0. */ timeout?: number;
  /** A toast with the key of one already shown replaces it instead of stacking a copy. */ key?: string;
}
export interface OuiToastItem { id: number; tone: OuiToastTone; title: string; body?: string; action?: OuiToastAction; key?: string; timeout: number }

export const TOAST_TIMEOUT: Record<OuiToastTone, number> = { info: 5000, success: 5000, warn: 8000, error: 0 };
/** More than this and the oldest leaves first: the oldest that is neither an error nor carries an action (those are
 * what the user still has to read or act on); only when every toast is one of those, the oldest of all. */
export const TOAST_MAX = 4;

const state = reactive<{ list: OuiToastItem[] }>({ list: [] });
const timers = new Map<number, ReturnType<typeof setTimeout>>();
const left = new Map<number, { ms: number; since: number }>();
let next = 1;

function arm(id: number): void {
  const rest = left.get(id);
  if (!rest || timers.has(id)) return;
  rest.since = Date.now();
  timers.set(id, setTimeout(() => dismissToast(id), rest.ms));
}
export function dismissToast(id: number): void {
  clearTimeout(timers.get(id)); timers.delete(id); left.delete(id);
  state.list = state.list.filter(x => x.id !== id);
}
/** Holds a toast's timer (hover, focus); resumeToast gives it the time it had left. */
export function pauseToast(id: number): void {
  const timer = timers.get(id); const rest = left.get(id);
  if (!timer || !rest) return;
  clearTimeout(timer); timers.delete(id);
  rest.ms = Math.max(1000, rest.ms - (Date.now() - rest.since));
}
export const resumeToast = (id: number): void => arm(id);
export function showToast(input: OuiToastInput): number {
  const tone = input.tone ?? 'info';
  const timeout = input.timeout ?? TOAST_TIMEOUT[tone];
  const same = input.key ? state.list.find(x => x.key === input.key) : undefined;
  if (same) dismissToast(same.id);
  while (state.list.length >= TOAST_MAX) {
    const quiet = state.list.find(x => x.tone !== 'error' && !x.action);
    dismissToast((quiet ?? state.list[0]).id);
  }
  const id = next++;
  state.list = [...state.list, { id, tone, title: input.title, body: input.body, action: input.action, key: input.key, timeout }];
  if (timeout > 0) { left.set(id, { ms: timeout, since: Date.now() }); arm(id); }
  return id;
}
export function clearToasts(): void { for (const x of [...state.list]) dismissToast(x.id); }
export const toastList = readonly(state);

/** `const toast = useToast(); toast.show({ tone: 'success', title: 'Saved' })`. */
export function useToast() {
  return { show: showToast, dismiss: dismissToast, clear: clearToasts, list: toastList };
}
