/** Re-reads Spoolman on a timer while the page is visible. Shared shape across the Orca plugins (Spooler, U1 Control,
 *  Kobra Control, Print Calculator).
 *  - every() seconds between reads (0 = off); paused while the page is hidden, one read at once when it shows again;
 *  - one read at a time: a tick during a read is dropped;
 *  - after failed reads it waits every × 1, 2, 4… up to BACKOFF_MAX_S, and says so through onFailing (no toasts);
 *  - while held() (a form being edited, a picker or dialog open) it waits for that to end instead of resetting it. */
export const REFRESH_DEFAULT_S = 30;
export const REFRESH_MIN_S = 10;
export const REFRESH_MAX_S = 300;
export const BACKOFF_MAX_S = 300;
export const HELD_RETRY_MS = 1000;

/** Seconds to wait before the next read after `failures` failed reads in a row. */
export function nextDelayS(everyS: number, failures: number): number {
  return Math.min(BACKOFF_MAX_S, everyS * 2 ** Math.max(0, Math.min(failures, 16) - 1));
}

/** A setting value as the plugins store it: 0 (off) or a whole number of seconds in 10–300; anything else = 30. */
export function cleanEvery(v: unknown): number {
  return v === 0 || (Number.isInteger(v) && (v as number) >= REFRESH_MIN_S && (v as number) <= REFRESH_MAX_S) ? v as number : REFRESH_DEFAULT_S;
}

/** Something the user is in the middle of: a field focused in a form, or an open dialog or picker overlay. */
export function userBusy(doc: Document = document): boolean {
  const el = doc.activeElement as HTMLElement | null;
  if (el && /^(INPUT|TEXTAREA|SELECT)$/.test(el.tagName) && el.closest('form')) return true;
  return !!doc.querySelector('[role="dialog"], [role="alertdialog"], .p-select-overlay, .p-popover, .p-autocomplete-overlay, .p-datepicker-panel');
}

interface DocLike { hidden: boolean; addEventListener(t: string, f: () => void): void; removeEventListener(t: string, f: () => void): void }
export interface AutoRefreshOptions {
  /** One read; resolves true when it worked. */
  load: () => Promise<boolean>;
  every: () => number;
  held?: () => boolean;
  onFailing?: (failing: boolean) => void;
  doc?: DocLike;
}
export interface AutoRefresh { stop(): void; restart(): void; readonly failures: number }

export function autoRefresh(o: AutoRefreshOptions): AutoRefresh {
  const doc = o.doc ?? document;
  let timer: ReturnType<typeof setTimeout> | undefined, busy = false, failures = 0, stopped = false;
  const arm = (ms: number) => {
    clearTimeout(timer);
    if (!stopped && o.every() > 0) timer = setTimeout(tick, ms);
  };
  async function tick(): Promise<void> {
    if (stopped || busy || doc.hidden || o.every() <= 0) return;   // hidden: the page showing again reads at once
    if (o.held?.()) { arm(HELD_RETRY_MS); return; }
    busy = true;
    let ok = false;
    try { ok = await o.load(); } catch { ok = false; }
    busy = false;
    const was = failures;
    failures = ok ? 0 : failures + 1;
    if (!was !== !failures) o.onFailing?.(failures > 0);
    arm(nextDelayS(o.every(), failures) * 1000);
  }
  const onVis = () => { if (doc.hidden) clearTimeout(timer); else void tick(); };
  doc.addEventListener('visibilitychange', onVis);
  arm(o.every() * 1000);
  return {
    stop() { stopped = true; clearTimeout(timer); doc.removeEventListener('visibilitychange', onVis); },
    restart() { arm(nextDelayS(o.every(), failures) * 1000); },
    get failures() { return failures; },
  };
}
