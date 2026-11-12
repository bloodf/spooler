import { boot } from './boot';

// OrcaSlicer's window.orca, with the same message contract as the previous pages. In the native tab, the
// Settings view tags what it sends with view:"settings" (the plugin routes on it), exactly as TAB_BRIDGE did.
type Handler = (m: any) => void;
const handlers = new Set<Handler>();
let attached = false;
let errorSink: (e: unknown) => void = () => {};
export const setErrorSink = (fn: (e: unknown) => void) => { errorSink = fn; };

function host(): OrcaHostBridge {
  if (!window.orca) throw new Error('OrcaSlicer bridge missing');
  return window.orca;
}
export function attach(): void {
  if (attached) return;
  attached = true;
  host().onMessage(m => {
    if (!m || typeof m !== 'object') return;
    handlers.forEach(h => { try { h(m); } catch (e) { errorSink(e); } });
  });
}
export const onMessage = (h: Handler) => { handlers.add(h); return () => handlers.delete(h); };
export const postMain = (m: Record<string, unknown>) => host().postMessage(m);
export const postSettings = (m: Record<string, unknown>) => host().postMessage(boot.mode === 'tab' ? { ...m, view: 'settings' } : m);
