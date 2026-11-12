import { applyOrcaTheme, type OrcaTheme } from '../../shared/src';

// The host paints the page through --orca-bg (as the previous pages assumed). We read the resolved colour and
// follow it; without it the system preference decides. Changes are picked up while the page runs (B-11).
function luminance(colour: string): number | null {
  const m = colour.match(/[\d.]+/g);
  if (!m || m.length < 3) return null;
  if (m.length >= 4 && Number(m[3]) === 0) return null;   // transparent: the host gave no colour
  return 0.299 * Number(m[0]) + 0.587 * Number(m[1]) + 0.114 * Number(m[2]);
}

export function detectTheme(): OrcaTheme {
  const probe = document.createElement('div');
  probe.style.cssText = 'position:absolute;visibility:hidden;background:var(--orca-bg, transparent)';
  document.body.appendChild(probe);
  const l = luminance(getComputedStyle(probe).backgroundColor);
  probe.remove();
  if (l != null) return l < 128 ? 'dark' : 'light';
  return matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light';
}

export function followHostTheme(onChange?: (t: OrcaTheme) => void): () => void {
  const forced = new URLSearchParams(location.search).get('theme');
  let current: OrcaTheme | null = null;
  const apply = () => {
    const next: OrcaTheme = forced === 'dark' || forced === 'light' ? forced : detectTheme();
    if (next === current) return;
    current = next;
    applyOrcaTheme(next);
    onChange?.(next);
  };
  apply();
  const mq = matchMedia('(prefers-color-scheme: dark)');
  mq.addEventListener('change', apply);
  const obs = new MutationObserver(apply);
  obs.observe(document.documentElement, { attributes: true, attributeFilter: ['style', 'class', 'data-theme'] });
  const timer = window.setInterval(apply, 3000);   // host may change --orca-* in a stylesheet we can't observe
  return () => { mq.removeEventListener('change', apply); obs.disconnect(); clearInterval(timer); };
}
