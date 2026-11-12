// The plugin fills the boot JSON before serving the page: which surface this is (the native tab with its two
// views, the separate spool window, or the separate Settings window), the saved settings and the plugin's
// constants. During `vite dev` it is absent and the defaults apply.
export interface ProgressSettings { on: boolean; finish: boolean; slot: boolean; idle: 'line' | 'hide' }
export interface StatsSettings { on: boolean; cur: string }
export interface SettingsBoot {
  url: string; verified_url: string; default_url: string; source: 'spoolman' | 'bambu'; low_stock: number;
  plate_check: boolean; plate_margin: number; weight_display: 'grams' | 'percent' | 'both'; show_cart: boolean;
  spool_columns: 1 | 2; progress: ProgressSettings; stats: StatsSettings; display: Record<string, boolean>;
  drying: Record<string, number>; cur_code: string; wizard: boolean; log_path: string;
}
export interface Boot {
  mode: 'tab' | 'main' | 'settings';
  view: 'main' | 'settings';
  version: string;
  lang: string | null;
  pref?: 'auto' | 'en' | 'pt-BR';
  low_stock_default: number;
  refresh_ms: number;
  display_defaults: Record<string, boolean>;
  own_fields: string[];
  logo?: string;
  settings: SettingsBoot;
}

export const DEFAULT_DISPLAY: Record<string, boolean> = {
  group_same: true, in_use: true, vendor: true, material: true, colour_code: false, diameter: false, rfid: true, bar: true,
  location: true, spool_id: false, comment: true, lot_nr: false, extra_fields: false, exact_weight: true, archived: false,
  dried: true, use_first: true, low_notice: true, head_vendor: true, head_material: true, head_colour_code: true,
  head_weight: true, head_bar: true, head_spool: true, head_preset: true, head_rfid: true,
};

function read(): Partial<Boot> {
  const text = document.getElementById('spooler-boot')?.textContent?.trim() ?? '';
  if (!text || text.startsWith('__')) return {};
  try { return JSON.parse(text) as Partial<Boot>; } catch { return {}; }
}

const raw = read();
export const boot: Boot = {
  mode: 'tab', view: 'main', version: 'dev', lang: null, low_stock_default: 100, refresh_ms: 60000,
  display_defaults: DEFAULT_DISPLAY, own_fields: ['tag', 'orca_settings', 'dried'],
  ...raw,
  settings: {
    url: '', verified_url: '', default_url: 'http://localhost:7912', source: 'spoolman', low_stock: 100, plate_check: true,
    plate_margin: 10, weight_display: 'both', show_cart: false, spool_columns: 1,
    progress: { on: true, finish: true, slot: true, idle: 'line' }, stats: { on: true, cur: 'spoolman' },
    display: { ...DEFAULT_DISPLAY }, drying: {}, cur_code: 'EUR', wizard: false, log_path: '',
    ...(raw.settings ?? {}),
  },
};
