// Pure rules of Settings > Presets (one preset per filament or per spool, and Advanced tuning) and of the spool editor's
// Use with field. No DOM, no Vue: the unit tests import this file directly. The plugin checks everything again
// (plugin/spooler/filament_profiles.py parse_presets, editor.py _use_with_text) before it is saved or written to Spoolman.

/** One material's tuning: the base preset to inherit ("Generic PLA", the part before "@") and values set over it. */
export type TuneRow = Partial<Record<TuneKey | 'parent', number | string>>;
export interface PresetSettings { per_spool: boolean; tuning: boolean; materials: Record<string, TuneRow> }
export interface ParentBase { name: string; type: string }
export interface UseWithInfo { on: boolean; printers: { target: string; label: string }[]; value: string[] | null }

/** The OrcaSlicer settings Advanced tuning sets, with the ranges the plugin takes and the digits the box shows. */
export const TUNE_FIELDS = [
  { key: 'filament_flow_ratio', min: 0.01, max: 2, digits: 4, unit: '' },
  { key: 'pressure_advance', min: 0, max: 2, digits: 4, unit: '' },
  { key: 'filament_retraction_length', min: 0, max: 50, digits: 2, unit: 'mm' },
  { key: 'filament_retraction_speed', min: 1, max: 500, digits: 0, unit: 'mm/s' },
  { key: 'filament_max_volumetric_speed', min: 0.1, max: 200, digits: 1, unit: 'mm³/s' },
  { key: 'fan_min_speed', min: 0, max: 100, digits: 0, unit: '%' },
  { key: 'fan_max_speed', min: 0, max: 100, digits: 0, unit: '%' },
] as const;
export type TuneKey = (typeof TUNE_FIELDS)[number]['key'];

/** Materials offered before any is tuned. */
export const TUNE_MATERIALS = ['PLA', 'PETG', 'ABS', 'ASA', 'TPU', 'PA', 'PC'];
export const DEFAULT_PRESETS: PresetSettings = { per_spool: false, tuning: false, materials: {} };

export const matName = (text: string) => text.trim().replace(/\s+/g, ' ').toUpperCase().slice(0, 24);

/** The materials the tuning picker lists: the usual ones, then any other already tuned. */
export const tuneMaterials = (materials: Record<string, TuneRow>) => [...new Set([...TUNE_MATERIALS, ...Object.keys(materials)])];

/** The table with one value of one material set (null or '' clears it); a row left empty is dropped. */
export function setTune(materials: Record<string, TuneRow>, material: string, key: TuneKey | 'parent', value: number | string | null): Record<string, TuneRow> {
  const row: TuneRow = { ...(materials[material] ?? {}) };
  if (value === null || value === '' || (typeof value === 'number' && !Number.isFinite(value))) delete row[key];
  else row[key] = value;
  const { [material]: _old, ...rest } = materials;
  return Object.keys(row).length ? { ...rest, [material]: row } : rest;
}

const norm = (text: string) => text.toLowerCase().replace(/[^a-z0-9+]/g, '');
/** The base presets offered for a material: those of that material (or a variant: PLA offers PLA Silk), else all. */
export function basesFor(parents: ParentBase[], material: string): ParentBase[] {
  const want = norm(material);
  const fit = parents.filter(p => { const type = norm(p.type); return !!type && (type.startsWith(want) || want.startsWith(type)); });
  return fit.length ? fit : parents;
}

/** What the editor sends for Use with: the printer presets picked, or null for the default (loaded on, else every printer). */
export const useWithPayload = (picked: string[] | null | undefined): string[] | null => (picked && picked.length ? [...picked] : null);
/** Whether Use with changed from what the editor opened with (order ignored). */
export const useWithChanged = (now: string[] | null, was: string[] | null): boolean =>
  JSON.stringify([...(now ?? [])].sort()) !== JSON.stringify([...(was ?? [])].sort());
