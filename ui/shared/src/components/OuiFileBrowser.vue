<script setup lang="ts">
import { computed, nextTick, onBeforeUpdate, onUpdated, ref, watch } from 'vue';
import Button from 'primevue/button';
import Select from 'primevue/select';
import OuiConfirm from './OuiConfirm.vue';
import OuiEmpty from './OuiEmpty.vue';
import OuiIcon from './OuiIcon.vue';
import OuiKeyValue, { type OuiFact } from './OuiKeyValue.vue';
import OuiThumb from './OuiThumb.vue';
import { chevronDown, chevronRight, file as fileIcon, files as filesIcon, folder as folderIcon, trash, x as closeIcon } from '../icons';

/*
 * The Files tab of a printer plugin: folders in a tree on the left, the open folder's files as a table in the middle,
 * and what is selected on the right. One component for every printer plugin: the storage is behind an adapter
 * (`OuiFileBackend`, ./fileBackend.ts) and `useFileBackend(adapter)` gives this component its props and handlers, so
 * loading, failure, reloading after a change and what is offered are the same everywhere. The component itself only
 * shows what it is given and emits `move`, `delete`, `open` and `retry`.
 *
 * A storage with no folders (no `folders`, or an empty list) has no tree, no path and no "Move to": the table takes the
 * rail's place, and selecting and deleting work as they do with folders. A storage that has folders but cannot move
 * files (`movable` false) keeps the tree for browsing and has no "Move to" and no dragging.
 *
 * Folders are shown in the tree only; the table lists files. What can be done to the open folder itself (rename it,
 * move it, delete it, make a folder in it) is the page's, in `#folder`, which gets that folder and sits beside the path.
 *
 * Selecting: a click selects one file; Cmd/Ctrl-click and the checkbox add or remove one; Shift-click (and Shift with
 * the arrows) selects the range from the last one; the header checkbox and Cmd/Ctrl+A select all; Escape clears.
 * Moving: drag the selection onto a folder in the tree, or use "Move to" in the bar over the table, which does the
 * same from the keyboard. Deleting always asks first (OuiConfirm), with the count and the first names.
 * Keys in the table: arrows, Home, End, Space (toggle), Enter (open), Delete. In the tree: arrows, Home, End,
 * Enter (open the folder).
 */
export interface OuiFolder { id: string; name: string; /** Missing or null: a root. */ parent?: string | null; count?: number; /** Not a place files can be moved to. */ locked?: boolean;
  /** Its files can be looked at and opened, not moved, deleted or added to (a camera or system folder). */ readonly?: boolean }
export interface OuiFile { id: string; name: string; /** Bytes and time for sorting; the texts are what is shown. */ size?: number | null; sizeText?: string; modified?: number | null; modifiedText?: string;
  /** A short tag after the name ("G-code", "3MF"). */ kind?: string; thumb?: string | null; /** Facts for the detail panel. */ facts?: OuiFact[] }
export interface OuiFileBrowserLabels { folders: string; files: string; name: string; size: string; modified: string; selectAll: string; select: (name: string) => string;
  items: (count: number) => string; selected: (count: number) => string; clear: string; moveTo: string; remove: string;
  removeTitle: (count: number) => string; removeText: string; andMore: (count: number) => string; cancel: string;
  empty: string; emptyText?: string; loading: string; nothingSelected: string; nothingSelectedText?: string;
  /** For `error`: what failed, in one sentence (the error itself is shown under it), and the button that tries again. */ loadFailed?: string; retry?: string }

const props = withDefaults(defineProps<{ /** The storage's folders, flat. None: the storage has no folders, and the tree and "Move to" are not shown. */ folders?: OuiFolder[];
  files: OuiFile[]; /** The open folder (v-model:folder); '' when there are no folders. */ folder?: string; /** Selected file ids (v-model:selected). */ selected: string[];
  labels: OuiFileBrowserLabels; loading?: boolean; /** Moving and deleting are off (the printer is busy); the page says why, once. */ readonly?: boolean; describedby?: string;
  /** The storage can move files between folders (default true). False: the tree stays, "Move to" and dragging go. */ movable?: boolean;
  /** The files could not be read: shown in place of the table, with `labels.loadFailed` and a `retry` button. */ error?: string | null;
  /** A move or delete is under way: the bulk actions wait for it. */ busy?: boolean;
  /** The order the list opens in (default: by name). A printer's list usually reads newest first: `{ key: 'modified', down: true }`. The user can still sort by any column. */
  sort?: { key: 'name' | 'size' | 'modified'; down?: boolean } }>(), { folders: () => [], folder: '', movable: true });
const emit = defineEmits<{ 'update:folder': [id: string]; 'update:selected': [ids: string[]]; move: [payload: { ids: string[]; to: string }]; delete: [ids: string[]]; open: [id: string]; retry: [] }>();
const hasTree = computed(() => props.folders.length > 0);
const locked = computed(() => props.readonly || props.busy || !!byId.value.get(props.folder)?.readonly);

// ---- folders -------------------------------------------------------------------------------------------------------
const byId = computed(() => new Map(props.folders.map(f => [f.id, f])));
const children = computed(() => {
  const map = new Map<string, OuiFolder[]>();
  for (const f of props.folders) { const key = f.parent ?? ''; map.set(key, [...(map.get(key) ?? []), f]); }
  return map;
});
const trail = (id: string): OuiFolder[] => { const out: OuiFolder[] = []; for (let f = byId.value.get(id); f; f = f.parent ? byId.value.get(f.parent) : undefined) out.unshift(f); return out; };
const path = computed(() => trail(props.folder));
const expanded = ref(new Set<string>());
// The open folder is always visible in the tree, and the roots start open.
watch(() => [props.folder, props.folders] as const, () => {
  expanded.value = new Set([...expanded.value, ...path.value.slice(0, -1).map(f => f.id), ...(expanded.value.size ? [] : (children.value.get('') ?? []).map(f => f.id))]);
}, { immediate: true });
interface Node { folder: OuiFolder; depth: number; branch: boolean; open: boolean }
const nodes = computed(() => {
  const out: Node[] = [];
  const walk = (parent: string, depth: number) => { for (const folder of children.value.get(parent) ?? []) {
    const branch = children.value.has(folder.id); const open = branch && expanded.value.has(folder.id);
    out.push({ folder, depth, branch, open }); if (open) walk(folder.id, depth + 1);
  } };
  walk('', 1);
  return out;
});
const treeFocus = ref(props.folder);
const tree = ref<HTMLElement>();
function toggle(id: string, open?: boolean) { const next = new Set(expanded.value); (open ?? !next.has(id)) ? next.add(id) : next.delete(id); expanded.value = next; }
function focusFolder(id: string) { treeFocus.value = id; nextTick(() => tree.value?.querySelector<HTMLElement>(`[data-folder="${CSS.escape(id)}"]`)?.focus()); }
function openFolder(id: string) { treeFocus.value = id; if (id !== props.folder) { emit('update:selected', []); emit('update:folder', id); } }
function onTreeKey(event: KeyboardEvent) {
  const list = nodes.value; const at = list.findIndex(n => n.folder.id === treeFocus.value); const node = list[at];
  if (!node) return;
  const go = (i: number) => { const n = list[Math.max(0, Math.min(list.length - 1, i))]; if (n) focusFolder(n.folder.id); };
  switch (event.key) {
    case 'ArrowDown': go(at + 1); break;
    case 'ArrowUp': go(at - 1); break;
    case 'Home': go(0); break;
    case 'End': go(list.length - 1); break;
    case 'ArrowRight': if (node.branch && !node.open) toggle(node.folder.id, true); else if (node.open) go(at + 1); break;
    case 'ArrowLeft': if (node.open) toggle(node.folder.id, false); else if (node.folder.parent) focusFolder(node.folder.parent); break;
    case 'Enter': case ' ': openFolder(node.folder.id); break;
    default: return;
  }
  event.preventDefault();
}

// ---- files and selection -------------------------------------------------------------------------------------------
type SortKey = 'name' | 'size' | 'modified';
const sortKey = ref<SortKey>(props.sort?.key ?? 'name'); const sortDown = ref(props.sort?.down ?? false);
function sortBy(key: SortKey) { if (sortKey.value === key) sortDown.value = !sortDown.value; else { sortKey.value = key; sortDown.value = key !== 'name'; } }
const rows = computed(() => {
  const key = sortKey.value; const sign = sortDown.value ? -1 : 1;
  return [...props.files].sort((a, b) => sign * (key === 'name' ? a.name.localeCompare(b.name, undefined, { numeric: true }) : (a[key] ?? -1) - (b[key] ?? -1)));
});
const picked = computed(() => new Set(props.selected));
const pickedRows = computed(() => rows.value.filter(f => picked.value.has(f.id)));
const all = computed(() => rows.value.length > 0 && pickedRows.value.length === rows.value.length);
const anchor = ref<string | null>(null);
const rowFocus = ref<string | null>(null);
const table = ref<HTMLElement>();
const setSelected = (ids: string[]) => { if (!ids.length) anchor.value = null; emit('update:selected', ids); };
// A file that left the folder (moved, deleted, another folder opened) leaves the selection with it.
watch(() => props.files, files => { const here = new Set(files.map(f => f.id)); const kept = props.selected.filter(id => here.has(id)); if (kept.length !== props.selected.length) setSelected(kept);
  if (rowFocus.value && !here.has(rowFocus.value)) rowFocus.value = null; });
function range(to: string): string[] {
  const ids = rows.value.map(f => f.id); const a = ids.indexOf(anchor.value ?? to); const b = ids.indexOf(to);
  return a < 0 || b < 0 ? [to] : ids.slice(Math.min(a, b), Math.max(a, b) + 1);
}
function toggleOne(id: string) { setSelected(picked.value.has(id) ? props.selected.filter(x => x !== id) : [...props.selected, id]); anchor.value = id; }
function onRowClick(event: MouseEvent, id: string) {
  rowFocus.value = id;
  if (event.shiftKey) setSelected(range(id));
  else if (event.metaKey || event.ctrlKey) toggleOne(id);
  else { setSelected([id]); anchor.value = id; }
}
function onCheck(event: MouseEvent, id: string) { focusRow(id); if (event.shiftKey && anchor.value) setSelected([...new Set([...props.selected, ...range(id)])]); else toggleOne(id); }
function focusRow(id: string) { rowFocus.value = id; nextTick(() => table.value?.querySelector<HTMLElement>(`[data-file="${CSS.escape(id)}"]`)?.focus()); }
function onTableKey(event: KeyboardEvent) {
  if ((event.target as HTMLElement).closest('input, button')) { if (event.key !== 'Escape') return; }
  const ids = rows.value.map(f => f.id); if (!ids.length) return;
  const at = Math.max(0, ids.indexOf(rowFocus.value ?? ids[0]));
  const go = (i: number) => { const id = ids[Math.max(0, Math.min(ids.length - 1, i))]; if (event.shiftKey) { anchor.value ??= ids[at]; setSelected(range(id)); } else anchor.value = id; focusRow(id); };
  if ((event.metaKey || event.ctrlKey) && event.key.toLowerCase() === 'a') setSelected(ids);
  else switch (event.key) {
    case 'ArrowDown': go(at + 1); break;
    case 'ArrowUp': go(at - 1); break;
    case 'Home': go(0); break;
    case 'End': go(ids.length - 1); break;
    case ' ': toggleOne(ids[at]); break;
    case 'Enter': emit('open', ids[at]); break;
    case 'Escape': setSelected([]); break;
    // props.selected is not updated yet when the row was selected just now: say which files, do not read them back.
    case 'Delete': case 'Backspace': if (props.selected.length) askDelete(); else { setSelected([ids[at]]); anchor.value = ids[at]; askDelete([ids[at]]); } break;
    default: return;
  }
  event.preventDefault();
}

// ---- move and delete -----------------------------------------------------------------------------------------------
const takes = (f: OuiFolder | undefined) => !!f && !f.locked && !f.readonly;
const targets = computed(() => props.folders.filter(f => takes(f) && f.id !== props.folder).map(f => ({ id: f.id, label: trail(f.id).map(x => x.name).join(' / ') })));
const moveChoice = ref<string | null>(null);
const canMove = computed(() => hasTree.value && props.movable && targets.value.length > 0);
function move(to: string, ids = props.selected) { if (!canMove.value || locked.value || !ids.length || to === props.folder || !takes(byId.value.get(to))) return; emit('move', { ids: [...ids], to }); setSelected([]); }
function onMoveChoice(to: string | null) { if (to) move(to); nextTick(() => { moveChoice.value = null; }); }
const confirming = ref<string[]>([]);
function askDelete(ids: string[] = props.selected) { if (!locked.value && ids.length) confirming.value = [...ids]; }
function confirmDelete() { emit('delete', confirming.value); confirming.value = []; }
const confirmNames = computed(() => confirming.value.slice(0, 4).map(id => props.files.find(f => f.id === id)?.name ?? id));

// Drag and drop: the dragged row joins or replaces the selection, and folders that can take it light up.
const dragging = ref<string[]>([]);
const dropOn = ref<string | null>(null);
const ghost = ref<HTMLElement>();
function onDragStart(event: DragEvent, id: string) {
  if (!canMove.value || locked.value || !event.dataTransfer) { event.preventDefault(); return; }
  const ids = picked.value.has(id) ? [...props.selected] : [id];
  if (!picked.value.has(id)) { setSelected(ids); anchor.value = id; }
  dragging.value = ids;
  event.dataTransfer.effectAllowed = 'move';
  event.dataTransfer.setData('text/plain', ids.map(x => props.files.find(f => f.id === x)?.name ?? x).join('\n'));
  if (ghost.value) { ghost.value.textContent = props.labels.selected(ids.length); event.dataTransfer.setDragImage(ghost.value, 12, 12); }
}
const canDrop = (id: string) => dragging.value.length > 0 && id !== props.folder && takes(byId.value.get(id));
function onDragOver(event: DragEvent, id: string) { if (!canDrop(id)) return; event.preventDefault(); if (event.dataTransfer) event.dataTransfer.dropEffect = 'move'; dropOn.value = id; }
function onDragLeave(id: string) { if (dropOn.value === id) dropOn.value = null; }
function onDrop(event: DragEvent, id: string) { if (!canDrop(id)) return; event.preventDefault(); const ids = dragging.value; dragging.value = []; dropOn.value = null; move(id, ids); }
function onDragEnd() { dragging.value = []; dropOn.value = null; }

const one = computed(() => (pickedRows.value.length === 1 ? pickedRows.value[0] : null));

// When what had focus goes away (the deleted or moved rows, the bar's buttons once nothing is selected), focus stays in the
// list instead of falling to the page: on the first row, or on the list itself when it is empty. The same when the delete
// question has closed and the row it would give focus back to is already gone.
const list = ref<HTMLElement>();
let hadFocus = false;
// Sticky until onUpdated has read it: one change of the files can update this component twice in the same flush (the rows,
// then the selection that the gone rows leave), and by the second time the focused row has already been removed.
onBeforeUpdate(() => { hadFocus ||= !!list.value?.contains(document.activeElement); });
function holdFocus() { if (!list.value?.contains(document.activeElement)) (table.value?.querySelector<HTMLElement>('.oui-files-row[tabindex="0"]') ?? list.value)?.focus(); }
onUpdated(() => { if (hadFocus) holdFocus(); hadFocus = false; });
</script>
<template>
  <div class="oui-files"><div class="oui-files-grid" :data-flat="!hasTree || undefined" :data-dragging="dragging.length ? true : undefined">
    <nav v-if="hasTree" class="oui-files-rail" :aria-label="labels.folders">
      <p class="oui-label oui-files-railhead">{{ labels.folders }}</p>
      <div ref="tree" class="oui-files-tree" role="tree" :aria-label="labels.folders" @keydown="onTreeKey">
        <div v-for="node in nodes" :key="node.folder.id" role="treeitem" class="oui-files-folder" :data-folder="node.folder.id" :aria-level="node.depth" :aria-expanded="node.branch ? node.open : undefined"
          :aria-selected="node.folder.id === folder" :aria-current="node.folder.id === folder ? 'true' : undefined" :tabindex="node.folder.id === treeFocus ? 0 : -1"
          :data-drop="dropOn === node.folder.id || undefined" :data-target="canDrop(node.folder.id) || undefined" :style="{ paddingInlineStart: 4 + (node.depth - 1) * 16 + 'px' }"
          @click="openFolder(node.folder.id)" @focus="treeFocus = node.folder.id" @dragover="onDragOver($event, node.folder.id)" @dragenter="onDragOver($event, node.folder.id)" @dragleave="onDragLeave(node.folder.id)" @drop="onDrop($event, node.folder.id)">
          <span class="oui-files-twisty" :data-branch="node.branch || undefined" aria-hidden="true" @click.stop="node.branch && toggle(node.folder.id)"><OuiIcon v-if="node.branch" :icon="node.open ? chevronDown : chevronRight" :size="14" /></span>
          <OuiIcon :icon="folderIcon" :size="15" /><span class="oui-truncate oui-files-foldername">{{ node.folder.name }}</span>
          <span v-if="node.folder.count != null" class="oui-meta oui-num">{{ node.folder.count }}</span>
        </div>
      </div>
      <div v-if="$slots.rail" class="oui-files-railfoot"><slot name="rail" /></div>
    </nav>

    <section ref="list" class="oui-files-list" :aria-label="labels.files" tabindex="-1">
      <div v-if="hasTree || $slots.toolbar" class="oui-files-toolbar">
        <ol v-if="hasTree" class="oui-files-path" :aria-label="labels.folders">
          <li v-for="(f, i) in path" :key="f.id"><OuiIcon v-if="i" :icon="chevronRight" :size="12" class="oui-muted" />
            <button v-if="i < path.length - 1" type="button" class="oui-files-crumb" @click="openFolder(f.id)">{{ f.name }}</button><strong v-else aria-current="page">{{ f.name }}</strong></li>
        </ol>
        <div v-if="hasTree && $slots.folder" class="oui-files-folderactions"><slot name="folder" :folder="byId.get(folder)" /></div>
        <div v-if="$slots.toolbar" class="oui-files-tools"><slot name="toolbar" /></div>
      </div>
      <!-- Always there, so selecting does not move the table: the count, and what can be done with the selection. -->
      <div class="oui-files-bar" role="toolbar" :aria-label="labels.selected(selected.length)">
        <span class="oui-num oui-strong" aria-live="polite">{{ selected.length ? labels.selected(selected.length) : labels.items(rows.length) }}</span>
        <template v-if="selected.length">
          <Button :label="labels.clear" severity="secondary" text size="small" @click="setSelected([])"><template #icon><OuiIcon :icon="closeIcon" :size="13" /></template></Button>
          <span class="oui-spacer" />
          <slot name="bulk" :ids="selected" />
          <Select v-if="canMove" v-model="moveChoice" :options="targets" option-label="label" option-value="id" :placeholder="labels.moveTo" :aria-label="labels.moveTo" size="small" class="oui-files-move"
            :disabled="locked" :aria-describedby="describedby" @update:model-value="onMoveChoice" />
          <Button :label="labels.remove" severity="danger" outlined size="small" :disabled="locked" :aria-describedby="describedby" @click="askDelete()"><template #icon><OuiIcon :icon="trash" :size="13" /></template></Button>
        </template>
      </div>
      <div class="oui-files-scroll">
        <OuiEmpty v-if="error" state="error" :title="labels.loadFailed ?? error" :text="labels.loadFailed ? error : undefined">
          <template v-if="labels.retry" #actions><Button :label="labels.retry" severity="secondary" size="small" data-files-retry @click="emit('retry')" /></template>
        </OuiEmpty>
        <table v-else ref="table" class="oui-files-table" role="grid" aria-multiselectable="true" :aria-busy="loading || busy || undefined" @keydown="onTableKey">
          <thead><tr>
            <th class="oui-files-check"><input type="checkbox" :checked="all" :indeterminate="selected.length > 0 && !all" :aria-label="labels.selectAll" :disabled="!rows.length" @change="setSelected(all ? [] : rows.map(f => f.id))"></th>
            <th v-for="col in (['name', 'size', 'modified'] as const)" :key="col" :class="{ 'oui-num': col !== 'name' }" :aria-sort="sortKey === col ? (sortDown ? 'descending' : 'ascending') : 'none'">
              <button type="button" class="oui-files-sort" @click="sortBy(col)">{{ labels[col] }}<OuiIcon v-if="sortKey === col" :icon="chevronDown" :size="12" :style="sortDown ? undefined : { transform: 'rotate(180deg)' }" /></button></th>
          </tr></thead>
          <tbody v-if="loading"><tr v-for="n in 6" :key="n" class="oui-files-skeleton"><td /><td><span class="oui-skeleton" :style="{ width: 40 + (n * 37) % 45 + '%' }" /></td><td><span class="oui-skeleton" /></td><td><span class="oui-skeleton" /></td></tr></tbody>
          <tbody v-else>
            <tr v-for="f in rows" :key="f.id" class="oui-files-row" :data-file="f.id" :aria-selected="picked.has(f.id)" :tabindex="(rowFocus ?? rows[0].id) === f.id ? 0 : -1" :draggable="canMove && !locked"
              :data-dragged="dragging.includes(f.id) || undefined" @click="onRowClick($event, f.id)" @dblclick="emit('open', f.id)" @focus="rowFocus = f.id" @dragstart="onDragStart($event, f.id)" @dragend="onDragEnd">
              <td class="oui-files-check" @click.stop><input type="checkbox" tabindex="-1" :checked="picked.has(f.id)" :aria-label="labels.select(f.name)" @click="onCheck($event, f.id)"></td>
              <td><div class="oui-files-name"><OuiThumb :src="f.thumb" :size="32" :icon="fileIcon" /><span class="oui-truncate" :title="f.name">{{ f.name }}</span><span v-if="f.kind" class="oui-chip">{{ f.kind }}</span></div></td>
              <td class="oui-num">{{ f.sizeText ?? '—' }}</td><td class="oui-num oui-muted">{{ f.modifiedText ?? '—' }}</td>
            </tr>
          </tbody>
        </table>
        <OuiEmpty v-if="!error && !loading && !rows.length" compact :icon="folderIcon" :title="labels.empty" :text="labels.emptyText"><template v-if="$slots.empty" #actions><slot name="empty" /></template></OuiEmpty>
      </div>
      <div v-if="!hasTree && $slots.rail" class="oui-files-listfoot"><slot name="rail" /></div>
    </section>

    <aside class="oui-files-detail" aria-live="polite">
      <template v-if="one">
        <div class="oui-files-preview"><img v-if="one.thumb" :src="one.thumb" alt="" draggable="false"><OuiIcon v-else :icon="fileIcon" :size="28" tone="neutral" /></div>
        <div class="oui-files-detailhead"><h3 class="oui-files-detailname" :title="one.name">{{ one.name }}</h3><span v-if="one.kind" class="oui-chip">{{ one.kind }}</span></div>
        <OuiKeyValue :items="[{ label: labels.size, value: one.sizeText }, { label: labels.modified, value: one.modifiedText }, ...(one.facts ?? [])]" />
        <div v-if="$slots.actions" class="oui-files-detailactions"><slot name="actions" :file="one" /></div>
      </template>
      <template v-else-if="pickedRows.length">
        <div class="oui-files-preview"><OuiIcon :icon="filesIcon" :size="28" tone="neutral" /></div>
        <h3 class="oui-files-detailname">{{ labels.selected(pickedRows.length) }}</h3>
        <ul class="oui-files-names oui-meta"><li v-for="f in pickedRows.slice(0, 6)" :key="f.id" class="oui-truncate">{{ f.name }}</li><li v-if="pickedRows.length > 6">{{ labels.andMore(pickedRows.length - 6) }}</li></ul>
        <div v-if="$slots.selection" class="oui-files-detailactions"><slot name="selection" :files="pickedRows" /></div>
      </template>
      <OuiEmpty v-else :icon="fileIcon" :title="labels.nothingSelected" :text="labels.nothingSelectedText" />
    </aside>
    <span ref="ghost" class="oui-files-ghost" aria-hidden="true" />
  </div>
  <OuiConfirm :visible="confirming.length > 0" :title="labels.removeTitle(confirming.length)" :confirm-label="labels.remove" :cancel-label="labels.cancel" danger
    @update:visible="(v: boolean) => { if (!v) confirming = []; }" @confirm="confirmDelete" @closed="holdFocus">
    <p>{{ labels.removeText }}</p>
    <ul class="oui-files-names"><li v-for="n in confirmNames" :key="n" class="oui-truncate oui-mono">{{ n }}</li><li v-if="confirming.length > confirmNames.length" class="oui-meta">{{ labels.andMore(confirming.length - confirmNames.length) }}</li></ul>
  </OuiConfirm></div>
</template>
<style>
/* One surface, three panes divided by hairlines. Give it a height (--oui-files-height) and each pane scrolls inside. */
.oui-files { container: oui-files / inline-size; min-width: 0; height: var(--oui-files-height, auto); min-height: 360px; }
.oui-files-grid { position: relative; display: grid; grid-template-columns: 232px minmax(0, 1fr) 300px; height: 100%; min-height: inherit; overflow: hidden; background: var(--oui-surface);
  border-radius: var(--oui-radius-lg); box-shadow: inset 0 0 0 1px var(--oui-border), var(--oui-shadow-panel); }
/* No folders: the table takes the rail's place. */
.oui-files-grid[data-flat] { grid-template-columns: minmax(0, 1fr) 300px; }
.oui-files-listfoot { padding: var(--oui-s2) var(--oui-s3); border-top: 1px solid var(--oui-border); }
.oui-files-rail { display: flex; flex-direction: column; min-width: 0; min-height: 0; border-inline-end: 1px solid var(--oui-border); background: var(--oui-raised); }
.oui-files-railhead { padding: var(--oui-s3) var(--oui-s3) var(--oui-s1); }
.oui-files-tree { flex: 1 1 auto; min-height: 0; overflow-y: auto; padding: 0 var(--oui-s1) var(--oui-s2); }
.oui-files-folder { display: flex; align-items: center; gap: 6px; min-height: 30px; padding-inline-end: var(--oui-s2); border-radius: var(--oui-radius); cursor: pointer; color: var(--oui-text); }
.oui-files-folder:hover { background: var(--oui-control); }
.oui-files-folder[aria-selected='true'] { font-weight: 650; background: var(--oui-control); box-shadow: inset 2px 0 0 var(--oui-primary-mark); }
.orca-ui .oui-files-folder:focus-visible { outline-offset: -2px; }
/* While files are dragged, folders that can take them are outlined; the one under the pointer is filled. */
.oui-files-grid[data-dragging] .oui-files-folder[data-target] { box-shadow: inset 0 0 0 1px var(--oui-control-border); }
.oui-files-grid[data-dragging] .oui-files-folder[data-drop] { background: var(--oui-primary-soft); box-shadow: inset 0 0 0 2px var(--oui-primary-mark); }
.oui-files-twisty { flex: none; display: grid; place-items: center; width: 18px; height: 22px; color: var(--oui-muted); border-radius: var(--oui-radius-sm); }
.oui-files-twisty[data-branch]:hover { color: var(--oui-text); background: var(--oui-control-hover); }
.oui-files-foldername { flex: 1 1 0; }
.oui-files-railfoot { padding: var(--oui-s3); border-top: 1px solid var(--oui-border); }
.oui-files-list { display: flex; flex-direction: column; min-width: 0; min-height: 0; }
/* Only the rows give way when the list is short: the toolbar, the bar and the foot keep their height (a wrapped toolbar was cut). */
.oui-files-toolbar, .oui-files-bar, .oui-files-listfoot { flex: none; }
.orca-ui .oui-files-list:focus { outline: none; }
.oui-files-toolbar { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2) var(--oui-s3); min-height: 48px; padding: var(--oui-s2) var(--oui-s3); }
/* The path, the open folder's actions right after it, and the page's tools at the far end. */
.oui-files-path { flex: 0 1 auto; display: flex; flex-wrap: wrap; align-items: center; gap: 2px; min-width: 0; margin: 0; padding: 0; list-style: none; }
.oui-files-path > li { display: inline-flex; align-items: center; gap: 2px; min-width: 0; }
.oui-files-path strong { padding: 0 4px; font-weight: 700; }
.oui-files-crumb { padding: 2px 4px; border: 0; border-radius: var(--oui-radius-sm); color: var(--oui-muted); background: none; cursor: pointer; }
.oui-files-crumb:hover { color: var(--oui-text); background: var(--oui-control); }
.oui-files-tools { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); margin-inline-start: auto; }
/* No folders, so no path before it: the slot is the whole bar, from its left. A page spreads its items with .oui-spacer. */
.oui-files-grid[data-flat] .oui-files-tools { flex: 1 1 auto; margin-inline-start: 0; }
.oui-files-folderactions { display: flex; align-items: center; gap: var(--oui-s1); }
.oui-files-bar { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); min-height: 40px; padding: 4px var(--oui-s3); background: var(--oui-raised); border-block: 1px solid var(--oui-border); }
.oui-files-move { min-width: 150px; }
.oui-files-scroll { flex: 1 1 auto; min-height: 0; overflow: auto; }
.oui-files-table { width: 100%; border-collapse: collapse; table-layout: fixed; }
.oui-files-table th { position: sticky; top: 0; z-index: 1; height: 30px; padding: 0 var(--oui-s3); text-align: start; background: var(--oui-surface); box-shadow: inset 0 -1px 0 var(--oui-border); }
.oui-files-table th:nth-child(3) { width: 96px; } .oui-files-table th:nth-child(4) { width: 168px; }
.oui-files-table th.oui-num, .oui-files-table td.oui-num { text-align: end; }
.oui-files-sort { display: inline-flex; align-items: center; gap: 2px; padding: 0; border: 0; background: none; cursor: pointer; font-size: var(--oui-text-xs); font-weight: 600; letter-spacing: .05em; text-transform: uppercase; color: var(--oui-muted); }
.oui-files-sort:hover { color: var(--oui-text); }
.oui-files-table td { height: 44px; padding: 0 var(--oui-s3); border-bottom: 1px solid var(--oui-border); white-space: nowrap; overflow: hidden; text-overflow: ellipsis; }
.oui-files-table :is(th, td).oui-files-check { width: 36px; padding: 0 0 0 var(--oui-s3); overflow: visible; }
.oui-files-check > input { display: block; width: 16px; height: 16px; margin: 0; cursor: pointer; }
.oui-files-row { cursor: default; user-select: none; -webkit-user-select: none; }
.oui-files-row:hover { background: var(--oui-raised); }
.oui-files-row[aria-selected='true'] { background: var(--oui-primary-soft); }
.oui-files-row[data-dragged] { opacity: .5; }
.orca-ui .oui-files-row:focus-visible { outline-offset: -2px; }
.oui-files-name { display: flex; align-items: center; gap: var(--oui-s2); min-width: 0; }
.oui-files-name > .oui-truncate { font-weight: 600; }
.oui-files-skeleton td { height: 44px; padding: 0 var(--oui-s3); border-bottom: 1px solid var(--oui-border); }
/* Rows are as tall as their content, never less: the picture has no minimum of its own (aspect-ratio, clipped), and in a
   pane shorter than its content an auto row would shrink it to nothing and draw it over the name. The pane scrolls instead. */
.oui-files-detail { display: grid; grid-auto-rows: max-content; align-content: start; gap: var(--oui-s3); min-width: 0; min-height: 0; overflow-y: auto; padding: var(--oui-s3); border-inline-start: 1px solid var(--oui-border); }
.oui-files-preview { display: grid; place-items: center; aspect-ratio: 16 / 10; overflow: hidden; border-radius: var(--oui-radius); background: var(--oui-inset); box-shadow: inset 0 0 0 1px var(--oui-border); }
.oui-files-preview > img { display: block; width: 100%; height: 100%; object-fit: contain; }
.oui-files-detailhead { display: flex; flex-wrap: wrap; align-items: center; gap: var(--oui-s2); min-width: 0; }
.orca-ui .oui-files-detailname { min-width: 0; font-size: var(--oui-text-lg); font-weight: 700; overflow-wrap: anywhere; }
.oui-files-detailactions { display: flex; flex-wrap: wrap; gap: var(--oui-s2); padding-top: var(--oui-s1); }
.oui-files-names { display: grid; gap: 2px; margin: 0; padding: 0; list-style: none; min-width: 0; }
.oui-files-ghost { position: absolute; top: -200px; left: 0; padding: 4px 10px; border-radius: var(--oui-radius); font-weight: 650; color: var(--oui-on-primary); background: var(--oui-primary); }
/* Narrower: the detail goes under the list; narrower still, the folders go above it. */
/* Stacked, the detail (and the tree, narrower still) get a share of the height at most and scroll inside it: the table
   keeps the rest. Sized to their content they took the height first, and a tall detail left the table none. */
@container oui-files (max-width: 980px) {
  .oui-files-grid { grid-template-columns: 208px minmax(0, 1fr); grid-template-rows: minmax(0, 1fr) fit-content(40%); }
  .oui-files-grid[data-flat] { grid-template-columns: minmax(0, 1fr); }
  .oui-files-detail { grid-column: 1 / -1; grid-template-columns: 160px minmax(0, 1fr); border-inline-start: 0; border-top: 1px solid var(--oui-border); }
  .oui-files-detail > .oui-files-preview { grid-row: span 3; }
  .oui-files-detail > .oui-empty { grid-column: 1 / -1; padding-block: var(--oui-s3); }
}
@container oui-files (max-width: 620px) {
  .oui-files-grid { grid-template-columns: minmax(0, 1fr); grid-template-rows: fit-content(26%) minmax(0, 1fr) fit-content(30%); }
  .oui-files-grid[data-flat] { grid-template-rows: minmax(0, 1fr) fit-content(40%); }
  .oui-files-rail { border-inline-end: 0; border-bottom: 1px solid var(--oui-border); }
  .oui-files-table th:nth-child(4), .oui-files-table td:nth-child(4) { display: none; }
}
</style>
