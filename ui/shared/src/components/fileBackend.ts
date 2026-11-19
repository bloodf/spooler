import { computed, reactive, ref } from 'vue';
import type { OuiFile, OuiFolder } from './OuiFileBrowser.vue';

/*
 * The storage behind OuiFileBrowser. Each printer plugin writes one of these over its own bridge (Moonraker's file
 * endpoints, the Kobra's file list) and gives it to useFileBackend(); everything else is shared, so the Files tab
 * behaves the same in every plugin. What the storage cannot do is left out, and the component stops offering it:
 * no `folders`: no tree, no path, no "Move to"; no `move`: the tree stays for browsing, "Move to" and dragging go.
 * Every method rejects (throws) on failure; nothing here turns a failure into an empty list.
 */
export interface OuiFileBackend {
  /** Every folder of the storage, flat, parents before or after their children. Omit it, or resolve to [], when the storage has no folders. */
  folders?(): Promise<OuiFolder[]>;
  /** The files of one folder; `folder` is '' when the storage has no folders. */
  list(folder: string): Promise<OuiFile[]>;
  /** Delete these files of `folder`. The user has already confirmed. */
  remove(ids: string[], folder: string): Promise<void>;
  /** Move these files from `from` to the folder `to`. Omit it when the storage cannot move files. */
  move?(ids: string[], to: string, from: string): Promise<void>;
}
export interface OuiFileBackendOptions {
  /** The folder to open first (default: the first root). */ folder?: string;
  /** A move or delete failed: tell the user (a toast), in the page's language. The list is read again either way. */
  onError(action: 'move' | 'delete', error: unknown, ids: string[]): void;
  /** A move or delete finished: news for a toast. */ onDone?(action: 'move' | 'delete', ids: string[], to?: string): void;
  /** The sentence shown when the files cannot be read (default: the error's own message). */ message?(error: unknown): string;
}

/**
 * State and handlers for one OuiFileBrowser over a backend:
 *   const files = useFileBackend(backend, { onError });
 *   <OuiFileBrowser v-bind="files.props" v-on="files.on" :labels="labels" />
 * `files.selected`, `files.folder`, `files.files` and the rest can be read (and `selected` set); `files.reload()` reads again.
 */
export function useFileBackend(backend: OuiFileBackend, options: OuiFileBackendOptions) {
  const folders = ref<OuiFolder[]>([]); const files = ref<OuiFile[]>([]); const folder = ref(options.folder ?? ''); const selected = ref<string[]>([]);
  const loading = ref(true); const busy = ref(false); const error = ref<string | null>(null);
  const say = (e: unknown) => options.message?.(e) ?? (e instanceof Error ? e.message : String(e));
  let turn = 0;   // only the newest read may write: a slow answer for a folder the user has left is dropped
  /** Reads the files of the open folder, and the folders too unless `filesOnly`. `quiet` keeps the rows on screen meanwhile. */
  async function reload({ filesOnly = false, quiet = false } = {}): Promise<void> {
    const mine = ++turn;
    if (!quiet) loading.value = true;
    try {
      // ponytail: the whole tree in one call, read again after every change; make it lazy per folder if a storage is too big for that.
      if (!filesOnly) {
        const tree = backend.folders ? await backend.folders() : [];
        if (mine !== turn) return;
        folders.value = tree;
        if (!tree.some(f => f.id === folder.value)) folder.value = (tree.find(f => !f.parent) ?? tree[0])?.id ?? '';
      }
      const list = await backend.list(folder.value);
      if (mine !== turn) return;
      files.value = list; error.value = null;
    } catch (e) {
      if (mine !== turn) return;
      files.value = []; error.value = say(e);
    } finally { if (mine === turn) loading.value = false; }
  }
  async function act(action: 'move' | 'delete', ids: string[], work: () => Promise<void>, to?: string) {
    if (busy.value) return;
    busy.value = true;
    try { await work(); options.onDone?.(action, ids, to); } catch (e) { options.onError(action, e, ids); }
    // Whatever happened, show what the storage holds now: a failed move may have moved some of them.
    finally { await reload({ quiet: true }); busy.value = false; }
  }
  const props = computed(() => ({ folders: folders.value, files: files.value, folder: folder.value, selected: selected.value, loading: loading.value, busy: busy.value,
    error: error.value, movable: !!backend.move }));
  const on = {
    'update:folder': (id: string) => { folder.value = id; selected.value = []; void reload({ filesOnly: true }); },
    'update:selected': (ids: string[]) => { selected.value = ids; },
    move: ({ ids, to }: { ids: string[]; to: string }) => { const from = folder.value; void act('move', ids, () => backend.move!(ids, to, from), to); },
    delete: (ids: string[]) => { const from = folder.value; void act('delete', ids, () => backend.remove(ids, from)); },
    retry: () => { void reload(); },
  };
  void reload();
  return reactive({ props, on, reload, folders, files, folder, selected, loading, busy, error });
}
