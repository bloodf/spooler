import { defineConfig } from 'vite';
import vue from '@vitejs/plugin-vue';
import { viteSingleFile } from 'vite-plugin-singlefile';

// One self-contained page (no CDN, no remote font, no eval). The plugin serves it for the tab and for the
// print setup window; the boot JSON the plugin fills in picks the mode.
export default defineConfig({
  plugins: [vue(), viteSingleFile({ removeViteModuleLoader: true })],
  // PrimeVue components use Vue's Options API, even when application SFCs use <script setup>.
  define: { __VUE_OPTIONS_API__: true, __VUE_PROD_DEVTOOLS__: false, __VUE_PROD_HYDRATION_MISMATCH_DETAILS__: false },
  build: { target: 'safari14', outDir: 'dist', emptyOutDir: true, reportCompressedSize: false },
});
