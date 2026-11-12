/// <reference types="vite/client" />
declare module '*.vue' {
  import type { DefineComponent } from 'vue';
  const component: DefineComponent<object, object, unknown>;
  export default component;
}
interface OrcaHostBridge {
  postMessage(message: unknown): void;
  onMessage(handler: (message: any) => void): void;
  submit?(result: unknown): void;
}
interface Window { orca?: OrcaHostBridge }
