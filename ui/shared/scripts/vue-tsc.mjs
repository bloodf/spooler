// TypeScript 7 (the native compiler) has no JS API, and vue-tsc needs one. Run vue-tsc on the TypeScript 6
// compiler from Microsoft's @typescript/typescript6 instead. Packages resolve from the working directory,
// so consumers run it from their own UI package: `node shared/scripts/vue-tsc.mjs --noEmit`.
import { createRequire } from 'node:module';
import { join } from 'node:path';

const require = createRequire(join(process.cwd(), 'package.json'));
const ts6 = createRequire(require.resolve('@typescript/typescript6/package.json'));
require('vue-tsc').run(ts6.resolve('@typescript/old/lib/tsc.js'));
