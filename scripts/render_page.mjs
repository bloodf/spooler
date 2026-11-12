// Capture mock artwork through the same owned Chrome session as the page tests.
import { writeFile, mkdir } from 'node:fs/promises';
import { join, basename } from 'node:path';
import { launch } from '../ui/tests/page/cdp.mjs';

const [url, out, width, height, scale, validate, evidence] = process.argv.slice(2);
const browser = await launch();
const page = await browser.newPage();
try {
  await page.size(Number(width), Number(height), Number(scale));
  await page.call('Network.enable');
  await page.call('Network.setBlockedURLs', { urls: ['http://*', 'https://*'] });
  await page.goto(url);
  await page.evaluate(`(async () => {
    await document.fonts.ready;
    if (${validate === 'true'}) {
      const deadline = Date.now() + 8000;
      while (document.documentElement.dataset.renderReady !== 'true') {
        if (document.documentElement.dataset.renderError) throw Error(document.documentElement.dataset.renderError);
        if (Date.now() > deadline) throw Error('Mock preview did not become ready');
        await new Promise(r => setTimeout(r, 50));
      }
    }
    if (document.documentElement.dataset.renderError) throw Error(document.documentElement.dataset.renderError);
  })()`);
  const errors = page.events.filter(e => e.method === 'Runtime.exceptionThrown');
  if (errors.length) throw Error(JSON.stringify(errors));
  await writeFile(out, await page.screenshot());
} catch (error) {
  await mkdir(evidence, { recursive: true });
  const prefix = join(evidence, basename(out) + '.failed');
  await writeFile(prefix + '.html', await page.evaluate('document.documentElement.outerHTML'));
  await writeFile(prefix + '.json', JSON.stringify({ error: String(error), events: page.events }, null, 2));
  throw error;
} finally {
  await page.close();
  await browser.close();
}
