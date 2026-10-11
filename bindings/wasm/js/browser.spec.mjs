import { expect, test } from '@playwright/test';
import { readFile } from 'node:fs/promises';
import { createServer } from 'node:http';
import path from 'node:path';

test('browser worker agrees with native core', async ({ page }) => {
	const root = path.resolve('../../..');
	const server = createServer(async (req, res) => {
		const paths = {
			'/': 'bindings/wasm/js/test.html',
			'/worker.mjs': 'bindings/wasm/js/worker.mjs',
			'/shellcheck.mjs': 'bindings/wasm/js/shellcheck.mjs',
			'/core.wasm': 'target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm',
			'/fixtures.json': '.cache/wasm-parity.json',
		};
		if (req.url === '/') {
			res.end('<!doctype html><title>WASM parity</title>');
			return;
		}
		if (!paths[req.url]) {
			res.writeHead(404).end();
			return;
		}
		try {
			const body = await readFile(path.join(root, paths[req.url]));
			res.setHeader('Content-Type', req.url.endsWith('.mjs') ? 'text/javascript' : 'application/octet-stream');
			res.end(body);
		} catch {
			res.writeHead(500).end();
		}
	});
	await new Promise((resolve) => server.listen(0, '127.0.0.1', resolve));
	try {
		await page.goto(`http://127.0.0.1:${server.address().port}`);
		const failures = await page.evaluate(async () => {
			const worker = new Worker('/worker.mjs', { type: 'module' });
			const ask = (data) =>
				new Promise((resolve, reject) => {
					worker.onmessage = ({ data }) => resolve(data);
					worker.onerror = reject;
					worker.postMessage(data);
				});
			try {
				const initialized = await ask({ id: 0, wasm: await (await fetch('/core.wasm')).arrayBuffer() });
				if (!initialized.ready) return [initialized];
				const fixtures = await (await fetch('/fixtures.json')).json();
				const errors = [];
				for (let id = 0; id < fixtures.length; id++) {
					const f = fixtures[id];
					const response = await ask({ id: id + 1, request: f.request });
					if (
						f.result.error
							? !response.error?.includes(f.result.error.split(' at line ')[0])
							: JSON.stringify(response.result) !== JSON.stringify(f.result)
					) errors.push({ id, response });
				}
				return errors;
			} finally {
				worker.terminate();
			}
		});
		expect(failures).toEqual([]);
	} finally {
		await new Promise((resolve) => server.close(resolve));
	}
});
