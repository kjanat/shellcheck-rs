import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createChecker } from './shellcheck.mjs';

const bytes = readFileSync('target/wasm32-unknown-unknown/release/shellcheck_wasm.wasm');
const fixtures = JSON.parse(readFileSync('.cache/wasm-parity.json', 'utf8'));
const module = await WebAssembly.compile(bytes);
assert.deepEqual(WebAssembly.Module.imports(module), []);
const checker = await createChecker(bytes);
for (const { request, result } of fixtures) {
	if (result.error) {
		assert.throws(() => checker.check(request), (e) => e.message.startsWith(result.error.split(' at line ')[0]));
	} else assert.deepEqual(checker.check(request), result);
}
for (let i = 0; i < 100; i++) assert.deepEqual(checker.check(fixtures[1].request), fixtures[1].result);
assert.throws(() => checker.check({ script: 'x'.repeat(16 * 1024 * 1024) }), /16 MiB/);
checker.close();
assert.throws(() => checker.check(fixtures[0].request), /closed/);
const { exports: e } = await WebAssembly.instantiate(module, {});
const read = () => {
	const ptr = e.sc_check() >>> 0;
	return JSON.parse(new TextDecoder().decode(new Uint8Array(e.memory.buffer, ptr, e.sc_output_len())));
};
assert.match(read().error, /sc_prepare/);
assert.equal(e.sc_prepare(16 * 1024 * 1024 + 1), 0);
assert.match(read().error, /sc_prepare/);
const ptr = e.sc_prepare(1);
new Uint8Array(e.memory.buffer)[ptr] = 255;
assert.ok(read().error);
console.log(`Node: ${fixtures.length} parity cases, reuse and ABI error paths passed`);
