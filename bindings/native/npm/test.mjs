import assert from 'node:assert/strict';
import { test } from 'node:test';
import { binaryPath } from './index.mjs';
import platforms from './platforms.json' with { type: 'json' };

test('rejects unsupported platforms before resolving a dependency', () => {
	assert.throws(() => binaryPath('plan9', 'x64'), /does not support plan9-x64/);
	assert.throws(() => binaryPath('linux', 'mips'), /does not support linux-mips/);
});
test('reports how to recover a missing optional binary', () => {
	assert.throws(() => binaryPath('android', 'ia32'), /optional dependencies enabled/);
});
test('covers Windows, macOS, Linux, FreeBSD and Android release targets', () => {
	assert.equal(Object.keys(platforms).length, 15);
	assert.equal(platforms['linux-arm'], 'armv7-unknown-linux-musleabihf');
	assert.equal(platforms['win32-ia32'], 'i686-pc-windows-msvc');
});
