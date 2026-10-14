#!/usr/bin/env node
import { spawnSync } from 'node:child_process';
import { binaryPath } from './index.mjs';

try {
	const result = spawnSync(binaryPath(), process.argv.slice(2), { stdio: 'inherit' });
	if (result.error) throw result.error;
	if (result.signal) process.kill(process.pid, result.signal);
	else process.exitCode = result.status ?? 1;
} catch (error) {
	console.error(`rshellcheck: ${error.message}`);
	process.exitCode = 1;
}
