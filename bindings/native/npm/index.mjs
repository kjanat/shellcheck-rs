import { createRequire } from 'node:module';
import platforms from './platforms.json' with { type: 'json' };

const require = createRequire(import.meta.url);

export function binaryPath(platform = process.platform, arch = process.arch) {
	const key = `${platform}-${arch}`;
	if (!Object.hasOwn(platforms, key)) throw new Error(`rshellcheck does not support ${key}`);
	const name = `@rshellcheck/rshellcheck-${key}`;
	try {
		return require.resolve(`${name}/bin/rshellcheck${platform === 'win32' ? '.exe' : ''}`);
	} catch (cause) {
		throw new Error(`Missing ${name}. Reinstall with optional dependencies enabled.`, { cause });
	}
}
