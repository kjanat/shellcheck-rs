/** Load the same import-free module used by the Go and Python bindings. */
export async function createChecker(bytes) {
	if (bytes === undefined) {
		const url = new URL('./shellcheck_wasm.wasm', import.meta.url);
		if (url.protocol === 'file:' && typeof process !== 'undefined' && process.versions?.node) {
			const { readFile } = await import('node:fs/promises');
			bytes = await readFile(url);
		} else {
			const response = await fetch(url);
			if (!response.ok) throw new Error(`Failed to load ShellCheck WASM: ${response.status}`);
			bytes = await response.arrayBuffer();
		}
	}
	const module = await WebAssembly.compile(bytes);
	if (WebAssembly.Module.imports(module).length) throw new Error('Unexpected WASM imports');
	const instance = await WebAssembly.instantiate(module, {});
	const e = instance.exports;
	if (e.sc_abi_version() !== 1) throw new Error('Unsupported ShellCheck ABI');
	const encoder = new TextEncoder();
	const decoder = new TextDecoder('utf-8', { fatal: true });
	let closed = false;
	return {
		check(request) {
			if (closed) throw new Error('Checker closed; create a new instance');
			const input = encoder.encode(JSON.stringify(request));
			if (input.length > 16 * 1024 * 1024) throw new Error('Request exceeds 16 MiB');
			let output;
			try {
				const ptr = e.sc_prepare(input.length) >>> 0;
				if (!ptr) throw new Error('Request rejected');
				new Uint8Array(e.memory.buffer, ptr, input.length).set(input);
				const result = e.sc_check() >>> 0;
				// Calls may grow memory, so always acquire a fresh view afterward.
				output = JSON.parse(decoder.decode(new Uint8Array(e.memory.buffer, result, e.sc_output_len() >>> 0)));
			} catch (error) {
				closed = true;
				throw error;
			}
			if (output.error) throw new Error(output.error);
			return output;
		},
		close() {
			if (!closed) e.sc_reset();
			closed = true;
		},
	};
}
