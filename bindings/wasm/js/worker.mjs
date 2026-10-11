import { createChecker } from './shellcheck.mjs';

// Each worker owns one instance. Terminate the worker to cancel a long check.
let checker;
self.onmessage = async ({ data }) => {
	const { id, wasm, request } = data;
	try {
		if (wasm) {
			checker?.close();
			checker = await createChecker(wasm);
			self.postMessage({ id, ready: true });
		} else {
			if (!checker) throw new Error('Initialize the worker with WASM bytes first');
			self.postMessage({ id, result: checker.check(request) });
		}
	} catch (error) {
		self.postMessage({ id, error: String(error) });
	}
};
