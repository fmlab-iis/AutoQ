// Runs AutoQ (compiled to WebAssembly by wasm/build.sh) off the main thread.
// Message in:  { args: string[], files: {name, content}[] }
// Messages out: { type: 'ready' } once the module is compiled,
//               { type: 'done', code, out, ms } or { type: 'error', message, out, ms }.
import createAutoQ from './autoq.js';

const WASM_URL = new URL('./autoq.wasm', import.meta.url);
let compiled = null;

async function compile() {
  if (compiled) return compiled;
  try {
    compiled = await WebAssembly.compileStreaming(fetch(WASM_URL));
  } catch {
    // Some servers send .wasm without the application/wasm type.
    const bytes = await (await fetch(WASM_URL)).arrayBuffer();
    compiled = await WebAssembly.compile(bytes);
  }
  return compiled;
}

self.onmessage = async ({ data }) => {
  if (data.type === 'warmup') {
    try { await compile(); self.postMessage({ type: 'ready' }); }
    catch (e) { self.postMessage({ type: 'error', message: String(e?.message ?? e), out: [], ms: 0 }); }
    return;
  }
  const { args, files } = data;
  const out = [];
  const t0 = performance.now();
  try {
    const wasmModule = await compile();
    // A fresh instance per run: main() keeps global state between calls.
    const mod = await createAutoQ({
      instantiateWasm(imports, done) {
        WebAssembly.instantiate(wasmModule, imports).then((instance) => done(instance, wasmModule));
        return {};
      },
      print: (line) => out.push({ stream: 'out', line }),
      printErr: (line) => out.push({ stream: 'err', line }),
    });
    mod.FS.mkdir('/work');
    mod.FS.chdir('/work');
    for (const f of files) mod.FS.writeFile(f.name, f.content);
    let code;
    try {
      code = mod.callMain(args);
    } catch (e) {
      if (e && e.name === 'ExitStatus') code = e.status;
      else throw e;
    }
    self.postMessage({ type: 'done', code, out, ms: performance.now() - t0 });
  } catch (e) {
    self.postMessage({ type: 'error', message: String(e?.message ?? e), out, ms: performance.now() - t0 });
  }
};
