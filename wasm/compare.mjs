// Runs every playground example with the native CLI and with the WebAssembly
// build, and checks that both print the same output (timing and memory
// figures are masked).
//
// Usage: node wasm/compare.mjs [path/to/native/autoq] [dir with autoq.js]
//        defaults: build/cli/autoq and site/playground
import { execFileSync } from 'node:child_process';
import { mkdtempSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const native = resolve(process.argv[2] ?? 'build/cli/autoq');
const wasmDir = resolve(process.argv[3] ?? 'site/playground');
const { EXAMPLES } = await import(pathToFileURL(join(wasmDir, 'examples.js')));
const { default: createAutoQ } = await import(pathToFileURL(join(wasmDir, 'autoq.js')));

const ARGS = { ver: ['pre.hsl', 'circuit.qasm', 'post.hsl'], ex: ['pre.hsl', 'circuit.qasm'], eq: ['a.qasm', 'b.qasm'] };
const mask = (s) => s
  .replace(/\[\d+(\.\d+)?(ms|s|m|h|d)?\](?= with| memory|\.|$)/g, '[T]')
  .replace(/\[\d+(\.\d+)?(ms|us|s|m)\]/g, '[T]')
  .replace(/\[\d+MB\]/g, '[MB]')
  .trim();

let failures = 0;
for (const ex of EXAMPLES) {
  const args = [ex.mode, ...ARGS[ex.mode]];
  const dir = mkdtempSync(join(tmpdir(), 'autoq-cmp-'));
  for (const f of ex.files) writeFileSync(join(dir, f.name), f.content);

  let nat, natCode = 0;
  try { nat = execFileSync(native, args, { cwd: dir, encoding: 'utf8', stdio: ['ignore', 'pipe', 'pipe'] }); }
  catch (e) { nat = (e.stdout ?? '') + (e.stderr ?? ''); natCode = e.status; }

  const lines = [];
  const mod = await createAutoQ({ print: (l) => lines.push(l), printErr: (l) => lines.push(l) });
  mod.FS.mkdir('/work'); mod.FS.chdir('/work');
  for (const f of ex.files) mod.FS.writeFile(f.name, f.content);
  let wasmCode;
  try { wasmCode = mod.callMain([...args]); } catch (e) { if (e?.name === 'ExitStatus') wasmCode = e.status; else throw e; }
  const wasm = lines.join('\n');

  const same = mask(nat) === mask(wasm) && natCode === wasmCode;
  if (!same) failures++;
  console.log(`${same ? 'same' : 'DIFF'}  ${ex.id.padEnd(8)} autoq ${args.join(' ')}  (exit ${natCode}/${wasmCode})`);
  if (process.env.VERBOSE) console.log('  ' + mask(wasm).split('\n').join('\n  '));
  if (!same) console.log(`  native: ${mask(nat)}\n  wasm:   ${mask(wasm)}`);
}
console.log(failures ? `${failures} example(s) differ` : 'All examples match.');
process.exit(failures ? 1 : 0);
