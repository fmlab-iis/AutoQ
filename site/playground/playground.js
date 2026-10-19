import { EXAMPLES } from './examples.js';

const $ = (id) => document.getElementById(id);
const els = {
  example: $('example'), tabs: $('tabs'), editor: $('editor'), cmd: $('cmd'), output: $('output'),
  status: $('status'), run: $('run'), stop: $('stop'), reset: $('reset'), toolbar: $('toolbar'),
  loopsum: $('loopsum'), loopsumWrap: $('loopsum-wrap'), version: $('version'),
};

// Files each command reads, in argument order.
const MODES = {
  ver: ['pre.hsl', 'circuit.qasm', 'post.hsl'],
  ex: ['pre.hsl', 'circuit.qasm'],
  eq: ['a.qasm', 'b.qasm'],
};
const TEMPLATES = {
  'pre.hsl': 'Extended Dirac\n{|0>}\n',
  'post.hsl': 'Extended Dirac\n{|1>}\n',
  'circuit.qasm': 'OPENQASM 3;\ninclude "stdgates.inc";\nqubit[1] qb;\n\nx qb[0];\n',
  'a.qasm': 'OPENQASM 2.0;\ninclude "qelib1.inc";\nqreg q[1];\nx q[0];\n',
  'b.qasm': 'OPENQASM 2.0;\ninclude "qelib1.inc";\nqreg q[1];\nh q[0];\nz q[0];\nh q[0];\n',
};

const state = { example: null, files: [], active: 0, mode: 'ver' };

// ---------- theme toggle (shared with the landing page) ----------
(function theme() {
  const btn = document.querySelector('.theme');
  if (!btn) return;
  const root = document.documentElement;
  const current = () => root.getAttribute('data-theme')
    || (matchMedia('(prefers-color-scheme: dark)').matches ? 'dark' : 'light');
  const label = () => btn.setAttribute('aria-label', current() === 'dark' ? 'Switch to light theme' : 'Switch to dark theme');
  btn.hidden = false;
  label();
  btn.addEventListener('click', () => {
    const next = current() === 'dark' ? 'light' : 'dark';
    root.setAttribute('data-theme', next);
    try { localStorage.setItem('autoq-theme', next); } catch (e) { /* storage unavailable */ }
    label();
  });
})();

// ---------- examples, tabs, editor ----------
for (const ex of EXAMPLES) {
  const o = document.createElement('option');
  o.value = ex.id;
  o.textContent = ex.title;
  els.example.append(o);
}

function loadExample(id) {
  const ex = EXAMPLES.find((e) => e.id === id) ?? EXAMPLES[0];
  state.example = ex;
  state.files = ex.files.map((f) => ({ ...f }));
  state.active = 0;
  setMode(ex.mode);
  els.example.value = ex.id;
  render();
}

function setMode(mode) {
  state.mode = mode;
  els.toolbar.querySelector(`input[name="mode"][value="${mode}"]`).checked = true;
  for (const name of MODES[mode]) {
    if (!state.files.some((f) => f.name === name)) state.files.push({ name, content: TEMPLATES[name] });
  }
  els.loopsumWrap.hidden = mode === 'eq';
}

function args() {
  const a = [state.mode];
  if (state.mode !== 'eq' && els.loopsum.checked) a.push('--loopsum');
  return a.concat(MODES[state.mode]);
}

function render() {
  els.tabs.replaceChildren(...state.files.map((f, i) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.role = 'tab';
    b.id = `tab-${i}`;
    b.textContent = f.name;
    b.setAttribute('aria-selected', String(i === state.active));
    b.setAttribute('aria-controls', 'editor');
    b.tabIndex = i === state.active ? 0 : -1;
    b.addEventListener('click', () => select(i));
    return b;
  }));
  const f = state.files[state.active];
  els.editor.value = f.content;
  els.editor.setAttribute('aria-labelledby', `tab-${state.active}`);
  els.cmd.innerHTML = '<span class="pr">$ </span>' + escapeHtml(['autoq', ...args()].join(' '));
}

function select(i, focus = false) {
  state.active = i;
  render();
  if (focus) document.getElementById(`tab-${i}`).focus();
}

els.tabs.addEventListener('keydown', (e) => {
  const n = state.files.length;
  const moves = { ArrowRight: 1, ArrowLeft: n - 1 };
  if (e.key in moves) { e.preventDefault(); select((state.active + moves[e.key]) % n, true); }
  else if (e.key === 'Home') { e.preventDefault(); select(0, true); }
  else if (e.key === 'End') { e.preventDefault(); select(n - 1, true); }
});
els.editor.addEventListener('input', () => { state.files[state.active].content = els.editor.value; });
els.example.addEventListener('change', () => loadExample(els.example.value));
els.toolbar.addEventListener('change', (e) => {
  if (e.target.name === 'mode') { setMode(e.target.value); render(); }
  if (e.target === els.loopsum) render();
});
els.reset.addEventListener('click', () => loadExample(state.example.id));

// ---------- running ----------
let worker = null;
let ready = false;
let running = false;
let timer = 0;

function startWorker() {
  ready = false;
  worker = new Worker(new URL('./worker.js', import.meta.url), { type: 'module' });
  worker.onmessage = onMessage;
  worker.onerror = (e) => {
    setStatus('');
    els.version.textContent = 'AutoQ could not be loaded in this browser.';
    show([{ stream: 'err', line: `Could not load AutoQ: ${e.message || 'unknown error'}` }]);
  };
  setStatus('Downloading AutoQ…', true);
  worker.postMessage({ type: 'warmup' });
}

let versionPending = false;
function onMessage({ data }) {
  if (data.type === 'ready') {
    if (!els.version.dataset.done) {
      // Ask for the version first; Run is enabled once it answers.
      versionPending = true;
      worker.postMessage({ args: ['-v'], files: [] });
    } else {
      markReady();
    }
    return;
  }
  if (versionPending) {
    versionPending = false;
    const v = (data.out ?? []).map((o) => o.line).join(' ').trim();
    els.version.dataset.done = '1';
    if (/^[0-9a-f]{40}$/.test(v)) {
      const a = document.createElement('a');
      a.href = `https://github.com/fmlab-iis/AutoQ/commit/${v}`;
      a.textContent = v.slice(0, 9);
      els.version.replaceChildren('AutoQ at commit ', a, ', compiled to WebAssembly.');
    } else {
      els.version.textContent = v ? `AutoQ ${v}, compiled to WebAssembly.` : 'AutoQ, compiled to WebAssembly.';
    }
    markReady();
    return;
  }
  if (!running) return;
  running = false;
  clearInterval(timer);
  els.run.disabled = false;
  els.stop.disabled = true;
  const secs = (data.ms / 1000).toFixed(2);
  if (data.type === 'error') {
    show([...data.out, { stream: 'err', line: `AutoQ stopped unexpectedly: ${data.message}` }]);
    setStatus(`Error after ${secs}s`);
  } else {
    show(data.out, `exit code ${data.code} · ${secs}s in the browser`);
    setStatus(`Finished in ${secs}s`);
  }
}

function markReady() {
  ready = true;
  setStatus('Ready');
  els.run.disabled = false;
}

function run() {
  if (!ready || running) return;
  running = true;
  els.run.disabled = true;
  els.stop.disabled = false;
  show([]);
  const t0 = performance.now();
  setStatus('Running… 0.0s', true);
  timer = setInterval(() => setStatus(`Running… ${((performance.now() - t0) / 1000).toFixed(1)}s`, true), 100);
  worker.postMessage({ args: args(), files: state.files });
}

function stop() {
  if (!running) return;
  running = false;
  clearInterval(timer);
  worker.terminate();
  els.stop.disabled = true;
  els.run.disabled = true;
  show([{ stream: 'err', line: 'Stopped.' }]);
  startWorker();
}

els.toolbar.addEventListener('submit', (e) => { e.preventDefault(); run(); });
els.stop.addEventListener('click', stop);
document.addEventListener('keydown', (e) => {
  if (e.key === 'Enter' && (e.ctrlKey || e.metaKey)) { e.preventDefault(); run(); }
});

// ---------- output ----------
function escapeHtml(s) {
  return s.replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
}
function highlight(line) {
  return escapeHtml(line)
    .replace(/\[OK\]/g, '<span class="ok">[OK]</span>')
    .replace(/\[failed\]|\[ERROR\]/g, (m) => `<span class="bad">${m}</span>`);
}
function show(lines, footer) {
  const html = lines.map((o) => o.stream === 'err'
    ? `<span class="err">${highlight(o.line)}</span>`
    : highlight(o.line));
  if (footer) html.push(`<span class="muted">\n${escapeHtml(footer)}</span>`);
  els.output.innerHTML = html.join('\n');
}
function setStatus(text, busy = false) {
  els.status.textContent = text;
  els.status.classList.toggle('busy', busy);
}

// ---------- start ----------
loadExample(new URLSearchParams(location.search).get('example') ?? EXAMPLES[0].id);
if (typeof WebAssembly === 'object') startWorker();
else {
  els.version.textContent = 'This browser does not support WebAssembly.';
}
