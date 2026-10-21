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
// ver and ex run one circuit on a set of states and share a workspace; eq
// compares two circuits and has its own files and examples. Each workspace
// keeps its edits while the other one is shown.
const kind = (mode) => (mode === 'eq' ? 'eq' : 'circuit');

const state = { mode: 'ver', workspaces: {} };
const ws = () => state.workspaces[kind(state.mode)];

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
// Loads an example into its workspace. Within the same workspace the command
// stays as it is (an ex run can switch examples); otherwise it becomes the
// example's own command.
function loadExample(id) {
  const ex = EXAMPLES.find((e) => e.id === id) ?? EXAMPLES[0];
  state.workspaces[kind(ex.mode)] = { example: ex, files: ex.files.map((f) => ({ ...f })), active: 0 };
  showMode(kind(ex.mode) === kind(state.mode) ? state.mode : ex.mode);
}

function setMode(mode) {
  if (!state.workspaces[kind(mode)]) {
    const first = EXAMPLES.find((e) => kind(e.mode) === kind(mode));
    state.workspaces[kind(mode)] = { example: first, files: first.files.map((f) => ({ ...f })), active: 0 };
  }
  showMode(mode);
}

function showMode(mode) {
  state.mode = mode;
  els.toolbar.querySelector(`input[name="mode"][value="${mode}"]`).checked = true;
  els.loopsumWrap.hidden = mode === 'eq';
  els.example.replaceChildren(...EXAMPLES
    .filter((e) => kind(e.mode) === kind(mode))
    .map((e) => new Option(e.title, e.id)));
  els.example.value = ws().example.id;
  render();
}

function args() {
  const a = [state.mode];
  if (state.mode !== 'eq' && els.loopsum.checked) a.push('--loopsum');
  return a.concat(MODES[state.mode]);
}

function render() {
  const { files, active } = ws();
  els.tabs.replaceChildren(...files.map((f, i) => {
    const b = document.createElement('button');
    b.type = 'button';
    b.role = 'tab';
    b.id = `tab-${i}`;
    b.textContent = f.name;
    b.setAttribute('aria-selected', String(i === active));
    b.setAttribute('aria-controls', 'editor');
    b.tabIndex = i === active ? 0 : -1;
    b.addEventListener('click', () => select(i));
    return b;
  }));
  els.editor.value = files[active].content;
  els.editor.setAttribute('aria-labelledby', `tab-${active}`);
  els.cmd.innerHTML = '<span class="pr">$ </span>' + escapeHtml(['autoq', ...args()].join(' '));
}

function select(i, focus = false) {
  ws().active = i;
  render();
  if (focus) document.getElementById(`tab-${i}`).focus();
}

els.tabs.addEventListener('keydown', (e) => {
  const { files, active } = ws();
  const n = files.length;
  const moves = { ArrowRight: 1, ArrowLeft: n - 1 };
  if (e.key in moves) { e.preventDefault(); select((active + moves[e.key]) % n, true); }
  else if (e.key === 'Home') { e.preventDefault(); select(0, true); }
  else if (e.key === 'End') { e.preventDefault(); select(n - 1, true); }
});
els.editor.addEventListener('input', () => { ws().files[ws().active].content = els.editor.value; });
els.example.addEventListener('change', () => loadExample(els.example.value));
els.toolbar.addEventListener('change', (e) => {
  if (e.target.name === 'mode') setMode(e.target.value);
  if (e.target === els.loopsum) render();
});
els.reset.addEventListener('click', () => loadExample(ws().example.id));

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
  worker.postMessage({ args: args(), files: ws().files });
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
    .replace(/\[OK\]|\[equal\]/g, (m) => `<span class="ok">${m}</span>`)
    .replace(/\[failed\]|\[unequal\]|\[ERROR\]/g, (m) => `<span class="bad">${m}</span>`);
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
