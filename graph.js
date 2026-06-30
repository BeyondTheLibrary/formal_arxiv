// Group-level proof-dependency DAG viewer, built on Cytoscape.js + dagre.
//
// Default view = the block diagram the paper's appendix shows: one rounded block
// per proof stage (a cluster of Lean modules), coloured by role, laid out
// top-down (roots/main theorems on top) with real dependency arrows.
//
// Clicking a block breaks it apart, in an animated relayout, into its individual
// Lean files. The exploded view shows the true file-level wiring: thin internal
// edges among the stage's own files, plus coloured arrows to/from the outside
// blocks those files actually depend on. Those file edges are derived from the
// paper's declaration-level dependency graph, so the picture stays faithful.
// Clicking a file opens its .lean source in the paper's Lean viewer.
//
// Cytoscape + dagre handle layout, animation, pan/zoom and arrowheads; the only
// hand-rolled pieces are the data wrangling and the figure-style HTML cards.

const $ = (sel) => document.querySelector(sel);
const ROOT = new URL('.', import.meta.url).href;
const PAPER_ID = (() => {
  const m = location.pathname.match(/\/p\/([^/]+)\/graph/);
  return m ? decodeURIComponent(m[1]) : null;
})();
const LEAN_WORKSPACE_PREFIX = 'lean_workspace/';

const ROLE_COLOR = {
  theorem: '#F5C81E', lemma_stage: '#5CB874', prior_work_reproven: '#2E8B57',
  external_axiom: '#EB8C1E', definitions_and_types: '#ECECEC', infrastructure: '#CBE9D4',
};

// ── module-level data derived from the declaration graph ──────────────────────
let STAGES = [], byId = new Map(), STAGE_EDGES = [];
let MOD_META = new Map();      // module → {file, short, lines, decls, stage, flag}
let MOD_STAGE = new Map();     // module → stageId
let STAGE_MODS = new Map();    // stageId → [module]
let MOD_EDGES = [];            // {from,to} module-level
let cy = null;
const expanded = new Map();      // stageId -> accent colour, for blocks broken into files
// distinct, dark-text-friendly accents so scattered files can be traced to their block
const PALETTE = ['#7FB3FF', '#7FD7A8', '#F3C969', '#E59BD0', '#F0996B', '#9CD4D0', '#C2A6F0', '#BFD46B'];
function nextAccent() {
  const used = new Set(expanded.values());
  return PALETTE.find((c) => !used.has(c)) || PALETTE[expanded.size % PALETTE.length];
}

const fmt = (n) => Number(n).toLocaleString('en-US');
const plural = (n, w) => `${fmt(n)} ${w}${n === 1 ? '' : 's'}`;
const escapeHtml = (s) => String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const _decoder = document.createElement('textarea');
const decode = (s) => { _decoder.innerHTML = String(s); return _decoder.value; };
const fileNode = (mod) => 'f::' + mod;

function deriveModuleGraph(declGraph) {
  const declMod = new Map(), flags = new Map();
  for (const n of declGraph.nodes) {
    if (!n.module) continue;
    declMod.set(n.id, n.module);
    const f = flags.get(n.module) || { axiom: false, sorry: false, tainted: false };
    f.axiom = f.axiom || !!n.is_axiom;
    f.sorry = f.sorry || !!n.has_sorry;
    f.tainted = f.tainted || !!n.assumption_tainted;
    flags.set(n.module, f);
  }
  const seen = new Set(), edges = [];
  for (const e of declGraph.edges) {
    const a = declMod.get(e.from), b = declMod.get(e.to);
    if (!a || !b || a === b) continue;
    const k = a + ' ' + b;
    if (seen.has(k)) continue;
    seen.add(k); edges.push({ from: a, to: b });
  }
  return { edges, flags };
}
const flagOf = (f) => !f ? null : f.axiom ? 'axiom' : f.sorry ? 'sorry' : f.tainted ? 'tainted' : null;

// estimate card height from how the title will wrap at ~24 chars/line
function cardHeight(title, hasAxiom) {
  const words = title.split(/\s+/); let line = '', lines = 1;
  for (const w of words) {
    if (line && (line + ' ' + w).length > 24) { lines++; line = w; } else line = line ? line + ' ' + w : w;
  }
  lines = Math.min(lines, 3);
  return 18 + lines * 18 + 18 + (hasAxiom ? 17 : 0);
}

// ── element builders ──────────────────────────────────────────────────────────
function stageNodeDef(s, position) {
  return {
    group: 'nodes',
    data: {
      id: s.id, kind: 'stage', title: s.label, statline: s._stat,
      axiomName: s._axiomName || '', color: s.color, role: s.role,
      w: 214, h: s._h, faded: false, hl: false,
    },
    ...(position ? { position } : {}),
  };
}
function fileNodeDef(mod, position) {
  const m = MOD_META.get(mod) || {};
  const sid = MOD_STAGE.get(mod);
  const accent = expanded.get(sid) || '#7FD7A8';
  const bcolor = m.flag === 'axiom' ? '#c0560a' : m.flag === 'sorry' ? '#b81f1f'
    : m.flag === 'tainted' ? '#9a6b00' : 'rgba(0,0,0,.4)';
  return {
    group: 'nodes',
    data: {
      id: fileNode(mod), kind: 'file', mod, stage: sid,
      label: (m.flag ? '⚠ ' : '') + (m.short || mod),
      color: accent, bcolor, file: m.file,
      lines: m.lines || 0, decls: m.decls || 0, flag: m.flag || '',
    },
    // copy: every file would otherwise share one position object and collapse
    ...(position ? { position: { x: position.x, y: position.y } } : {}),
  };
}
function stageEdgeDefs() {
  const out = [], seen = new Set();
  for (const e of STAGE_EDGES) {
    if (!byId.get(e.from) || !byId.get(e.to)) continue;
    const id = 'se::' + e.from + '::' + e.to;
    if (seen.has(id)) continue; seen.add(id);
    out.push({ group: 'edges', data: { id, source: e.from, target: e.to, etype: 'stage' } });
  }
  return out;
}
// Edges are a pure function of which stages are expanded. Every module edge a→b
// is drawn at the right granularity: its endpoint is a *file* node if that file's
// stage is expanded, else the collapsed *stage* node. Collapsed↔collapsed pairs
// use the clean transitively-reduced stage edges from the DAG json instead.
function computeEdges() {
  const defs = [], seen = new Set();
  const add = (source, target, etype) => {
    const id = 'e::' + source + '>>' + target;
    if (seen.has(id)) return; seen.add(id);
    defs.push({ group: 'edges', data: { id, source, target, etype } });
  };
  for (const e of STAGE_EDGES) {
    if (expanded.has(e.from) || expanded.has(e.to)) continue;
    if (!byId.get(e.from) || !byId.get(e.to)) continue;
    add(e.from, e.to, 'stage');
  }
  for (const e of MOD_EDGES) {
    const sa = MOD_STAGE.get(e.from), sb = MOD_STAGE.get(e.to);
    if (!sa || !sb) continue;
    if (!expanded.has(sa) && !expanded.has(sb)) continue;
    const ua = expanded.has(sa) ? fileNode(e.from) : sa;
    const ub = expanded.has(sb) ? fileNode(e.to) : sb;
    if (ua === ub) continue;
    add(ua, ub, sa === sb ? 'int' : 'cross');
  }
  return defs;
}
function rebuildEdges() { cy.edges().remove(); cy.add(computeEdges()); }

// Two animated dagre runs at once pile nodes on top of each other, so we never
// run concurrently: if a layout is mid-flight, remember a run was requested and
// fire one more when it finishes (coalescing a burst of expand/collapse calls).
// The "finished" signal is a timer, not the layoutstop event, so the busy flag
// can never get stuck (a stuck flag would silently skip every later relayout).
let _layoutRunning = false, _layoutPending = false, _layoutTimer = null;
function runLayout(animate) {
  if (_layoutRunning) { _layoutPending = true; return; }
  _layoutRunning = true;
  const dur = animate ? 420 : 0;
  cy.layout({
    name: 'dagre', rankDir: 'TB', nodeSep: 26, rankSep: 64, edgeSep: 12,
    animate: !!animate, animationDuration: dur, animationEasing: 'ease-in-out-cubic',
    fit: true, padding: 48,
  }).run();
  clearTimeout(_layoutTimer);
  _layoutTimer = setTimeout(() => {
    _layoutRunning = false;
    if (_layoutPending) { _layoutPending = false; runLayout(true); }
  }, dur + 120);
}
const scheduleLayout = () => runLayout(true);

// average position of a set of (existing) node ids, for a natural burst/implosion
function avgPos(ids) {
  let x = 0, y = 0, n = 0;
  for (const id of ids) { const el = cy.getElementById(id); if (el.nonempty()) { const p = el.position(); x += p.x; y += p.y; n++; } }
  return n ? { x: x / n, y: y / n } : undefined;
}

function expand(id) {
  if (expanded.has(id)) return;
  const p = cy.getElementById(id).position();
  expanded.set(id, nextAccent());
  cy.batch(() => {
    cy.getElementById(id).remove();              // also drops its stage edges
    for (const m of (STAGE_MODS.get(id) || [])) cy.add(fileNodeDef(m, p));
    rebuildEdges();
  });
  renderChips();
  scheduleLayout();
}

function collapse(id) {
  if (!expanded.has(id)) return;
  const mods = STAGE_MODS.get(id) || [];
  const p = avgPos(mods.map(fileNode));
  expanded.delete(id);
  cy.batch(() => {
    for (const m of mods) cy.getElementById(fileNode(m)).remove();
    cy.add(stageNodeDef(byId.get(id), p));
    rebuildEdges();
  });
  renderChips();
  scheduleLayout();
}

function collapseAll() {
  if (!expanded.size) return;
  cy.batch(() => {
    for (const id of Array.from(expanded.keys())) {
      const mods = STAGE_MODS.get(id) || [];
      const p = avgPos(mods.map(fileNode));
      for (const m of mods) cy.getElementById(fileNode(m)).remove();
      expanded.delete(id);
      cy.add(stageNodeDef(byId.get(id), p));
    }
    rebuildEdges();
  });
  renderChips();
  scheduleLayout();
}

// ── "broken apart" chips: see what's open, collapse any one ────────────────────
function renderChips() {
  const bar = $('#g-open');
  if (!bar) return;
  bar.innerHTML = '';
  if (!expanded.size) { bar.hidden = true; return; }
  bar.hidden = false;
  for (const [id, accent] of expanded) {
    const s = byId.get(id);
    const chip = document.createElement('button');
    chip.className = 'g-chip';
    chip.title = 'Collapse "' + (s ? s.label : id) + '"';
    chip.innerHTML = `<span class="g-chip-dot" style="background:${accent}"></span>` +
      `<span class="g-chip-name">${escapeHtml(s ? s.label : id)}</span><span class="g-chip-x">✕</span>`;
    chip.addEventListener('click', () => collapse(id));
    bar.appendChild(chip);
  }
}

// ── tooltip ───────────────────────────────────────────────────────────────────
const tip = $('#g-tip');
function showTip(node, ev) {
  const d = node.data();
  let html;
  if (d.kind === 'stage') {
    html = `<div class="tip-name">${escapeHtml(d.title)}</div><div class="tip-stats">${d.statline}</div>` +
      (d.axiomName ? `<div class="tip-file">axiom: ${escapeHtml(d.axiomName)}</div>` : '') +
      `<div class="tip-open">click to break into ${plural((STAGE_MODS.get(d.id) || []).length, 'file')}</div>`;
  } else {
    let uses = 0, used = 0;
    for (const e of MOD_EDGES) { if (e.from === d.mod) uses++; if (e.to === d.mod) used++; }
    html = `<div class="tip-name">${escapeHtml(d.mod.replace(/^Workspace\./, ''))}</div>` +
      `<div class="tip-file">${escapeHtml((d.file || '').replace(/^lean_workspace\//, ''))}</div>` +
      (d.flag ? `<div class="tip-badges"><span class="tip-badge b-${d.flag}">${d.flag === 'tainted' ? 'rests on assumption' : d.flag}</span></div>` : '') +
      `<div class="tip-stats">${plural(d.lines, 'line')} · ${plural(d.decls, 'decl')} · uses ${uses} · used by ${used} files</div>` +
      `<div class="tip-open">click to open the Lean source ↗ · shift-click to collapse this block</div>`;
  }
  tip.innerHTML = html; tip.hidden = false;
  const e = ev && ev.originalEvent;
  if (e) placeTip(e.clientX + 16, e.clientY + 16);
}
function placeTip(x, y) {
  const r = tip.getBoundingClientRect(), vw = innerWidth, vh = innerHeight;
  if (x + r.width > vw - 8) x = x - r.width - 32;
  if (y + r.height > vh - 8) y = Math.max(8, vh - r.height - 8);
  tip.style.left = x + 'px'; tip.style.top = y + 'px';
}

// ── cytoscape style ───────────────────────────────────────────────────────────
function styleSheet() {
  return [
    { selector: 'node[kind="stage"]', style: {
      'background-opacity': 0, 'width': 'data(w)', 'height': 'data(h)', 'shape': 'round-rectangle',
    } },
    { selector: 'node[kind="file"]', style: {
      'shape': 'round-rectangle', 'background-color': 'data(color)', 'background-opacity': 0.55,
      'border-width': 1.5, 'border-color': 'data(bcolor)', 'label': 'data(label)',
      'font-family': 'ui-monospace, SFMono-Regular, Menlo, monospace', 'font-size': 10,
      'color': '#10202a', 'text-valign': 'center', 'text-halign': 'center',
      'width': 152, 'height': 24, 'text-max-width': 140, 'text-wrap': 'ellipsis',
    } },
    { selector: 'node.hl[kind="file"]', style: { 'border-color': '#79c0ff', 'border-width': 2.4 } },
    { selector: 'node.faded', style: { 'opacity': 0.18 } },

    { selector: 'edge', style: {
      'curve-style': 'bezier', 'target-arrow-shape': 'triangle', 'arrow-scale': 1.05,
      'width': 1.6, 'line-color': '#6b7079', 'target-arrow-color': '#6b7079',
    } },
    { selector: 'edge[etype="stage"]', style: { 'width': 2.2, 'line-color': '#7a808a', 'target-arrow-color': '#7a808a' } },
    { selector: 'edge[etype="int"]', style: { 'width': 1.2, 'line-color': '#9aa1ad', 'target-arrow-color': '#9aa1ad', 'opacity': 0.6, 'arrow-scale': 0.8 } },
    { selector: 'edge[etype="cross"]', style: { 'width': 2, 'line-color': '#2f7fe0', 'target-arrow-color': '#2f7fe0' } },
    { selector: 'edge.hl', style: { 'width': 3, 'line-color': '#79c0ff', 'target-arrow-color': '#79c0ff', 'opacity': 1, 'z-index': 9 } },
    { selector: 'edge.faded', style: { 'opacity': 0.06 } },
  ];
}

function htmlLabels() {
  cy.nodeHtmlLabel([{
    query: 'node[kind="stage"]',
    valign: 'center', halign: 'center', valignBox: 'center', halignBox: 'center',
    tpl: (d) => {
      const cls = ['gcard', `role-${d.role}`, d.faded ? 'is-faded' : '', d.hl ? 'is-hl' : ''].join(' ');
      const ax = d.axiomName ? `<div class="gcard-axiom">${escapeHtml(d.axiomName)}</div>` : '';
      return `<div class="${cls}" style="width:${d.w}px;height:${d.h}px;background:${d.color}">` +
        `<div class="gcard-title">${escapeHtml(d.title)}</div>` +
        `<div class="gcard-stats">${d.statline}</div>${ax}</div>`;
    },
  }]);
}

// ── interactions ──────────────────────────────────────────────────────────────
function wireEvents() {
  cy.on('tap', 'node[kind="stage"]', (e) => { tip.hidden = true; expand(e.target.id()); });
  cy.on('tap', 'node[kind="file"]', (e) => {
    const oe = e.originalEvent || {};
    if (oe.shiftKey || oe.altKey || oe.metaKey) { tip.hidden = true; collapse(e.target.data('stage')); return; }
    const f = e.target.data('file'); if (!f) return;
    window.open(`${ROOT}p/${encodeURIComponent(PAPER_ID)}/?file=${encodeURIComponent(f)}`, '_blank', 'noopener');
  });
  cy.on('tap', (e) => { if (e.target === cy) collapseAll(); });

  cy.on('mouseover', 'node', (e) => {
    const nd = e.target;
    if (nd.data('kind') === 'file') nd.addClass('hl');
    nd.connectedEdges().addClass('hl');
    showTip(nd, e);
  });
  cy.on('mousemove', 'node', (e) => { if (!tip.hidden && e.originalEvent) placeTip(e.originalEvent.clientX + 16, e.originalEvent.clientY + 16); });
  cy.on('mouseout', 'node', (e) => { e.target.removeClass('hl'); e.target.connectedEdges().removeClass('hl'); tip.hidden = true; });
}

// ── controls ──────────────────────────────────────────────────────────────────
function wireControls() {
  $('#g-fit').addEventListener('click', () => cy.animate({ fit: { padding: 48 } }, { duration: 300 }));
  $('#g-collapse').addEventListener('click', () => collapseAll());
  window.addEventListener('keydown', (ev) => { if (ev.key === 'Escape') collapseAll(); });
  const search = $('#g-search');
  if (search) search.addEventListener('input', () => {
    const q = search.value.trim().toLowerCase();
    cy.nodes().forEach((nd) => {
      const d = nd.data();
      const hay = d.kind === 'stage'
        ? (d.title + ' ' + (STAGE_MODS.get(d.id) || []).join(' ')).toLowerCase()
        : (d.mod || '').toLowerCase();
      const hit = q && hay.includes(q);
      if (d.kind === 'file') nd.toggleClass('hl', !!hit);
      else nd.data('hl', !!hit);
    });
  });
}

// ── boot ──────────────────────────────────────────────────────────────────────
async function boot() {
  if (!PAPER_ID) return fail('No paper id in the URL.');
  $('#g-back').href = `${ROOT}p/${encodeURIComponent(PAPER_ID)}/`;
  if (typeof cytoscape === 'undefined') return fail('Graph libraries failed to load.');
  try { cytoscape.use(window.cytoscapeDagre); } catch (e) { /* auto-registered */ }

  try {
    const [meta, dag, decl] = await Promise.all([
      fetch(`${ROOT}api/${PAPER_ID}/meta`).then((r) => r.ok ? r.json() : null).catch(() => null),
      fetch(`${ROOT}proof_dags/${PAPER_ID}.json`).then((r) => {
        if (r.status === 404) throw new Error('no-dag');
        if (!r.ok) throw new Error('http ' + r.status);
        return r.json();
      }),
      fetch(`${ROOT}api/${PAPER_ID}/graph.json`).then((r) => r.ok ? r.json() : null).catch(() => null),
    ]);
    const title = (meta && meta.title) || dag.title;
    if (title) { $('#g-title').textContent = title; document.title = title + ' · proof graph'; }

    STAGES = dag.nodes.map((n) => ({ ...n, label: decode(n.label), color: n.color || ROLE_COLOR[n.role] || '#5CB874' }));
    byId = new Map(STAGES.map((n) => [n.id, n]));
    STAGE_EDGES = dag.edges || [];
    const axiomByStage = new Map();
    for (const a of (dag.axioms_beyond_kernel || [])) if (a.stage) axiomByStage.set(a.stage, decode(a.name));

    const derived = decl ? deriveModuleGraph(decl) : { edges: [], flags: new Map() };
    MOD_EDGES = derived.edges;
    for (const s of STAGES) {
      const mods = [];
      for (const m of (s.modules || [])) {
        mods.push(m.module);
        MOD_STAGE.set(m.module, s.id);
        const short = m.module.replace(/^Workspace\./, '').replace(/^Lemmas\.Lemma_/, '');
        const file = m.file.startsWith(LEAN_WORKSPACE_PREFIX) ? m.file : LEAN_WORKSPACE_PREFIX + m.file;
        MOD_META.set(m.module, { file, short, lines: m.lines, decls: m.decls, stage: s.id, flag: flagOf(derived.flags.get(m.module)) });
      }
      STAGE_MODS.set(s.id, mods);
      s._stat = `${plural(s.files, 'file')} · ${plural(s.lines, 'line')} · ${plural(s.decls, 'decl')}`;
      s._axiomName = s.role === 'external_axiom' ? (axiomByStage.get(s.id) || axiomByStage.get('axiom') || null) : null;
      s._h = cardHeight(s.label, !!s._axiomName);
    }

    const nStageEdges = stageEdgeDefs().length;
    $('#g-subtitle').textContent =
      `${STAGES.length} proof stage${STAGES.length === 1 ? '' : 's'} · ${nStageEdges} dependencies · click blocks to break them into files`;

    cy = cytoscape({
      container: $('#g-cy'),
      elements: [...STAGES.map((s) => stageNodeDef(s)), ...stageEdgeDefs()],
      style: styleSheet(),
      wheelSensitivity: 0.2, minZoom: 0.1, maxZoom: 2.5,
    });
    htmlLabels();
    wireEvents();
    wireControls();
    renderChips();
    runLayout(false);
    $('#g-status').hidden = true;

    // ?expand=a,b,c pre-breaks one or more blocks (deep link / testing)
    const wantExpand = new URLSearchParams(location.search).get('expand');
    if (wantExpand) {
      const ids = wantExpand.split(',').map((s) => s.trim()).filter((s) => byId.get(s));
      if (ids.length) setTimeout(() => ids.forEach(expand), 50);
    }
  } catch (e) {
    if (e.message === 'no-dag') fail('This paper has no proof-stage graph (proof_dags/' + PAPER_ID + '.json).');
    else fail('Could not load the proof graph: ' + (e && e.message || e));
  }
}
function fail(msg) { const s = $('#g-status'); s.textContent = msg; s.classList.add('err'); s.hidden = false; }

boot();
