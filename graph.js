// Self-contained declaration-level dependency-graph viewer.
//
// One node per meaningful Lean declaration; edges point from a declaration to
// each declaration it directly uses. Only declarations on the main theorem's
// dependency path are shown (the server omits dead code and contracts away
// compiler-generated noise). Layout is a layered DAG (roots/main theorems on
// top) with a relaxation pass for an organic, low-crossing feel; node size
// encodes how heavily a declaration is used, so the backbone stands out.
// No external libraries — plain SVG with hand-rolled pan/zoom + hover detail.

const SVGNS = "http://www.w3.org/2000/svg";
const $ = (sel) => document.querySelector(sel);

// Site root, resolved from this module's own URL so api/page links work whether
// served at the origin root or under a project sub-path (GitHub Pages).
const ROOT = new URL('.', import.meta.url).href;
const PAPER_ID = (() => {
  const m = location.pathname.match(/\/p\/([^/]+)\/graph/);
  return m ? decodeURIComponent(m[1]) : null;
})();

const ROW_GAP = 96;   // vertical distance between layers (world units)
const COL_GAP = 52;   // minimum horizontal gap between nodes in a layer
const R_MIN = 5, R_MAX = 15, R_ROOT = 16;

const svg = $("#g-svg");
const tip = $("#g-tip");
const statusEl = $("#g-status");

let RAW = null;                      // { nodes, edges, roots } from the server
let viewT = { x: 0, y: 0, k: 1 };    // pan/zoom transform
let rootG = null;                    // <g> holding the whole graph
let NODES = [];                      // node records of the *current* view
let byId = new Map();
let adj = { deps: new Map(), users: new Map() };
let pinned = null;

const DEF_KINDS = new Set(["def", "abbrev", "structure", "instance", "inductive", "classInductive"]);

// ── status / colour of a node (most-severe wins) ─────────────────────────────
function statusOf(n) {
  if (n.is_root) return "root";
  if (n.is_axiom) return "axiom";
  if (n.has_sorry) return "sorry";
  if (n.assumption_tainted) return "tainted";
  if (DEF_KINDS.has(n.kind)) return "def";
  return "proven";
}

function radiusOf(n, maxDeg) {
  if (n.is_root) return R_ROOT;
  const f = maxDeg > 0 ? Math.sqrt((n.deg_in || 0) / maxDeg) : 0;
  return R_MIN + (R_MAX - R_MIN) * f;
}

// ── build the displayed graph from RAW (optionally the theorem skeleton) ──────
function contract(nodes, edges, keepPred) {
  const uses = new Map();
  nodes.forEach((n) => uses.set(n.id, []));
  for (const e of edges) if (uses.has(e.from)) uses.get(e.from).push(e.to);
  const keep = new Set(nodes.filter(keepPred).map((n) => n.id));
  const out = [];
  for (const u of keep) {
    const seen = new Set(), res = new Set(), stack = [...(uses.get(u) || [])];
    while (stack.length) {
      const x = stack.pop();
      if (seen.has(x)) continue;
      seen.add(x);
      if (keep.has(x)) { if (x !== u) res.add(x); }
      else for (const y of (uses.get(x) || [])) stack.push(y);
    }
    for (const v of res) out.push({ from: u, to: v });
  }
  return { nodes: nodes.filter((n) => keep.has(n.id)), edges: out };
}

function buildView(thmsOnly) {
  let nodes = RAW.nodes.map((n) => ({ ...n }));
  let edges = RAW.edges.map((e) => ({ ...e }));
  if (thmsOnly) {
    const keep = (n) => n.is_root || n.kind === "theorem" || n.is_axiom;
    ({ nodes, edges } = contract(nodes, edges, keep));
  }
  // degrees within the displayed graph (drives node sizing + tooltip counts)
  const din = new Map(), dout = new Map();
  nodes.forEach((n) => { din.set(n.id, 0); dout.set(n.id, 0); });
  for (const e of edges) {
    if (dout.has(e.from)) dout.set(e.from, dout.get(e.from) + 1);
    if (din.has(e.to)) din.set(e.to, din.get(e.to) + 1);
  }
  nodes.forEach((n) => { n.deg_in = din.get(n.id); n.deg_out = dout.get(n.id); });
  return { nodes, edges };
}

// ── layered layout + relaxation ──────────────────────────────────────────────
function layout(nodes, edges) {
  const deps = new Map(), users = new Map();
  nodes.forEach((n) => { deps.set(n.id, []); users.set(n.id, []); });
  for (const e of edges) {
    if (!deps.has(e.from) || !deps.has(e.to)) continue;
    deps.get(e.from).push(e.to);
    users.get(e.to).push(e.from);
  }

  // layer = longest path from a "top" (a decl nothing else uses; every root is
  // one), so a declaration sits strictly above all it depends on.
  const layer = new Map(), onstack = new Set();
  function lay(id) {
    if (layer.has(id)) return layer.get(id);
    if (onstack.has(id)) return 0;
    onstack.add(id);
    let best = 0;
    for (const u of users.get(id)) best = Math.max(best, lay(u) + 1);
    onstack.delete(id);
    layer.set(id, best);
    return best;
  }
  nodes.forEach((n) => lay(n.id));
  const maxD = Math.max(0, ...nodes.map((n) => layer.get(n.id)));
  const layers = Array.from({ length: maxD + 1 }, () => []);
  nodes.forEach((n) => layers[layer.get(n.id)].push(n));

  const idx = new Map();
  const reindex = () => layers.forEach((L) => L.forEach((n, i) => idx.set(n.id, i)));
  for (const L of layers)
    L.sort((a, b) => (a.file || "").localeCompare(b.file || "") || a.name.localeCompare(b.name));
  reindex();

  // barycenter crossing reduction (order only)
  const bary = (id, ad) => {
    const a = ad.get(id);
    if (!a.length) return idx.get(id);
    let s = 0; for (const x of a) s += idx.get(x);
    return s / a.length;
  };
  for (let pass = 0; pass < 8; pass++) {
    const down = pass % 2 === 0;
    const range = down ? [...layers.keys()] : [...layers.keys()].reverse();
    for (const li of range) layers[li].sort((a, b) => bary(a.id, down ? users : deps) - bary(b.id, down ? users : deps));
    reindex();
  }

  // initial x by order, each layer centred
  const lb = new Map(nodes.map((n) => [n.id, n]));
  for (const L of layers) {
    const w = (L.length - 1) * COL_GAP;
    L.forEach((n, i) => { n.x = i * COL_GAP - w / 2; n.y = layer.get(n.id) * ROW_GAP; });
  }

  // relaxation: pull each node toward the mean x of its neighbours while keeping
  // the layer order and a minimum gap — straightens edges, organic look.
  for (let it = 0; it < 60; it++) {
    const down = it % 2 === 0;
    const range = down ? [...layers.keys()] : [...layers.keys()].reverse();
    for (const li of range) {
      const L = layers[li];
      for (const n of L) {
        let s = 0, c = 0;
        for (const m of deps.get(n.id)) { const o = lb.get(m); if (o) { s += o.x; c++; } }
        for (const m of users.get(n.id)) { const o = lb.get(m); if (o) { s += o.x; c++; } }
        n.x = c ? s / c : n.x;
      }
      for (let i = 1; i < L.length; i++)             // enforce order + min gap (L→R)
        if (L[i].x < L[i - 1].x + COL_GAP) L[i].x = L[i - 1].x + COL_GAP;
    }
  }
  // recentre the whole drawing on x = 0
  let mn = Infinity, mx = -Infinity;
  for (const n of nodes) { mn = Math.min(mn, n.x); mx = Math.max(mx, n.x); }
  const off = (mn + mx) / 2;
  for (const n of nodes) n.x -= off;

  return { deps, users };
}

// ── render ───────────────────────────────────────────────────────────────────
function render(view) {
  if (rootG) rootG.remove();
  clearHi();
  pinned = null;
  tip.hidden = true;
  svg.classList.remove("focus");

  NODES = view.nodes;
  byId = new Map(NODES.map((n) => [n.id, n]));
  adj = layout(NODES, view.edges);

  const maxDeg = Math.max(0, ...NODES.map((n) => n.deg_in || 0));
  rootG = document.createElementNS(SVGNS, "g");
  const edgeG = document.createElementNS(SVGNS, "g");
  const nodeG = document.createElementNS(SVGNS, "g");
  rootG.appendChild(edgeG);
  rootG.appendChild(nodeG);

  for (const e of view.edges) {
    const a = byId.get(e.from), b = byId.get(e.to);
    if (!a || !b) continue;
    const path = document.createElementNS(SVGNS, "path");
    const my = (a.y + b.y) / 2;
    path.setAttribute("d", `M${a.x},${a.y} C${a.x},${my} ${b.x},${my} ${b.x},${b.y}`);
    path.setAttribute("class", "edge");
    path.dataset.from = e.from; path.dataset.to = e.to;
    edgeG.appendChild(path);
    (a._edges = a._edges || []).push(path);
    (b._edges = b._edges || []).push(path);
  }

  for (const n of NODES) {
    n._edges = n._edges || [];
    const g = document.createElementNS(SVGNS, "g");
    g.setAttribute("class", "node " + (n.is_root ? "root" : ""));
    g.setAttribute("transform", `translate(${n.x},${n.y})`);
    const st = statusOf(n);
    const r = radiusOf(n, maxDeg);

    let shape;
    if (n.is_axiom) {
      shape = document.createElementNS(SVGNS, "rect");
      const s = r * 1.6;
      shape.setAttribute("x", -s / 2); shape.setAttribute("y", -s / 2);
      shape.setAttribute("width", s); shape.setAttribute("height", s);
      shape.setAttribute("transform", "rotate(45)");
    } else {
      shape = document.createElementNS(SVGNS, "circle");
      shape.setAttribute("r", r);
    }
    shape.setAttribute("class", "shape fill-" + st);
    g.appendChild(shape);

    const label = document.createElementNS(SVGNS, "text");
    label.setAttribute("class", "nlabel");
    label.setAttribute("x", r + 4);
    label.setAttribute("y", 3.5);
    label.textContent = n.name.length > 38 ? n.name.slice(0, 37) + "…" : n.name;
    g.appendChild(label);

    n._g = g; n._status = st;
    g.addEventListener("mouseenter", () => { if (!pinned) focusNode(n.id); });
    g.addEventListener("mouseleave", () => { if (!pinned) unfocus(); });
    g.addEventListener("mousemove", (ev) => { if (!pinned) positionTip(ev); });
    g.addEventListener("click", (ev) => { ev.stopPropagation(); pin(n.id); });
    nodeG.appendChild(g);
  }

  svg.appendChild(rootG);
  statusEl.hidden = true;
  if (NODES.length > 220) $("#g-labels").checked = false;
  applyLabels();
  applySearch();
  fit();
}

// ── focus / tooltip ──────────────────────────────────────────────────────────
let _hi = { nodes: [], edges: [] };
function clearHi() {
  for (const el of _hi.nodes) el.classList.remove("keep", "sel");
  for (const el of _hi.edges) el.classList.remove("hot");
  _hi = { nodes: [], edges: [] };
}
function neighbours(id) {
  return new Set([id, ...(adj.deps.get(id) || []), ...(adj.users.get(id) || [])]);
}
function focusNode(id, persistent) {
  clearHi();
  svg.classList.add("focus");
  for (const nid of neighbours(id)) {
    const el = byId.get(nid)._g; el.classList.add("keep"); _hi.nodes.push(el);
  }
  byId.get(id)._g.classList.add("sel");
  for (const path of (byId.get(id)._edges || [])) { path.classList.add("hot"); _hi.edges.push(path); }
  showTip(byId.get(id), persistent);
}
function unfocus() {
  svg.classList.remove("focus");
  clearHi();
  tip.hidden = true; tip.classList.remove("pinned");
}
function pin(id) {
  if (pinned === id) { pinned = null; unfocus(); return; }
  pinned = id; focusNode(id, true);
}

const KIND_LABEL = { theorem: "theorem", def: "def", axiom: "axiom", inductive: "inductive",
                     ctor: "constructor", rec: "recursor", structure: "structure", abbrev: "abbrev" };
function esc(s) { return String(s).replace(/[&<>]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;" }[c])); }

function showTip(n, persistent) {
  const st = n._status;
  const bmap = { root: ["b-root", "main theorem"], axiom: ["b-axiom", "axiom — assumed"],
    sorry: ["b-sorry", "contains sorry"], tainted: ["b-tainted", "rests on assumption"],
    proven: ["b-proven", "proven"], def: ["b-def", "definition"] };
  const badges = [`<span class="tip-badge b-kind">${esc(KIND_LABEL[n.kind] || n.kind)}</span>`];
  if (bmap[st]) badges.push(`<span class="tip-badge ${bmap[st][0]}">${bmap[st][1]}</span>`);
  if (st !== "tainted" && st !== "axiom" && st !== "sorry" && n.assumption_tainted)
    badges.push(`<span class="tip-badge b-tainted">rests on assumption</span>`);

  let html = `<div class="tip-name">${esc(n.name)}</div>`;
  html += `<div class="tip-badges">${badges.join("")}</div>`;
  if (n.file) html += `<div class="tip-file">${esc(n.file.replace(/^lean_workspace\//, ""))}</div>`;
  else if (n.module) html += `<div class="tip-file">${esc(n.module)}</div>`;
  if (n.rationale)
    html += `<div class="tip-sec"><div class="tip-sec-h">Formalizes</div><div class="tip-rationale">${esc(n.rationale)}</div></div>`;
  else if (n.docstring)
    html += `<div class="tip-sec"><div class="tip-rationale">${esc(n.docstring)}</div></div>`;
  if (n.offenders && n.offenders.length)
    html += `<div class="tip-sec"><div class="tip-sec-h">Rests on</div><div class="tip-offenders">` +
            n.offenders.map((o) => `${esc(o.name)} (${esc(o.kind)})`).join(", ") + `</div></div>`;
  html += `<div class="tip-stats">uses ${n.deg_out} · used by ${n.deg_in}</div>`;

  tip.innerHTML = html;
  tip.hidden = false;
  tip.classList.toggle("pinned", !!persistent);
  if (persistent) { const p = worldToScreen(n.x, n.y); placeTip(p.x + 18, p.y + 18); }
}
function positionTip(ev) { placeTip(ev.clientX + 16, ev.clientY + 16); }
function placeTip(x, y) {
  const r = tip.getBoundingClientRect(), vw = window.innerWidth, vh = window.innerHeight;
  if (x + r.width > vw - 8) x = x - r.width - 32;
  if (y + r.height > vh - 8) y = Math.max(8, vh - r.height - 8);
  tip.style.left = x + "px"; tip.style.top = y + "px";
}

// ── pan / zoom / fit ─────────────────────────────────────────────────────────
function applyT() { rootG.setAttribute("transform", `translate(${viewT.x},${viewT.y}) scale(${viewT.k})`); }
function worldToScreen(wx, wy) {
  const rect = svg.getBoundingClientRect();
  return { x: rect.left + viewT.x + wx * viewT.k, y: rect.top + viewT.y + wy * viewT.k };
}
svg.addEventListener("wheel", (ev) => {
  ev.preventDefault();
  const rect = svg.getBoundingClientRect();
  const mx = ev.clientX - rect.left, my = ev.clientY - rect.top;
  const k2 = Math.min(4, Math.max(0.05, viewT.k * Math.exp(-ev.deltaY * 0.0015)));
  viewT.x = mx - (mx - viewT.x) * (k2 / viewT.k);
  viewT.y = my - (my - viewT.y) * (k2 / viewT.k);
  viewT.k = k2; applyT();
  if (pinned) { const n = byId.get(pinned); const p = worldToScreen(n.x, n.y); placeTip(p.x + 18, p.y + 18); }
}, { passive: false });

let drag = null;
svg.addEventListener("mousedown", (ev) => {
  if (ev.button !== 0) return;
  drag = { sx: ev.clientX, sy: ev.clientY, ox: viewT.x, oy: viewT.y, moved: false };
  svg.classList.add("panning");
});
window.addEventListener("mousemove", (ev) => {
  if (!drag) return;
  viewT.x = drag.ox + (ev.clientX - drag.sx);
  viewT.y = drag.oy + (ev.clientY - drag.sy);
  if (Math.abs(ev.clientX - drag.sx) + Math.abs(ev.clientY - drag.sy) > 3) drag.moved = true;
  applyT();
});
window.addEventListener("mouseup", (ev) => {
  if (drag && !drag.moved && ev.target === svg) { pinned = null; unfocus(); }
  drag = null; svg.classList.remove("panning");
});
window.addEventListener("keydown", (ev) => { if (ev.key === "Escape") { pinned = null; unfocus(); } });

function fit() {
  if (!NODES.length) return;
  const xs = NODES.map((n) => n.x), ys = NODES.map((n) => n.y);
  const minx = Math.min(...xs) - 60, maxx = Math.max(...xs) + 220;
  const miny = Math.min(...ys) - 40, maxy = Math.max(...ys) + 40;
  const rect = svg.getBoundingClientRect();
  viewT.k = Math.max(0.05, Math.min(rect.width / (maxx - minx), rect.height / (maxy - miny), 1.4));
  viewT.x = (rect.width - (maxx + minx) * viewT.k) / 2;
  viewT.y = (rect.height - (maxy + miny) * viewT.k) / 2;
  applyT();
}

// ── controls ─────────────────────────────────────────────────────────────────
function applyLabels() {
  const show = $("#g-labels").checked;
  for (const n of NODES) { const l = n._g.querySelector(".nlabel"); if (l) l.style.display = show ? "" : "none"; }
}
function applySearch() {
  const q = $("#g-search").value.trim().toLowerCase();
  for (const n of NODES) {
    const hit = q && (n.name.toLowerCase().includes(q) || n.id.toLowerCase().includes(q));
    n._g.classList.toggle("match", !!hit);
  }
}
function rebuild() { render(buildView($("#g-thms-only").checked)); }

$("#g-thms-only").addEventListener("change", rebuild);
$("#g-labels").addEventListener("change", applyLabels);
$("#g-search").addEventListener("input", applySearch);
$("#g-fit").addEventListener("click", fit);

// ── boot ─────────────────────────────────────────────────────────────────────
async function boot() {
  if (!PAPER_ID) { fail("No paper id in the URL."); return; }
  $("#g-back").href = `${ROOT}p/${encodeURIComponent(PAPER_ID)}/`;
  try {
    const [meta, graph] = await Promise.all([
      fetch(`${ROOT}api/${PAPER_ID}/meta`).then((r) => r.ok ? r.json() : null).catch(() => null),
      fetch(`${ROOT}api/${PAPER_ID}/graph.json`).then((r) => {
        if (r.status === 404) throw new Error("no-graph");
        if (!r.ok) throw new Error("http " + r.status);
        return r.json();
      }),
    ]);
    if (meta && meta.title) {
      $("#g-title").textContent = meta.title;
      document.title = meta.title + " · dependency graph";
    }
    RAW = graph;
    if (!RAW.nodes.length) { fail("This paper's dependency graph is empty."); return; }
    $("#g-subtitle").textContent =
      `${RAW.nodes.length} declarations on the main path · ${RAW.edges.length} dependencies · ` +
      `${RAW.roots.length} root${RAW.roots.length === 1 ? "" : "s"}`;
    rebuild();
  } catch (e) {
    if (e.message === "no-graph")
      fail("This paper has no committed dependency graph (lean_depgraph.json). " +
           "It must be produced on a build-capable machine and committed to the paper repo.");
    else fail("Could not load the dependency graph: " + e.message);
  }
}
function fail(msg) { statusEl.textContent = msg; statusEl.classList.add("err"); statusEl.hidden = false; }

boot();
