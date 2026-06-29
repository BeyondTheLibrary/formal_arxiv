# Proof-dependency DAGs — data drop

This folder contains, for each formalized paper, a **group-level proof-dependency
DAG** of its Lean development, exported as self-describing JSON plus a rendered
image. It is a raw data drop for the website; nothing here is wired into the site
yet. Wire it in however fits `formal_arxiv` best.

## What a "graph" is

Each graph summarizes one paper's Lean proof as a small directed graph of
**proof stages**. A stage (node) is a cluster of Lean modules grouped by their
role in the paper's argument (e.g. "Lemma 5: deconvolution TV gap",
"Definitions & types", "External axioms"). An edge `A → B` means stage `A`
*uses* (depends on) stage `B`. The graph is what the figures in the paper's
appendix show; the rendered PDF/PNG of each is in `images/`.

## Files

- `index.json` — list of all graphs: `{paper_id, title, json, image, node_count, edge_count, axioms_beyond_kernel}`.
- `<paper_id>.json` — one per paper. `paper_id` matches the site's existing ids
  (`ASharp`, `Refuting`, `AGeneralizedTrace`, `ApproximantionMedian`,
  `EfficientlyLeanringMixtures`).
- `images/<name>_dag.pdf` and `images/<name>.png` — the rendered figure for each
  graph (the `.json`'s `image` field points at these, paths relative to this folder).

## How to read `<paper_id>.json`

Top level:

| field | meaning |
|---|---|
| `paper_id` | site id for the paper |
| `title` | paper title |
| `graph_type` | always `group_level_proof_dependency_dag` |
| `description` | one-paragraph human description of how to read the graph |
| `image.pdf` / `image.png` | rendered figure, path relative to this folder |
| `node_count`, `edge_count` | sizes |
| `roots` | node ids with no incoming edge — the paper's main theorem(s) |
| `axioms_beyond_kernel` | list of `{stage, name}`: results admitted as axioms beyond Lean's kernel (empty ⇒ fully kernel-only) |
| `nodes` | the stages (see below) |
| `edges` | the dependencies (see below) |

Each entry of `nodes`:

| field | meaning |
|---|---|
| `id` | stable node id, referenced by `edges` and `roots` |
| `label` | human label (already cleaned: no HTML, `&` and `→` are literal) |
| `role` | one of `theorem`, `lemma_stage`, `definitions_and_types`, `external_axiom`, `prior_work_reproven`, `infrastructure` |
| `color` | hex fill used in the rendered figure (matches `role`) |
| `files`, `lines`, `decls` | aggregate size of the stage (Lean files, source lines, declaration count) |
| `is_root` | true for a main-theorem node |
| `modules` | **the exact Lean modules in this stage**, each `{module, file, lines, decls}` where `module` is the Lean module name (e.g. `Workspace.ProofLemmas.Foo`), `file` is its path (`Workspace/ProofLemmas/Foo.lean`), and `lines`/`decls` are that module's own counts |

So "which files are in a node" = `nodes[i].modules[*].file`. The module's
source lives in the site's existing per-paper Lean store (e.g.
`files/<paper_id>/...` or `api/<paper_id>/lean.*`), keyed by the same module path.

Each entry of `edges`:

| field | meaning |
|---|---|
| `from`, `to` | node ids; `from` uses `to` |
| `bidirectional` | true ⇒ `from` and `to` are mutually recursive (an SCC of the dependency graph); such a pair appears as two edges, one each way, both flagged `true`. Render them as a single double-headed edge if you prefer. |

Edges are **transitively reduced**: a direct `A → B` is omitted whenever a longer
path `A → … → B` already implies it. So the edge set is the minimal one that
preserves reachability (modulo the bidirectional pairs).

## Role → colour legend (matches the figures)

| role | colour | meaning |
|---|---|---|
| `theorem` | `#F5C81E` (yellow) | a main theorem (root) |
| `lemma_stage` | `#5CB874` (green) | a proved stage of the argument |
| `prior_work_reproven` | `#2E8B57` (dark green) | a cited prior result that was reproved from scratch |
| `external_axiom` | `#EB8C1E` (orange) | a result admitted as an axiom (see `axioms_beyond_kernel`) |
| `definitions_and_types` | `#ECECEC` (grey) | the paper's definitions / Lean types |
| `infrastructure` | `#CBE9D4` (light green) | shared supporting machinery |

## Regenerating

These files are produced by `Autoformalization/fig/dag_src/export_dags.py`
(run `python3 export_dags.py`), which reads each repo's `lean_depgraph.json` and
the same grouping used to draw the appendix figures.
