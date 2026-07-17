import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Bridge
import Workspace.PriorWorkProofs.Jaeger.Moves

/-!
# Prior-work black box: Fleischner's Splitting Lemma (degree ≥ 4)

The admitted prior-work `axiom` for Fleischner's Splitting Lemma, in the edge-reduced form the
Jaeger reduction consumes. The `reroute` move it references is defined in
`Workspace.PriorWorkProofs.Jaeger.Moves`.

> **Lemma 1 (Fleischner).** Let `v` be a vertex of degree at least `4` in a bridgeless graph
> `G`. There exist two edges `e₁, e₂` incident with `v` such that the split `G(v, e₁, e₂)`
> — detach `e₁, e₂` from `v` onto a fresh degree-2 vertex `v*` — is again bridgeless.

H. Fleischner, *Spanning Eulerian subgraphs, the Splitting Lemma, and Petersen's theorem*,
Discrete Math. **101** (1992) 33–37; restated (degree-≥4, unconditional) by Kaiser, Kužel, Li,
Wang, *A note on k-walks in bridgeless graphs*.
-/

open scoped Graph
open Workspace.PriorWorkProofs.Jaeger

namespace Workspace.PriorWork

/-- **E1 — Fleischner's Splitting Lemma (degree ≥ 4), edge-reduced form.**

For a finite bridgeless loopless graph `G` and a vertex `v` of degree at least `4`, there
exist two distinct edges `e₁ = v v₁`, `e₂ = v v₂` incident with `v` such that the
edge-reduced split `reroute G v₁ v₂ e₁ e₂` (delete `e₂`, relabel `e₁` to join `v₁`–`v₂`) is
bridgeless. Its edge count is one less than that of `G` (`edgeSet_reroute`).

Admitted from Fleischner (Discrete Math. 101, 1992); see the module docstring. -/
axiom fleischner_splitting_lemma {α β : Type*} (G : Graph α β) (v : α)
    (hV : V(G).Finite) (hE : E(G).Finite) (hll : G.IsLoopless) (hbr : G.Bridgeless)
    (hdeg : 4 ≤ G.degree v) :
    ∃ (v1 v2 : α) (e1 e2 : β), e1 ≠ e2 ∧ G.IsLink e1 v v1 ∧ G.IsLink e2 v v2 ∧
      (reroute G v1 v2 e1 e2).Bridgeless

end Workspace.PriorWork
