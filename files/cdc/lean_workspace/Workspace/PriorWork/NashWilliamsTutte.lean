import Mathlib
import Workspace.PriorWorkProofs.EightFlow.NashWilliams

/-!
# Prior-work black box: Nash–Williams–Tutte (edge-disjoint spanning trees)

The admitted prior-work `axiom` for the Nash–Williams–Tutte theorem. The connectivity notions
it references (`IsEdgeConnected`, `IsSpanningTree`) are defined in
`Workspace.PriorWorkProofs.EightFlow.NashWilliams`.
-/

open scoped Graph
open Workspace.PriorWorkProofs.EightFlow

namespace Workspace.PriorWork

/-- **Nash–Williams (1961); Tutte (1961); Dvořák, *Nowhere-zero flows*, Theorem 13, case `k = 3`.**

> Every `6`-edge-connected finite multigraph has three pairwise edge-disjoint spanning trees.

The single non-elementary ingredient of the 8-flow theorem, admitted here as prior work. -/
axiom nash_williams_three_edge_disjoint_spanning_trees {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hconn : IsEdgeConnected G 6) :
    ∃ T₁ T₂ T₃ : Set β,
      IsSpanningTree G T₁ ∧ IsSpanningTree G T₂ ∧ IsSpanningTree G T₃ ∧
        Disjoint T₁ T₂ ∧ Disjoint T₁ T₃ ∧ Disjoint T₂ T₃

end Workspace.PriorWork
