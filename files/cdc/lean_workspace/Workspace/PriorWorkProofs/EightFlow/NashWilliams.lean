import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph
import Workspace.PriorWorkProofs.EightFlow.FundamentalCycle

/-!
# Nash–Williams–Tutte and the spanning-tree even cover (§3.2, §3.3)

This file supplies the graph-connectivity notions the 8-flow proof needs on the multigraph type
`Graph α β` (`cutEdges`, `IsEdgeConnected`, `IsSpanningTree`; Mathlib has these only for
`SimpleGraph`), and packages the spanning-tree flow (Dvořák Lemma 12) in even-subgraph form as
`spanning_tree_even_cover`. The `k = 3` Nash–Williams–Tutte theorem is admitted as prior work in
`Workspace.PriorWork.NashWilliamsTutte`.
-/

open Set
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.Orientation
open Workspace.PriorWorkProofs.EightFlow

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*} {G : Graph α β}

/-! ## Edge cuts and edge-connectivity -/

/-- The **edge cut** of a vertex set `S`: the edges of `G` with exactly one end in `S`. A loop
never lies in a cut; each parallel edge is counted separately. -/
def cutEdges (G : Graph α β) (S : Set α) : Set β :=
  {e ∈ E(G) | ∃ x y, G.IsLink e x y ∧ x ∈ S ∧ y ∉ S}

/-- `G` is **`k`-edge-connected**: it has at least two vertices and every nontrivial vertex
bipartition `(S, V ∖ S)` is crossed by at least `k` edges. -/
def IsEdgeConnected (G : Graph α β) (k : ℕ) : Prop :=
  2 ≤ V(G).ncard ∧
    ∀ S : Set α, S.Nonempty → S ⊆ V(G) → (V(G) \ S).Nonempty → k ≤ (cutEdges G S).ncard

/-! ## Spanning trees -/

/-- `T ⊆ E(G)` is a **spanning tree** of `G`: the spanning subgraph `G.restrict T` is connected
and has exactly `|V(G)| - 1` edges. On a finite graph this is precisely the tree condition,
without a separate acyclicity clause. -/
def IsSpanningTree (G : Graph α β) (T : Set β) : Prop :=
  T ⊆ E(G) ∧ (G.restrict T).Connected ∧ T.ncard + 1 = V(G).ncard

/-! ## Nash–Williams–Tutte (admitted prior work in `Workspace.PriorWork.NashWilliamsTutte`) -/

/-! ## The spanning-tree flow, as an even cover of the non-tree edges -/

/-- **Dvořák, *Nowhere-zero flows*, Lemma 12 (the spanning-tree flow), in even-subgraph form.**
For a connected `G` with spanning tree `T`, there is an even subgraph `H` containing every
non-tree edge `E(G) \ T`. Proved via the fundamental-cycle argument of
`spanning_tree_even_cover_core`. -/
theorem spanning_tree_even_cover {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) (hG : G.Connected) (T : Set β)
    (hT : IsSpanningTree G T) :
    ∃ H : Set β, IsEvenSubgraph G H ∧ (E(G) \ T) ⊆ H :=
  spanning_tree_even_cover_core hE hT.1 hT.2.1

end Workspace.PriorWorkProofs.EightFlow
