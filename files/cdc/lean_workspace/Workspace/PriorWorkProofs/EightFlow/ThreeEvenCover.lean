import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Orientation
import Workspace.Types.Flow
import Workspace.PriorWorkProofs.EightFlow.EvenSubgraph
import Workspace.PriorWorkProofs.EightFlow.NashWilliams
import Workspace.PriorWork.NashWilliamsTutte
import Workspace.PriorWorkProofs.EightFlow.Doubling

/-!
# Every bridgeless graph's edges are covered by three even subgraphs (§3.5–§3.8)

Corollary 8: the edge set of every finite bridgeless multigraph is the union of three even
subgraphs. `three_even_subgraphs_cover_of_3edgeConnected` handles the `3`-edge-connected case,
combining `three_spanning_trees_cover` (the doubling + projection step, proved in `Doubling.lean`)
with the spanning-tree even cover `spanning_tree_even_cover`. The reduction to the
`3`-edge-connected case and the final `bridgeless_gamma_flow` are in `Reduction.lean`.
-/

open Set
open scoped Graph
open Workspace.Types.Gamma
open Workspace.Types.Orientation

namespace Workspace.PriorWorkProofs.EightFlow

variable {α β : Type*} {G : Graph α β}

/-! ## The doubling + projection step -/

/-- **Lemmas 3–4 (doubling + projection).** A `3`-edge-connected finite multigraph has three
spanning trees such that every edge lies outside at least one of them. Proved in `Doubling.lean`
(`doubling_covering`): double `G` to the `6`-edge-connected `2G`, apply the Nash–Williams axiom to
get three edge-disjoint spanning trees of `2G`, and project them back to `G`. -/
theorem three_spanning_trees_cover (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite)
    (hconn : IsEdgeConnected G 3) :
    ∃ T₁ T₂ T₃ : Set β,
      IsSpanningTree G T₁ ∧ IsSpanningTree G T₂ ∧ IsSpanningTree G T₃ ∧
        ∀ e ∈ E(G), e ∉ T₁ ∨ e ∉ T₂ ∨ e ∉ T₃ :=
  doubling_covering G hV hE hconn

/-! ## The 3-edge-connected case -/

/-- **Proposition 5 / Corollary 8, `3`-edge-connected case.** Every `3`-edge-connected (hence
connected) finite multigraph has its edge set covered by three even subgraphs.

Proved from `three_spanning_trees_cover` and the spanning-tree even cover
`spanning_tree_even_cover`: attach to each spanning tree `Tᵢ` the even subgraph `Hᵢ ⊇ E(G) \ Tᵢ`;
since every edge lies outside some `Tⱼ`, it lies in `E(G) \ Tⱼ ⊆ Hⱼ`. -/
theorem three_even_subgraphs_cover_of_3edgeConnected (G : Graph α β) (hV : V(G).Finite)
    (hE : E(G).Finite) (hGc : G.Connected) (hconn : IsEdgeConnected G 3) :
    ∃ H₁ H₂ H₃ : Set β,
      IsEvenSubgraph G H₁ ∧ IsEvenSubgraph G H₂ ∧ IsEvenSubgraph G H₃ ∧
        E(G) ⊆ H₁ ∪ H₂ ∪ H₃ := by
  obtain ⟨T₁, T₂, T₃, hT₁, hT₂, hT₃, hcov⟩ := three_spanning_trees_cover G hV hE hconn
  obtain ⟨H₁, hH₁, hsub₁⟩ := spanning_tree_even_cover G hV hE hGc T₁ hT₁
  obtain ⟨H₂, hH₂, hsub₂⟩ := spanning_tree_even_cover G hV hE hGc T₂ hT₂
  obtain ⟨H₃, hH₃, hsub₃⟩ := spanning_tree_even_cover G hV hE hGc T₃ hT₃
  refine ⟨H₁, H₂, H₃, hH₁, hH₂, hH₃, ?_⟩
  intro e he
  simp only [Set.mem_union]
  rcases hcov e he with h | h | h
  · exact Or.inl (Or.inl (hsub₁ ⟨he, h⟩))
  · exact Or.inl (Or.inr (hsub₂ ⟨he, h⟩))
  · exact Or.inr (hsub₃ ⟨he, h⟩)

/-! ## The reduction to the 3-edge-connected case and the 8-flow theorem

The reduction `bridgeless ⟶ 3-edge-connected` and the final nowhere-zero `Γ`-flow
`bridgeless_gamma_flow` are proved in `Reduction.lean`; see
`Workspace.PriorWorkProofs.EightFlow.bridgeless_gamma_flow`. They are not restated here to avoid a
duplicate declaration. -/

end Workspace.PriorWorkProofs.EightFlow
