import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas

/-- Deleting a matching that covers every maximum-degree vertex lowers the
maximum degree by one. -/
theorem DeleteCoveringMatchingMaxDegree
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (M : G.Subgraph)
    (hM : M.IsMatching)
    (hcover : ∀ v : W, G.degree v = G.maxDegree → v ∈ M.verts) :
    letI : DecidablePred (· ∈ M.edgeSet) := Classical.decPred _
    (G.deleteEdges M.edgeSet).maxDegree ≤ G.maxDegree - 1 := by
  classical
  apply SimpleGraph.maxDegree_le_of_forall_degree_le
  intro v
  have hsub : (G.deleteEdges M.edgeSet).neighborFinset v ⊆ G.neighborFinset v := by
    intro w hw
    simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj] at hw ⊢
    exact hw.1
  have hle : (G.deleteEdges M.edgeSet).degree v ≤ G.degree v := Finset.card_le_card hsub
  have hmax : G.degree v ≤ G.maxDegree := SimpleGraph.degree_le_maxDegree G v
  by_cases hv : G.degree v = G.maxDegree
  · obtain ⟨w, hw, -⟩ := hM (hcover v hv)
    have hwmem : w ∈ G.neighborFinset v := by
      simp only [SimpleGraph.mem_neighborFinset]
      exact M.adj_sub hw
    have hwnot : w ∉ (G.deleteEdges M.edgeSet).neighborFinset v := by
      simp only [SimpleGraph.mem_neighborFinset, SimpleGraph.deleteEdges_adj, not_and, not_not]
      intro _
      exact (SimpleGraph.Subgraph.mem_edgeSet).2 hw
    have hssub : (G.deleteEdges M.edgeSet).neighborFinset v ⊂ G.neighborFinset v :=
      ⟨hsub, fun h => hwnot (h hwmem)⟩
    have hlt : (G.deleteEdges M.edgeSet).degree v < G.degree v := Finset.card_lt_card hssub
    omega
  · omega

end Workspace.ProofLemmas
