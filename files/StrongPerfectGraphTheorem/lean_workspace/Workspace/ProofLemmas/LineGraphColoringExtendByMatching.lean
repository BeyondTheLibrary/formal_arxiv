import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas

/-- From a matching edge and an incident vertex, recover the unique matching
partner and present the edge in the form `s(v, w)`. -/
private lemma matching_edge_at {W : Type*} {G : SimpleGraph W} {M : G.Subgraph}
    {e : Sym2 W} (he : e ∈ M.edgeSet) {v : W} (hv : v ∈ e) :
    ∃ w, M.Adj v w ∧ e = s(v, w) := by
  induction e with
  | _ a b =>
    rw [SimpleGraph.Subgraph.mem_edgeSet] at he
    rw [Sym2.mem_iff] at hv
    rcases hv with rfl | rfl
    · exact ⟨b, he, rfl⟩
    · exact ⟨a, he.symm, Sym2.eq_swap⟩

/-- A coloring of the line graph after deleting a matching extends by one
fresh color to the original line graph. -/
theorem LineGraphColoringExtendByMatching
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (M : G.Subgraph) (d : Nat)
    (hM : M.IsMatching)
    (hcolor : (G.deleteEdges M.edgeSet).lineGraph.Colorable d) :
    G.lineGraph.Colorable (d + 1) := by
  classical
  obtain ⟨c⟩ := hcolor
  -- surviving edges of `G` are vertices of the deleted graph's line graph
  have hsurv : ∀ e : G.edgeSet, (e : Sym2 W) ∉ M.edgeSet →
      (e : Sym2 W) ∈ (G.deleteEdges M.edgeSet).edgeSet := by
    intro e he
    rw [SimpleGraph.edgeSet_deleteEdges]
    exact ⟨e.2, he⟩
  refine ⟨SimpleGraph.Coloring.mk
    (fun e => if h : (e : Sym2 W) ∈ M.edgeSet then Fin.last d
      else (c ⟨(e : Sym2 W), hsurv e h⟩).castSucc) ?_⟩
  intro e₁ e₂ hadj
  obtain ⟨hne, v, hv₁, hv₂⟩ := SimpleGraph.lineGraph_adj_iff_exists.1 hadj
  by_cases h₁ : (e₁ : Sym2 W) ∈ M.edgeSet <;> by_cases h₂ : (e₂ : Sym2 W) ∈ M.edgeSet
  · -- both edges lie in the matching: impossible, they meet at `v`
    exfalso
    obtain ⟨w₁, hw₁, he₁⟩ := matching_edge_at h₁ hv₁
    obtain ⟨w₂, hw₂, he₂⟩ := matching_edge_at h₂ hv₂
    exact hne (Subtype.ext (by rw [he₁, he₂, hM.eq_of_adj_left hw₁ hw₂]))
  · dsimp only
    rw [dif_pos h₁, dif_neg h₂]
    exact (Fin.castSucc_lt_last _).ne'
  · dsimp only
    rw [dif_neg h₁, dif_pos h₂]
    exact (Fin.castSucc_lt_last _).ne
  · dsimp only
    rw [dif_neg h₁, dif_neg h₂]
    have hadj' : (G.deleteEdges M.edgeSet).lineGraph.Adj
        ⟨(e₁ : Sym2 W), hsurv e₁ h₁⟩ ⟨(e₂ : Sym2 W), hsurv e₂ h₂⟩ := by
      refine SimpleGraph.lineGraph_adj_iff_exists.2 ⟨?_, v, hv₁, hv₂⟩
      intro h
      exact hne (Subtype.ext (Subtype.mk.inj h))
    exact fun h => c.valid hadj' (Fin.castSucc_injective d h)

end Workspace.ProofLemmas
