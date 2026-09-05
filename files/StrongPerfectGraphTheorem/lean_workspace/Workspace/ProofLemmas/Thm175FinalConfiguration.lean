import Workspace.ProofLemmas.Thm175FinalBlocks
import Workspace.ProofLemmas.PathGlue

/-! The first two vertices and the rest of an antipath, as used at the end of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175FinalConfiguration

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-- Deleting the first two vertices leaves an anticonnected set. The first
vertex is complete to this set, and the second is not. -/
theorem head_pair_facts {G : SimpleGraph V} {x₁ x₂ : V} {R : List V}
    (h : IsPathList Gᶜ (x₁ :: x₂ :: R)) (hR : R ≠ []) :
    AnticonnectedSet G {v | v ∈ R} ∧
      x₁ ≠ x₂ ∧ x₁ ∉ R ∧ x₂ ∉ R ∧ ¬ G.Adj x₁ x₂ ∧
      VertexComplete G x₁ {v | v ∈ R} ∧
      ¬ VertexComplete G x₂ {v | v ∈ R} := by
  have hnd := h.2.1
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  have hx₁x₂ : ¬ G.Adj x₁ x₂ := by
    have ha := PathBasics.path_adj_succ h (i := 0) (by simp)
    exact ((SimpleGraph.compl_adj _ _ _).mp ha).2
  refine ⟨?_, hnd.1.1, hnd.1.2, hnd.2.1, hx₁x₂, ?_, ?_⟩
  · have hc := (InducedPathExtraction.isChain_of_isPathList h).drop 2
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain (by simpa using hc)
  · intro v hv
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    have hne : x₁ ≠ R[k] := fun he => hnd.1.2 (he ▸ List.getElem_mem hk)
    have hno := PathBasics.path_not_adj_of_gap h
      (i := 0) (j := k+2) (by simp) (by simp; omega) (by omega) (by omega)
    have hno' : ¬ Gᶜ.Adj x₁ R[k] := by simpa using hno
    by_contra hn
    exact hno' ((SimpleGraph.compl_adj _ _ _).mpr ⟨hne, hn⟩)
  · intro hc
    obtain ⟨v, s, rfl⟩ := List.exists_cons_of_ne_nil hR
    have ha := PathBasics.path_adj_succ h (i := 1) (by simp)
    exact ((SimpleGraph.compl_adj _ _ _).mp ha).2 (hc v (by simp))

end Workspace.ProofLemmas.Thm175FinalConfiguration
