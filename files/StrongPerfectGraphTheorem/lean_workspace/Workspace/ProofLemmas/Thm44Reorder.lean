import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue

/-!
# *"a path of length 3 can be reordered to be an antipath of length 3"*

PAPER (proof of 4.4, printed p. 16): *"Consequently, every path pair is also an antipath pair
(because a path of length `3` can be reordered to be an antipath of length `3`)."*

Concretely: if `u-x-y-v` is a path of `G`, then `x-v-u-y` is an antipath of `G`.  Indeed
`xv`, `vu`, `uy` are the three non-edges of the path and `xu`, `uv`... — more precisely, the
three edges of the new list, read in `Ḡ`, are the three non-edges `xv`, `vu`, `uy` of the old
path, and the three non-edges of the new list, read in `Ḡ`, are the three edges `xu`, `xy`,
`yv` of the old path.  The new list has the same four vertices, so the same length `3`, and its
ends `x`, `y` are the interior of the old path while its interior `v`, `u` is the pair of ends of
the old path — which is exactly the swap of roles a path pair / antipath pair needs.

Applied in `Ḡ` the same statement reads *"an antipath of length 3 can be reordered to be a path
of length 3"*, which is the other half of the printed parenthesis.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm44Reorder

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- **Reordering a path of length `3` into an antipath of length `3`.**  If `p = u-x-y-v` is a
path of `G` then `x-v-u-y` is an antipath of `G`, its ends `x, y` being the interior of `p` and
its interior being the two ends `v, u` of `p`. -/
theorem antipath_of_path_three {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (h3 : pathLength p = 3) :
    ∃ x y : V, G.Adj x y ∧ x ∈ SPGT.interior p ∧ y ∈ SPGT.interior p ∧
      IsAntipathFrom G [x, v, u, y] x y := by
  have hl : IsPathList G p := hp.1
  have hlen : p.length = 4 := by
    have h := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hl
    omega
  obtain ⟨a, b, c, d, rfl⟩ := Workspace.ProofLemmas.PathGlue.length_eq_four hlen
  have ha : a = u := by simpa using hp.2.1
  have hd : d = v := by simpa using hp.2.2
  -- the three edges of the path
  have e01 : G.Adj a b := by
    have h := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 0) (j := 1)
      (by simp) (by simp)).mpr (Or.inl rfl)
    simpa using h
  have e12 : G.Adj b c := by
    have h := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 1) (j := 2)
      (by simp) (by simp)).mpr (Or.inl rfl)
    simpa using h
  have e23 : G.Adj c d := by
    have h := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 2) (j := 3)
      (by simp) (by simp)).mpr (Or.inl rfl)
    simpa using h
  -- the three non-edges of the path
  have n02 : ¬ G.Adj a c := by
    intro h
    have h' := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 0) (j := 2)
      (by simp) (by simp)).mp (by simpa using h)
    omega
  have n03 : ¬ G.Adj a d := by
    intro h
    have h' := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 0) (j := 3)
      (by simp) (by simp)).mp (by simpa using h)
    omega
  have n13 : ¬ G.Adj b d := by
    intro h
    have h' := (Workspace.ProofLemmas.PathBasics.path_adj_iff hl (i := 1) (j := 3)
      (by simp) (by simp)).mp (by simpa using h)
    omega
  have hnd : ([a, b, c, d] : List V).Nodup := hl.2.1
  have hdis : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
    have h := hnd
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, ne_eq] at h
    tauto
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hdis
  have h1' : b ≠ a := h1.symm
  have h2' : c ≠ a := h2.symm
  have h3' : d ≠ a := h3.symm
  have h4' : c ≠ b := h4.symm
  have h5' : d ≠ b := h5.symm
  have h6' : d ≠ c := h6.symm
  have hnd' : ([b, d, a, c] : List V).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, ne_eq]
    tauto
  -- `x-v-u-y` = `b-d-a-c` is a path of `Ḡ`
  have hpath : IsPathList Gᶜ [b, d, a, c] := by
    refine Workspace.ProofLemmas.PathGlue.isPathList_four hnd' ?_ ?_ ?_ ?_ ?_ ?_
    · exact (SimpleGraph.compl_adj G b d).mpr ⟨h5, n13⟩
    · exact (SimpleGraph.compl_adj G d a).mpr ⟨h3', fun h => n03 h.symm⟩
    · exact (SimpleGraph.compl_adj G a c).mpr ⟨h2, n02⟩
    · exact fun h => ((SimpleGraph.compl_adj G b a).mp h).2 e01.symm
    · exact fun h => ((SimpleGraph.compl_adj G b c).mp h).2 e12
    · exact fun h => ((SimpleGraph.compl_adj G d c).mp h).2 e23.symm
  refine ⟨b, c, e12, by simp [SPGT.interior], by simp [SPGT.interior], ?_⟩
  rw [← ha, ← hd]
  exact ⟨hpath, by simp, by simp⟩

end Workspace.ProofLemmas.Thm44Reorder
