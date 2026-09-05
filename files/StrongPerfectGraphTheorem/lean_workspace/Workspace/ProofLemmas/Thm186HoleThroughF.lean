import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue

/-!
# 18.6 — *"`p₁-⋯-p_c-Q-p₁` is a hole"*

PAPER (`paper/proofs/18_6.md`, closing paragraph, published page 114):

> *"Choose `c` with `c` minimum, and let `Q` be a path between `p₁, p_c` with interior in `F`.
> Then `p₁-⋯-p_c-Q-p₁` is a hole …"*

The same construction is used in claim (1) (*"`f₁-⋯-f_k-p_{a₂}-p_{a₂−1}-⋯-p_{b₁}-f₁` is a
hole"*) and twice in claim (2), always for the same reason: the stretch of the induced path `P`
between two attachments has **no** attachment strictly inside it, so the only edges between that
stretch and the interior of `Q` are the two at the ends.

This module isolates that step.  The hole is the list
`P.take (c+1) ++ (interior Q).reverse`, i.e. `p₁, …, p_c` followed by the interior of `Q`
traversed backwards, which is the paper's cyclic order.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm186HoleThroughF

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- **The paper's hole `p₁-⋯-p_c-Q-p₁`.**

`P` is an induced path, `Q` an induced path from `P[0]` to `P[c]` whose interior lies in a set
`F` disjoint from `V(P)`, and no vertex of `P` strictly between `P[0]` and `P[c]` has a
neighbour in `F`.  Then the stretch `P[0], …, P[c]` closed through the interior of `Q` is a
hole. -/
theorem hole_through_F {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    {F : Set V} (hFP : ∀ f ∈ F, f ∉ P)
    {c : ℕ} (hc : c < P.length) (hc2 : 2 ≤ c)
    {Q : List V} (hQ : IsPathFrom G Q (P[0]'(by omega)) (P[c]'hc))
    (hQ3 : 3 ≤ Q.length)
    (hQint : ∀ z ∈ SPGT.interior Q, z ∈ F)
    (hnoatt : ∀ (k : ℕ) (hk : k < P.length), 0 < k → k < c →
        ∀ f ∈ F, ¬ G.Adj (P[k]'hk) f) :
    IsHoleList G (P.take (c + 1) ++ (SPGT.interior Q).reverse) := by
  have hQl : IsPathList G Q := hQ.1
  have hQpos : 0 < Q.length := by omega
  have hPpos : 0 < P.length := by omega
  have hQ0 : (Q[0]'(by omega)) = (P[0]'hPpos) :=
    PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hQlast : (Q[Q.length - 1]'(by omega)) = (P[c]'hc) :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
  -- the stretch `p₁ … p_c` of `P`
  have hslice : IsPathFrom G (P.take (c + 1)) (P[0]'hPpos) (P[c]'hc) := by
    have h := PathBasics.isPathFrom_slice hP (i := 0) (j := c) (by omega) hc
    simpa using h
  -- the interior of `Q`, traversed backwards
  have hIQ : IsPathFrom G (SPGT.interior Q)
      (Q[1]'(by omega)) (Q[Q.length - 2]'(by omega)) :=
    PathGlue.isPathFrom_interior hQl hQ3
  have hR : IsPathFrom G (SPGT.interior Q).reverse
      (Q[Q.length - 2]'(by omega)) (Q[1]'(by omega)) :=
    PathBasics.isPathFrom_reverse hIQ
  -- decoders
  have hmemtake : ∀ x : V, x ∈ P.take (c + 1) ↔
      ∃ (k : ℕ) (hk : k < P.length), k ≤ c ∧ (P[k]'hk) = x := by
    intro x
    have h := PathBasics.mem_slice_iff P (i := 0) (j := c) (Nat.zero_le c) hc (x := x)
    simpa using h
  have hmemR : ∀ y : V, y ∈ (SPGT.interior Q).reverse ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ m + 2 ≤ Q.length ∧ (Q[m]'hm) = y := by
    intro y
    rw [List.mem_reverse]
    constructor
    · exact fun hy => PathBasics.exists_getElem_of_mem_interior hQl hy
    · rintro ⟨m, hm, h1, h2, rfl⟩
      exact PathBasics.getElem_mem_interior hQl hm h1 h2
  refine PathGlue.glue_hole hslice hR ?_ ?_ ?_
  · -- the two pieces are vertex-disjoint: the interior of `Q` lies in `F`, which misses `P`
    intro x hx hcon
    obtain ⟨m, hm, h1, h2, rfl⟩ := (hmemR x).mp hcon
    exact hFP _ (hQint _ (PathBasics.getElem_mem_interior hQl hm h1 h2))
      (List.mem_of_mem_take hx)
  · -- the only edges between them are the two at the ends
    intro x hx y hy
    obtain ⟨k, hk, hkc, rfl⟩ := (hmemtake x).mp hx
    obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hmemR y).mp hy
    have hyF : (Q[m]'hm) ∈ F := hQint _ (PathBasics.getElem_mem_interior hQl hm hm1 hm2)
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · -- `x = p₁`, and `Q` is induced, so its only interior neighbour of `p₁` is `Q[1]`
      have hne : (P[0]'hPpos) ≠ (P[c]'hc) :=
        PathBasics.path_ne_of_ne_index hP hPpos hc (by omega)
      constructor
      · intro hadj
        refine Or.inr ⟨rfl, ?_⟩
        have : G.Adj (Q[0]'(by omega)) (Q[m]'hm) := by rw [hQ0]; exact hadj
        have hidx := (PathBasics.path_adj_iff hQl (by omega : 0 < Q.length) hm).mp this
        have hm1' : m = 1 := by omega
        subst hm1'
        rfl
      · rintro (⟨hcon, -⟩ | ⟨-, hy1⟩)
        · exact absurd hcon hne
        · have hmeq : m = 1 := by
            by_contra hcon
            exact PathBasics.path_ne_of_ne_index hQl hm (by omega) hcon hy1
          subst hmeq
          rw [← hQ0]
          exact (PathBasics.path_adj_iff hQl (by omega : 0 < Q.length) hm).mpr (Or.inl rfl)
    rcases Nat.lt_or_ge k c with hklt | hkge
    · -- `x` is strictly inside the stretch, so it has no neighbour in `F` at all
      constructor
      · intro hadj
        exact absurd hadj (hnoatt k hk hkpos hklt _ hyF)
      · rintro (⟨hcon, -⟩ | ⟨hcon, -⟩)
        · exact absurd hcon (PathBasics.path_ne_of_ne_index hP hk hc (by omega))
        · exact absurd hcon (PathBasics.path_ne_of_ne_index hP hk hPpos (by omega))
    · -- `x = p_c`, the other end of `Q`
      have hkc' : k = c := by omega
      subst hkc'
      have hne : (P[k]'hk) ≠ (P[0]'hPpos) :=
        PathBasics.path_ne_of_ne_index hP hk hPpos (by omega)
      constructor
      · intro hadj
        refine Or.inl ⟨rfl, ?_⟩
        have : G.Adj (Q[Q.length - 1]'(by omega)) (Q[m]'hm) := by
          rw [hQlast]
          exact hadj
        have hidx := (PathBasics.path_adj_iff hQl (by omega : Q.length - 1 < Q.length) hm).mp this
        have hmeq : m = Q.length - 2 := by omega
        subst hmeq
        rfl
      · rintro (⟨-, hy2⟩ | ⟨hcon, -⟩)
        · have hmeq : m = Q.length - 2 := by
            by_contra hcon
            exact PathBasics.path_ne_of_ne_index hQl hm (by omega) hcon hy2
          subst hmeq
          rw [← hQlast]
          exact (PathBasics.path_adj_iff hQl (by omega : Q.length - 1 < Q.length) hm).mpr
            (Or.inr (by omega))
        · exact absurd hcon hne
  · -- the hole has at least four vertices
    have h1 : (P.take (c + 1)).length = c + 1 := by
      rw [List.length_take]; omega
    have h2 : ((SPGT.interior Q).reverse).length = Q.length - 2 := by
      rw [List.length_reverse, PathBasics.interior_length]
    omega

/-- The vertex list of the hole, for transporting a `Y`-complete-edge count across it: the hole
consists of the stretch `p₁ … p_c` together with the interior of `Q`. -/
theorem mem_hole_iff {P : List V} {c : ℕ} {Q : List V} (x : V) :
    x ∈ (P.take (c + 1) ++ (SPGT.interior Q).reverse) ↔
      x ∈ P.take (c + 1) ∨ x ∈ SPGT.interior Q := by
  simp

end Workspace.ProofLemmas.Thm186HoleThroughF
