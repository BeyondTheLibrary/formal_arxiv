import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue

/-!
# Closing an antipath into an antihole

Two sentence-shapes recur throughout §§13–18 of Chudnovsky–Robertson–Seymour–Thomas whenever an
antipath with prescribed interior has to be shown even or odd:

* *"… the antipath joining `pₙ₋₂, pₙ₋₁` with interior in `X` is even since it can be completed
  to an antihole via `pₙ₋₁-p₁-pₙ₋₂`"* (18.3, published page 110) — a **single witness vertex**
  `z` that is `X`-complete and non-adjacent to both ends closes the antipath into an antihole
  with two more vertices, so Berge forces the antipath to be even;
* *"Since `Q ∪ Q'` is an antihole it follows that `Q'` is odd"* (18.3, same page) — **two
  antipaths with the same ends**, one with interior in `Y` and one with interior in `X`, close
  into an antihole because `X` is complete to `Y`, so their lengths sum to an even number.

Both are instances of `Workspace.ProofLemmas.PathGlue.glue_hole` applied to `Gᶜ`.  They are
stated here once, for `Berge G`, rather than being re-derived at each use.

Throughout, the two ends `u, v` of the antipath are **adjacent in `G`** — that is how every use
in the paper arises (they are consecutive vertices of a path of `G`) and it is what forces the
antipath to have at least three vertices, which `glue_hole` needs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.AntiholeCompletion

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-- An antipath whose two ends are **adjacent in `G`** has at least three vertices: it cannot be
a single vertex (the ends are distinct) and it cannot be a single edge of `Gᶜ` (the ends are
adjacent in `G`). -/
theorem three_le_length_of_antipath {G : SimpleGraph V} {Q : List V} {u v : V}
    (hQ : IsAntipathFrom G Q u v) (hadj : G.Adj u v) : 3 ≤ Q.length := by
  have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  by_contra hcon
  have h12 : Q.length = 1 ∨ Q.length = 2 := by omega
  rcases h12 with h | h
  · obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp h
    have hu : a = u := by simpa using hQ.2.1
    have hv : a = v := by simpa using hQ.2.2
    exact hadj.ne (hu.symm.trans hv)
  · obtain ⟨a, b, rfl⟩ := PathGlue.length_eq_two h
    have hu : a = u := by simpa using hQ.2.1
    have hv : b = v := by simpa using hQ.2.2
    have hadj' : Gᶜ.Adj a b := by
      simpa using PathBasics.path_adj_succ hQ.1 (i := 0) (by simp)
    subst hu; subst hv
    exact hadj'.2 hadj

/-- **"… can be completed to an antihole via `z`"**.

If `z` is `X`-complete and non-adjacent (in `G`) to both `u` and `v`, then `z` is `Gᶜ`-adjacent
to exactly the two ends of any antipath `Q` from `u` to `v` whose interior lies in `X`, so
`Q ++ [z]` is an antihole.  Since `G` is Berge that antihole has even length `pathLength Q + 2`,
i.e. `Q` is even. -/
theorem even_pathLength_of_witness {G : SimpleGraph V} (hBerge : Berge G) {X : Set V}
    {u v z : V} (hadjuv : G.Adj u v)
    (hzX : VertexComplete G z X) (hzu : ¬ G.Adj z u) (hzv : ¬ G.Adj z v)
    (hzneu : z ≠ u) (hznev : z ≠ v)
    {Q : List V} (hQ : IsAntipathFrom G Q u v)
    (hQint : ∀ w ∈ SPGT.interior Q, w ∈ X) :
    Even (pathLength Q) := by
  have hQ3 : 3 ≤ Q.length := three_le_length_of_antipath hQ hadjuv
  -- `z ∉ X`, since `z` is `X`-complete and `G` has no loops.
  have hznotX : z ∉ X := fun h => G.irrefl (hzX z h)
  -- `z` is not a vertex of `Q`: it is neither end, and the interior lies in `X`.
  have hznotQ : z ∉ Q := by
    intro hz
    exact hznotX (hQint z ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hz, hzneu, hznev⟩))
  have hRpath : IsPathFrom Gᶜ [z] z z := ⟨PathBasics.isPathList_singleton Gᶜ z, rfl, rfl⟩
  have hdisj : ∀ x ∈ Q, x ∉ [z] := by
    intro x hx hmem
    have hxz : x = z := by simpa using hmem
    exact hznotQ (hxz ▸ hx)
  have hcross : ∀ x ∈ Q, ∀ y ∈ [z], (Gᶜ.Adj x y ↔ (x = v ∧ y = z) ∨ (x = u ∧ y = z)) := by
    intro x hx y hy
    have hyz : y = z := by simpa using hy
    subst hyz
    constructor
    · intro hadjxz
      by_cases hxu : x = u
      · exact Or.inr ⟨hxu, rfl⟩
      by_cases hxv : x = v
      · exact Or.inl ⟨hxv, rfl⟩
      exact absurd (hzX x (hQint x
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩))).symm hadjxz.2
    · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
      · exact ⟨fun h => hznev h.symm, fun h => hzv h.symm⟩
      · exact ⟨fun h => hzneu h.symm, fun h => hzu h.symm⟩
  have hhole : IsHoleList Gᶜ (Q ++ [z]) :=
    PathGlue.glue_hole hQ hRpath hdisj hcross (by simp only [List.length_singleton]; omega)
  have heven := hBerge.2 _ hhole
  simp only [holeLength, List.length_append, List.length_singleton] at heven
  have hple := PathBasics.pathLength_eq Q
  rw [Nat.even_iff] at heven ⊢
  omega

/-- **"Since `Q ∪ Q'` is an antihole it follows that `Q'` is odd"**.

`Q` and `R` are antipaths with the same ends `u, v` (adjacent in `G`), the interior of `Q` in
`Y` and the interior of `R` in `X`, with `X` and `Y` disjoint and complete to each other.  Then
`Q ++ (R*)ᵣₑᵥ` is an antihole: the two interiors are `Gᶜ`-anticomplete because `X` is complete
to `Y` in `G`, and `u`, `v` see only the two ends of `R*`.  Berge therefore makes
`pathLength Q + pathLength R` even. -/
theorem even_add_pathLength_of_two_antipaths {G : SimpleGraph V} (hBerge : Berge G)
    {X Y : Set V} (hXY : Disjoint X Y) (hcompl : Complete G X Y)
    {u v : V} (hadjuv : G.Adj u v)
    (huX : u ∉ X) (hvX : v ∉ X) (huY : u ∉ Y) (hvY : v ∉ Y)
    {Q R : List V}
    (hQ : IsAntipathFrom G Q u v) (hQint : ∀ w ∈ SPGT.interior Q, w ∈ Y)
    (hR : IsAntipathFrom G R u v) (hRint : ∀ w ∈ SPGT.interior R, w ∈ X) :
    Even (pathLength Q + pathLength R) := by
  have hQ3 : 3 ≤ Q.length := three_le_length_of_antipath hQ hadjuv
  have hR3 : 3 ≤ R.length := three_le_length_of_antipath hR hadjuv
  have hRpos : 0 < R.length := by omega
  have hR1lt : 1 < R.length := by omega
  have hRm2 : R.length - 2 < R.length := by omega
  have hRm1 : R.length - 1 < R.length := by omega
  have hR0 : R[0]'hRpos = u := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRL : R[R.length - 1]'hRm1 = v := PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  -- The interior of `R`, reversed, is a path of `Gᶜ` from `R[len-2]` to `R[1]`.
  have hIpath : IsPathFrom Gᶜ (SPGT.interior R) (R[1]'hR1lt) (R[R.length - 2]'hRm2) :=
    PathGlue.isPathFrom_interior hR.1 hR3
  have hIrev : IsPathFrom Gᶜ (SPGT.interior R).reverse (R[R.length - 2]'hRm2) (R[1]'hR1lt) :=
    PathBasics.isPathFrom_reverse hIpath
  -- Membership in `R*` as an index range.
  have hIeq : SPGT.interior R = (R.drop 1).take ((R.length - 2) - 1 + 1) := by
    rw [PathBasics.interior_eq_drop_take]; congr 1; omega
  have hImem : ∀ y : V, y ∈ SPGT.interior R ↔
      ∃ (k : ℕ) (hk : k < R.length), 1 ≤ k ∧ k ≤ R.length - 2 ∧ (R[k]'hk) = y := by
    intro y
    rw [hIeq]
    exact PathBasics.mem_slice_iff R (by omega) hRm2
  -- `R*` lies in `X`, so it misses `Q` entirely.
  have hdisj : ∀ x ∈ Q, x ∉ (SPGT.interior R).reverse := by
    intro x hx hmem
    have hxX : x ∈ X := hRint x (List.mem_reverse.mp hmem)
    by_cases hxu : x = u
    · exact huX (hxu ▸ hxX)
    by_cases hxv : x = v
    · exact hvX (hxv ▸ hxX)
    exact (Set.disjoint_left.mp hXY hxX)
      (hQint x ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩))
  have hcross : ∀ x ∈ Q, ∀ y ∈ (SPGT.interior R).reverse,
      (Gᶜ.Adj x y ↔ (x = v ∧ y = R[R.length - 2]'hRm2) ∨ (x = u ∧ y = R[1]'hR1lt)) := by
    intro x hx y hy
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hImem y).mp (List.mem_reverse.mp hy)
    have hkX : (R[k]'hk) ∈ X := hRint _ ((hImem _).mpr ⟨k, hk, hk1, hk2, rfl⟩)
    have hinjR : ∀ (m : ℕ) (hm : m < R.length), ((R[k]'hk) = (R[m]'hm) ↔ k = m) := by
      intro m hm
      exact List.Nodup.getElem_inj_iff hRnd
    have huv : u ≠ v := hadjuv.ne
    -- `u` is `R[0]` and `v` is `R[R.length-1]`, so `Gᶜ`-adjacency to `R[k]` pins `k`.
    have hadju : Gᶜ.Adj u (R[k]'hk) ↔ k = 1 := by
      rw [← hR0, PathBasics.path_adj_iff hR.1 hRpos hk]; omega
    have hadjv : Gᶜ.Adj v (R[k]'hk) ↔ k = R.length - 2 := by
      rw [← hRL, PathBasics.path_adj_iff hR.1 hRm1 hk]; omega
    have hik1 : ((R[k]'hk) = (R[1]'hR1lt)) ↔ k = 1 := hinjR 1 hR1lt
    have hikm : ((R[k]'hk) = (R[R.length - 2]'hRm2)) ↔ k = R.length - 2 := hinjR _ hRm2
    by_cases hxu : x = u
    · rw [hxu, hadju, hikm, hik1]
      constructor
      · intro h
        exact Or.inr ⟨rfl, h⟩
      · rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact absurd h huv
        · exact h
    by_cases hxv : x = v
    · rw [hxv, hadjv, hikm, hik1]
      constructor
      · intro h
        exact Or.inl ⟨rfl, h⟩
      · rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact h
        · exact absurd h.symm huv
    · -- `x` is an interior vertex of `Q`, hence in `Y`, hence `G`-adjacent to `R[k] ∈ X`.
      have hxY : x ∈ Y := hQint x ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hx, hxu, hxv⟩)
      refine iff_of_false (fun hcon => hcon.2 (hcompl _ hkX x hxY).symm) ?_
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hxv h
      · exact hxu h
  have hlen : 4 ≤ Q.length + (SPGT.interior R).reverse.length := by
    rw [List.length_reverse, PathBasics.interior_length]
    omega
  have hhole : IsHoleList Gᶜ (Q ++ (SPGT.interior R).reverse) :=
    PathGlue.glue_hole hQ hIrev hdisj hcross hlen
  have heven := hBerge.2 _ hhole
  simp only [holeLength, List.length_append, List.length_reverse,
    PathBasics.interior_length] at heven
  have hpq := PathBasics.pathLength_eq Q
  have hpr := PathBasics.pathLength_eq R
  rw [Nat.even_iff] at heven ⊢
  omega

end Workspace.ProofLemmas.AntiholeCompletion
