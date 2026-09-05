import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.HoleBasics

import Workspace.ProofLemmas.FiveHoleBasics
import Workspace.ProofLemmas.SquareConnectedAdjoinByCrossingSquare

/-!
# 14.1, the closing contradiction

PAPER (printed p. 88, the last paragraph of the proof of 14.1):

> *"Let `A₁ = A ∩ X`, and `A₂ = A \ A₁`; and define `B₁, B₂` etc. similarly.  We have shown so far
> that `A₁, B₂, D₁, D₂` are nonempty.  Choose an antisquare `c₂-d₁-d₂-c₁-c₂` such that `d₁ ∈ D₁`
> and `d₂ ∈ D₂`, and choose `b₂ ∈ B₂`.  Since `v-c₂-d₂-b₂-d₁-v` is not an odd hole, it follows
> that `c₂ ∈ C₂`.  Hence `A₁` is complete to `B₁`; for if `a₁ ∈ A₁` and `b₁ ∈ B₁` are nonadjacent
> then `v-a₁-c₂-d₂-b₁-v` is an odd hole.  If `A₁ = A`, then since `(A,B)` is square-connected and
> `A₁` is complete to `B₁` it follows that `B₁` is empty; but then we can add `v` to `C` (because
> `v-d₂-d₁-c₂-v` becomes a new antisquare), contrary to the maximality of the cube.  So `A₂` is
> nonempty.  Hence there is a square `a₁-b₁-b₂-a₂-a₁` with `a₁ ∈ A₁` and `a₂ ∈ A₂`.  Since `a₁` is
> nonadjacent to `b₂` and complete to `B₁`, it follows that `b₂ ∈ B₂`; but then
> `v-a₁-a₂-b₂-d₁-v` is an odd hole, a contradiction."*

The four hypotheses `A₁, B₂, D₁, D₂` nonempty are exactly the four hypotheses of the theorem
below; the earlier part of the printed proof (the `X ⊆ …` cases, the `… ⊆ X` cases obtained from
them by complementation, and the two symmetry reductions) is what supplies them.  Stating the
paragraph as a standalone "produce `False`" lemma is what lets 14.1 feed it all four of its
symmetric images.

Only `Berge G` is used, together with maximality of the cube (for the *"contrary to the
maximality"* step).

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CubeMajorCoreContradiction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Reading off a square -/

/-- The six adjacency facts and the six distinctness facts carried by a square
`a₁-b₁-b₂-a₂-a₁`. -/
theorem square_adj {S T : Set V} {a₁ b₁ b₂ a₂ : V} (h : IsSquare G S T a₁ b₁ b₂ a₂) :
    G.Adj a₁ b₁ ∧ G.Adj b₁ b₂ ∧ G.Adj b₂ a₂ ∧ G.Adj a₂ a₁ ∧
      ¬ G.Adj a₁ b₂ ∧ ¬ G.Adj b₁ a₂ ∧
      a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧ b₁ ≠ a₂ ∧ b₂ ≠ a₂ := by
  have hh := h.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using HoleBasics.hole_adj_succ hh (i := 0) (by simp)
  · simpa using HoleBasics.hole_adj_succ hh (i := 1) (by simp)
  · simpa using HoleBasics.hole_adj_succ hh (i := 2) (by simp)
  · simpa using HoleBasics.hole_adj_wrap hh
  · simpa using HoleBasics.hole_not_adj_of_gap' hh (i := 0) (j := 2) (by simp) (by simp)
      (by simp) (by simp)
  · simpa using HoleBasics.hole_not_adj_of_gap' hh (i := 1) (j := 3) (by simp) (by simp)
      (by simp) (by simp)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 0) (j := 1) (by simp) (by simp) (by omega)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 0) (j := 2) (by simp) (by simp) (by omega)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 0) (j := 3) (by simp) (by simp) (by omega)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 1) (j := 2) (by simp) (by simp) (by omega)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 1) (j := 3) (by simp) (by simp) (by omega)
  · simpa using HoleBasics.hole_ne_of_ne_index hh (i := 2) (j := 3) (by simp) (by simp) (by omega)

/-- A non-edge of `Gᶜ` between distinct vertices is an edge of `G`. -/
theorem adj_of_not_compl_adj {u w : V} (hne : u ≠ w) (h : ¬ Gᶜ.Adj u w) : G.Adj u w := by
  by_contra hcon
  exact h ⟨hne, hcon⟩

/-! ### The statement -/

/-- **14.1, closing paragraph.**  With `X` the neighbourhood of `v` inside the maximal cube, the
configuration `A ∩ X ≠ ∅`, `B ⊄ X`, `D ∩ X ≠ ∅`, `D ⊄ X` is impossible. -/
theorem CubeMajorCoreContradiction [Fintype V] [DecidableEq V] (hB : Berge G) {A B C D : Set V}
    (hcube : MaximalCube G A B C D) {v : V} (hv : v ∉ A ∪ B ∪ C ∪ D)
    {X : Set V} (hX : X = G.neighborSet v ∩ (A ∪ B ∪ C ∪ D))
    (hA1 : (A ∩ X).Nonempty) (hD1 : (D ∩ X).Nonempty)
    (hB2 : ¬ (B ⊆ X)) (hD2 : ¬ (D ⊆ X)) : False := by
  obtain ⟨hcubeG, hmax⟩ := hcube
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcubeG
  -- membership shorthands
  have memA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inl hu))
  have memB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inr hu))
  have memC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inr hu)
  have memD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inr hu
  have hadjX : ∀ {u : V}, u ∈ X → G.Adj v u := by
    intro u hu; rw [hX] at hu; exact hu.1
  have hnadjX : ∀ {u : V}, u ∈ A ∪ B ∪ C ∪ D → u ∉ X → ¬ G.Adj v u := by
    intro u hu hnu hadj; exact hnu (by rw [hX]; exact ⟨hadj, hu⟩)
  have hvne : ∀ {u : V}, u ∈ A ∪ B ∪ C ∪ D → v ≠ u := by
    intro u hu he; exact hv (he ▸ hu)
  -- `B₂` and `D₂` are nonempty
  obtain ⟨bout, hboutB, hboutX⟩ : ∃ u, u ∈ B ∧ u ∉ X := by
    by_contra hcon
    push_neg at hcon
    exact hB2 fun u hu => hcon u hu
  obtain ⟨dout, hdoutD, hdoutX⟩ : ∃ u, u ∈ D ∧ u ∉ X := by
    by_contra hcon
    push_neg at hcon
    exact hD2 fun u hu => hcon u hu
  -- the partition `(D₁, D₂)` of `D`
  have hDpart : (D ∩ X) ∪ (D \ X) = D := by
    ext u
    by_cases h : u ∈ X <;> simp [h]
  have hDdisj : Disjoint (D ∩ X) (D \ X) :=
    Set.disjoint_left.mpr fun u hu hu' => hu'.2 hu.2
  -- *"Choose an antisquare `c₂-d₁-d₂-c₁-c₂` such that `d₁ ∈ D₁` and `d₂ ∈ D₂`"*
  obtain ⟨c₂, d₁, d₂, c₁, hasq, hd₁, hd₂⟩ :=
    sCD.2.2 (D ∩ X) (D \ X) hDpart hDdisj hD1 ⟨dout, hdoutD, hdoutX⟩
  obtain ⟨e01, e12, e23, e30, n02, n13, ne01, ne02, ne03, ne12, ne13, ne23⟩ := square_adj hasq
  have hc₂C : c₂ ∈ C := hasq.2.1
  have hc₁C : c₁ ∈ C := hasq.2.2.1
  have hd₁D : d₁ ∈ D := hd₁.1
  have hd₁X : d₁ ∈ X := hd₁.2
  have hd₂D : d₂ ∈ D := hd₂.1
  have hd₂X : d₂ ∉ X := hd₂.2
  -- the two `G`-edges of the antisquare
  have gc₂d₂ : G.Adj c₂ d₂ := adj_of_not_compl_adj ne02 n02
  -- *"Since `v-c₂-d₂-b₂-d₁-v` is not an odd hole, it follows that `c₂ ∈ C₂`."*
  have hc₂X : c₂ ∉ X := by
    intro hc₂X
    exact FiveHoleBasics.five_hole_absurd (x := v) (y := c₂) (z := d₂) (w := bout) (t := d₁) hB
      (FiveHoleBasics.nodup_five (hvne (memC hc₂C)) (hvne (memD hd₂D)) (hvne (memB hboutB))
        (hvne (memD hd₁D))
        (fun he => (Set.disjoint_left.mp dCD hc₂C) (he ▸ hd₂D))
        (fun he => (Set.disjoint_left.mp dBC hboutB) (he ▸ hc₂C))
        (fun he => (Set.disjoint_left.mp dCD hc₂C) (he ▸ hd₁D))
        (fun he => (Set.disjoint_left.mp dBD hboutB) (he ▸ hd₂D))
        (fun he => ne12 he.symm)
        (fun he => (Set.disjoint_left.mp dBD hboutB) (he ▸ hd₁D)))
      (hadjX hc₂X) gc₂d₂ (cBD bout hboutB d₂ hd₂D).symm (cBD bout hboutB d₁ hd₁D)
      (hadjX hd₁X).symm
      (hnadjX (memD hd₂D) hd₂X) (hnadjX (memB hboutB) hboutX)
      (fun hadj => aBC bout hboutB c₂ hc₂C hadj.symm)
      (fun hadj => e01.2 hadj)
      (fun hadj => e12.2 hadj.symm)
  -- *"Hence `A₁` is complete to `B₁`"*
  have hA1B1 : ∀ a ∈ A ∩ X, ∀ b ∈ B ∩ X, G.Adj a b := by
    rintro a ⟨haA, haX⟩ b ⟨hbB, hbX⟩
    by_contra hab
    exact FiveHoleBasics.five_hole_absurd (x := v) (y := a) (z := c₂) (w := d₂) (t := b) hB
      (FiveHoleBasics.nodup_five (hvne (memA haA)) (hvne (memC hc₂C)) (hvne (memD hd₂D))
        (hvne (memB hbB))
        (fun he => (Set.disjoint_left.mp dAC haA) (he ▸ hc₂C))
        (fun he => (Set.disjoint_left.mp dAD haA) (he ▸ hd₂D))
        (fun he => (Set.disjoint_left.mp dAB haA) (he ▸ hbB))
        (fun he => (Set.disjoint_left.mp dCD hc₂C) (he ▸ hd₂D))
        (fun he => (Set.disjoint_left.mp dBC hbB) (he ▸ hc₂C))
        (fun he => (Set.disjoint_left.mp dBD hbB) (he ▸ hd₂D)))
      (hadjX haX) (cAC a haA c₂ hc₂C) gc₂d₂ (cBD b hbB d₂ hd₂D).symm (hadjX hbX).symm
      (hnadjX (memC hc₂C) hc₂X) (hnadjX (memD hd₂D) hd₂X) (aAD a haA d₂ hd₂D) hab
      (fun hadj => aBC b hbB c₂ hc₂C hadj.symm)
  -- *"So `A₂` is nonempty."*
  have hA2 : ¬ (A ⊆ X) := by
    intro hAX
    -- *"… it follows that `B₁` is empty"*
    have hB1empty : ∀ u, u ∈ B → u ∉ X := by
      intro u huB huX
      have hBpart : (B ∩ X) ∪ (B \ X) = B := by
        ext w
        by_cases h : w ∈ X <;> simp [h]
      have hBdisj : Disjoint (B ∩ X) (B \ X) :=
        Set.disjoint_left.mpr fun w hw hw' => hw'.2 hw.2
      obtain ⟨a₁, b₁, b₂, a₂, hsq, hb₁, hb₂⟩ :=
        sAB.2.2 (B ∩ X) (B \ X) hBpart hBdisj ⟨u, huB, huX⟩ ⟨bout, hboutB, hboutX⟩
      obtain ⟨-, -, -, -, -, m13, -⟩ := square_adj hsq
      exact m13 (hA1B1 a₂ ⟨hsq.2.2.1, hAX hsq.2.2.1⟩ b₁ ⟨hb₁.1, hb₁.2⟩).symm
    -- *"but then we can add `v` to `C`"*
    have hvC : v ∉ C := fun h => hv (memC h)
    have hnewcube : IsCube G A B (C ∪ {v}) D := by
      refine ⟨⟨⟨dAB, ?_, dAD, ?_, dBD, ?_⟩, nA, nB, ⟨c₂, Or.inl hc₂C⟩, nD⟩,
        ⟨?_, cBD, aAD, ?_⟩, sAB, ?_⟩
      · rw [Set.disjoint_right]
        rintro u (hu | hu)
        · exact Set.disjoint_right.mp dAC hu
        · rw [Set.mem_singleton_iff] at hu
          subst hu
          exact fun h => hv (memA h)
      · rw [Set.disjoint_right]
        rintro u (hu | hu)
        · exact Set.disjoint_right.mp dBC hu
        · rw [Set.mem_singleton_iff] at hu
          subst hu
          exact fun h => hv (memB h)
      · rw [Set.disjoint_left]
        rintro u (hu | hu)
        · exact Set.disjoint_left.mp dCD hu
        · rw [Set.mem_singleton_iff] at hu
          subst hu
          exact fun h => hv (memD h)
      · rintro a haA u (hu | hu)
        · exact cAC a haA u hu
        · rw [Set.mem_singleton_iff] at hu
          subst hu
          exact (hadjX (hAX haA)).symm
      · rintro b hbB u (hu | hu)
        · exact aBC b hbB u hu
        · rw [Set.mem_singleton_iff] at hu
          subst hu
          exact fun hadj => hnadjX (memB hbB) (hB1empty b hbB) hadj.symm
      · -- *"because `v-d₂-d₁-c₂-v` becomes a new antisquare"*
        refine SquareConnectedAdjoinByCrossingSquare (G := Gᶜ) sCD hvC
          ⟨c₂, hc₂C, d₂, hd₂D, d₁, hd₁D, ?_, Or.inr rfl, Or.inl hc₂C, hd₂D, hd₁D⟩
        refine FiveHoleBasics.isHoleList_four
          (FiveHoleBasics.nodup_four (hvne (memD hd₂D)) (hvne (memD hd₁D)) (hvne (memC hc₂C))
            ne12.symm ne02.symm ne01.symm)
          ⟨hvne (memD hd₂D), hnadjX (memD hd₂D) hd₂X⟩ e12.symm e01.symm
          ⟨fun he => hvne (memC hc₂C) he.symm, fun hadj => hnadjX (memC hc₂C) hc₂X hadj.symm⟩
          (fun hcadj => hcadj.2 (hadjX hd₁X)) (fun hcadj => hcadj.2 gc₂d₂.symm)
    obtain ⟨-, -, hCeq, -⟩ := hmax A B (C ∪ {v}) D hnewcube (le_refl A) (le_refl B)
      Set.subset_union_left (le_refl D)
    exact hvC (hCeq ▸ (Or.inr rfl : v ∈ C ∪ {v}))
  -- *"Hence there is a square `a₁-b₁-b₂-a₂-a₁` with `a₁ ∈ A₁` and `a₂ ∈ A₂`."*
  obtain ⟨aout, haoutA, haoutX⟩ : ∃ u, u ∈ A ∧ u ∉ X := by
    by_contra hcon
    push_neg at hcon
    exact hA2 fun u hu => hcon u hu
  have hApart : (A ∩ X) ∪ (A \ X) = A := by
    ext u
    by_cases h : u ∈ X <;> simp [h]
  have hAdisj : Disjoint (A ∩ X) (A \ X) :=
    Set.disjoint_left.mpr fun u hu hu' => hu'.2 hu.2
  obtain ⟨a₁, b₁, b₂, a₂, hsq, ha₁, ha₂⟩ :=
    sAB.2.1 (A ∩ X) (A \ X) hApart hAdisj hA1 ⟨aout, haoutA, haoutX⟩
  obtain ⟨f01, f12, f23, f30, m02, m13, p01, p02, p03, p12, p13, p23⟩ := square_adj hsq
  have ha₁A : a₁ ∈ A := ha₁.1
  have ha₁X : a₁ ∈ X := ha₁.2
  have ha₂A : a₂ ∈ A := ha₂.1
  have ha₂X : a₂ ∉ X := ha₂.2
  have hb₂B : b₂ ∈ B := hsq.2.2.2.2
  -- *"Since `a₁` is nonadjacent to `b₂` and complete to `B₁`, it follows that `b₂ ∈ B₂`"*
  have hb₂X : b₂ ∉ X := fun h => m02 (hA1B1 a₁ ⟨ha₁A, ha₁X⟩ b₂ ⟨hb₂B, h⟩)
  -- *"but then `v-a₁-a₂-b₂-d₁-v` is an odd hole, a contradiction."*
  exact FiveHoleBasics.five_hole_absurd (x := v) (y := a₁) (z := a₂) (w := b₂) (t := d₁) hB
    (FiveHoleBasics.nodup_five (hvne (memA ha₁A)) (hvne (memA ha₂A)) (hvne (memB hb₂B))
      (hvne (memD hd₁D)) p03 p02
      (fun he => (Set.disjoint_left.mp dAD ha₁A) (he ▸ hd₁D))
      (fun he => (Set.disjoint_left.mp dAB ha₂A) (he ▸ hb₂B))
      (fun he => (Set.disjoint_left.mp dAD ha₂A) (he ▸ hd₁D))
      (fun he => (Set.disjoint_left.mp dBD hb₂B) (he ▸ hd₁D)))
    (hadjX ha₁X) f30.symm f23.symm (cBD b₂ hb₂B d₁ hd₁D) (hadjX hd₁X).symm
    (hnadjX (memA ha₂A) ha₂X) (hnadjX (memB hb₂B) hb₂X) m02 (aAD a₁ ha₁A d₁ hd₁D)
    (aAD a₂ ha₂A d₁ hd₁D)

end Workspace.ProofLemmas.CubeMajorCoreContradiction
