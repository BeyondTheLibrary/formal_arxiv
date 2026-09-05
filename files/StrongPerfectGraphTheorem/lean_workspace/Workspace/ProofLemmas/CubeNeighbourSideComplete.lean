import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.FiveHoleBasics

/-!
# 14.1, first half: a vertex whose neighbourhood lies on one side of the cube

PAPER (printed p. 87, the opening of the proof of 14.1):

> *"If `X ⊆ A ∪ B`, and there exists `a ∈ X ∩ A` and `b ∈ X ∩ B`, nonadjacent, then choose
> `c ∈ C` and `d ∈ D`, adjacent, and `v-a-c-d-b-v` is an odd hole.  So if `X ⊆ A ∪ B` then the
> theorem holds.  Similarly it holds if `X ⊆ C ∪ D`; and trivially it holds if `X` is a subset of
> one of `A ∪ C`, `B ∪ D`."*

This module is exactly that paragraph.  The `C ∪ D` case is the promised *"similarly"*: it uses
the five-hole `v-c-a-b-d-v`, with the adjacent pair `a ∈ A`, `b ∈ B` supplied by
square-connectedness of `(A,B)` where the `A ∪ B` case used the adjacent pair `c ∈ C`, `d ∈ D`
supplied by antisquare-connectedness of `(C,D)`.  The `A ∪ C` and `B ∪ D` cases are the
*"trivially"*: there `X ∩ (B ∪ D)` (resp. `X ∩ (A ∪ C)`) is empty.

Only `Berge G` is used, not the full strength of `G ∈ F₅`.

Nothing here corresponds to a numbered result of the paper; it is the first half of 14.1, split
off because 14.1's second half is obtained from it by complementation.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CubeNeighbourSideComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Edges supplied by (anti)square-connectedness -/

/-- A square-connected pair carries at least one edge between its two sides: the paper's
*"choose `a ∈ A` and `b ∈ B`, adjacent"*. -/
theorem exists_edge_of_squareConnected {A B : Set V} (h : SquareConnected G A B) :
    ∃ a ∈ A, ∃ b ∈ B, G.Adj a b := by
  obtain ⟨⟨⟨x, hx, y, hy, hxy⟩, -⟩, h1, -⟩ := h
  obtain ⟨a₁, b₁, b₂, a₂, hsq, -, -⟩ :=
    h1 {x} (A \ {x}) (by
        ext u
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
        constructor
        · rintro (rfl | ⟨hu, -⟩)
          · exact hx
          · exact hu
        · intro hu
          by_cases h : u = x
          · exact Or.inl h
          · exact Or.inr ⟨hu, h⟩)
      (by
        rw [Set.disjoint_left]
        rintro u rfl hu
        exact hu.2 rfl)
      ⟨x, rfl⟩ ⟨y, hy, hxy.symm⟩
  refine ⟨a₁, hsq.2.1, b₁, hsq.2.2.2.1, ?_⟩
  have := HoleBasics.hole_adj_succ hsq.1 (i := 0) (by simp)
  simpa using this

/-- An antisquare-connected pair carries at least one edge of `G` between its two sides: in the
antisquare `c₁-d₁-d₂-c₂-c₁` of `Gᶜ`, the pair `c₁ d₂` is a non-edge of `Gᶜ`, hence an edge of
`G`.  This is the paper's *"choose `c ∈ C` and `d ∈ D`, adjacent"*. -/
theorem exists_edge_of_antisquareConnected {C D : Set V} (h : AntisquareConnected G C D) :
    ∃ c ∈ C, ∃ d ∈ D, G.Adj c d := by
  obtain ⟨⟨⟨x, hx, y, hy, hxy⟩, -⟩, h1, -⟩ := h
  obtain ⟨c₁, d₁, d₂, c₂, hsq, -, -⟩ :=
    h1 {x} (C \ {x}) (by
        ext u
        simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_diff]
        constructor
        · rintro (rfl | ⟨hu, -⟩)
          · exact hx
          · exact hu
        · intro hu
          by_cases h : u = x
          · exact Or.inl h
          · exact Or.inr ⟨hu, h⟩)
      (by
        rw [Set.disjoint_left]
        rintro u rfl hu
        exact hu.2 rfl)
      ⟨x, rfl⟩ ⟨y, hy, hxy.symm⟩
  refine ⟨c₁, hsq.2.1, d₂, hsq.2.2.2.2, ?_⟩
  have hne : c₁ ≠ d₂ := by
    have := HoleBasics.hole_ne_of_ne_index hsq.1 (i := 0) (j := 2) (by simp) (by simp) (by omega)
    simpa using this
  have hnadj : ¬ Gᶜ.Adj c₁ d₂ := by
    have := HoleBasics.hole_not_adj_of_gap' hsq.1 (i := 0) (j := 2) (by simp) (by simp)
      (by simp) (by simp)
    simpa using this
  by_contra hcon
  exact hnadj ⟨hne, hcon⟩

/-! ### The statement -/

/-- **14.1, first half.**  If the neighbourhood `X` of `v` inside the cube lies inside one of
`A ∪ B`, `C ∪ D`, `A ∪ C`, `B ∪ D`, then `X ∩ (A ∪ C)` is complete to `X ∩ (B ∪ D)`. -/
theorem CubeNeighbourSideComplete (hB : Berge G) {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (hv : v ∉ A ∪ B ∪ C ∪ D) {X : Set V} (hX : X = G.neighborSet v ∩ (A ∪ B ∪ C ∪ D))
    (hsub : X ⊆ A ∪ B ∨ X ⊆ C ∪ D ∨ X ⊆ A ∪ C ∨ X ⊆ B ∪ D) :
    Complete G (X ∩ (A ∪ C)) (X ∩ (B ∪ D)) := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := hcube
  -- membership shorthands
  have memA : ∀ {u : V}, u ∈ A → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inl hu))
  have memB : ∀ {u : V}, u ∈ B → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inl (Or.inr hu))
  have memC : ∀ {u : V}, u ∈ C → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inl (Or.inr hu)
  have memD : ∀ {u : V}, u ∈ D → u ∈ A ∪ B ∪ C ∪ D := fun hu => Or.inr hu
  -- `v` is adjacent to every member of `X`, and to nothing of `V(K)` outside `X`
  have hadjX : ∀ {u : V}, u ∈ X → G.Adj v u := by
    intro u hu; rw [hX] at hu; exact hu.1
  have hnadjX : ∀ {u : V}, u ∈ A ∪ B ∪ C ∪ D → u ∉ X → ¬ G.Adj v u := by
    intro u hu hnu hadj; exact hnu (by rw [hX]; exact ⟨hadj, hu⟩)
  -- `v` differs from every vertex of `V(K)`
  have hvne : ∀ {u : V}, u ∈ A ∪ B ∪ C ∪ D → v ≠ u := by
    intro u hu he; exact hv (he ▸ hu)
  intro p hp q hq
  obtain ⟨hpX, hpAC⟩ := hp
  obtain ⟨hqX, hqBD⟩ := hq
  by_contra hpq
  rcases hsub with hs | hs | hs | hs
  · -- `X ⊆ A ∪ B`: the odd hole `v-a-c-d-b-v`
    have hpA : p ∈ A := by
      rcases hpAC with h | h
      · exact h
      · exact absurd h (fun hC => by
          rcases hs hpX with hA | hB
          · exact (Set.disjoint_left.mp dAC hA) hC
          · exact (Set.disjoint_left.mp dBC hB) hC)
    have hqB : q ∈ B := by
      rcases hqBD with h | h
      · exact h
      · exact absurd h (fun hD => by
          rcases hs hqX with hA | hB
          · exact (Set.disjoint_left.mp dAD hA) hD
          · exact (Set.disjoint_left.mp dBD hB) hD)
    obtain ⟨c, hc, d, hd, hcd⟩ := exists_edge_of_antisquareConnected sCD
    have hcX : c ∉ X := fun h => by
      rcases hs h with hA | hB
      · exact (Set.disjoint_left.mp dAC hA) hc
      · exact (Set.disjoint_left.mp dBC hB) hc
    have hdX : d ∉ X := fun h => by
      rcases hs h with hA | hB
      · exact (Set.disjoint_left.mp dAD hA) hd
      · exact (Set.disjoint_left.mp dBD hB) hd
    refine FiveHoleBasics.five_hole_absurd (x := v) (y := p) (z := c) (w := d) (t := q) hB
      (FiveHoleBasics.nodup_five (hvne (memA hpA)) (hvne (memC hc)) (hvne (memD hd))
        (hvne (memB hqB))
        (fun he => (Set.disjoint_left.mp dAC hpA) (he ▸ hc))
        (fun he => (Set.disjoint_left.mp dAD hpA) (he ▸ hd))
        (fun he => (Set.disjoint_left.mp dAB hpA) (he ▸ hqB))
        (fun he => (Set.disjoint_left.mp dCD hc) (he ▸ hd))
        (fun he => (Set.disjoint_left.mp dBC hqB) (he ▸ hc))
        (fun he => (Set.disjoint_left.mp dBD hqB) (he ▸ hd)))
      (hadjX hpX) (cAC p hpA c hc) hcd (cBD q hqB d hd).symm (hadjX hqX).symm
      (hnadjX (memC hc) hcX) (hnadjX (memD hd) hdX) (aAD p hpA d hd) hpq
      (fun hadj => aBC q hqB c hc hadj.symm)
  · -- `X ⊆ C ∪ D`: the odd hole `v-c-a-b-d-v`
    have hpC : p ∈ C := by
      rcases hpAC with h | h
      · exact absurd h (fun hA => by
          rcases hs hpX with hC | hD
          · exact (Set.disjoint_left.mp dAC hA) hC
          · exact (Set.disjoint_left.mp dAD hA) hD)
      · exact h
    have hqD : q ∈ D := by
      rcases hqBD with h | h
      · exact absurd h (fun hB => by
          rcases hs hqX with hC | hD
          · exact (Set.disjoint_left.mp dBC hB) hC
          · exact (Set.disjoint_left.mp dBD hB) hD)
      · exact h
    obtain ⟨a, ha, b, hb, hab⟩ := exists_edge_of_squareConnected sAB
    have haX : a ∉ X := fun h => by
      rcases hs h with hC | hD
      · exact (Set.disjoint_left.mp dAC ha) hC
      · exact (Set.disjoint_left.mp dAD ha) hD
    have hbX : b ∉ X := fun h => by
      rcases hs h with hC | hD
      · exact (Set.disjoint_left.mp dBC hb) hC
      · exact (Set.disjoint_left.mp dBD hb) hD
    refine FiveHoleBasics.five_hole_absurd (x := v) (y := p) (z := a) (w := b) (t := q) hB
      (FiveHoleBasics.nodup_five (hvne (memC hpC)) (hvne (memA ha)) (hvne (memB hb))
        (hvne (memD hqD))
        (fun he => (Set.disjoint_left.mp dAC ha) (he ▸ hpC))
        (fun he => (Set.disjoint_left.mp dBC hb) (he ▸ hpC))
        (fun he => (Set.disjoint_left.mp dCD hpC) (he ▸ hqD))
        (fun he => (Set.disjoint_left.mp dAB ha) (he ▸ hb))
        (fun he => (Set.disjoint_left.mp dAD ha) (he ▸ hqD))
        (fun he => (Set.disjoint_left.mp dBD hb) (he ▸ hqD)))
      (hadjX hpX) (cAC a ha p hpC).symm hab (cBD b hb q hqD) (hadjX hqX).symm
      (hnadjX (memA ha) haX) (hnadjX (memB hb) hbX)
      (fun hadj => aBC b hb p hpC hadj.symm) hpq (aAD a ha q hqD)
  · -- `X ⊆ A ∪ C`: `X ∩ (B ∪ D)` is empty
    rcases hs hqX with h | h
    · rcases hqBD with h' | h'
      · exact (Set.disjoint_left.mp dAB h) h'
      · exact (Set.disjoint_left.mp dAD h) h'
    · rcases hqBD with h' | h'
      · exact (Set.disjoint_left.mp dBC h' ) h
      · exact (Set.disjoint_left.mp dCD h) h'
  · -- `X ⊆ B ∪ D`: `X ∩ (A ∪ C)` is empty
    rcases hs hpX with h | h
    · rcases hpAC with h' | h'
      · exact (Set.disjoint_left.mp dAB h') h
      · exact (Set.disjoint_left.mp dBC h) h'
    · rcases hpAC with h' | h'
      · exact (Set.disjoint_left.mp dAD h') h
      · exact (Set.disjoint_left.mp dCD h') h

end Workspace.ProofLemmas.CubeNeighbourSideComplete
