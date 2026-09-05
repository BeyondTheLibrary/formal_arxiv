import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.HoleBasics

/-!
# Cubes under complementation

Steps (1) and (3) of the printed proof of 14.3 (p. 91) are discharged in one sentence each —
*"This is immediate from 14.2 by taking complements"* and *"This follows from (2) by taking
complements"* — and the final paragraph opens *"and by taking complements, `F` is nonempty"*.
Every one of those needs the complement of a cube to be a cube, and the complement of a *minor*
vertex to be a *major* one.  Neither is in the workspace; this module supplies both.

The transport is **not** the identity permutation.  Writing the cube conditions out,

* `A` is complete to `C` and `B` to `D`, while `A` is anticomplete to `D` and `B` to `C`,

the `Gᶜ`-complete pairs are `{A,D}` and `{B,C}` and the `Gᶜ`-anticomplete pairs are `{A,C}` and
`{B,D}`, so the quadruple that works is

```
(A, B, C, D)  in  G      ↦      (D, C, A, B)  in  Gᶜ
```

(`isCube_compl`).  Applied twice this is not the identity but the involution
`(A,B,C,D) ↦ (B,A,D,C)`, which is itself a symmetry of `IsCube` (`isCube_swap`); the two together
give `maximalCube_compl`.  Both rest on `squareConnected_symm`, i.e. that being square-connected
does not depend on the order of the pair — for which the square `a₁-b₁-b₂-a₂-a₁` has to be
re-read as `b₁-a₁-a₂-b₂-b₁`, the reverse of the original rotated by two.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CubeComplement

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Complete / anticomplete under complementation -/

theorem anticomplete_symm {S T : Set V} (h : Anticomplete G S T) : Anticomplete G T S :=
  fun t ht s hs hadj => h s hs t ht hadj.symm

theorem complete_symm {S T : Set V} (h : Complete G S T) : Complete G T S :=
  fun t ht s hs => (h s hs t ht).symm

theorem complete_compl_of_anticomplete {S T : Set V} (hdisj : Disjoint S T)
    (h : Anticomplete G S T) : Complete Gᶜ S T := by
  intro s hs t ht
  exact ⟨fun he => (Set.disjoint_left.mp hdisj hs) (by rw [he]; exact ht), h s hs t ht⟩

theorem anticomplete_compl_of_complete {S T : Set V} (h : Complete G S T) :
    Anticomplete Gᶜ S T := fun s hs t ht hadj => hadj.2 (h s hs t ht)

/-! ### Squares -/

theorem isSquare_swap {A B : Set V} {a₁ b₁ b₂ a₂ : V} (h : IsSquare G A B a₁ b₁ b₂ a₂) :
    IsSquare G B A b₁ a₁ a₂ b₂ := by
  obtain ⟨hhole, ha₁, ha₂, hb₁, hb₂⟩ := h
  refine ⟨?_, hb₁, hb₂, ha₁, ha₂⟩
  have h1 : IsHoleList G [a₂, b₂, b₁, a₁] := by
    have hr := HoleBasics.isHoleList_reverse hhole
    simpa using hr
  have h2 := HoleBasics.isHoleList_rotate h1 2
  simpa using h2

theorem squareConnected_symm {A B : Set V} (h : SquareConnected G A B) :
    SquareConnected G B A := by
  obtain ⟨⟨hA, hB⟩, h1, h2⟩ := h
  refine ⟨⟨hB, hA⟩, ?_, ?_⟩
  · intro X Y hXY hd hX hY
    obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, hm2⟩ := h2 X Y hXY hd hX hY
    exact ⟨b₁, a₁, a₂, b₂, isSquare_swap hsq, hm1, hm2⟩
  · intro X Y hXY hd hX hY
    obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, hm2⟩ := h1 X Y hXY hd hX hY
    exact ⟨b₁, a₁, a₂, b₂, isSquare_swap hsq, hm1, hm2⟩

theorem antisquareConnected_symm {A B : Set V} (h : AntisquareConnected G A B) :
    AntisquareConnected G B A := squareConnected_symm h

/-! ### Cubes -/

/-- `IsCube` is invariant under simultaneously swapping the two "square" sets and the two
"antisquare" sets. -/
theorem isCube_swap {A B C D : Set V} (h : IsCube G A B C D) : IsCube G B A D C := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := h
  exact ⟨⟨⟨dAB.symm, dBD, dBC, dAD, dAC, dCD.symm⟩, nB, nA, nD, nC⟩,
    ⟨cBD, cAC, aBC, aAD⟩,
    squareConnected_symm sAB, antisquareConnected_symm sCD⟩

/-- **The complement of a cube is a cube**, with the quadruple re-ordered as `(D, C, A, B)`. -/
theorem isCube_compl {A B C D : Set V} (h : IsCube G A B C D) : IsCube Gᶜ D C A B := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, nA, nB, nC, nD⟩,
    ⟨cAC, cBD, aAD, aBC⟩, sAB, sCD⟩ := h
  refine ⟨⟨⟨dCD.symm, dAD.symm, dBD.symm, dAC.symm, dBC.symm, dAB⟩, nD, nC, nA, nB⟩,
    ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact complete_compl_of_anticomplete dAD.symm (anticomplete_symm aAD)
  · exact complete_compl_of_anticomplete dBC.symm (anticomplete_symm aBC)
  · exact anticomplete_symm (anticomplete_compl_of_complete cBD)
  · exact anticomplete_symm (anticomplete_compl_of_complete cAC)
  · exact squareConnected_symm sCD
  · show SquareConnected Gᶜᶜ A B
    rw [compl_compl]
    exact sAB

/-- The inverse transport, obtained by composing `isCube_compl` in `Gᶜ` with `isCube_swap`. -/
theorem isCube_of_compl {A' B' C' D' : Set V} (h : IsCube Gᶜ A' B' C' D') :
    IsCube G C' D' B' A' := by
  have h1 : IsCube Gᶜᶜ D' C' A' B' := isCube_compl h
  rw [compl_compl] at h1
  exact isCube_swap h1

/-- **The complement of a maximal cube is a maximal cube.** -/
theorem maximalCube_compl {A B C D : Set V} (h : MaximalCube G A B C D) :
    MaximalCube Gᶜ D C A B := by
  refine ⟨isCube_compl h.1, ?_⟩
  intro A' B' C' D' hcube hDA' hCB' hAC' hBD'
  obtain ⟨e1, e2, e3, e4⟩ := h.2 C' D' B' A' (isCube_of_compl hcube) hAC' hBD' hCB' hDA'
  exact ⟨e4, e3, e1, e2⟩

/-! ### Minor and major vertices -/

section MinorMajor

variable {A B C D : Set V} {v : V}

private theorem mem_compl_nbr (hv : v ∉ A ∪ B ∪ C ∪ D) {u : V} (hu : u ∈ A ∪ B ∪ C ∪ D) :
    (u ∈ Gᶜ.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ↔ u ∉ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) := by
  constructor
  · rintro ⟨hadj, -⟩ ⟨hadj', -⟩
    exact hadj.2 hadj'
  · intro hcon
    refine ⟨⟨fun he => hv (by rw [he]; exact hu), fun hadj => hcon ⟨hadj, hu⟩⟩, hu⟩

/-- **A minor vertex of a cube is a major vertex of the complementary cube.** -/
theorem majorForCube_compl (hcube : IsCube G A B C D)
    (h : MinorForCube G A B C D v) : MajorForCube Gᶜ D C A B v := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube
  obtain ⟨hv, hsub, hcompl⟩ := h
  have hKeq : D ∪ C ∪ A ∪ B = A ∪ B ∪ C ∪ D := by
    ext u; simp only [Set.mem_union]; tauto
  have hv' : v ∉ D ∪ C ∪ A ∪ B := by rw [hKeq]; exact hv
  have hnb : ∀ u : V, u ∈ A ∪ B ∪ C ∪ D →
      (u ∈ Gᶜ.neighborSet v ∩ (D ∪ C ∪ A ∪ B) ↔ u ∉ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) := by
    intro u hu
    rw [hKeq]
    exact mem_compl_nbr hv hu
  refine ⟨hv', ?_, ?_⟩
  · -- the four "includes" clauses are the four "is included in" clauses of `MinorForCube`
    have key : ∀ S T : Set V, S ⊆ A ∪ B ∪ C ∪ D →
        (∀ u : V, u ∈ S → u ∉ T) →
        G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ⊆ T →
        S ⊆ Gᶜ.neighborSet v ∩ (D ∪ C ∪ A ∪ B) := by
      intro S T hSK hST hXT u hu
      exact (hnb u (hSK hu)).mpr (fun hx => hST u hu (hXT hx))
    rcases hsub with hs | hs | hs | hs
    · exact Or.inl (key (D ∪ C) (A ∪ B) (by intro u hu; rcases hu with h | h <;> simp [h])
        (by
          rintro u (hu | hu) (h | h)
          · exact (Set.disjoint_left.mp dAD.symm hu) h
          · exact (Set.disjoint_left.mp dBD.symm hu) h
          · exact (Set.disjoint_left.mp dAC.symm hu) h
          · exact (Set.disjoint_left.mp dBC.symm hu) h) hs)
    · exact Or.inr (Or.inl (key (A ∪ B) (C ∪ D) (by intro u hu; rcases hu with h | h <;> simp [h])
        (by
          rintro u (hu | hu) (h | h)
          · exact (Set.disjoint_left.mp dAC hu) h
          · exact (Set.disjoint_left.mp dAD hu) h
          · exact (Set.disjoint_left.mp dBC hu) h
          · exact (Set.disjoint_left.mp dBD hu) h) hs))
    · exact Or.inr (Or.inr (Or.inl
        (key (D ∪ B) (A ∪ C) (by intro u hu; rcases hu with h | h <;> simp [h])
        (by
          rintro u (hu | hu) (h | h)
          · exact (Set.disjoint_left.mp dAD.symm hu) h
          · exact (Set.disjoint_left.mp dCD.symm hu) h
          · exact (Set.disjoint_left.mp dAB.symm hu) h
          · exact (Set.disjoint_left.mp dBC hu) h) hs)))
    · exact Or.inr (Or.inr (Or.inr
        (key (C ∪ A) (B ∪ D) (by intro u hu; rcases hu with h | h <;> simp [h])
        (by
          rintro u (hu | hu) (h | h)
          · exact (Set.disjoint_left.mp dBC.symm hu) h
          · exact (Set.disjoint_left.mp dCD hu) h
          · exact (Set.disjoint_left.mp dAB hu) h
          · exact (Set.disjoint_left.mp dAD hu) h) hs)))
  · -- the anticomplete clause is the complete clause of `MinorForCube`
    intro s hs t ht hadj
    have hsK : s ∈ A ∪ B ∪ C ∪ D := by
      rcases hs.1 with h | h
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr h))
    have htK : t ∈ A ∪ B ∪ C ∪ D := by
      rcases ht.1 with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl (Or.inl h))
    have hsX : s ∈ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) := by
      by_contra hcon
      exact hs.2 ((hnb s hsK).mpr hcon)
    have htX : t ∈ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) := by
      by_contra hcon
      exact ht.2 ((hnb t htK).mpr hcon)
    have hsAC : s ∈ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D) := by
      refine ⟨hsX, ?_⟩
      rcases hs.1 with h | h
      · exact Or.inr h
      · exact Or.inl h
    have htBD : t ∈ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C) := by
      refine ⟨htX, ?_⟩
      rcases ht.1 with h | h
      · exact Or.inr h
      · exact Or.inl h
    exact hadj.2 (hcompl t htBD s hsAC).symm

end MinorMajor

end Workspace.ProofLemmas.CubeComplement
