import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.CubeComplement
import Workspace.ProofLemmas.CubeClaimTwo

/-!
# Claim (3) of the proof of 14.3

PAPER (printed p. 91):

> *"(3) There is no component of `F` such that its set of attachments in `K` is a subset of one of
> `A ∪ C`, `B ∪ D`.*
>
> *This follows from (2) by taking complements."*

The dictionary, which is the only non-obvious part.  Apply claim (2) to `Gᶜ` with the cube
`(D, C, A, B)` supplied by `CubeComplement.maximalCube_compl`.  Then

* `Y^{Gᶜ}` — the majors of the `Gᶜ`-cube — **is** `F`, the minors of the `G`-cube;
* an anticomponent of `F` in `Gᶜ` is a component of `F` in `G`, by `compl_compl`;
* *"complete in `Gᶜ` to `A' ∪ D' = D ∪ B`"* means *"anticomplete in `G` to `B ∪ D`"*, which —
  because attachments lie in `K` — is exactly *"attachments ⊆ `A ∪ C`"*.

The other disjunct `B' ∪ C' = C ∪ A` gives *"attachments ⊆ `B ∪ D`"*, and since `cube_claim_two`
is stated only for `A ∪ D` it is reached through the extra symmetry
`(A,B,C,D) ↦ (B,A,D,C)` of `IsCube` (`CubeComplement.isCube_swap`), lifted here to
`maximalCube_swap`, `minorForCube_swap` and `majorForCube_swap`.

`minorForCube_compl` is the mirror of `CubeComplement.majorForCube_compl`, and together they give
the two directions of `MinorForCube G A B C D v ↔ MajorForCube Gᶜ D C A B v` that the set equality
`F = {v | MajorForCube Gᶜ D C A B v}` needs.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.CubeClaimThree

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-! ### The `(A,B,C,D) ↦ (B,A,D,C)` symmetry -/

private theorem union4_comm (A B C D : Set V) : B ∪ A ∪ D ∪ C = A ∪ B ∪ C ∪ D := by
  ext x; simp only [Set.mem_union]; tauto

theorem minorForCube_swap {G : SimpleGraph V} {A B C D : Set V} {v : V}
    (h : MinorForCube G A B C D v) : MinorForCube G B A D C v := by
  have hKeq := union4_comm A B C D
  obtain ⟨hv, hsub, hcomp⟩ := h
  refine ⟨by rw [hKeq]; exact hv, ?_, ?_⟩
  · rw [hKeq]
    rcases hsub with h | h | h | h
    · exact Or.inl (fun x hx => (h hx).symm)
    · exact Or.inr (Or.inl (fun x hx => (h hx).symm))
    · exact Or.inr (Or.inr (Or.inr (fun x hx => h hx)))
    · exact Or.inr (Or.inr (Or.inl (fun x hx => h hx)))
  · rw [hKeq]
    exact CubeComplement.complete_symm hcomp

theorem majorForCube_swap {G : SimpleGraph V} {A B C D : Set V} {v : V}
    (h : MajorForCube G A B C D v) : MajorForCube G B A D C v := by
  have hKeq := union4_comm A B C D
  obtain ⟨hv, hsup, hanti⟩ := h
  refine ⟨by rw [hKeq]; exact hv, ?_, ?_⟩
  · rw [hKeq]
    rcases hsup with h | h | h | h
    · exact Or.inl (fun x hx => h hx.symm)
    · exact Or.inr (Or.inl (fun x hx => h hx.symm))
    · exact Or.inr (Or.inr (Or.inr (fun x hx => h hx)))
    · exact Or.inr (Or.inr (Or.inl (fun x hx => h hx)))
  · rw [hKeq]
    exact CubeComplement.anticomplete_symm hanti

theorem maximalCube_swap {G : SimpleGraph V} {A B C D : Set V} (h : MaximalCube G A B C D) :
    MaximalCube G B A D C := by
  refine ⟨CubeComplement.isCube_swap h.1, ?_⟩
  intro A' B' C' D' hcube' hB hA hD hC
  obtain ⟨e1, e2, e3, e4⟩ := h.2 B' A' D' C' (CubeComplement.isCube_swap hcube') hA hB hC hD
  exact ⟨e2, e1, e4, e3⟩

/-! ### A major vertex of `G` is a minor vertex of `Gᶜ` -/

theorem minorForCube_compl {G : SimpleGraph V} {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (h : MajorForCube G A B C D v) : MinorForCube Gᶜ D C A B v := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube
  obtain ⟨hv, hsup, hanti⟩ := h
  have hKeq : D ∪ C ∪ A ∪ B = A ∪ B ∪ C ∪ D := by ext u; simp only [Set.mem_union]; tauto
  have hv' : v ∉ D ∪ C ∪ A ∪ B := by rw [hKeq]; exact hv
  have hnb : ∀ u : V, u ∈ A ∪ B ∪ C ∪ D →
      (u ∈ Gᶜ.neighborSet v ∩ (D ∪ C ∪ A ∪ B) ↔ u ∉ G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) := by
    intro u hu
    rw [hKeq]
    constructor
    · rintro ⟨hadj, -⟩ ⟨hadj', -⟩
      exact hadj.2 hadj'
    · intro hcon
      exact ⟨⟨fun he => hv (by rw [he]; exact hu), fun hadj => hcon ⟨hadj, hu⟩⟩, hu⟩
  have hmemK : ∀ u : V, u ∈ Gᶜ.neighborSet v ∩ (D ∪ C ∪ A ∪ B) → u ∈ A ∪ B ∪ C ∪ D := by
    intro u hu
    rw [← hKeq]
    exact hu.2
  refine ⟨hv', ?_, ?_⟩
  · rcases hsup with hs | hs | hs | hs
    · -- `A ∪ B ⊆ X`, so `X' ⊆ D ∪ C`
      refine Or.inl (fun u hu => ?_)
      have huK := hmemK u hu
      have hux := (hnb u huK).mp hu
      rcases huK with ((hh | hh) | hh) | hh
      · exact absurd (hs (Or.inl hh)) hux
      · exact absurd (hs (Or.inr hh)) hux
      · exact Or.inr hh
      · exact Or.inl hh
    · -- `C ∪ D ⊆ X`, so `X' ⊆ A ∪ B`
      refine Or.inr (Or.inl (fun u hu => ?_))
      have huK := hmemK u hu
      have hux := (hnb u huK).mp hu
      rcases huK with ((hh | hh) | hh) | hh
      · exact Or.inl hh
      · exact Or.inr hh
      · exact absurd (hs (Or.inl hh)) hux
      · exact absurd (hs (Or.inr hh)) hux
    · -- `A ∪ D ⊆ X`, so `X' ⊆ C ∪ B`
      refine Or.inr (Or.inr (Or.inr (fun u hu => ?_)))
      have huK := hmemK u hu
      have hux := (hnb u huK).mp hu
      rcases huK with ((hh | hh) | hh) | hh
      · exact absurd (hs (Or.inl hh)) hux
      · exact Or.inr hh
      · exact Or.inl hh
      · exact absurd (hs (Or.inr hh)) hux
    · -- `B ∪ C ⊆ X`, so `X' ⊆ D ∪ A`
      refine Or.inr (Or.inr (Or.inl (fun u hu => ?_)))
      have huK := hmemK u hu
      have hux := (hnb u huK).mp hu
      rcases huK with ((hh | hh) | hh) | hh
      · exact Or.inr hh
      · exact absurd (hs (Or.inl hh)) hux
      · exact absurd (hs (Or.inr hh)) hux
      · exact Or.inl hh
  · -- the `Complete` clause is the `Anticomplete` clause of `MajorForCube`
    intro s hs t ht
    have hsK : s ∈ A ∪ B ∪ C ∪ D := hmemK s hs.1
    have htK : t ∈ A ∪ B ∪ C ∪ D := hmemK t ht.1
    have hsAD : s ∈ (A ∪ D) \ (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) := by
      refine ⟨?_, (hnb s hsK).mp hs.1⟩
      rcases hs.2 with hh | hh
      · exact Or.inr hh
      · exact Or.inl hh
    have htBC : t ∈ (B ∪ C) \ (G.neighborSet v ∩ (A ∪ B ∪ C ∪ D)) := by
      refine ⟨?_, (hnb t htK).mp ht.1⟩
      rcases ht.2 with hh | hh
      · exact Or.inr hh
      · exact Or.inl hh
    have hst : s ≠ t := by
      intro he
      rcases hsAD.1 with hh | hh
      · rcases htBC.1 with hh' | hh'
        · exact Set.disjoint_left.mp dAB hh (by rw [he]; exact hh')
        · exact Set.disjoint_left.mp dAC hh (by rw [he]; exact hh')
      · rcases htBC.1 with hh' | hh'
        · exact Set.disjoint_left.mp dBD hh' (by rw [← he]; exact hh)
        · exact Set.disjoint_left.mp dCD hh' (by rw [← he]; exact hh)
    exact ⟨hst, hanti s hsAD t htBC⟩

theorem minorForCube_of_compl {G : SimpleGraph V} {A B C D : Set V} (hcube : IsCube G A B C D)
    {v : V} (h : MajorForCube Gᶜ D C A B v) : MinorForCube G A B C D v := by
  have hcube' : IsCube Gᶜ D C A B := CubeComplement.isCube_compl hcube
  have h1 : MinorForCube Gᶜᶜ B A D C v := minorForCube_compl hcube' h
  rw [compl_compl] at h1
  exact minorForCube_swap h1

/-! ### Claim (3) -/

theorem cube_claim_three [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B C D F : Set V}
    (hG : InF5 G) (hno : ¬ AdmitsBalancedSkewPartition G)
    (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v}) (hFne : F.Nonempty)
    (F₁ : Set V) (hF₁ : IsComponent G F F₁)
    (hatt : (∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ A ∪ C) ∨
      (∀ w ∈ attachments G F₁ (A ∪ B ∪ C ∪ D), w ∈ B ∪ D)) :
    False := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube.1
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  -- `Gᶜ` inherits the hypotheses of 14.3
  have hGc : InF5 Gᶜ := ClassLemmas.inF5_compl.mpr hG
  have hnoc : ¬ AdmitsBalancedSkewPartition Gᶜ := fun hc =>
    hno (ClassLemmas.admitsBalancedSkewPartition_compl.mp hc)
  have hcubec : MaximalCube Gᶜ D C A B := CubeComplement.maximalCube_compl hcube
  -- `F` is the set of majors of the complementary cube
  have hYdef : F = {v : V | MajorForCube Gᶜ D C A B v} := by
    ext v
    constructor
    · intro hv
      exact CubeComplement.majorForCube_compl hcube.1 (hFmin v hv)
    · intro hv
      rw [hFdef]
      exact minorForCube_of_compl hcube.1 hv
  have hanti : IsAnticomponent Gᶜ F F₁ := by
    show IsComponent Gᶜᶜ F F₁
    rw [compl_compl]
    exact hF₁
  -- the two cases
  rcases hatt with hAC | hBD
  · -- attachments ⊆ `A ∪ C`, i.e. `F₁` is complete in `Gᶜ` to `D ∪ B = A' ∪ D'`
    refine CubeClaimTwo.cube_claim_two hGc hnoc hcubec hYdef hFne F₁ hanti ?_
    intro f hf u hu
    have hfF : f ∈ F := hF₁.1 hf
    have hfK : f ∉ A ∪ B ∪ C ∪ D := hFK f hfF
    have huK : u ∈ A ∪ B ∪ C ∪ D := by
      rcases hu with hh | hh
      · exact Or.inr hh
      · exact Or.inl (Or.inl (Or.inr hh))
    refine ⟨fun he => hfK (by rw [he]; exact huK), fun hadjG => ?_⟩
    have hatt' : u ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) := ⟨huK, f, hf, hadjG.symm⟩
    rcases hu with hh | hh
    · rcases hAC u hatt' with h' | h'
      · exact Set.disjoint_left.mp dAD h' hh
      · exact Set.disjoint_left.mp dCD h' hh
    · rcases hAC u hatt' with h' | h'
      · exact Set.disjoint_left.mp dAB h' hh
      · exact Set.disjoint_left.mp dBC.symm h' hh
  · -- attachments ⊆ `B ∪ D`; use the swapped complementary cube `(C, D, B, A)`
    have hcubec' : MaximalCube Gᶜ C D B A := maximalCube_swap hcubec
    have hYdef' : F = {v : V | MajorForCube Gᶜ C D B A v} := by
      rw [hYdef]
      ext v
      exact ⟨fun hv => majorForCube_swap hv, fun hv => majorForCube_swap hv⟩
    refine CubeClaimTwo.cube_claim_two hGc hnoc hcubec' hYdef' hFne F₁ hanti ?_
    intro f hf u hu
    have hfF : f ∈ F := hF₁.1 hf
    have hfK : f ∉ A ∪ B ∪ C ∪ D := hFK f hfF
    have huK : u ∈ A ∪ B ∪ C ∪ D := by
      rcases hu with hh | hh
      · exact Or.inl (Or.inr hh)
      · exact Or.inl (Or.inl (Or.inl hh))
    refine ⟨fun he => hfK (by rw [he]; exact huK), fun hadjG => ?_⟩
    have hatt' : u ∈ attachments G F₁ (A ∪ B ∪ C ∪ D) := ⟨huK, f, hf, hadjG.symm⟩
    rcases hu with hh | hh
    · rcases hBD u hatt' with h' | h'
      · exact Set.disjoint_left.mp dBC h' hh
      · exact Set.disjoint_left.mp dCD.symm h' hh
    · rcases hBD u hatt' with h' | h'
      · exact Set.disjoint_left.mp dAB.symm h' hh
      · exact Set.disjoint_left.mp dAD.symm h' hh

end Workspace.ProofLemmas.CubeClaimThree
