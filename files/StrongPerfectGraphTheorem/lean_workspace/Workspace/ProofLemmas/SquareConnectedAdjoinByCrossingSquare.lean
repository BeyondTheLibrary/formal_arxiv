import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.HoleBasics

/-!
# Enlarging a square-connected pair by one vertex

The printed proof of 14.1 (p. 88) says

> *"… but then we can add `v` to `C` (because `v-d₂-d₁-c₂-v` becomes a new antisquare), contrary
> to the maximality of the cube."*

The parenthesis is the whole justification the authors give that `(C ∪ {v}, D)` is still
antisquare-connected; this module supplies the routine verification behind it.  Only two things
have to be checked beyond what `(C, D)` already gives: a partition of `C ∪ {v}` that isolates `v`
is crossed by the new square, and any other partition restricts to a partition of `C` that the old
square-connectedness already crosses.  The `D`-side condition is inherited verbatim.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

/-- A square of `(S, T)` is a square of `(S', T)` for any larger first side. -/
private theorem isSquare_mono {V : Type*} {G : SimpleGraph V} {S S' T : Set V}
    (hSS' : S ⊆ S') {a₁ b₁ b₂ a₂ : V} (h : IsSquare G S T a₁ b₁ b₂ a₂) :
    IsSquare G S' T a₁ b₁ b₂ a₂ :=
  ⟨h.1, hSS' h.2.1, hSS' h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- Reading a square backwards exchanges the roles of its two first-side vertices. -/
private theorem isSquare_rev {V : Type*} {G : SimpleGraph V} {S T : Set V}
    {a₁ b₁ b₂ a₂ : V} (h : IsSquare G S T a₁ b₁ b₂ a₂) : IsSquare G S T a₂ b₂ b₁ a₁ := by
  refine ⟨?_, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩
  have := HoleBasics.isHoleList_reverse h.1
  simpa using this

/-- Adjoining an outside first-side vertex along one crossing square preserves
square-connectedness. -/
theorem SquareConnectedAdjoinByCrossingSquare {V : Type*} {G : SimpleGraph V}
    {S T : Set V} {x : V} (hST : SquareConnected G S T) (hxS : x ∉ S)
    (hcross : ∃ s ∈ S, ∃ t₁ ∈ T, ∃ t₂ ∈ T,
      IsSquare G (S ∪ {x}) T x t₁ t₂ s) :
    SquareConnected G (S ∪ {x}) T := by
  obtain ⟨⟨hSnt, hTnt⟩, hS, hT⟩ := hST
  obtain ⟨s, hs, t₁, ht₁, t₂, ht₂, hsq⟩ := hcross
  have hSS' : S ⊆ S ∪ {x} := Set.subset_union_left
  have hxmem : x ∈ S ∪ {x} := Or.inr rfl
  refine ⟨⟨hSnt.mono hSS', hTnt⟩, ?_, ?_⟩
  · intro Y Z hYZ hd hY hZ
    have hxYZ : x ∈ Y ∪ Z := by rw [hYZ]; exact hxmem
    rcases hxYZ with hxY | hxZ
    · -- `x` lies in the first part
      have hZS : Z ⊆ S := by
        intro z hz
        have : z ∈ S ∪ {x} := by rw [← hYZ]; exact Or.inr hz
        rcases this with h | h
        · exact h
        · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hz)
            (Set.disjoint_left.mp hd hxY)
      by_cases hYS : (Y ∩ S).Nonempty
      · have hpart : (Y ∩ S) ∪ Z = S := by
          ext u
          constructor
          · rintro (⟨-, hu⟩ | hu)
            · exact hu
            · exact hZS hu
          · intro hu
            have : u ∈ Y ∪ Z := by rw [hYZ]; exact hSS' hu
            rcases this with h | h
            · exact Or.inl ⟨h, hu⟩
            · exact Or.inr h
        have hdis : Disjoint (Y ∩ S) Z :=
          Set.disjoint_of_subset_left Set.inter_subset_left hd
        obtain ⟨a₁, b₁, b₂, a₂, hsq', hm1, hm2⟩ := hS (Y ∩ S) Z hpart hdis hYS hZ
        exact ⟨a₁, b₁, b₂, a₂, isSquare_mono hSS' hsq', hm1.1, hm2⟩
      · -- `Y = {x}`, so `Z = S` and the new square crosses
        have hZeqS : S ⊆ Z := by
          intro u hu
          have : u ∈ Y ∪ Z := by rw [hYZ]; exact hSS' hu
          rcases this with h | h
          · exact absurd (⟨u, h, hu⟩ : (Y ∩ S).Nonempty) hYS
          · exact h
        exact ⟨x, t₁, t₂, s, hsq, hxY, hZeqS hs⟩
    · -- `x` lies in the second part
      have hYS : Y ⊆ S := by
        intro y hy
        have : y ∈ S ∪ {x} := by rw [← hYZ]; exact Or.inl hy
        rcases this with h | h
        · exact h
        · exact absurd hy ((Set.mem_singleton_iff.mp h) ▸
            (Set.disjoint_right.mp hd hxZ))
      by_cases hZS : (Z ∩ S).Nonempty
      · have hpart : Y ∪ (Z ∩ S) = S := by
          ext u
          constructor
          · rintro (hu | ⟨-, hu⟩)
            · exact hYS hu
            · exact hu
          · intro hu
            have : u ∈ Y ∪ Z := by rw [hYZ]; exact hSS' hu
            rcases this with h | h
            · exact Or.inl h
            · exact Or.inr ⟨h, hu⟩
        have hdis : Disjoint Y (Z ∩ S) :=
          Set.disjoint_of_subset_right Set.inter_subset_left hd
        obtain ⟨a₁, b₁, b₂, a₂, hsq', hm1, hm2⟩ := hS Y (Z ∩ S) hpart hdis hY hZS
        exact ⟨a₁, b₁, b₂, a₂, isSquare_mono hSS' hsq', hm1, hm2.1⟩
      · -- `Z = {x}`, so `Y = S` and the new square crosses, read backwards
        have hYeqS : S ⊆ Y := by
          intro u hu
          have : u ∈ Y ∪ Z := by rw [hYZ]; exact hSS' hu
          rcases this with h | h
          · exact h
          · exact absurd (⟨u, h, hu⟩ : (Z ∩ S).Nonempty) hZS
        exact ⟨s, t₂, t₁, x, isSquare_rev hsq, hYeqS hs, hxZ⟩
  · intro Y Z hYZ hd hY hZ
    obtain ⟨a₁, b₁, b₂, a₂, hsq', hm1, hm2⟩ := hT Y Z hYZ hd hY hZ
    exact ⟨a₁, b₁, b₂, a₂, isSquare_mono hSS' hsq', hm1, hm2⟩

end Workspace.ProofLemmas
