import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ComponentsOfSetBasics

/-!
# The separation used in the proof of 10.5

After the cutset `Z` is fixed, the vertices of the prism outside `Z` split
into two anticomplete nonempty sets `S` and `T`.  If no component outside both
the prism and `Z` attaches to both, the components can be assigned to the two
sides of a separation.  This is the component form of the sentence following
claim (1) in the printed proof.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm105Separation

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V]

/-- Separate the two anticomplete parts of `K \ Z` by assigning every component
outside `K ∪ Z` that attaches to `S` to the `S` side. -/
theorem separate (G : SimpleGraph V) (K Z S T : Set V)
    (hKZ : K \ Z = S ∪ T) (hSZ : ∀ x ∈ S, x ∉ Z) (hTZ : ∀ x ∈ T, x ∉ Z)
    (hSTdisj : Disjoint S T) (hSTanti : Anticomplete G S T)
    (hno : ∀ C : Set V, IsComponent G (K ∪ Z)ᶜ C →
      (∃ s ∈ S, ∃ c ∈ C, G.Adj s c) →
      (∃ t ∈ T, ∃ c ∈ C, G.Adj t c) → False) :
    ∃ L M : Set V, L ∪ M = Zᶜ ∧ Disjoint L M ∧ Anticomplete G L M ∧
      S ⊆ L ∧ T ⊆ M := by
  classical
  let L : Set V := S ∪ {x : V | ∃ C : Set V, IsComponent G (K ∪ Z)ᶜ C ∧
    (∃ s ∈ S, ∃ c ∈ C, G.Adj s c) ∧ x ∈ C}
  let M : Set V := Zᶜ \ L
  have hSsubK : S ⊆ K := by
    intro x hx
    have hxST : x ∈ S ∪ T := Or.inl hx
    rw [← hKZ] at hxST
    exact hxST.1
  have hTsubK : T ⊆ K := by
    intro x hx
    have hxST : x ∈ S ∪ T := Or.inr hx
    rw [← hKZ] at hxST
    exact hxST.1
  have hLsubZc : L ⊆ Zᶜ := by
    rintro x (hxS | ⟨C, hC, -, hxC⟩)
    · exact hSZ x hxS
    · exact fun hxZ ↦ hC.1 hxC (Or.inr hxZ)
  have hTsubM : T ⊆ M := by
    intro t ht
    refine ⟨hTZ t ht, ?_⟩
    rintro (htS | ⟨C, hC, -, htC⟩)
    · exact Set.disjoint_left.mp hSTdisj htS ht
    · exact hC.1 htC (Or.inl (hTsubK ht))
  refine ⟨L, M, ?_, Set.disjoint_sdiff_right, ?_, Set.subset_union_left, hTsubM⟩
  · exact Set.union_diff_cancel' (le_refl L) hLsubZc
  · rintro x (hxS | ⟨C, hC, hCS, hxC⟩) y ⟨hyZ, hyL⟩ hxy
    · by_cases hyK : y ∈ K
      · have hyKZ : y ∈ K \ Z := ⟨hyK, hyZ⟩
        rw [hKZ] at hyKZ
        rcases hyKZ with hyS | hyT
        · exact hyL (Or.inl hyS)
        · exact hSTanti x hxS y hyT hxy
      · have hyO : y ∈ (K ∪ Z)ᶜ := by
          rintro (h | h)
          · exact hyK h
          · exact hyZ h
        obtain ⟨D, hD, hyD⟩ :=
          Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G (K ∪ Z)ᶜ hyO
        exact hyL (Or.inr ⟨D, hD, ⟨x, hxS, y, hyD, hxy⟩, hyD⟩)
    · by_cases hyK : y ∈ K
      · have hyKZ : y ∈ K \ Z := ⟨hyK, hyZ⟩
        rw [hKZ] at hyKZ
        rcases hyKZ with hyS | hyT
        · exact hyL (Or.inl hyS)
        · exact hno C hC hCS ⟨y, hyT, x, hxC, hxy.symm⟩
      · have hyO : y ∈ (K ∪ Z)ᶜ := by
          rintro (h | h)
          · exact hyK h
          · exact hyZ h
        obtain ⟨D, hD, hyD⟩ :=
          Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G (K ∪ Z)ᶜ hyO
        by_cases hCD : C = D
        · subst D
          exact hyL (Or.inr ⟨C, hC, hCS, hyD⟩)
        · exact Workspace.ProofLemmas.ComponentsOfSetBasics.anticomplete_of_isComponent
            G hC hD hCD x hxC y hyD hxy

end Workspace.ProofLemmas.Thm105Separation
