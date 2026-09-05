import Workspace.ProofLemmas.PositiveIntegralFlowHasSimpleSourceSinkPath
import Workspace.ProofLemmas.PositiveValueUnitPathSubtractionPreservesFeasibleFlow

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.ProofLemmas.FiniteIntegralMaxFlowMinCutForLabelledArcs

theorem IntegralFlowDecomposesIntoSimpleSourceSinkPaths
    {V A : Type*}
    [Fintype V] [Fintype A] [DecidableEq A]
    (tail head : A → V) (cap f : A → ℕ) (s t : V) (k : ℕ)
    (hst : s ≠ t)
    (hflow : IsFeasibleIntegralFlow tail head cap f s t k)
    (hk : 2 ≤ k) :
    ∃ ρ₁ ρ₂ : List A,
      ρ₁ ≠ [] ∧
      ρ₂ ≠ [] ∧
      (∀ ρ ∈ [ρ₁, ρ₂],
        (∃ a, ρ.head? = some a ∧ tail a = s) ∧
        (∃ a, ρ.getLast? = some a ∧ head a = t) ∧
        (∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2) ∧
        (s :: ρ.map head).Nodup) ∧
      ∀ a, ρ₁.count a + ρ₂.count a ≤ f a := by
  classical
  have hkpos : 0 < k := by omega
  obtain ⟨ρ₁, hρ₁ne, hρ₁head, hρ₁last, hρ₁link, hρ₁nodup,
      _hρ₁positive, hρ₁load⟩ :=
    PositiveIntegralFlowHasSimpleSourceSinkPath
      tail head cap f s t k hst hflow hkpos
  let f₁ : A → ℕ := fun a => f a - ρ₁.count a
  have hflow₁ : IsFeasibleIntegralFlow tail head cap f₁ s t (k - 1) := by
    simpa [f₁] using
      PositiveValueUnitPathSubtractionPreservesFeasibleFlow
        tail head cap f s t k hst hkpos hflow ρ₁ hρ₁ne hρ₁head hρ₁last
          hρ₁link hρ₁nodup hρ₁load
  have hk₁pos : 0 < k - 1 := by omega
  obtain ⟨ρ₂, hρ₂ne, hρ₂head, hρ₂last, hρ₂link, hρ₂nodup,
      _hρ₂positive, hρ₂load⟩ :=
    PositiveIntegralFlowHasSimpleSourceSinkPath
      tail head cap f₁ s t (k - 1) hst hflow₁ hk₁pos
  refine ⟨ρ₁, ρ₂, hρ₁ne, hρ₂ne, ?_, ?_⟩
  · intro ρ hρ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
    rcases hρ with rfl | rfl
    · exact ⟨hρ₁head, hρ₁last, hρ₁link, hρ₁nodup⟩
    · exact ⟨hρ₂head, hρ₂last, hρ₂link, hρ₂nodup⟩
  · intro a
    have h₂ : ρ₂.count a ≤ f a - ρ₁.count a := by
      simpa [f₁] using hρ₂load a
    have hsum : ρ₂.count a + ρ₁.count a ≤ f a :=
      Nat.add_le_of_le_sub (hρ₁load a) h₂
    simpa [Nat.add_comm] using hsum

end Workspace.ProofLemmas
