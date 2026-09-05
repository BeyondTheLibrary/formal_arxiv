import Mathlib

set_option autoImplicit false

namespace Workspace.ProofLemmas

theorem Thm123Claim3RungEdgeCharacterization {V : Type*}
    (G : SimpleGraph V) (B C : Set V) (f R₂ : List V) (f₁ fk a₂ : V)
    (hf₁a₂ : G.Adj f₁ a₂)
    (hNoTailA₂ : ∀ u ∈ f, u ≠ f₁ → ¬ G.Adj u a₂)
    (hR₂BC : ∀ v ∈ R₂, v ≠ a₂ → v ∈ B ∪ C)
    (hattuniq : ∀ u ∈ f, (∃ y ∈ B ∪ C, G.Adj u y) → u = fk)
    (hfkNoR₂ : ∀ v ∈ R₂, ¬ G.Adj fk v) :
    ∀ u ∈ f, ∀ v ∈ R₂, (G.Adj u v ↔ (u = f₁ ∧ v = a₂)) := by
  intro u hu v hv
  constructor
  · intro huv
    by_cases hva₂ : v = a₂
    · subst v
      refine ⟨?_, rfl⟩
      by_contra huf₁
      exact hNoTailA₂ u hu huf₁ huv
    · have hvBC := hR₂BC v hv hva₂
      have hufk := hattuniq u hu ⟨v, hvBC, huv⟩
      subst u
      exact (hfkNoR₂ v hv huv).elim
  · rintro ⟨rfl, rfl⟩
    exact hf₁a₂

end Workspace.ProofLemmas
