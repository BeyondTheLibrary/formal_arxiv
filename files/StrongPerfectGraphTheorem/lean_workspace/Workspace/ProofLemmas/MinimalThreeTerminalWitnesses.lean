import Workspace.Types.Core

set_option autoImplicit false

namespace Workspace.Types.MinimalThreeTerminalWitnesses

open Workspace.Types.Core.SPGT

theorem minimalThreeTerminalWitnesses
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V)
    (hmeet : ∀ i : Fin 3, ∃ f ∈ F, f ∈ N i)
    (hsep : ∀ w ∈ F, ∀ i j : Fin 3, i ≠ j → ¬ (w ∈ N i ∧ w ∈ N j))
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ f ∈ S, f ∈ N i) → F.ncard ≤ S.ncard) :
    ∃ v : Fin 3 → V,
      (∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i) ∧
      (∀ i j : Fin 3, i ≠ j → v i ≠ v j) ∧
      (∀ S : Set V, S ⊆ F → ConnectedSet G S →
        (∀ i : Fin 3, v i ∈ S) → S = F) := by
  classical
  choose v hvF hvN using hmeet
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    exact ⟨hvF i, hvN i⟩
  · intro i j hij hvij
    apply (hsep (v i) (hvF i) i j hij)
    refine ⟨hvN i, ?_⟩
    rw [hvij]
    exact hvN j
  · intro S hSF hconnected hvS
    apply Set.eq_of_subset_of_ncard_le hSF
    · apply hmin S hSF hconnected
      intro i
      exact ⟨v i, hvS i, hvN i⟩

end Workspace.Types.MinimalThreeTerminalWitnesses
