import Mathlib

set_option maxHeartbeats 800000

theorem SublemmaCompositumGalois {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, IsGalois ℚ ↥(L i)] [∀ i, FiniteDimensional ℚ ↥(L i)] :
    IsGalois ℚ ↥(⨆ i, L i) ∧
      Nat.card (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) = Module.finrank ℚ ↥(⨆ i, L i) := by
  haveI hn : ∀ i, Normal ℚ ↥(L i) := fun i => IsGalois.to_normal
  haveI hs : ∀ i, Algebra.IsSeparable ℚ ↥(L i) := fun i => IsGalois.to_isSeparable
  haveI hnsup : Normal ℚ ↥(⨆ i, L i) := IntermediateField.normal_iSup ℚ ℂ (t := L) (h := hn)
  haveI hssup : Algebra.IsSeparable ℚ ↥(⨆ i, L i) :=
    IntermediateField.isSeparable_iSup ℚ ℂ (t := L) (h := hs)
  haveI hgal : IsGalois ℚ ↥(⨆ i, L i) := ⟨⟩
  haveI hfd : FiniteDimensional ℚ ↥(⨆ i, L i) :=
    IntermediateField.finiteDimensional_iSup_of_finite (t := L)
  exact ⟨hgal, IsGalois.card_aut_eq_finrank ℚ ↥(⨆ i, L i)⟩
