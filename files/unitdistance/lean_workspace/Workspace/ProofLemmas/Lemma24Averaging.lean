import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaAveragingExists
import Workspace.ProofLemmas.SublemmaArithmeticBound

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem Lemma24Averaging (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R) (γ : ℝ) (hγ : 0 < γ)
    (U : Finset (Fin f → ℂ))
    (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (hU_ne : ∀ u ∈ U, u ≠ 0)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1)
    (hU_card : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ)))
    (hρ : Real.log (rho R) > -γ / 2) :
    ∃ a : Fin f → ℂ, (Xset sel DD R a).Nonempty ∧
      (Ecount sel DD R U a : ℝ) ≥ Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ) := by
  obtain ⟨a, hne, hE⟩ :=
    SublemmaAveragingExists hcm sel DD hDD R hR U hU_lat hU_ne hU_coord
  have harith : (U.card : ℝ) * rho R ^ f ≥ Real.exp (γ * (f : ℝ) / 2) :=
    SublemmaArithmeticBound R hR γ hγ U hU_card hρ
  refine ⟨a, hne, ?_⟩
  -- Ncount ≥ 0
  have hN : (0 : ℝ) ≤ (Ncount sel DD R a : ℝ) := Nat.cast_nonneg _
  -- exp(γf/2) * Ncount ≤ (U.card * rho^f) * Ncount ≤ Ecount
  calc Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ)
      ≤ (U.card : ℝ) * rho R ^ f * (Ncount sel DD R a : ℝ) :=
        mul_le_mul_of_nonneg_right harith hN
    _ ≤ (Ecount sel DD R U a : ℝ) := hE

end MinkowskiLemmas
