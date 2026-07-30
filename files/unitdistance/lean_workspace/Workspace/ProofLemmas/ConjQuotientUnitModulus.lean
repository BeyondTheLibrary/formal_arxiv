import Mathlib
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.ConjIsComplexConjugationUnderEmbedding

open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 2000000

theorem ConjQuotientUnitModulus {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (σ : K →+* ℂ) (α : K) (hα : α ≠ 0) :
    ‖σ (α / conjAut h α)‖ = 1 := by
  -- `σ (conjAut h α) = conj (σ α)`.
  have hcc : σ (conjAut h α) = (starRingEnd ℂ) (σ α) :=
    ConjIsComplexConjugationUnderEmbedding h σ α
  have hσα : σ α ≠ 0 := by
    intro hh
    exact hα (σ.injective (by rw [hh, map_zero]))
  rw [map_div₀, hcc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hσα)]
