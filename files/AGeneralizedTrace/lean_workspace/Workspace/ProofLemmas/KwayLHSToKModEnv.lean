import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.KModEnvBound
import Workspace.ProofLemmas.KwayFTAsKConv
import Workspace.ProofLemmas.PerFactorFTEnvelope
import Workspace.ProofLemmas.KwayFactorSummable

open scoped Real Complex

set_option maxHeartbeats 4000000

namespace KwayLHSToKModEnv

open KFoldConvolutionTheorem
open KModEnvBound
open KwayFTAsKConv
open PerFactorFTEnvelope
open KwayFactorSummable

/-- The Fourier transform of each abstract factor `fseq n k ℓ j` is continuous,
for every `j : ℕ`.  For `j < k` the factor has finite support (via
`factorC_support`); for `j ≥ k` it is identically `0`. -/
theorem FT_fseq_continuous (n k : ℕ) (ℓ : Fin k → ℕ) (j : ℕ) :
    Continuous (fun η : ℝ => FT (fseq n k ℓ j) η) := by
  by_cases hj : j < k
  · have hfun : fseq n k ℓ j
        = (fun r => ((KwayFactorSummable.factor n (ℓ ⟨j, hj⟩) r : ℝ) : ℂ)) := by
      funext r
      simp only [fseq, KwayFactorSummable.fcx, dif_pos hj]
    rw [hfun]
    exact FT_continuous_of_finite_support _
      (Finset.Icc (-(((n : ℤ) - 1) / 4 + ((ℓ ⟨j, hj⟩ : ℕ) : ℤ)))
                  ((n : ℤ) - (((n : ℤ) - 1) / 4 + ((ℓ ⟨j, hj⟩ : ℕ) : ℤ))))
      (PerFactorFTEnvelope.factorC_support n (ℓ ⟨j, hj⟩))
  · have hfun : fseq n k ℓ j = (fun _ : ℤ => (0 : ℂ)) := by
      funext r
      simp only [fseq, KwayFactorSummable.fcx, dif_neg hj]
    rw [hfun]
    exact FT_continuous_of_finite_support (fun _ => 0) ∅
      (by intro r hr; exact absurd rfl hr)

/-- The Fourier transform of each abstract factor `fseq n k ℓ j` is `2π`-periodic,
for every `j : ℕ` (true of every discrete Fourier transform). -/
theorem FT_fseq_periodic (n k : ℕ) (ℓ : Fin k → ℕ) (j : ℕ) (x : ℝ) :
    FT (fseq n k ℓ j) (x + 2 * Real.pi) = FT (fseq n k ℓ j) x :=
  FT_periodic (fseq n k ℓ j) x

/-- **The parent `T4` Fourier-sum modulus is bounded by the iterated modulus
envelope `kModEnv`.**  Combines `FT_T4_eq_kConv` (rewriting the LHS as a k-fold
circular convolution) with `kConv_modulus_le_kModEnv` (the iterated
modulus-triangle bound), whose continuity / periodicity hypotheses are discharged
by `FT_fseq_continuous` and `FT_fseq_periodic`. -/
theorem T4_modulus_le_kModEnv (n k : ℕ) (ℓ : Fin k → ℕ) (hk : 1 ≤ k) (ξ : ℝ) :
    ‖∑' r : ℤ, (((∏ j : Fin k, KwayFactorSummable.factor n (ℓ j) r : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
      ≤ kModEnv (fseq n k ℓ) k ξ := by
  rw [FT_T4_eq_kConv n k ℓ hk ξ]
  exact kConv_modulus_le_kModEnv (fseq n k ℓ)
    (fun j => FT_fseq_continuous n k ℓ j)
    (fun j x => FT_fseq_periodic n k ℓ j x)
    k hk ξ

end KwayLHSToKModEnv
