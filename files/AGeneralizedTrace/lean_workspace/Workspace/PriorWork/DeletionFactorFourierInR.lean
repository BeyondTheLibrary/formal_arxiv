-- The Fourier transform IN r of the deletion factor
-- (Rivkin–Valiant–Valiant 2024, arXiv:2412.00674v1, §3, line 369).
--
-- The second/third binomial factors of `Fterm` are `Bin(n/4 ± r, 1-δ, z)`, whose
-- number-of-trials `n/4 ± r` VARIES with the summation index `r`. This file
-- computes the discrete Fourier transform IN r of `r ↦ binPMFInt (n/4+r) (1-δ) z`
-- in closed form and bounds its modulus.
--
-- The closed form is obtained by reindexing `m = n/4 + r - z` (excess deletions),
-- which turns the r-sum into the negative-binomial generating function already
-- proved in `DeletionBinomialFourier.deletionBinomial_closedForm`.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionBinomialFourier

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.DeletionFactorFourierInR

open Workspace.Types.AlternatingSumExpression
open Complex

/-- **Closed form of the deletion binomial pmf on its support.** For `z ≤ m` and
`0 ≤ 1-δ`, `binPMFInt m (1-δ) z = C(m, z) (1-δ)^z δ^{m-z}`. -/
theorem binPMFInt_deletion_on_support (m z : ℕ) (δ : ℝ) (hz : z ≤ m) :
    binPMFInt m (1 - δ) (z : ℤ)
      = (Nat.choose m z : ℝ) * (1 - δ) ^ z * δ ^ (m - z) := by
  unfold binPMFInt
  rw [if_pos ⟨by positivity, by exact_mod_cast hz⟩]
  unfold binPMF
  rw [if_pos (by simpa using hz)]
  rw [Int.toNat_natCast]
  congr 2
  norm_num

/-- `binPMFInt m (1-δ) z = 0` when `z > m`. -/
theorem binPMFInt_deletion_off_support (m z : ℕ) (δ : ℝ) (hz : m < z) :
    binPMFInt m (1 - δ) (z : ℤ) = 0 := by
  unfold binPMFInt
  rw [if_neg (by omega)]

/-- **The "true" deletion factor** `r ↦ Bin(n4 + r, 1-δ, z)` as a function of the
integer index `r`, with `n4 + r` trials. On its support (`n4 + r ≥ z`) it is the
honest binomial mass `C(n4+r, z) (1-δ)^z δ^{n4+r-z}`; elsewhere it is `0`. This is
the deletion factor of `Fterm` with the `n/4 ± r` number-of-trials, written without
the `.toNat`-clamping artifact (the two agree whenever `n4 + r ≥ 0`; see
`delFac_eq_binPMFInt`). -/
noncomputable def delFac (n4 : ℤ) (δ : ℝ) (z : ℕ) (r : ℤ) : ℝ :=
  if z ≤ n4 + r then
    (Nat.choose (n4 + r).toNat z : ℝ) * (1 - δ) ^ z * δ ^ ((n4 + r).toNat - z)
  else 0

/-- On the region `n4 + r ≥ 0`, the clean deletion factor agrees with the
`binPMFInt`-based factor appearing in `Fterm`. -/
theorem delFac_eq_binPMFInt (n4 : ℤ) (δ : ℝ) (z : ℕ) (r : ℤ) (hr : 0 ≤ n4 + r) :
    delFac n4 δ z r = binPMFInt (n4 + r).toNat (1 - δ) (z : ℤ) := by
  unfold delFac
  by_cases hz : z ≤ n4 + r
  · rw [if_pos hz]
    rw [binPMFInt_deletion_on_support (n4 + r).toNat z δ (by omega)]
  · rw [if_neg hz]
    rw [binPMFInt_deletion_off_support (n4 + r).toNat z δ (by omega)]

/-- The reindexing map `m ↦ z + m - n4` from excess-deletions `m : ℕ` to the
summation index `r : ℤ`. -/
private def reidx (n4 : ℤ) (z : ℕ) : ℕ → ℤ := fun m => (z : ℤ) + (m : ℤ) - n4

private theorem reidx_injective (n4 : ℤ) (z : ℕ) :
    Function.Injective (reidx n4 z) := by
  intro a b h
  unfold reidx at h
  omega

/-- **Fourier transform IN r of the deletion factor (closed form).** For
`0 ≤ δ < 1`, integer `n4` and `z : ℕ`,
`∑_{r ∈ ℤ} delFac(n4, δ, z, r) · e^{-iξr}
  = e^{iξ(n4 - z)} · (1-δ)^z / (1 - δ e^{-iξ})^{z+1}`.
Obtained by reindexing `m = n4 + r - z` and invoking the negative-binomial
generating function `DeletionBinomialFourier.deletionBinomial_closedForm`. -/
theorem delFac_fourier_closedForm
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (ξ : ℝ) (n4 : ℤ) (z : ℕ) :
    (∑' r : ℤ,
        ((delFac n4 δ z r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = Complex.exp (Complex.I * (ξ : ℂ) * ((n4 - z : ℤ) : ℂ))
          * ((1 - δ : ℂ) ^ z)
          / (1 - (δ : ℂ) * Complex.exp (-(Complex.I * (ξ : ℂ)))) ^ (z + 1) := by
  -- Reindex the ℤ-sum to a ℕ-sum via `reidx`.
  have hsupp : Function.support
      (fun r : ℤ => ((delFac n4 δ z r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      ⊆ Set.range (reidx n4 z) := by
    intro r hr
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hr
    obtain ⟨hdf, _⟩ := hr
    -- delFac nonzero ⇒ support: n4 + r ≥ z
    have hz : z ≤ n4 + r := by
      by_contra hzc
      apply hdf
      unfold delFac
      rw [if_neg hzc]
      norm_num
    refine ⟨(n4 + r).toNat - z, ?_⟩
    unfold reidx
    omega
  rw [← Function.Injective.tsum_eq (reidx_injective n4 z) hsupp]
  -- Compute the reindexed summand.
  have hterm : ∀ m : ℕ,
      ((delFac n4 δ z (reidx n4 z m) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * ((reidx n4 z m : ℤ) : ℂ)))
      = ((Nat.choose ((z : ℤ).toNat + m) (z : ℤ).toNat : ℂ)
            * ((1 - δ : ℂ) ^ (z : ℤ).toNat) * ((δ : ℂ) ^ m))
          * Complex.exp (Complex.I * ((-ξ : ℝ) : ℂ) *
              ((((z : ℤ) + m : ℤ) - n4 : ℤ) : ℂ)) := by
    intro m
    have hdf : delFac n4 δ z (reidx n4 z m)
        = (Nat.choose (z + m) z : ℝ) * (1 - δ) ^ z * δ ^ m := by
      unfold delFac reidx
      rw [if_pos (by omega)]
      have htn : (n4 + ((z : ℤ) + (m : ℤ) - n4)).toNat = z + m := by omega
      rw [htn]
      congr 2
      omega
    rw [hdf]
    push_cast [Int.toNat_natCast]
    rw [show (reidx n4 z m : ℤ) = ((z : ℤ) + m : ℤ) - n4 from by unfold reidx; ring]
    push_cast
    ring_nf
  rw [tsum_congr hterm]
  -- Apply the negative-binomial generating function with ξ ↦ -ξ, a ↦ n4.
  have hcf := deletionBinomial_closedForm δ hδ0 hδ1 (-ξ) n4 (z : ℤ)
  simp only [Int.toNat_natCast] at hcf ⊢
  rw [hcf]
  -- Reconcile the RHS phases / geometric factor under ξ ↦ -ξ.
  congr 1
  · congr 1
    push_cast
    congr 1
    ring
  · congr 2
    rw [show ((-ξ : ℝ) : ℂ) = -(ξ : ℂ) by push_cast; ring]
    rw [show Complex.I * -(ξ : ℂ) = -(Complex.I * (ξ : ℂ)) by ring]

/-- **The `r`-indexed deletion FT equals the `m`-indexed deletion FT (at `-ξ`).**
The Fourier sum IN r of `delFac` is, term-by-term after reindexing, the
`m`-indexed negative-binomial Fourier sum of `DeletionBinomialFourier` evaluated
at frequency `-ξ` and offset `a = n4`. -/
theorem delFac_fourier_eq_mSum
    (δ : ℝ) (ξ : ℝ) (n4 : ℤ) (z : ℕ) :
    (∑' r : ℤ,
        ((delFac n4 δ z r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = ∑' m : ℕ,
          ((Nat.choose ((z : ℤ).toNat + m) (z : ℤ).toNat : ℂ)
            * ((1 - δ : ℂ) ^ (z : ℤ).toNat) * ((δ : ℂ) ^ m))
            * Complex.exp (Complex.I * ((-ξ : ℝ) : ℂ) *
                ((((z : ℤ) + m : ℤ) - n4 : ℤ) : ℂ)) := by
  have hsupp : Function.support
      (fun r : ℤ => ((delFac n4 δ z r : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      ⊆ Set.range (reidx n4 z) := by
    intro r hr
    simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hr
    obtain ⟨hdf, _⟩ := hr
    have hz : z ≤ n4 + r := by
      by_contra hzc
      apply hdf
      unfold delFac
      rw [if_neg hzc]
      norm_num
    refine ⟨(n4 + r).toNat - z, ?_⟩
    unfold reidx
    omega
  rw [← Function.Injective.tsum_eq (reidx_injective n4 z) hsupp]
  apply tsum_congr
  intro m
  have hdf : delFac n4 δ z (reidx n4 z m)
      = (Nat.choose (z + m) z : ℝ) * (1 - δ) ^ z * δ ^ m := by
    unfold delFac reidx
    rw [if_pos (by omega)]
    have htn : (n4 + ((z : ℤ) + (m : ℤ) - n4)).toNat = z + m := by omega
    rw [htn]
    congr 2
    omega
  rw [hdf]
  push_cast [Int.toNat_natCast]
  rw [show (reidx n4 z m : ℤ) = ((z : ℤ) + m : ℤ) - n4 from by unfold reidx; ring]
  push_cast
  ring_nf

/-- **Modulus bound on the deletion-factor Fourier transform (off-axis decay).**
For `0 < δ ≤ 1/2` and `1/3 ≤ |ξ| ≤ π`, the magnitude of the Fourier transform IN r
of the deletion factor is bounded by `exp(-δ z / 20) / (1 - δ)`.

This is the modulus bound the 3-fold convolution at `ξ = π` consumes; it is obtained
from `delFac_fourier_eq_mSum` together with the already-proved
`DeletionBinomialFourier.deletionBinomial_FT_magnitude_bound` (applied at frequency
`-ξ`, whose absolute value equals `|ξ|`). -/
theorem delFac_fourier_magnitude_bound
    (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2) (ξ : ℝ)
    (hξπ : |ξ| ≤ Real.pi) (hξ : 1 / 3 ≤ |ξ|) (n4 : ℤ) (z : ℕ) :
    ‖(∑' r : ℤ,
        ((delFac n4 δ z r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))‖
      ≤ Real.exp (- δ * z / 20) / (1 - δ) := by
  rw [delFac_fourier_eq_mSum δ ξ n4 z]
  have hξπ' : |(-ξ)| ≤ Real.pi := by rwa [abs_neg]
  have hξ' : 1 / 3 ≤ |(-ξ)| := by rwa [abs_neg]
  exact deletionBinomial_FT_magnitude_bound δ hδ0 hδ (-ξ) hξπ' hξ' n4 z

/-- **On-axis value (ξ = 0): the deletion-factor Fourier transform equals
`(1-δ)^z / (1-δ)^{z+1} = 1/(1-δ)`.** This is the maximum modulus, attained at
`ξ = 0`; combined with `delFac_fourier_magnitude_bound` it gives the global bound
`|FT(ξ)| ≤ 1/(1-δ)` with off-axis decay to `exp(-δz/20)/(1-δ)`. -/
theorem delFac_fourier_at_zero
    (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (n4 : ℤ) (z : ℕ) :
    (∑' r : ℤ,
        ((delFac n4 δ z r : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * ((0 : ℝ) : ℂ) * (r : ℂ))))
      = ((1 - δ : ℂ)) ⁻¹ := by
  rw [delFac_fourier_closedForm δ hδ0 hδ1 0 n4 z]
  have h1δ : (1 - δ : ℂ) ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have : (δ : ℝ) = 1 := by exact_mod_cast h.symm
    linarith
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, neg_zero, Complex.exp_zero,
    one_mul, mul_one]
  rw [pow_succ]
  field_simp
