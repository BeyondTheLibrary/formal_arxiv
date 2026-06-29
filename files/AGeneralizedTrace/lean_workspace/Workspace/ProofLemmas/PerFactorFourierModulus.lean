import Mathlib
import Workspace.ProofLemmas.KwayFactorSummable
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.MGFCalibrationAtSqrtN

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Per-factor Fourier-modulus geometric core (paper Lemma 7, step G2)

This file isolates the *scalar / per-point* core of the G2 step of the paper's
Lemma 7 (arXiv:2412.00674v1, lines 320-334): the geometric-series expansion
`z / (1 - z) = ∑_{b ≥ 1} z^b` (valid because `z = α · bin(n, ½, ·) ≤ 1/2 < 1`),
applied pointwise to the per-factor function
`factor_j(r) = α · bin(n, ½, r + n_q + ℓ_j) / (1 - α · bin(n, ½, r + n_q + ℓ_j))`.

These lemmas are the analytic heart of G2 and feed the full Fourier-modulus
bound `|FT(factor_j)(η)| ≤ h(η)`; the remaining FT/circular-convolution assembly
(G3/G4) is past this front's budget and is *not* attempted here. Everything in
this file is proved sorry-free.
-/

namespace PerFactorFourierModulus

open KwayFactorSummable

/-! ### The scalar geometric identity `z/(1-z) = ∑_{b≥1} z^b`. -/

/-- Geometric series shifted to start at `b = 1`: for `0 ≤ z < 1`,
`∑' b : ℕ, z^(b+1) = z / (1 - z)`. This is the `z/(1-z) = ∑_{b≥1} z^b`
expansion the paper uses for each factor. -/
theorem geom_shift_eq (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    (∑' b : ℕ, z ^ (b + 1)) = z / (1 - z) := by
  have hfun : (fun b : ℕ => z ^ (b + 1)) = (fun b : ℕ => z * z ^ b) := by
    funext b; rw [pow_succ]; ring
  rw [hfun, tsum_mul_left, tsum_geometric_of_lt_one hz0 hz1]
  rw [div_eq_mul_inv]

/-- Summability of the shifted geometric series for `0 ≤ z < 1`. -/
theorem geom_shift_summable (z : ℝ) (hz1 : |z| < 1) :
    Summable (fun b : ℕ => z ^ (b + 1)) := by
  have h : Summable (fun b : ℕ => z ^ b) := summable_geometric_of_abs_lt_one hz1
  exact (h.mul_left z).congr (fun b => by rw [pow_succ]; ring)

/-! ### The per-point binomial atom and the `α · bin ≤ 1/2` bound. -/

/-- The (real) binomial atom at index `r`, for fixed `n`, shift `ℓj`:
`bin(n, ½, r + n_q + ℓj)` extended by zero off the support `[0, n]`,
where `n_q = (n-1)/4`. This is the `z` of the geometric expansion (before the
`α` factor). -/
noncomputable def binAtom (n : ℕ) (ℓj : ℕ) (r : ℤ) : ℝ :=
  let m : ℤ := r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
  if 0 ≤ m ∧ m ≤ (n : ℤ) then
    ((Nat.choose n m.toNat : ℝ) * (2 ^ n : ℝ)⁻¹)
  else 0

/-- The constant `α := (1 / (4 e² √(2π))) · √n` used throughout Lemma 7. -/
noncomputable def alphaC (n : ℕ) : ℝ :=
  (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)

theorem alphaC_nonneg (n : ℕ) : 0 ≤ alphaC n := by
  unfold alphaC
  apply mul_nonneg
  · apply div_nonneg one_pos.le
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Real.exp_pos _).le)
      (Real.sqrt_nonneg _)
  · exact Real.sqrt_nonneg _

/-- The binomial atom is non-negative. -/
theorem binAtom_nonneg (n : ℕ) (ℓj : ℕ) (r : ℤ) : 0 ≤ binAtom n ℓj r := by
  show 0 ≤ if 0 ≤ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
              ∧ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ) ≤ (n : ℤ)
           then ((Nat.choose n (r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0
  split_ifs with h
  · positivity
  · exact le_refl 0

/-- **Convergence condition (per-point).** For `n ≥ 1`, the scaled binomial atom
satisfies `α · binAtom ≤ 1/(4πe²) ≤ 1/2`. This is the `z ≤ 1/2 < 1` hypothesis
that makes the per-factor geometric series converge.

The bound comes from the binomial pmf maximum bound
`bin(n,½,·) ≤ √(2/(πn))` (`BinomialPmfMaxBound`) and the calibration identity
`α · √(8π/n) · e² = 1/2` (`MGFCalibrationAtSqrtN`), via
`√(2/(πn)) = √(8π/n) / (2π)`. -/
theorem alphaC_binAtom_le_half (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    alphaC n * binAtom n ℓj r ≤ 1 / 2 := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- α ≥ 0.
  have hα_nn : 0 ≤ alphaC n := alphaC_nonneg n
  -- binAtom ≤ √(2/(πn)).
  have hbin_le : binAtom n ℓj r ≤ Real.sqrt (2 / (Real.pi * (n : ℝ))) := by
    show (if 0 ≤ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
              ∧ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ) ≤ (n : ℤ)
           then ((Nat.choose n (r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)
           else 0) ≤ Real.sqrt (2 / (Real.pi * (n : ℝ)))
    split_ifs with h
    · exact BinomialPmfMaxBound n hn _
    · positivity
  -- α · √(2/(πn)) = 1/(4πe²).
  have h_relate : Real.sqrt (2 / (Real.pi * (n : ℝ)))
      = Real.sqrt (8 * Real.pi / (n : ℝ)) / (2 * Real.pi) := by
    rw [eq_div_iff (by positivity)]
    -- √(2/(πn)) · (2π) = √(2/(πn)) · √((2π)²) = √( (2/(πn))·(2π)² ) = √(8π/n)
    have h2π : (2 * Real.pi) = Real.sqrt ((2 * Real.pi) ^ 2) := by
      rw [Real.sqrt_sq (by positivity)]
    rw [h2π, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp; ring
  have h_calib := MGFCalibrationAtSqrtN n hn
  have hexp_pos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have hexp_ne : Real.exp 2 ≠ 0 := ne_of_gt hexp_pos
  -- α · √(8π/n) = 1/(2 e²).
  have h_ag : alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) = 1 / (2 * Real.exp 2) := by
    have h_pre : alphaC n * Real.sqrt (8 * Real.pi / (n : ℝ)) * Real.exp 2 = 1 / 2 := by
      unfold alphaC; linarith [h_calib]
    have h_div := congrArg (fun x => x / Real.exp 2) h_pre
    simp only at h_div
    rw [mul_div_assoc, div_self hexp_ne, mul_one] at h_div
    rw [h_div]; field_simp
  -- α · √(2/(πn)) = 1/(4π e²).
  have h_av : alphaC n * Real.sqrt (2 / (Real.pi * (n : ℝ)))
      = 1 / (4 * Real.pi * Real.exp 2) := by
    rw [h_relate, mul_div_assoc', h_ag]
    field_simp; ring
  -- 1/(4π e²) ≤ 1/2.
  have h_small : (1 / (4 * Real.pi * Real.exp 2) : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hpi_gt : (3 : ℝ) ≤ Real.pi := by
      have := Real.pi_gt_three; linarith
    have hexp_gt : (1 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    nlinarith [hpi_gt, hexp_gt]
  calc alphaC n * binAtom n ℓj r
      ≤ alphaC n * Real.sqrt (2 / (Real.pi * (n : ℝ))) :=
        mul_le_mul_of_nonneg_left hbin_le hα_nn
    _ = 1 / (4 * Real.pi * Real.exp 2) := h_av
    _ ≤ 1 / 2 := h_small

/-- The `KwayFactorSummable.factor` equals `z/(1-z)` with `z = α · binAtom`,
*everywhere* on `ℤ` (off the support both sides are `0/(1-0) = 0`). This rewrites
the factor into the standard geometric form. -/
theorem factor_eq_geom (n : ℕ) (ℓj : ℕ) (r : ℤ) :
    KwayFactorSummable.factor n ℓj r
      = (alphaC n * binAtom n ℓj r) / (1 - alphaC n * binAtom n ℓj r) := by
  show (if 0 ≤ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)
            ∧ r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ) ≤ (n : ℤ)
         then ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
                 * ((Nat.choose n (r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)).toNat : ℝ)
                      * (2 ^ n : ℝ)⁻¹))
              / (1 - (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
                       * ((Nat.choose n (r + ((n - 1) / 4 : ℤ) + (ℓj : ℤ)).toNat : ℝ)
                            * (2 ^ n : ℝ)⁻¹))
         else 0)
      = (alphaC n * binAtom n ℓj r) / (1 - alphaC n * binAtom n ℓj r)
  unfold alphaC binAtom
  simp only
  split_ifs with h
  · ring_nf
  · norm_num

/-! ### The per-point geometric expansion of the factor (G2 core). -/

/-- **Per-point geometric expansion (G2 core).** For `n ≥ 1`, each factor of the
k-way product unfolds as the geometric series in its scaled binomial atom:
`factor n ℓj r = ∑' b : ℕ, (α · binAtom n ℓj r)^(b+1)`.

This is exactly the paper's `z/(1-z) = ∑_{b≥1} z^b` expansion applied per factor
(arXiv:2412.00674v1, lines 320-334), valid because `z = α · bin ≤ 1/2 < 1`
(`alphaC_binAtom_le_half`). It is the analytic heart of the G2 step. -/
theorem factor_geom_expansion (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    KwayFactorSummable.factor n ℓj r
      = ∑' b : ℕ, (alphaC n * binAtom n ℓj r) ^ (b + 1) := by
  set z : ℝ := alphaC n * binAtom n ℓj r with hz_def
  have hz0 : 0 ≤ z := mul_nonneg (alphaC_nonneg n) (binAtom_nonneg n ℓj r)
  have hz_half : z ≤ 1 / 2 := alphaC_binAtom_le_half n hn ℓj r
  have hz1 : z < 1 := lt_of_le_of_lt hz_half (by norm_num)
  rw [factor_eq_geom n ℓj r, ← hz_def, geom_shift_eq z hz0 hz1]

/-- Summability (in `b`) of the per-factor geometric series, for `n ≥ 1`. The
geometric ratio `z = α · binAtom ≤ 1/2 < 1`, so the series converges absolutely. -/
theorem factor_geom_summable (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    Summable (fun b : ℕ => (alphaC n * binAtom n ℓj r) ^ (b + 1)) := by
  set z : ℝ := alphaC n * binAtom n ℓj r with hz_def
  have hz0 : 0 ≤ z := mul_nonneg (alphaC_nonneg n) (binAtom_nonneg n ℓj r)
  have hz_half : z ≤ 1 / 2 := alphaC_binAtom_le_half n hn ℓj r
  have hz1 : |z| < 1 := by rw [abs_of_nonneg hz0]; linarith
  exact geom_shift_summable z hz1

/-- **Per-term factorisation of the geometric expansion.** Each term of the
per-factor series splits as `α^(b+1) · binAtom^(b+1)`, exposing the powers of the
binomial atom whose Fourier transforms are the b-fold self-convolutions
`Hconv (b+1)` in the parent proof. -/
theorem factor_geom_expansion_split (n : ℕ) (hn : 1 ≤ n) (ℓj : ℕ) (r : ℤ) :
    KwayFactorSummable.factor n ℓj r
      = ∑' b : ℕ, alphaC n ^ (b + 1) * binAtom n ℓj r ^ (b + 1) := by
  rw [factor_geom_expansion n hn ℓj r]
  apply tsum_congr
  intro b
  rw [mul_pow]

end PerFactorFourierModulus
