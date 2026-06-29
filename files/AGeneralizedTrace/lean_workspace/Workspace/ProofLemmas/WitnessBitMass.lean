import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.WitnessBitTail

/-!
# WitnessBitMass — witness per-coordinate value bound and prefix mass

The witness `Se` (resp. `So`) assigns to coordinate `i`

  `Se.p i = if i % 2 = 0 then C₀·√n·(C(n,i)·2^{-n}) else 0`,  `C₀ = 1/(4·e²·√(2π))`.

Since `C₀ ≤ 1` and `C(n,i)·2^{-n} = binPMF n (1/2) i`, we have the crude
`Se.p i ≤ √n · binPMF n (1/2) i`.  Summed over the prefix range `i < 3n/8`,
the binomial tail `WitnessBitTail.binPMF_prefix_tail` gives

  `∑_{i < 3n/8} Se.p i ≤ √n · exp(-n/256)`.

All lemmas sorry-free.
-/

open Workspace.Types.ProbVec
open Workspace.Types.AlternatingSumExpression

namespace WitnessBitMass

/-- The witness constant `C₀ = 1/(4·e²·√(2π))` is `≤ 1`. -/
theorem witness_const_le_one :
    (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) ≤ (1 : ℝ) := by
  rw [div_le_one (by positivity)]
  have he2 : (1 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hsqrt : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1:ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  nlinarith [he2, hsqrt, Real.exp_pos (2:ℝ)]

/-- Crude pointwise bound for the witness value (each `i`):
`witnessVal i ≤ √n · binPMF n (1/2) i`, where `witnessVal i` is the explicit
witness formula at coordinate `i`. -/
theorem witness_val_le (n : ℕ) (i : ℕ) (hi : i ≤ n) :
    (if i % 2 = 0
     then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
          Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
     else 0)
      ≤ Real.sqrt n * binPMF n (1 / 2 : ℝ) i := by
  have hbin : binPMF n (1 / 2 : ℝ) i = (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹ := by
    rw [CentralBinomialLowerTailWideProof.binPMF_half_eq n i hi]
    have : (1 / 2 : ℝ) ^ n = (2 ^ n : ℝ)⁻¹ := by
      rw [one_div, inv_pow]
    rw [this]
  rw [hbin]
  have hbin_nn : (0 : ℝ) ≤ (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹ := by positivity
  have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt n := Real.sqrt_nonneg _
  by_cases h : i % 2 = 0
  · rw [if_pos h]
    have hc := witness_const_le_one
    calc (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
            * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
        ≤ 1 * Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) := by
          apply mul_le_mul_of_nonneg_right _ hbin_nn
          apply mul_le_mul_of_nonneg_right hc hsqrt_nn
      _ = Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) := by ring
  · rw [if_neg h]
    positivity

/-- Prefix bit-mass: the witness `S.p`-mass summed over coordinates `i < 3n/8`
is `≤ √n · exp(-n/256)`. -/
theorem witness_prefix_mass (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) :
    (∑ i ∈ Finset.range (3 * n / 8),
      (if i % 2 = 0
       then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
            Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
       else 0))
      ≤ Real.sqrt n * Real.exp (-((n : ℝ) / 256)) := by
  have hstep :
      (∑ i ∈ Finset.range (3 * n / 8),
        (if i % 2 = 0
         then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
              Real.sqrt n * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
         else 0))
        ≤ ∑ i ∈ Finset.range (3 * n / 8), Real.sqrt n * binPMF n (1 / 2 : ℝ) i := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    apply witness_val_le n i
    omega
  refine le_trans hstep ?_
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left (WitnessBitTail.binPMF_prefix_tail n hn)
    (Real.sqrt_nonneg _)

end WitnessBitMass
