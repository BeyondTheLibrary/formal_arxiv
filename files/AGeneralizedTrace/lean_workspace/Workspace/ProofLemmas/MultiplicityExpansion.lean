import Mathlib
import Workspace.ProofLemmas.KwayEnvelopeProperties
import Workspace.ProofLemmas.LinMultiplicityExpansion
import Workspace.ProofLemmas.GlinWeightedMGF
import Workspace.ProofLemmas.GenvConvergence
import Workspace.PriorWork.PrekopaLogConcave

open scoped Real
open MeasureTheory
open GlinWeightedMGF GenvConvergence
open PeriodicBaseKfoldPeriodisation
open LinMultiplicityExpansion
open CircMultiplicityExpansion
open PerFactorFourierModulus
open Workspace.ProofLemmas.KwayEnvelopeProperties

set_option maxHeartbeats 4000000

namespace MultiplicityExpansion

/-- The pointwise log-concavity of `g(ξ) := cos(ξ/2)` on `[-π,π]`, in the
multiplicative (geometric-mean) form. -/
theorem cosHalf_logConcave
    (x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hx : |x| ≤ Real.pi) (hy : |y| ≤ Real.pi) :
    Real.cos (x / 2) ^ t * Real.cos (y / 2) ^ (1 - t)
      ≤ Real.cos ((t * x + (1 - t) * y) / 2) := by
  have hcos_nn : ∀ z : ℝ, |z| ≤ Real.pi → 0 ≤ Real.cos (z / 2) := by
    intro z hz
    have habs2 : |z / 2| ≤ Real.pi / 2 := by
      rw [abs_div]; simp; linarith [hz]
    rw [abs_le] at habs2
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [habs2.1]) habs2.2
  have hcx : 0 ≤ Real.cos (x / 2) := hcos_nn x hx
  have hcy : 0 ≤ Real.cos (y / 2) := hcos_nn y hy
  have hamgm :
      Real.cos (x / 2) ^ t * Real.cos (y / 2) ^ (1 - t)
        ≤ t * Real.cos (x / 2) + (1 - t) * Real.cos (y / 2) :=
    Real.geom_mean_le_arith_mean2_weighted ht0 (by linarith) hcx hcy (by ring)
  have hconc := (strictConcaveOn_cos_Icc).concaveOn
  have hmx : (x / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hx; constructor <;> [linarith [hx.1]; linarith [hx.2]]
  have hmy : (y / 2) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    rw [abs_le] at hy; constructor <;> [linarith [hy.1]; linarith [hy.2]]
  have hcc :=
    hconc.2 hmx hmy ht0 (by linarith : (0:ℝ) ≤ 1 - t) (by ring : t + (1 - t) = 1)
  have hcomb : t • (x / 2) + (1 - t) • (y / 2) = (t * x + (1 - t) * y) / 2 := by
    simp only [smul_eq_mul]; ring
  have hcc' :
      t * Real.cos (x / 2) + (1 - t) * Real.cos (y / 2)
        ≤ Real.cos ((t * x + (1 - t) * y) / 2) := by
    rw [hcomb] at hcc
    simpa only [smul_eq_mul] using hcc
  exact le_trans hamgm hcc'

/-- `Bbase0 n` is multiplicatively log-concave on all of ℝ, for `n ≥ 1`. -/
theorem Bbase0_logConcave (n : ℕ) (hn : 1 ≤ n)
    (x y t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Bbase0 n x ^ t * Bbase0 n y ^ (1 - t)
      ≤ Bbase0 n (t * x + (1 - t) * y) := by
  rcases eq_or_lt_of_le ht0 with ht0' | ht0'
  · subst ht0'
    simp only [Real.rpow_zero, one_mul, sub_zero, Real.rpow_one, zero_mul, zero_add, one_mul]
    exact le_refl _
  rcases eq_or_lt_of_le ht1 with ht1' | ht1'
  · subst ht1'
    simp only [Real.rpow_one, sub_self, Real.rpow_zero, mul_one, one_mul, sub_self, zero_mul,
      add_zero]
    exact le_refl _
  set m := t * x + (1 - t) * y with hm
  by_cases hx : |x| ≤ Real.pi
  · by_cases hy : |y| ≤ Real.pi
    · have hm_range : |m| ≤ Real.pi := by
        rw [abs_le] at hx hy ⊢
        rw [hm]
        constructor
        · nlinarith [hx.1, hy.1, ht0, (by linarith : (0:ℝ) ≤ 1 - t)]
        · nlinarith [hx.2, hy.2, ht0, (by linarith : (0:ℝ) ≤ 1 - t)]
      have hBx : Bbase0 n x = Real.cos (x / 2) ^ n := by
        unfold Bbase0; rw [if_pos hx, Bbase_eq_cos_pow n hn x hx]
      have hBy : Bbase0 n y = Real.cos (y / 2) ^ n := by
        unfold Bbase0; rw [if_pos hy, Bbase_eq_cos_pow n hn y hy]
      have hBm : Bbase0 n m = Real.cos (m / 2) ^ n := by
        unfold Bbase0; rw [if_pos hm_range, Bbase_eq_cos_pow n hn m hm_range]
      rw [hBx, hBy, hBm]
      have hcos_nn : ∀ z : ℝ, |z| ≤ Real.pi → 0 ≤ Real.cos (z / 2) := by
        intro z hz
        have habs2 : |z / 2| ≤ Real.pi / 2 := by
          rw [abs_div]; simp; linarith [hz]
        rw [abs_le] at habs2
        exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [habs2.1]) habs2.2
      have hcx : 0 ≤ Real.cos (x / 2) := hcos_nn x hx
      have hcy : 0 ≤ Real.cos (y / 2) := hcos_nn y hy
      have hcm : 0 ≤ Real.cos (m / 2) := hcos_nn m hm_range
      have hbase := cosHalf_logConcave x y t ht0 ht1 hx hy
      rw [← hm] at hbase
      rw [← Real.rpow_natCast (Real.cos (x / 2)) n, ← Real.rpow_natCast (Real.cos (y / 2)) n,
        ← Real.rpow_natCast (Real.cos (m / 2)) n,
        ← Real.rpow_mul hcx, ← Real.rpow_mul hcy]
      rw [mul_comm (n : ℝ) t, mul_comm (n : ℝ) (1 - t),
        Real.rpow_mul hcx t, Real.rpow_mul hcy (1 - t),
        ← Real.mul_rpow (Real.rpow_nonneg hcx t) (Real.rpow_nonneg hcy (1 - t))]
      apply Real.rpow_le_rpow (by positivity) hbase (by positivity)
    · have hBy0 : Bbase0 n y = 0 := Bbase0_supp n y (not_le.mp hy)
      rw [hBy0, Real.zero_rpow (by linarith : (1 - t) ≠ 0), mul_zero]
      exact Bbase0_nonneg n m
  · have hBx0 : Bbase0 n x = 0 := Bbase0_supp n x (not_le.mp hx)
    rw [hBx0, Real.zero_rpow (by linarith : t ≠ 0), zero_mul]
    exact Bbase0_nonneg n m

/-- The iterated linear convolutions `linPow (Bbase0 n) m` are log-concave. -/
theorem linPow_Bbase0_logConcave (n : ℕ) (hn : 1 ≤ n) :
    ∀ m : ℕ, 1 ≤ m → ∀ x y t, 0 ≤ t → t ≤ 1 →
      linPow (Bbase0 n) m x ^ t * linPow (Bbase0 n) m y ^ (1 - t)
        ≤ linPow (Bbase0 n) m (t * x + (1 - t) * y) := by
  intro m hm
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hm)
  clear hm
  induction m' with
  | zero =>
    intro x y t ht0 ht1
    rw [linPow_one]
    exact Bbase0_logConcave n hn x y t ht0 ht1
  | succ i ih =>
    intro x y t ht0 ht1
    show linPow (Bbase0 n) (i + 1 + 1) x ^ t * linPow (Bbase0 n) (i + 1 + 1) y ^ (1 - t)
        ≤ linPow (Bbase0 n) (i + 1 + 1) (t * x + (1 - t) * y)
    simp only [linPow_succ_succ]
    exact PrekopaLogConcave_convolution
      (linPow (Bbase0 n) (i + 1)) (Bbase0 n)
      (fun z => linPow_Bbase0_nn n (i + 1) (by omega) z)
      (Bbase0_nonneg n)
      (linPow_Bbase0_integrable' n hn (i + 1) (by omega))
      (Bbase0_integrable n hn)
      ih
      (Bbase0_logConcave n hn)
      x y t ht0 ht1

/-- `linPow (Bbase0 n) m` is antitone on `[0, ∞)`. -/
theorem linPow_Bbase0_antitone (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (hm : 1 ≤ m) :
    ∀ x y, 0 ≤ x → x ≤ y → linPow (Bbase0 n) m y ≤ linPow (Bbase0 n) m x :=
  even_logConcave_antitone (linPow (Bbase0 n) m)
    (fun x => linPow_Bbase0_nn n m hm x)
    (linPow_even (Bbase0 n) (Bbase0_even n hn) m)
    (linPow_Bbase0_logConcave n hn m hm)

/-- **Keystone (faithful tex:357 replacement).** `linPow (Glin n) k` is antitone on
`[0, ∞)`, derived from antitonicity of the compact-support iterates `linPow (Bbase0 n)`
through the linear multiplicity expansion — NOT through log-concavity of the sum `Glin`. -/
theorem linPow_Glin_antitone_faithful (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k) :
    ∀ x y, 0 ≤ x → x ≤ y → linPow (Glin n) k y ≤ linPow (Glin n) k x := by
  intro x y hx hxy
  rw [lin_expansion n hn k hk y, lin_expansion n hn k hk x]
  apply Summable.tsum_le_tsum _
    (expansion_summable_lin n hn k hk y) (expansion_summable_lin n hn k hk x)
  intro m
  have hc_nn : 0 ≤ (multM k m : ℝ) * alphaC n ^ (k + m) :=
    mul_nonneg (by positivity) (pow_nonneg (alphaC_nonneg n) _)
  have hterm : linPow (Bbase0 n) (k + m) y ≤ linPow (Bbase0 n) (k + m) x :=
    linPow_Bbase0_antitone n hn (k + m) (by omega) x y hx hxy
  exact mul_le_mul_of_nonneg_left hterm hc_nn

end MultiplicityExpansion
