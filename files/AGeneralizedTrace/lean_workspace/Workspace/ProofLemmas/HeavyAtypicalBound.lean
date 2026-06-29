import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.AtypicalZTailBound
import Workspace.ProofLemmas.CentralBinomialLowerTail
import Workspace.ProofLemmas.CentralBinomialLowerTailWide
import Workspace.ProofLemmas.CentralBinomialUpperTailWide
import Workspace.ProofLemmas.HeavyEllCount
import Workspace.ProofLemmas.BinomialPmfMaxBound

/-!
# HeavyAtypicalBound — proof attempt 7 (final close)
-/

set_option maxHeartbeats 32000000

open Classical
open Workspace.Types.AlternatingSumExpression

namespace HeavyAtypicalBoundProof7

/- Nonneg of binPMFInt -/
lemma binPMFInt_nonneg' (m : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (z : ℤ) :
    0 ≤ binPMFInt m p z := by
  unfold binPMFInt
  split_ifs
  · unfold binPMF
    split_ifs
    · apply mul_nonneg; apply mul_nonneg
      · exact_mod_cast Nat.zero_le _
      · exact pow_nonneg hp _
      · exact pow_nonneg (by linarith) _
    · exact le_refl 0
  · exact le_refl 0

lemma binPMF_nonneg' (m z : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binPMF m p z := by
  unfold binPMF
  split_ifs
  · apply mul_nonneg; apply mul_nonneg
    · exact_mod_cast Nat.zero_le _
    · exact pow_nonneg hp _
    · exact pow_nonneg (by linarith) _
  · exact le_refl 0

/- |ellFactor| ≤ 1 globally (no heavy hypothesis needed). -/
lemma abs_ellFactor_le_one
    (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (j : ℕ) :
    |ellFactor n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r j| ≤ 1 := by
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hαdef
  have hn_pos : (0:ℝ) < n := by exact_mod_cast hn
  have hsqrtn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hexp2_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have h2pi_pos : 0 < 2 * Real.pi := by linarith
  have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'def
  have hc'_pos : 0 < c' := by rw [hc'def]; positivity
  have hα_eq : α = c' * Real.sqrt n := by rw [hαdef, hc'def]
  have hα_pos : 0 < α := by rw [hα_eq]; exact mul_pos hc'_pos hsqrtn_pos
  have hα_nn : 0 ≤ α := le_of_lt hα_pos
  set k := r + ((n : ℤ) / 4) + (j : ℤ) with hkdef
  set X := binPMFInt n (1/2) k with hXdef
  have hX_nn : 0 ≤ X := binPMFInt_nonneg' n (1/2) (by norm_num) (by norm_num) k
  have hαX_bound : α * X ≤ c' * Real.sqrt (2 / Real.pi) := by
    have hbin_bound : X ≤ Real.sqrt (2 / (Real.pi * n)) := by
      rw [hXdef]; unfold binPMFInt
      split_ifs with hcase
      · unfold binPMF
        split_ifs with hcase2
        · have hbin := BinomialPmfMaxBound n hn k.toNat
          have hpow : ((1 : ℝ) / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)
              = (2 ^ n : ℝ)⁻¹ := by
            rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring]
            rw [show ((1 : ℝ) / 2) ^ k.toNat * (1 / 2) ^ (n - k.toNat)
                  = (1 / 2) ^ (k.toNat + (n - k.toNat)) from by rw [← pow_add]]
            rw [Nat.add_sub_of_le hcase2]
            rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ from by ring]
            rw [inv_pow]
          have hrearr : (n.choose k.toNat : ℝ) * (1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)
              = (n.choose k.toNat : ℝ) * ((1 / 2) ^ k.toNat * (1 - 1 / 2) ^ (n - k.toNat)) := by ring
          rw [hrearr, hpow]
          exact hbin
        · push_neg at hcase2
          obtain ⟨hk_nn, hk_le⟩ := hcase
          have : k.toNat ≤ n := by
            have hk_int : (k.toNat : ℤ) ≤ (n : ℤ) := by
              rw [Int.toNat_of_nonneg hk_nn]; exact hk_le
            exact_mod_cast hk_int
          omega
      · positivity
    calc α * X
        ≤ α * Real.sqrt (2 / (Real.pi * n)) := by
          apply mul_le_mul_of_nonneg_left hbin_bound hα_nn
      _ = c' * Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) := by rw [hα_eq]
      _ = c' * (Real.sqrt n * Real.sqrt (2 / (Real.pi * n))) := by ring
      _ = c' * Real.sqrt (n * (2 / (Real.pi * n))) := by
          rw [show Real.sqrt (n : ℝ) * Real.sqrt (2 / (Real.pi * n))
                = Real.sqrt ((n : ℝ) * (2 / (Real.pi * n))) from
              (Real.sqrt_mul (le_of_lt hn_pos) _).symm]
      _ = c' * Real.sqrt (2 / Real.pi) := by
          congr 2; field_simp
  have hsqrt2pi_lower : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.pi_gt_three]
  have hexp2_lower : 1 ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ); linarith
  have hsqrt_2_div_pi_le_one : Real.sqrt (2 / Real.pi) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    apply Real.sqrt_le_sqrt
    rw [div_le_one hpi_pos]
    linarith [Real.pi_gt_three]
  have hsqrt_2_div_pi_nn : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  have hc'_le_1_2 : c' ≤ 1/2 := by
    rw [hc'def]
    have hdenom_pos : 0 < 4 * Real.exp 2 * Real.sqrt (2 * Real.pi) := by positivity
    rw [div_le_iff₀ hdenom_pos]
    nlinarith [hexp2_lower, hsqrt2pi_lower]
  have hαX_le_half : α * X ≤ 1/2 := by
    calc α * X ≤ c' * Real.sqrt (2 / Real.pi) := hαX_bound
      _ ≤ (1/2) * 1 := by
          apply mul_le_mul hc'_le_1_2 hsqrt_2_div_pi_le_one hsqrt_2_div_pi_nn (by norm_num)
      _ = 1/2 := by ring
  have hαX_nn : 0 ≤ α * X := mul_nonneg hα_nn hX_nn
  have h_one_minus_αX_pos : 0 < 1 - α * X := by linarith
  have h_ell_eq : ellFactor n α r j = α * X / (1 - α * X) := by
    unfold ellFactor; rfl
  rw [h_ell_eq]
  rw [abs_of_nonneg (div_nonneg hαX_nn (le_of_lt h_one_minus_αX_pos))]
  rw [div_le_one h_one_minus_αX_pos]
  linarith

lemma prod_abs_ellFactor_le_one
    (n : ℕ) (hn : 1 ≤ n) (r : ℤ) (ℓ : Finset ℕ) :
    |∏ j ∈ ℓ, ellFactor n
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) r j| ≤ 1 := by
  rw [Finset.abs_prod]
  apply Finset.prod_le_one
  · intro j _; exact abs_nonneg _
  · intro j _; exact abs_ellFactor_le_one n hn r j

/- Sum of binPMFInt over Finset.range k for k ≤ m+1 is ≤ 1. -/
lemma sum_binPMFInt_range_le_one
    (m : ℕ) (p : ℝ) (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (k : ℕ) :
    (∑ z ∈ Finset.range k, binPMFInt m p (z : ℤ)) ≤ 1 := by
  -- We bound the sum by the full sum over [0, m+1) which equals 1.
  have h_split : (∑ z ∈ Finset.range k, binPMFInt m p (z : ℤ))
                = (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMFInt m p (z : ℤ))
                  + (∑ z ∈ Finset.range k \ Finset.range (m + 1), binPMFInt m p (z : ℤ)) := by
    rw [← Finset.sum_inter_add_sum_diff (Finset.range k) (Finset.range (m + 1))
        (f := fun z => binPMFInt m p (z : ℤ))]
  have h_outside_zero : (∑ z ∈ Finset.range k \ Finset.range (m + 1), binPMFInt m p (z : ℤ)) = 0 := by
    apply Finset.sum_eq_zero
    intro z hz
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range] at hz
    have hz_gt : (z : ℤ) > (m : ℤ) := by
      have : ¬ z < m + 1 := hz.2
      have : m + 1 ≤ z := by omega
      exact_mod_cast (by omega : (m : ℤ) < z)
    unfold binPMFInt
    rw [if_neg (by push_neg; intro _; linarith)]
  rw [h_split, h_outside_zero, add_zero]
  have h_eq : (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMFInt m p (z : ℤ))
            = (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMF m p z) := by
    apply Finset.sum_congr rfl
    intro z hz
    simp only [Finset.mem_inter, Finset.mem_range] at hz
    unfold binPMFInt
    have h0 : (0 : ℤ) ≤ (z : ℤ) := Int.ofNat_nonneg _
    have h1 : (z : ℤ) ≤ (m : ℤ) := by
      have : z ≤ m := by omega
      exact_mod_cast this
    rw [if_pos ⟨h0, h1⟩]
    simp [Int.toNat_natCast]
  rw [h_eq]
  -- Now bound by full sum over range (m+1)
  have h_subset : Finset.range k ∩ Finset.range (m + 1) ⊆ Finset.range (m + 1) :=
    Finset.inter_subset_right
  have h_full_sum : (∑ z ∈ Finset.range (m + 1), binPMF m p z) = 1 := by
    have h1 : (∑ z ∈ Finset.range (m + 1), (m.choose z : ℝ) * p^z * (1-p)^(m-z))
              = (p + (1-p))^m := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro z _; ring
    have h2 : (∑ z ∈ Finset.range (m + 1), binPMF m p z)
              = (∑ z ∈ Finset.range (m + 1), (m.choose z : ℝ) * p^z * (1-p)^(m-z)) := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.mem_range] at hz
      unfold binPMF
      rw [if_pos (by omega)]
    rw [h2, h1]
    rw [show p + (1 - p) = 1 from by ring]
    exact one_pow m
  calc (∑ z ∈ Finset.range k ∩ Finset.range (m + 1), binPMF m p z)
      ≤ (∑ z ∈ Finset.range (m + 1), binPMF m p z) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg h_subset
        intros z _ _
        exact binPMF_nonneg' m z p hp_lb hp_ub
    _ = 1 := h_full_sum

/- Sum over Ico of binPMFInt ≤ 1. -/
lemma sum_binPMFInt_Ico_le_one
    (m : ℕ) (p : ℝ) (hp_lb : 0 ≤ p) (hp_ub : p ≤ 1) (a b : ℕ) :
    (∑ z ∈ Finset.Ico a b, binPMFInt m p (z : ℤ)) ≤ 1 := by
  by_cases hab : a ≤ b
  · -- range b = Ico 0 b = Ico 0 a ∪ Ico a b (disjoint)
    have h_eq : Finset.range b = Finset.Ico 0 a ∪ Finset.Ico a b := by
      ext x
      simp [Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
      omega
    have h_dis : Disjoint (Finset.Ico 0 a) (Finset.Ico a b) := by
      apply Finset.disjoint_left.mpr
      intro x hx1 hx2
      rw [Finset.mem_Ico] at hx1 hx2; omega
    have h_sum_split : (∑ z ∈ Finset.range b, binPMFInt m p (z : ℤ))
                  = (∑ z ∈ Finset.Ico 0 a, binPMFInt m p (z : ℤ))
                    + (∑ z ∈ Finset.Ico a b, binPMFInt m p (z : ℤ)) := by
      rw [h_eq, Finset.sum_union h_dis]
    have h_first_nn : 0 ≤ (∑ z ∈ Finset.Ico 0 a, binPMFInt m p (z : ℤ)) := by
      apply Finset.sum_nonneg
      intro z _
      exact binPMFInt_nonneg' m p hp_lb hp_ub _
    have h_full := sum_binPMFInt_range_le_one m p hp_lb hp_ub b
    linarith
  · push_neg at hab
    have : Finset.Ico a b = ∅ := Finset.Ico_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    norm_num

/- Numerical inequality. -/
lemma numeric_final (n : ℕ) (hn : (10^12 : ℕ) ≤ n) :
    4 * (n : ℝ) * Real.exp (Real.sqrt n / 2) * Real.exp (-((n : ℝ) / 128))
      ≤ (1/8 : ℝ) * Real.exp (-(Real.sqrt n / 4)) := by
  have hn_real : (10^12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_pos : (0:ℝ) < (n : ℝ) := by linarith
  have hsqrtn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtn_sq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt (le_of_lt hn_pos)
  have hsqrtn_ge : 10^6 ≤ Real.sqrt n := by
    rw [show ((10:ℝ)^6) = Real.sqrt (10^12) from by
      rw [show ((10:ℝ)^12) = ((10:ℝ)^6)^2 from by ring]
      rw [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 10^6)]]
    exact Real.sqrt_le_sqrt hn_real
  have h_combined : 4 * (n : ℝ) * Real.exp (Real.sqrt n / 2) * Real.exp (-((n : ℝ) / 128))
                  = 4 * (n : ℝ) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128) := by
    rw [mul_assoc (4 * (n:ℝ)), ← Real.exp_add]; ring_nf
  rw [h_combined]
  have h_8_pos : (0:ℝ) < 8 := by norm_num
  rw [show (1/8 : ℝ) * Real.exp (-(Real.sqrt n / 4)) = Real.exp (-(Real.sqrt n / 4)) / 8 from by ring]
  rw [le_div_iff₀ h_8_pos]
  rw [show (4 * (n:ℝ) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128)) * 8
        = 32 * (n:ℝ) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128) from by ring]
  have h_n_le_exp_sqrtn : (n : ℝ) ≤ Real.exp (Real.sqrt n) := by
    have h_taylor : (Real.sqrt n)^4 / 24 ≤ Real.exp (Real.sqrt n) := by
      have := Real.pow_div_factorial_le_exp (Real.sqrt n) hsqrtn_nn 4
      simp only [Nat.factorial, Nat.cast_mul, Nat.cast_succ, Nat.cast_ofNat] at this
      convert this using 2
      norm_num [Nat.factorial]
    have h_pow4 : (Real.sqrt n)^4 = (n : ℝ)^2 := by
      have : (Real.sqrt n)^4 = ((Real.sqrt n)^2)^2 := by ring
      rw [this, Real.sq_sqrt (le_of_lt hn_pos)]
    rw [h_pow4] at h_taylor
    have h_n_le_n2_div_24 : (n : ℝ) ≤ (n : ℝ)^2 / 24 := by
      have hn_ge : 24 ≤ (n : ℝ) := by linarith
      nlinarith [hn_pos]
    linarith
  have h_32_le_exp_4 : (32 : ℝ) ≤ Real.exp 4 := by
    have h_exp1 : (5/2 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9
      linarith
    have h_exp4_eq : Real.exp 4 = (Real.exp 1)^4 := by
      rw [show (4 : ℝ) = 1 + 1 + 1 + 1 from by norm_num]
      rw [Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    rw [h_exp4_eq]
    calc (32 : ℝ) ≤ (5/2)^4 := by norm_num
      _ ≤ (Real.exp 1)^4 := by
        apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5/2) h_exp1
  have h_32n_le : (32 : ℝ) * (n : ℝ) ≤ Real.exp 4 * Real.exp (Real.sqrt n) := by
    apply mul_le_mul h_32_le_exp_4 h_n_le_exp_sqrtn (le_of_lt hn_pos) (Real.exp_pos _).le
  have h_combined_exp : Real.exp 4 * Real.exp (Real.sqrt n) = Real.exp (4 + Real.sqrt n) := by
    rw [← Real.exp_add]
  rw [h_combined_exp] at h_32n_le
  have h_exp_pos := Real.exp_pos (Real.sqrt n / 2 - (n : ℝ) / 128)
  have h_step : (32 * (n : ℝ)) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128)
              ≤ Real.exp (4 + Real.sqrt n) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128) := by
    apply mul_le_mul_of_nonneg_right h_32n_le (le_of_lt h_exp_pos)
  have h_exp_combined : Real.exp (4 + Real.sqrt n) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128)
                       = Real.exp (4 + Real.sqrt n + (Real.sqrt n / 2 - (n : ℝ) / 128)) := by
    rw [← Real.exp_add]
  rw [h_exp_combined] at h_step
  rw [show (32 : ℝ) * (n : ℝ) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128)
        = (32 * (n:ℝ)) * Real.exp (Real.sqrt n / 2 - (n : ℝ) / 128) from by ring]
  refine le_trans h_step ?_
  apply Real.exp_le_exp.mpr
  have h_sqrt_n_le : 7 * Real.sqrt n / 4 ≤ (n : ℝ) / 256 := by
    have h448 : (448 : ℝ) ≤ Real.sqrt n := by linarith
    have h_aux : 448 * Real.sqrt n ≤ (n : ℝ) := by
      calc 448 * Real.sqrt n ≤ Real.sqrt n * Real.sqrt n := by nlinarith [hsqrtn_nn]
        _ = (n : ℝ) := hsqrtn_sq
    linarith
  have h_4_le : (4 : ℝ) ≤ (n : ℝ) / 256 := by linarith
  have h_combined : 4 + 7 * Real.sqrt n / 4 ≤ (n : ℝ) / 128 := by
    calc 4 + 7 * Real.sqrt n / 4 ≤ (n : ℝ) / 256 + (n : ℝ) / 256 := by linarith
      _ = (n : ℝ) / 128 := by ring
  linarith

end HeavyAtypicalBoundProof7

theorem HeavyAtypicalBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 320 / Real.sqrt n ≤ δ → δ ≤ 1/2 →
      let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let n_h : ℕ := n / 2
      let S_er : ℤ → ℕ → ℝ := fun r j =>
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
          Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ))
      let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j))
      let P_H : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            Real.exp (-(Real.sqrt n / 2)) ≤ widetildeMu_er r ℓ)
      let T_II : ℝ :=
        ∑ ℓ ∈ P_H,
          ((∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            +
           (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))
      T_II ≤ (1 : ℝ) / 8 * Real.exp (-(Real.sqrt n / 4)) := by
  intro n hn hn8 δ hδ_lb hδ_ub
  simp only
  -- Numerical setup
  have hn_pos : (0 : ℕ) < n := by
    have : (10 ^ 12 : ℕ) ≤ n := hn
    omega
  have hn_one : (1 : ℕ) ≤ n := hn_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_real_ge : (10 ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrtn_nn : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hsqrtn_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_real_pos
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hαdef
  have hδ_nn : 0 ≤ δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  have h_one_minus_δ_nn : 0 ≤ 1 - δ := by linarith
  have h_one_minus_δ_le : 1 - δ ≤ 1 := by linarith
  have hδ_pos : 0 < δ := by
    have h1 : 0 < 320 / Real.sqrt n := by positivity
    linarith
  set P_H_full : Finset (Finset ℕ) :=
    ((Finset.Icc 1 (n / 2)).powerset).filter (fun ℓ =>
      sameParity ℓ ∧
      ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
        Real.exp (-(Real.sqrt n / 2)) ≤
          ∏ j ∈ Finset.Icc 1 (n / 2),
            (if j ∈ ℓ then
              (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ))
            else
              1 - (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                binPMFInt n (1/2) (r + ((n : ℤ) / 4) + (j : ℤ)))) with hP_H_full_def
  have h_card_PH : (P_H_full.card : ℝ) ≤ (n : ℝ) * Real.exp (Real.sqrt n / 2) := by
    have h := HeavyEllCount n hn hn8
    simp only at h
    convert h using 1
  -- Triangle inequality on altRSum
  have triangle : ∀ (zMinus zPlus : ℕ) (ℓ : Finset ℕ),
      |altRSum n δ α zMinus zPlus ℓ|
        ≤ ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
            |Fterm n δ α r zMinus zPlus ℓ| := by
    intro zMinus zPlus ℓ
    unfold altRSum
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro r _
    rw [abs_mul]
    have h_pow_abs : |(-1 : ℝ) ^ r.natAbs| = 1 := by
      rcases Nat.even_or_odd r.natAbs with hev | hodd
      · rw [hev.neg_one_pow]; norm_num
      · rw [hodd.neg_one_pow]; norm_num
    rw [h_pow_abs, one_mul]
  -- Bound |Fterm| ≤ B1 · B2 · B3
  have Fterm_bound : ∀ (r : ℤ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ),
      |Fterm n δ α r zMinus zPlus ℓ|
        ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus := by
    intro r zMinus zPlus ℓ
    unfold Fterm
    have h_b1_nn : 0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) :=
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    have h_b2_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus :=
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_b3_nn : 0 ≤ binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus :=
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_prod_abs : |∏ j ∈ ℓ, ellFactor n α r (j - 1)| ≤ 1 := by
      rw [Finset.abs_prod]
      apply Finset.prod_le_one
      · intro j _; exact abs_nonneg _
      · intro j _; exact HeavyAtypicalBoundProof7.abs_ellFactor_le_one n hn_one r (j - 1)
    rw [abs_mul, abs_mul, abs_mul]
    rw [abs_of_nonneg h_b1_nn, abs_of_nonneg h_b2_nn, abs_of_nonneg h_b3_nn]
    have h_prod_nn :
        0 ≤ binPMFInt (n/2) (1 / 2) (r + ((n : ℤ) / 4)) *
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus := by
      apply mul_nonneg; apply mul_nonneg h_b1_nn h_b2_nn; exact h_b3_nn
    nlinarith [h_prod_nn, h_prod_abs, abs_nonneg (∏ j ∈ ℓ, ellFactor n α r (j - 1))]
  -- The bound on a single |altRSum| in terms of a triple-product over r
  have altRSum_le : ∀ (zMinus zPlus : ℕ) (ℓ : Finset ℕ),
      |altRSum n δ α zMinus zPlus ℓ| ≤
        ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus := by
    intro zMinus zPlus ℓ
    refine (triangle zMinus zPlus ℓ).trans ?_
    apply Finset.sum_le_sum
    intro r _
    exact Fterm_bound r zMinus zPlus ℓ
  -- Define the triple-product function for cleanness
  let G : ℤ → ℕ → ℕ → ℝ := fun r zMinus zPlus =>
    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus
  have G_nn : ∀ r zMinus zPlus, 0 ≤ G r zMinus zPlus := by
    intro r zMinus zPlus
    simp only [G]
    apply mul_nonneg
    apply mul_nonneg
    · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
  -- Bound Piece A := ∑_{zMinus<n/16} ∑_{zPlus<n/2+1} |altRSum| for fixed ℓ
  -- ≤ ∑_r B1(r) · (∑_{zMinus<n/16} B2(r,zMinus)) · (∑_{zPlus<n/2+1} B3(r,zPlus))
  -- ≤ ∑_r B1(r) · (∑_{zMinus<n/16} B2(r,zMinus)) · 1
  set rRange : Finset ℤ := Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) with hrRange_def
  -- Bound for Piece A (fixed ℓ)
  have pieceA_bound_per_ell : ∀ (ℓ : Finset ℕ),
      (∑ zMinus ∈ Finset.range (n / 16),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |altRSum n δ α zMinus zPlus ℓ|)
        ≤ ∑ r ∈ rRange,
            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
    intro ℓ
    -- Step 1: |altRSum| ≤ ∑_r G r zMinus zPlus
    have h_step1 : (∑ zMinus ∈ Finset.range (n / 16),
                      ∑ zPlus ∈ Finset.range (n / 2 + 1),
                        |altRSum n δ α zMinus zPlus ℓ|)
                  ≤ (∑ zMinus ∈ Finset.range (n / 16),
                      ∑ zPlus ∈ Finset.range (n / 2 + 1),
                        ∑ r ∈ rRange, G r zMinus zPlus) := by
      apply Finset.sum_le_sum
      intro zMinus _
      apply Finset.sum_le_sum
      intro zPlus _
      exact altRSum_le zMinus zPlus ℓ
    refine h_step1.trans ?_
    -- Step 2: swap sums (zPlus inside, then zMinus inside, then r outside)
    have h_swap1 : ∀ zMinus, (∑ zPlus ∈ Finset.range (n / 2 + 1),
                              ∑ r ∈ rRange, G r zMinus zPlus)
                            = ∑ r ∈ rRange, ∑ zPlus ∈ Finset.range (n / 2 + 1),
                                G r zMinus zPlus := by
      intro zMinus
      exact Finset.sum_comm
    have h_step2 : (∑ zMinus ∈ Finset.range (n / 16),
                      ∑ zPlus ∈ Finset.range (n / 2 + 1),
                        ∑ r ∈ rRange, G r zMinus zPlus)
                = (∑ zMinus ∈ Finset.range (n / 16),
                      ∑ r ∈ rRange,
                        ∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus) := by
      apply Finset.sum_congr rfl
      intros zMinus _
      exact h_swap1 zMinus
    rw [h_step2]
    -- Step 3: swap zMinus and r
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r _
    -- Inner: ∑_{zMinus<n/16} ∑_{zPlus} G r zMinus zPlus
    --      = ∑_{zMinus<n/16} B1(r) * B2(r,zMinus) * (∑_{zPlus} B3(r,zPlus))
    have h_factor1 : ∀ zMinus,
        (∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus)
          = binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
              (∑ zPlus ∈ Finset.range (n / 2 + 1),
                  binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      intro zMinus
      rw [Finset.mul_sum]
    have h_step3 : (∑ zMinus ∈ Finset.range (n / 16),
                      ∑ zPlus ∈ Finset.range (n / 2 + 1), G r zMinus zPlus)
                = (∑ zMinus ∈ Finset.range (n / 16),
                    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
                    (∑ zPlus ∈ Finset.range (n / 2 + 1),
                      binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) := by
      apply Finset.sum_congr rfl
      intros zMinus _
      exact h_factor1 zMinus
    rw [h_step3]
    -- Bound the zPlus sum by 1
    have h_zplus_sum_le : (∑ zPlus ∈ Finset.range (n / 2 + 1),
                            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 :=
      HeavyAtypicalBoundProof7.sum_binPMFInt_range_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _
    have h_zplus_sum_nn : 0 ≤ (∑ zPlus ∈ Finset.range (n / 2 + 1),
                              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply Finset.sum_nonneg
      intros _ _
      exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    -- Sum over zMinus < n/16
    have h_b1_nn : 0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) :=
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    have h_each_term_nn : ∀ zMinus, 0 ≤
        binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus := by
      intro zMinus
      apply mul_nonneg h_b1_nn
      exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    -- Sum:  ∑_{zMinus} (B1 * B2) * (∑_{zPlus} B3) ≤ ∑_{zMinus} (B1 * B2) * 1 = B1 * (∑_{zMinus} B2)
    calc (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
            (∑ zPlus ∈ Finset.range (n / 2 + 1),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
        ≤ (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus * 1) := by
          apply Finset.sum_le_sum
          intros zMinus _
          apply mul_le_mul_of_nonneg_left h_zplus_sum_le (h_each_term_nn zMinus)
      _ = binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zMinus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intros zMinus _
          ring
  -- Bound for Piece B (symmetric, with zMinus ranging in Ico (n/16) (n/2+1) and zPlus < n/16)
  -- After swapping argument order: sum is over zPlus < n/16, zMinus ∈ Ico ...
  -- Strategy: same as A but with B2 sum ≤ 1 (bounded over Ico)
  have pieceB_bound_per_ell : ∀ (ℓ : Finset ℕ),
      (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 16),
            |altRSum n δ α zMinus zPlus ℓ|)
        ≤ ∑ r ∈ rRange,
            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
    intro ℓ
    have h_step1 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ zPlus ∈ Finset.range (n / 16),
                        |altRSum n δ α zMinus zPlus ℓ|)
                  ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ zPlus ∈ Finset.range (n / 16),
                        ∑ r ∈ rRange, G r zMinus zPlus) := by
      apply Finset.sum_le_sum
      intro zMinus _
      apply Finset.sum_le_sum
      intro zPlus _
      exact altRSum_le zMinus zPlus ℓ
    refine h_step1.trans ?_
    -- Move r outside: zMinus → zPlus → r becomes r → zMinus → zPlus
    have h_swap1 : ∀ zMinus, (∑ zPlus ∈ Finset.range (n / 16),
                              ∑ r ∈ rRange, G r zMinus zPlus)
                            = ∑ r ∈ rRange, ∑ zPlus ∈ Finset.range (n / 16),
                                G r zMinus zPlus := by
      intro zMinus
      exact Finset.sum_comm
    have h_step2 : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ zPlus ∈ Finset.range (n / 16),
                        ∑ r ∈ rRange, G r zMinus zPlus)
                = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ r ∈ rRange,
                        ∑ zPlus ∈ Finset.range (n / 16), G r zMinus zPlus) := by
      apply Finset.sum_congr rfl
      intros zMinus _
      exact h_swap1 zMinus
    rw [h_step2]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro r _
    -- Inner: ∑_{zMinus∈Ico} ∑_{zPlus<n/16} G r zMinus zPlus
    -- G = B1(r) · B2(r,zMinus) · B3(r,zPlus)
    -- = B1(r) · (∑_{zMinus∈Ico} B2(r,zMinus)) · (∑_{zPlus<n/16} B3(r,zPlus))
    have h_factor : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      ∑ zPlus ∈ Finset.range (n / 16), G r zMinus zPlus)
                  = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                      binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
                    (binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                      (∑ zPlus ∈ Finset.range (n / 16),
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intros zMinus _
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intros zPlus _
      simp only [G]
      ring
    rw [h_factor]
    -- bound the zMinus-Ico sum ≤ 1
    have h_zminus_sum_le : (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 :=
      HeavyAtypicalBoundProof7.sum_binPMFInt_Ico_le_one _ _ h_one_minus_δ_nn h_one_minus_δ_le _ _
    have h_zminus_sum_nn : 0 ≤ (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
      apply Finset.sum_nonneg
      intros _ _
      exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_inner_nn : 0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zPlus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      apply mul_nonneg
      · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1/2) (by norm_num) (by norm_num) _
      · apply Finset.sum_nonneg
        intros _ _
        exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    calc (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) *
          (binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
        ≤ 1 *
          (binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) := by
          apply mul_le_mul_of_nonneg_right h_zminus_sum_le h_inner_nn
      _ = binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
          (∑ zPlus ∈ Finset.range (n / 16),
            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by ring
  -- Step: bound ∑_r B1(r) · (∑_{zMinus<n/16} B2(r,zMinus)) ≤ 2 · exp(-n/128)
  -- By splitting r-range into [-n/4, -n/16-1] and [-n/16, n/4]
  -- Range (-n/4, -n/16-1): use B2 sum ≤ 1, bound ∑_r B1(r) by CentralBinomialLowerTailWide ≤ exp(-n/128)
  -- Range [-n/16, n/4]: use AtypicalZTailBound on ∑_{zMinus<n/16} B2(r,zMinus) ≤ exp(-n/128)
  --                     and ∑_r B1(r) ≤ 1
  have rRangeA_bound : (∑ r ∈ rRange,
              binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
              (∑ zMinus ∈ Finset.range (n / 16),
                binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
            ≤ 2 * Real.exp (-((n : ℝ) / 128)) := by
    -- Split rRange = Icc(-n/4, -n/16-1) ∪ Icc(-n/16, n/4) (almost; need to handle carefully)
    set rA1 : Finset ℤ := Finset.Icc (-((n : ℤ) / 4)) (-((n : ℤ) / 16) - 1) with hrA1_def
    set rA2 : Finset ℤ := Finset.Icc (-((n : ℤ) / 16)) ((n : ℤ) / 4) with hrA2_def
    have hn16_int : (0 : ℤ) ≤ (n : ℤ) / 16 := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    have hn4_int : (0 : ℤ) ≤ (n : ℤ) / 4 := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    have h_rRange_eq : rRange = rA1 ∪ rA2 := by
      simp only [hrRange_def, hrA1_def, hrA2_def]
      ext r
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have h_rA_disj : Disjoint rA1 rA2 := by
      simp only [hrA1_def, hrA2_def]
      apply Finset.disjoint_left.mpr
      intros r hr1 hr2
      rw [Finset.mem_Icc] at hr1 hr2
      omega
    have h_term_nn : ∀ r,
        0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
      intro r
      apply mul_nonneg
      · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1/2) (by norm_num) (by norm_num) _
      · apply Finset.sum_nonneg
        intros _ _
        exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_sum_split : (∑ r ∈ rRange,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zMinus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                = (∑ r ∈ rA1,
                    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                    (∑ zMinus ∈ Finset.range (n / 16),
                      binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                + (∑ r ∈ rA2,
                    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                    (∑ zMinus ∈ Finset.range (n / 16),
                      binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus)) := by
      rw [h_rRange_eq, Finset.sum_union h_rA_disj]
    rw [h_sum_split]
    -- Bound rA1 part: ≤ ∑_r B1(r) · 1 ≤ exp(-n/128)
    have h_rA1_inner_le_one : ∀ r ∈ rA1,
        (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ 1 := by
      intros r _
      exact HeavyAtypicalBoundProof7.sum_binPMFInt_range_le_one _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_rA1_inner_nn : ∀ r ∈ rA1,
        0 ≤ (∑ zMinus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) := by
      intros r _
      apply Finset.sum_nonneg
      intros _ _
      exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_rA1_b1_nn : ∀ r,
        0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) := fun r =>
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    have h_rA1_le : (∑ r ∈ rA1,
                      binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                      (∑ zMinus ∈ Finset.range (n / 16),
                        binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                  ≤ (∑ r ∈ rA1, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) := by
      apply Finset.sum_le_sum
      intros r hr
      have h1 : 0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) := h_rA1_b1_nn r
      have h2 := h_rA1_inner_le_one r hr
      nlinarith [h_rA1_inner_nn r hr, h_rA1_b1_nn r]
    have h_central_lower_tail := CentralBinomialLowerTailWideHalf n hn hn8
    have h_rA1_total_le : (∑ r ∈ rA1, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                        ≤ Real.exp (-((n : ℝ) / 128)) := by
      simp only [hrA1_def]
      exact h_central_lower_tail
    have h_rA1_part_le : (∑ r ∈ rA1,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zMinus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                      ≤ Real.exp (-((n : ℝ) / 128)) := by linarith
    -- Bound rA2 part: ≤ ∑_r B1(r) · exp(-n/128) ≤ 1 · exp(-n/128)
    have h_rA2_inner_le : ∀ r ∈ rA2,
        (∑ zMinus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus) ≤ Real.exp (-((n : ℝ) / 128)) := by
      intros r hr
      rw [hrA2_def] at hr
      rw [Finset.mem_Icc] at hr
      have hr_lb : -((n : ℤ) / 16) ≤ r := hr.1
      have hr_ub : r ≤ (n : ℤ) / 4 := hr.2
      -- Apply AtypicalZTailBound: needs -(n/8) + (n/16) ≤ r ≤ n/4
      -- Since -(n/8) + (n/16) ≤ -(n/16) (i.e. n/16 ≤ n/8 - n/16 = n/16)
      have h_lb_target : -((n : ℤ) / 8) + ((n : ℤ) / 16) ≤ r := by
        -- Need: -(n/8) + (n/16) ≤ -(n/16). Equivalent: 2*(n/16) ≤ n/8.
        -- Actually -(n/8) + (n/16) = -(n/8 - n/16). For n ≥ 16: n/8 - n/16 ≥ n/16, so -(n/8) + (n/16) ≤ -(n/16).
        -- Just need omega
        have hn16_nn : (0 : ℤ) ≤ (n : ℤ) / 16 := hn16_int
        have hn8_int : (0 : ℤ) ≤ (n : ℤ) / 8 := by
          have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
          omega
        have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        omega
      have h_ub_target : r ≤ ((n : ℤ) / 4) := hr_ub
      exact AtypicalZTailBound n hn hn8 δ hδ_pos hδ_ub r h_lb_target h_ub_target
    -- Now: ∑_{r∈rA2} B1(r) · (inner) ≤ ∑_{r∈rA2} B1(r) · exp(-n/128) ≤ exp(-n/128) · ∑_r B1
    have h_rA2_le_step : (∑ r ∈ rA2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            (∑ zMinus ∈ Finset.range (n / 16),
                              binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                      ≤ (∑ r ∈ rA2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            Real.exp (-((n : ℝ) / 128))) := by
      apply Finset.sum_le_sum
      intros r hr
      apply mul_le_mul_of_nonneg_left
      · exact h_rA2_inner_le r hr
      · exact h_rA1_b1_nn r
    have h_rA2_factored : (∑ r ∈ rA2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            Real.exp (-((n : ℝ) / 128)))
                      = (∑ r ∈ rA2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                        * Real.exp (-((n : ℝ) / 128)) := by
      rw [Finset.sum_mul]
    rw [h_rA2_factored] at h_rA2_le_step
    -- Bound ∑_{r∈rA2} B1(r) ≤ 1
    have h_b1_sum_le_one : (∑ r ∈ rA2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) ≤ 1 := by
      -- New first factor: Binomial(n/2). Substitute k = r + n/4, with r ∈ rA2 = [-(n/16), n/4],
      -- so k ∈ [n/4 - n/16, n/2] ⊆ [0, n/2]. Bound by the full Binomial(n/2) sum over range (n/2 + 1), which is ≤ 1.
      have hn_cast2 : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
        omega
      have h_inj : Set.InjOn (fun (r : ℤ) => (r + ((n : ℤ) / 4)).toNat) (rA2 : Set ℤ) := by
        intros r1 hr1 r2 hr2 h_eq
        rw [Finset.mem_coe, hrA2_def, Finset.mem_Icc] at hr1 hr2
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n4 : (0 : ℤ) ≤ (n : ℤ) / 4 := hn4_int
        have h_n16_le_n4 : (n : ℤ) / 16 ≤ (n : ℤ) / 4 := by omega
        have hr1_plus_nn : 0 ≤ r1 + ((n : ℤ) / 4) := by linarith [hr1.1]
        have hr2_plus_nn : 0 ≤ r2 + ((n : ℤ) / 4) := by linarith [hr2.1]
        simp only at h_eq
        have hh : ((r1 + ((n : ℤ) / 4)).toNat : ℤ) = ((r2 + ((n : ℤ) / 4)).toNat : ℤ) := by
          exact_mod_cast h_eq
        rw [Int.toNat_of_nonneg hr1_plus_nn, Int.toNat_of_nonneg hr2_plus_nn] at hh
        linarith
      have h_eq_via_image : (∑ r ∈ rA2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                          = (∑ k ∈ rA2.image (fun (r : ℤ) => (r + ((n : ℤ) / 4)).toNat),
                              binPMFInt (n/2) (1/2) (k : ℤ)) := by
        rw [Finset.sum_image (fun r1 hr1 r2 hr2 h_eq => h_inj hr1 hr2 h_eq)]
        apply Finset.sum_congr rfl
        intros r hr
        rw [hrA2_def, Finset.mem_Icc] at hr
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n16_le_n4 : (n : ℤ) / 16 ≤ (n : ℤ) / 4 := by omega
        have hr_plus_nn : 0 ≤ r + ((n : ℤ) / 4) := by linarith [hr.1]
        rw [Int.toNat_of_nonneg hr_plus_nn]
      rw [h_eq_via_image]
      -- Now bound by the full Binomial(n/2) sum
      apply le_trans _ (HeavyAtypicalBoundProof7.sum_binPMFInt_range_le_one (n/2) (1/2)
        (by norm_num) (by norm_num) (n/2 + 1))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intros k hk
        rw [Finset.mem_image] at hk
        obtain ⟨r, hr_in, hr_eq⟩ := hk
        rw [hrA2_def, Finset.mem_Icc] at hr_in
        rw [Finset.mem_range]
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n4_nn : (0 : ℤ) ≤ (n : ℤ) / 4 := hn4_int
        have h_n16_le_n4 : (n : ℤ) / 16 ≤ (n : ℤ) / 4 := by omega
        have h_k_ub : (k : ℤ) ≤ (n : ℤ) / 2 := by
          have hr_plus_nn : 0 ≤ r + ((n : ℤ) / 4) := by linarith [hr_in.1]
          have h_n4_n4_le : (n : ℤ) / 4 + (n : ℤ) / 4 ≤ (n : ℤ) / 2 := by omega
          have hr_plus_ub : r + ((n : ℤ) / 4) ≤ (n : ℤ) / 2 := by linarith [hr_in.2]
          rw [← hr_eq]
          rw [Int.toNat_of_nonneg hr_plus_nn]
          exact hr_plus_ub
        have h_k_ub_nat : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hn_cast2]; exact h_k_ub
        have : k ≤ n / 2 := by exact_mod_cast h_k_ub_nat
        omega
      · intros k _ _
        exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    have h_exp_nn : (0 : ℝ) ≤ Real.exp (-((n : ℝ) / 128)) := (Real.exp_pos _).le
    have h_rA2_part_le : (∑ r ∈ rA2,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zMinus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus))
                      ≤ Real.exp (-((n : ℝ) / 128)) := by
      have h_step1 := h_rA2_le_step
      have h_step2 : (∑ r ∈ rA2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) *
                      Real.exp (-((n : ℝ) / 128))
                  ≤ 1 * Real.exp (-((n : ℝ) / 128)) := by
        apply mul_le_mul_of_nonneg_right h_b1_sum_le_one h_exp_nn
      linarith
    linarith
  -- Bound for Piece B (similarly): need ∑_r B1 · (∑_{zPlus<n/16} B3) ≤ 2 · exp(-n/128)
  -- Same structure as A but use AtypicalZPlusTailBound on B3.
  have rRangeB_bound : (∑ r ∈ rRange,
              binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
              (∑ zPlus ∈ Finset.range (n / 16),
                binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
            ≤ 2 * Real.exp (-((n : ℝ) / 128)) := by
    -- Split rRange = Icc(-n/4, n/16) ∪ Icc(n/16+1, n/4)? No, let's think again.
    -- For B3: B3(r,zPlus) = bin(n/4 - r, 1-δ, zPlus). Use AtypicalZPlusTailBound which needs:
    -- -((n:ℤ)/4) ≤ r ≤ ((n:ℤ)/8) - ((n:ℤ)/16) = ((n:ℤ)/16)? Let me re-check.
    -- AtypicalZPlusTailBound: r ∈ [-(n/4), (n/8) - (n/16)]. Let's call that [-(n/4), (n/16)].
    -- Wait n/8 - n/16 might not equal n/16 in integer division. But 2(n/16) ≤ n/8.
    -- Actually n/8 - n/16 ≥ 0 ≤ n/16. For n divisible by 16, they're equal. In general n/8 - n/16 ≤ n/16.
    -- So the AtypicalZPlusTailBound applies for r ∈ [-(n/4), (n/8) - (n/16)].
    -- Above this range, r ∈ [(n/8) - (n/16) + 1, n/4]. Length ≤ n/4 - (n/8 - n/16) = n/16 + n/8 = 3n/16.
    -- For these r, k = r + n/2 ∈ [(n/8 - n/16) + 1 + n/2, n/4 + n/2] = [n/2 + n/16 + 1, 3n/4]
    -- This is the upper tail of Bin(n, 1/2). By symmetry CentralBinomialLowerTailWide should work.
    -- But we need the upper tail. Hmm...
    --
    -- Actually let's think more carefully. We have rA2 splits the r range.
    -- For Piece B (z+ tail), we need similar split:
    -- Range r1 = [-(n/4), (n/8 - n/16)]: use AtypicalZPlusTailBound
    -- Range r2 = [(n/8 - n/16) + 1, n/4]: use upper tail of Bin
    --
    -- For the upper tail: ∑_{r ∈ r2} bin(n, 1/2, r + n/2) corresponds to sum over k = r + n/2
    -- in [n/2 + (n/8 - n/16) + 1, n/2 + n/4] = [(n/2 + n/16 - n/16 + n/16) + 1, ...]
    -- Hmm. Use symmetry: bin(n, 1/2, k) = bin(n, 1/2, n - k). So sum over k upper tail = sum over k' = n-k lower tail.
    -- Specifically, we'd want to bound the sum of bin(n, 1/2, k) for k ∈ [n/2 + (n/8 - n/16) + 1, n/2 + n/4]
    -- which equals sum of bin(n, 1/2, k') for k' = n - k ∈ [n - 3n/4, n - n/2 - (n/8 - n/16) - 1] = [n/4, n/2 - n/8 + n/16 - 1].
    -- Hmm, we'd need a more general bound. But actually, for Piece B, the relevant range and the relevant Hoeffding tail
    -- can be reduced by symmetry to CentralBinomialLowerTailWide.
    --
    -- Alternative simpler approach: for Piece B, we use Atypical bounds on B3 similar to B2 in Piece A,
    -- but reverse. Specifically, AtypicalZPlusTailBound gives us:
    -- For r ∈ [-n/4, (n/8) - (n/16)]: ∑_{zPlus < n/16} bin(n/4 - r, 1-δ, zPlus) ≤ exp(-n/128)
    -- And the COMPLEMENT range r ∈ [(n/8)-(n/16)+1, n/4]: B1 lower tail bound.
    -- Actually this matches Piece A's structure with roles of upper/lower swapped.
    --
    -- For the second range, we need: ∑_{r ∈ [(n/8)-(n/16)+1, n/4]} bin(n, 1/2, r+n/2)
    -- = ∑_{k ∈ [n/2 + (n/8) - (n/16) + 1, n/2 + n/4]} bin(n, 1/2, k)
    -- This is an upper tail. Bound it by symmetry: bin(n, 1/2, k) = bin(n, 1/2, n - k).
    -- So sum becomes ∑_{k' ∈ [n - 3n/4, n - n/2 - (n/8) + (n/16) - 1]} bin(n, 1/2, k')
    -- = ∑_{k' ∈ [n/4, n/2 - (n/8) + (n/16) - 1]} bin(n, 1/2, k')
    -- For r' = k' - n/2, this is r' ∈ [-(n/4), -(n/8) + (n/16) - 1] ⊆ [-(n/4), -(n/16) - 1] (since (n/16) - 1 ≤ -(n/16) when 2(n/16) ≤ 1?? No that's wrong).
    -- Actually -(n/8) + (n/16) - 1 ≤ -(n/16) - 1 iff -(n/8) + (n/16) ≤ -(n/16) iff 2(n/16) ≤ n/8, which holds.
    -- So sum over k' ∈ [n/4, ...] is ⊆ Icc(-n/4, -n/16 - 1) range r-shifted. Use CentralBinomialLowerTailWide.
    --
    -- This is getting complex. For now, let me try the following easier approach that avoids the symmetry:
    -- Use a coarser split. Since rA2 was r ∈ [-(n/16), n/4], for Piece B use rB2 = [-(n/4), (n/16)].
    -- Then by symmetry bin(n, 1/2, r + n/2) under r → -r gives the same distribution.
    -- Actually, let me set rB1 = Icc(((n:ℤ)/16) + 1, (n:ℤ)/4) and rB2 = Icc(-(n:ℤ)/4, (n:ℤ)/16).
    set rB1 : Finset ℤ := Finset.Icc (((n : ℤ) / 16) + 1) ((n : ℤ) / 4) with hrB1_def
    set rB2 : Finset ℤ := Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 16) with hrB2_def
    have hn16_int : (0 : ℤ) ≤ (n : ℤ) / 16 := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    have hn4_int : (0 : ℤ) ≤ (n : ℤ) / 4 := by
      have : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
      omega
    have h_rRange_eq : rRange = rB1 ∪ rB2 := by
      simp only [hrRange_def, hrB1_def, hrB2_def]
      ext r
      simp only [Finset.mem_Icc, Finset.mem_union]
      omega
    have h_rB_disj : Disjoint rB1 rB2 := by
      simp only [hrB1_def, hrB2_def]
      apply Finset.disjoint_left.mpr
      intros r hr1 hr2
      rw [Finset.mem_Icc] at hr1 hr2
      omega
    have h_term_nn : ∀ r,
        0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
            (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      intro r
      apply mul_nonneg
      · exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1/2) (by norm_num) (by norm_num) _
      · apply Finset.sum_nonneg
        intros _ _
        exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_sum_split : (∑ r ∈ rRange,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zPlus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                = (∑ r ∈ rB1,
                    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                    (∑ zPlus ∈ Finset.range (n / 16),
                      binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                + (∑ r ∈ rB2,
                    binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                    (∑ zPlus ∈ Finset.range (n / 16),
                      binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus)) := by
      rw [h_rRange_eq, Finset.sum_union h_rB_disj]
    rw [h_sum_split]
    -- Bound rB1 part: r ∈ [n/16+1, n/4] is upper tail.
    -- By symmetry: bin(n, 1/2, r + n/2) when r > 0 corresponds to upper tail.
    -- Use the substitution r → -r. Specifically: bin(n, 1/2, r + n/2) ≤ ... hmm.
    -- The cleanest approach: for r ∈ rB1, use bin(n, 1/2, r + n/2) bound by reflecting.
    -- Actually let's try using a more direct argument:
    -- Since r ∈ [n/16 + 1, n/4], use the AtypicalZTailBound on B2 SUM... No, that doesn't apply.
    --
    -- Try: use the bound for inner sum (over zPlus) ≤ 1, and bound ∑_r B1(r) for r ∈ rB1.
    -- For rB1 = [n/16+1, n/4], k = r+n/2 ∈ [n/2 + n/16 + 1, 3n/4].
    -- By symmetry, this sum equals sum over k' = n-k ∈ [n/4, n/2 - n/16 - 1].
    -- That is, after substituting r' = k' - n/2 = -k + n/2 - n/2 = -r, we get r' ∈ [-(n/4), n/16 - 1].
    -- But our hypothesis is for r' ∈ [-(n/4), -(n/16) - 1], which is in fact the same when we flip.
    -- So we need: ∑_{r ∈ rB1} B1(r) = ∑_{r' ∈ [-(n/4), (n/16) - 1]} B1(-r' + 0) (by some reindexing)
    -- This is getting nested. Let me try yet another approach: AtypicalZPlusTailBound on B3.
    --
    -- Wait — for rB1 part, why not use AtypicalZPlusTailBound? It gives, for r ≤ n/8 - n/16:
    -- ∑_{zPlus < n/16} bin(n/4 - r, 1-δ, zPlus) ≤ exp(-n/128)
    -- For rB1, r ≥ n/16 + 1 > n/8 - n/16 (when n/16 ≥ 1)? Let me check: n/8 - n/16. For 16 | n: = n/16. So n/8 - n/16 = n/16 (when 16 | n).
    -- For n not divisible: ≤ n/16. So rB1 starts at n/16 + 1 > n/8 - n/16. Good. But that means rB1 is OUTSIDE the AtypicalZPlusTailBound range.
    -- For rB2, r ≤ n/16, but AtypicalZPlusTailBound needs r ≤ n/8 - n/16 ≤ n/16. So rB2 might exceed.
    --
    -- Let me use a different split. Use:
    -- rA2 (used for Piece A) = [-(n/16), n/4] applies AtypicalZTailBound (B2).
    -- For Piece B, mirror: use rB' = [-(n/4), (n/16)] applying AtypicalZPlusTailBound (B3).
    -- But for AtypicalZPlusTailBound, the range is [-(n/4), (n/8) - (n/16)].
    -- (n/8) - (n/16) ≤ n/16 in general (with equality when 16 | n).
    -- So rB' might be too large. Hmm.
    --
    -- Let me use rB1 = [(n/8) - (n/16) + 1, n/4] (upper tail) and rB2 = [-(n/4), (n/8) - (n/16)] (Atypical).
    -- For rB1 (small r-range, upper tail of bin): use symmetry. The k = r + n/2 ranges over
    -- [n/2 + (n/8) - (n/16) + 1, n/2 + n/4]. Reflect k → n - k: [n/2 - n/4, n/2 - (n/8) + (n/16) - 1] = [n/4, 3n/8 + (n/16) - 1].
    -- This is r' = k' - n/2 = -r, so r' ranges in [-(n/4), -(n/8) + (n/16) - 1] ⊆ [-(n/4), -(n/16) - 1].
    -- Hmm wait: -(n/8) + (n/16) - 1 vs -(n/16) - 1. We have -(n/8) + (n/16) ≤ -(n/16) (i.e. n/8 ≥ 2(n/16) = 2n/16, which is ≤ n/8).
    -- Yes -(n/8) + (n/16) ≤ -(n/16), so r' ∈ [-(n/4), -(n/16) - 1] (subset). But CentralBinomialLowerTailWide gives bound on this r' range.
    -- So sum over rB1 of B1(r) = sum over r' (via reflection) ≤ sum over r' ∈ [-(n/4), -(n/16) - 1] = exp(-n/128).
    --
    -- Now use CentralBinomialUpperTailWide for rB1, AtypicalZPlusTailBound for rB2.
    -- rB1 = Icc((n/16) + 1, n/4): bound inner sum by 1, then ∑ B1 ≤ exp(-n/128) by CentralBinomialUpperTailWide.
    -- rB2 = Icc(-n/4, n/16): bound inner sum by exp(-n/128) via AtypicalZPlusTailBound (since n/16 ≤ (n/8)-(n/16)).
    have h_rB_b1_nn : ∀ r,
        0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) := fun r =>
      HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    -- Bound rB1 part
    have h_rB1_inner_le_one : ∀ r ∈ rB1,
        (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ 1 := by
      intros r _
      exact HeavyAtypicalBoundProof7.sum_binPMFInt_range_le_one _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_rB1_inner_nn : ∀ r ∈ rB1,
        0 ≤ (∑ zPlus ∈ Finset.range (n / 16),
              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) := by
      intros r _
      apply Finset.sum_nonneg
      intros _ _
      exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' _ (1-δ) h_one_minus_δ_nn h_one_minus_δ_le _
    have h_rB1_le : (∑ r ∈ rB1,
                      binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                      (∑ zPlus ∈ Finset.range (n / 16),
                        binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                  ≤ (∑ r ∈ rB1, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) := by
      apply Finset.sum_le_sum
      intros r hr
      have h1 : 0 ≤ binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) := h_rB_b1_nn r
      have h2 := h_rB1_inner_le_one r hr
      nlinarith [h_rB1_inner_nn r hr, h_rB_b1_nn r]
    have h_central_upper_tail := CentralBinomialUpperTailWideHalf n hn hn8
    have h_rB1_total_le : (∑ r ∈ rB1, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                        ≤ Real.exp (-((n : ℝ) / 128)) := by
      simp only [hrB1_def]
      exact h_central_upper_tail
    have h_rB1_part_le : (∑ r ∈ rB1,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zPlus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                      ≤ Real.exp (-((n : ℝ) / 128)) := by linarith
    -- Bound rB2 part: ≤ ∑_r B1(r) · exp(-n/128) ≤ 1 · exp(-n/128)
    have h_rB2_inner_le : ∀ r ∈ rB2,
        (∑ zPlus ∈ Finset.range (n / 16),
          binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus) ≤ Real.exp (-((n : ℝ) / 128)) := by
      intros r hr
      rw [hrB2_def] at hr
      rw [Finset.mem_Icc] at hr
      have hr_lb : -((n : ℤ) / 4) ≤ r := hr.1
      have hr_ub : r ≤ (n : ℤ) / 16 := hr.2
      -- Apply AtypicalZPlusTailBound: needs -(n/4) ≤ r ≤ (n/8) - (n/16)
      -- We need: r ≤ (n/16) ≤ (n/8) - (n/16). Since (n/8) ≥ 2(n/16), this holds.
      have h_ub_target : r ≤ ((n : ℤ) / 8) - ((n : ℤ) / 16) := by
        have hn_int : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n8_int : (0 : ℤ) ≤ (n : ℤ) / 8 := by omega
        have h_2n16_le_n8 : 2 * ((n : ℤ) / 16) ≤ (n : ℤ) / 8 := by omega
        omega
      exact AtypicalZPlusTailBound n hn hn8 δ hδ_pos hδ_ub r hr_lb h_ub_target
    -- Now: ∑_{r ∈ rB2} B1(r) · (inner) ≤ ∑_{r ∈ rB2} B1(r) · exp(-n/128)
    have h_rB2_le_step : (∑ r ∈ rB2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            (∑ zPlus ∈ Finset.range (n / 16),
                              binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                      ≤ (∑ r ∈ rB2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            Real.exp (-((n : ℝ) / 128))) := by
      apply Finset.sum_le_sum
      intros r hr
      apply mul_le_mul_of_nonneg_left
      · exact h_rB2_inner_le r hr
      · exact h_rB_b1_nn r
    have h_rB2_factored : (∑ r ∈ rB2,
                            binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                            Real.exp (-((n : ℝ) / 128)))
                      = (∑ r ∈ rB2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                        * Real.exp (-((n : ℝ) / 128)) := by
      rw [Finset.sum_mul]
    rw [h_rB2_factored] at h_rB2_le_step
    -- Bound ∑_{r ∈ rB2} B1(r) ≤ 1
    have h_b1_sum_rB2_le_one : (∑ r ∈ rB2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) ≤ 1 := by
      -- New first factor: Binomial(n/2). Substitute k = r + n/4; for r ∈ rB2 = [-(n/4), n/16],
      -- k ∈ [0, n/16 + n/4] ⊆ [0, n/2]. Bound by the full Binomial(n/2) sum over range (n/2 + 1) ≤ 1.
      have hn_cast2 : ((n / 2 : ℕ) : ℤ) = (n : ℤ) / 2 := by
        omega
      have h_inj : Set.InjOn (fun (r : ℤ) => (r + ((n : ℤ) / 4)).toNat) (rB2 : Set ℤ) := by
        intros r1 hr1 r2 hr2 h_eq
        rw [Finset.mem_coe, hrB2_def, Finset.mem_Icc] at hr1 hr2
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n4 : (0 : ℤ) ≤ (n : ℤ) / 4 := hn4_int
        have hr1_plus_nn : 0 ≤ r1 + ((n : ℤ) / 4) := by linarith [hr1.1]
        have hr2_plus_nn : 0 ≤ r2 + ((n : ℤ) / 4) := by linarith [hr2.1]
        simp only at h_eq
        have hh : ((r1 + ((n : ℤ) / 4)).toNat : ℤ) = ((r2 + ((n : ℤ) / 4)).toNat : ℤ) := by
          exact_mod_cast h_eq
        rw [Int.toNat_of_nonneg hr1_plus_nn, Int.toNat_of_nonneg hr2_plus_nn] at hh
        linarith
      have h_eq_via_image : (∑ r ∈ rB2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)))
                          = (∑ k ∈ rB2.image (fun (r : ℤ) => (r + ((n : ℤ) / 4)).toNat),
                              binPMFInt (n/2) (1/2) (k : ℤ)) := by
        rw [Finset.sum_image (fun r1 hr1 r2 hr2 h_eq => h_inj hr1 hr2 h_eq)]
        apply Finset.sum_congr rfl
        intros r hr
        rw [hrB2_def, Finset.mem_Icc] at hr
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have hr_plus_nn : 0 ≤ r + ((n : ℤ) / 4) := by linarith [hr.1]
        rw [Int.toNat_of_nonneg hr_plus_nn]
      rw [h_eq_via_image]
      apply le_trans _ (HeavyAtypicalBoundProof7.sum_binPMFInt_range_le_one (n/2) (1/2)
        (by norm_num) (by norm_num) (n/2 + 1))
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intros k hk
        rw [Finset.mem_image] at hk
        obtain ⟨r, hr_in, hr_eq⟩ := hk
        rw [hrB2_def, Finset.mem_Icc] at hr_in
        rw [Finset.mem_range]
        have hn_int_nn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
        have h_n4_nn : (0 : ℤ) ≤ (n : ℤ) / 4 := hn4_int
        have h_k_ub : (k : ℤ) ≤ (n : ℤ) / 2 := by
          have hr_plus_nn : 0 ≤ r + ((n : ℤ) / 4) := by linarith [hr_in.1]
          -- r ≤ n/16 and n/16 + n/4 ≤ n/2
          have h_n16_n4_le : (n : ℤ) / 16 + (n : ℤ) / 4 ≤ (n : ℤ) / 2 := by omega
          have hr_plus_ub : r + ((n : ℤ) / 4) ≤ (n : ℤ) / 2 := by linarith [hr_in.2]
          rw [← hr_eq]
          rw [Int.toNat_of_nonneg hr_plus_nn]
          exact hr_plus_ub
        have h_k_ub_nat : (k : ℤ) ≤ ((n / 2 : ℕ) : ℤ) := by rw [hn_cast2]; exact h_k_ub
        have : k ≤ n / 2 := by exact_mod_cast h_k_ub_nat
        omega
      · intros k _ _
        exact HeavyAtypicalBoundProof7.binPMFInt_nonneg' (n/2) (1/2) (by norm_num) (by norm_num) _
    have h_exp_nn : (0 : ℝ) ≤ Real.exp (-((n : ℝ) / 128)) := (Real.exp_pos _).le
    have h_rB2_part_le : (∑ r ∈ rB2,
                          binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4)) *
                          (∑ zPlus ∈ Finset.range (n / 16),
                            binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus))
                      ≤ Real.exp (-((n : ℝ) / 128)) := by
      have h_step1 := h_rB2_le_step
      have h_step2 : (∑ r ∈ rB2, binPMFInt (n/2) (1/2) (r + ((n : ℤ) / 4))) *
                      Real.exp (-((n : ℝ) / 128))
                  ≤ 1 * Real.exp (-((n : ℝ) / 128)) := by
        apply mul_le_mul_of_nonneg_right h_b1_sum_rB2_le_one h_exp_nn
      linarith
    linarith
  -- Combine Piece A and Piece B bounds.
  -- T_II = ∑_ℓ (Piece_A_ℓ + Piece_B_ℓ) ≤ |P_H| · (2 exp(-n/128) + 2 exp(-n/128)) = 4|P_H| exp(-n/128)
  -- ≤ 4 n exp(√n/2) exp(-n/128) ≤ (1/8) exp(-√n/4) by numeric_final.
  have h_T_II_le : (∑ x ∈ P_H_full,
                      ((∑ zMinus ∈ Finset.range (n / 16),
                          ∑ zPlus ∈ Finset.range (n / 2 + 1),
                            |altRSum n δ α zMinus zPlus x|) +
                       (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                          ∑ zPlus ∈ Finset.range (n / 16),
                            |altRSum n δ α zMinus zPlus x|)))
                  ≤ (P_H_full.card : ℝ) * (2 * Real.exp (-((n : ℝ) / 128))
                                              + 2 * Real.exp (-((n : ℝ) / 128))) := by
    have h_constant_eq : (∑ _ ∈ P_H_full,
                          (2 * Real.exp (-((n : ℝ) / 128))
                            + 2 * Real.exp (-((n : ℝ) / 128))))
                      = (P_H_full.card : ℝ) * (2 * Real.exp (-((n : ℝ) / 128))
                                                + 2 * Real.exp (-((n : ℝ) / 128))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [← h_constant_eq]
    apply Finset.sum_le_sum
    intros ℓ _
    have hA := pieceA_bound_per_ell ℓ
    have hB := pieceB_bound_per_ell ℓ
    have hA' := hA.trans rRangeA_bound
    have hB' := hB.trans rRangeB_bound
    linarith
  -- Final numeric bound
  refine h_T_II_le.trans ?_
  -- (P_H_full.card : ℝ) ≤ n * exp(√n/2)
  -- 2*e + 2*e = 4*e where e = exp(-n/128)
  have h_4 : (2 * Real.exp (-((n : ℝ) / 128))
                + 2 * Real.exp (-((n : ℝ) / 128)))
            = 4 * Real.exp (-((n : ℝ) / 128)) := by ring
  rw [h_4]
  have h_factor_nn : (0 : ℝ) ≤ 4 * Real.exp (-((n : ℝ) / 128)) := by
    apply mul_nonneg (by norm_num) (Real.exp_pos _).le
  have h_step1 : (P_H_full.card : ℝ) * (4 * Real.exp (-((n : ℝ) / 128)))
                ≤ ((n : ℝ) * Real.exp (Real.sqrt n / 2)) *
                  (4 * Real.exp (-((n : ℝ) / 128))) := by
    apply mul_le_mul_of_nonneg_right h_card_PH h_factor_nn
  refine h_step1.trans ?_
  rw [show ((n : ℝ) * Real.exp (Real.sqrt n / 2)) * (4 * Real.exp (-((n : ℝ) / 128)))
        = 4 * (n : ℝ) * Real.exp (Real.sqrt n / 2) * Real.exp (-((n : ℝ) / 128)) from by ring]
  exact HeavyAtypicalBoundProof7.numeric_final n hn
