import Mathlib
import Workspace.Types.DelProb
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.AltSumThreeWayDecomposition
import Workspace.ProofLemmas.HeavyTypicalBound
import Workspace.ProofLemmas.HeavyAtypicalBound
import Workspace.ProofLemmas.LightContributionBound

set_option maxHeartbeats 4000000

open Classical

theorem AlternatingSumWitnessBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
      ∀ (δ : ℝ), (320 : ℝ) / Real.sqrt n ≤ δ → δ ≤ 1 / 2 →
      (4 : ℝ) * Workspace.Types.AlternatingSumExpression.altSum n δ
          ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n)
        + Real.exp (-(n : ℝ) / 512)
        + Real.exp (-((1 : ℝ) / 2 * Real.sqrt n))
      ≤ Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) := by
  intro n hn hmod δ hδ_lb hδ_ub
  -- Apply the three-way decomposition.
  have h_decomp := AltSumThreeWayDecomposition n hn hmod δ hδ_lb hδ_ub
  simp only at h_decomp
  -- Apply the three sub-lemma bounds.
  have h_HT := HeavyTypicalBound n hn hmod δ hδ_lb hδ_ub
  simp only at h_HT
  have h_HA := HeavyAtypicalBound n hn hmod δ hδ_lb hδ_ub
  simp only at h_HA
  have h_LC := LightContributionBound n hn hmod δ hδ_lb hδ_ub
  simp only at h_LC
  -- The HeavyTypicalBound uses a nested-filter form for P_H; convert via filter_filter.
  -- We'll just sumbind all the bounds.
  -- Step: rewrite altSum as T_I + T_II + T_III using h_decomp.
  rw [h_decomp]
  -- Goal: T_I_3way + T_II_3way + T_III_3way + exp(-√n/2) ≤ exp(-√n/4)
  -- We want: T_I_3way ≤ 1/4 · exp(-√n/4) (use h_HT after converting P_H form)
  --         T_II_3way ≤ 1/8 · exp(-√n/4) (use h_HA)
  --         T_III_3way ≤ 1/8 · exp(-√n/4) (use h_LC)
  --         exp(-√n/2) ≤ 1/2 · exp(-√n/4) (slack bound)
  -- First convert HeavyTypicalBound's P_H to match AltSumThreeWayDecomposition's P_H form.
  -- HT's P_H = (powerset.filter sameParity).filter (∃ r, ...)
  -- 3way's P_H = powerset.filter (sameParity ∧ ∃ r, ...)
  -- These are equal by Finset.filter_filter.
  have h_PH_eq :
      (((Finset.Icc 1 (n / 2)).powerset).filter
        (Workspace.Types.AlternatingSumExpression.sameParity)).filter
        (fun ℓ =>
          ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            Real.exp (-(Real.sqrt n / 2)) ≤
              ∏ j ∈ Finset.Icc 1 (n / 2),
                (if j ∈ ℓ then
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
                    Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
                      (r + ((n : ℤ) / 4) + (j : ℤ))
                 else
                  (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
                    Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
                      (r + ((n : ℤ) / 4) + (j : ℤ)))))
      =
      ((Finset.Icc 1 (n / 2)).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∃ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            Real.exp (-(Real.sqrt n / 2)) ≤
              ∏ j ∈ Finset.Icc 1 (n / 2),
                (if j ∈ ℓ then
                  ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
                    Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
                      (r + ((n : ℤ) / 4) + (j : ℤ))
                 else
                  (1 - ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) *
                    Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
                      (r + ((n : ℤ) / 4) + (j : ℤ))))) := by
    rw [Finset.filter_filter]
  rw [h_PH_eq] at h_HT
  -- Now h_HT bounds the same T_I as h_decomp.
  have hsqrtn_ge : (10 : ℝ) ^ 6 ≤ Real.sqrt n := by
    have h1 : ((10 : ℕ) ^ 12 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : Real.sqrt ((10 : ℕ) ^ 12 : ℝ) ≤ Real.sqrt n :=
      Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt ((10 : ℕ) ^ 12 : ℝ) = (10 : ℝ) ^ 6 := by
      rw [show ((10 : ℕ) ^ 12 : ℝ) = ((10 : ℝ) ^ 6) ^ 2 by norm_num]
      exact Real.sqrt_sq (by positivity)
    linarith [h2, h3.symm.le]
  have hsqrtn_pos : 0 < Real.sqrt n := by
    have : (10 : ℝ) ^ 6 ≤ Real.sqrt n := hsqrtn_ge
    have : (0 : ℝ) < (10 : ℝ) ^ 6 := by norm_num
    linarith
  -- Convert h_HT, h_HA bounds: they use Real.sqrt n / 4, we need 1/4 · Real.sqrt n.
  -- (F88: h_LC now outputs exp(-√n/64), so it is converted separately below.)
  have h_eq1 : Real.sqrt n / 4 = (1 : ℝ) / 4 * Real.sqrt n := by ring
  rw [h_eq1] at h_HT h_HA
  have h_eq64 : Real.sqrt n / 64 = (1 : ℝ) / 64 * Real.sqrt n := by ring
  rw [h_eq64] at h_LC
  -- Common output envelope E64 = exp(-√n/64), and the Heavy envelope E4 = exp(-√n/4).
  set E4 : ℝ := Real.exp (-((1 : ℝ) / 4 * Real.sqrt n)) with hE4_def
  set E64 : ℝ := Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) with hE64_def
  have hE4_pos : 0 < E4 := Real.exp_pos _
  have hE64_pos : 0 < E64 := Real.exp_pos _
  -- √n ≥ 10^6 facts reused below.
  have hsqrt_sq : Real.sqrt n ^ 2 = (n : ℝ) := by
    rw [Real.sq_sqrt]; positivity
  -- altSum is a sum of |·| terms, hence nonnegative.
  have h_altSum_nonneg :
      (0 : ℝ) ≤ Workspace.Types.AlternatingSumExpression.altSum n δ
        ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n) := by
    unfold Workspace.Types.AlternatingSumExpression.altSum
    apply Finset.sum_nonneg
    intro k _
    unfold Workspace.Types.AlternatingSumExpression.innerSumOverEll
    apply Finset.sum_nonneg; intro ℓ _
    apply Finset.sum_nonneg; intro zMinus _
    apply Finset.sum_nonneg; intro zPlus _
    exact abs_nonneg _
  -- ── Reduce every Heavy/slack term to a fraction of E64 (the output envelope). ──
  -- Heavy: E4 = exp(-√n/4) ≤ (1/8)·E64.  Need 8·exp(-√n/4) ≤ exp(-√n/64), i.e. 8 ≤ exp(√n·15/64).
  have h_E4_le_E64 : (8 : ℝ) * E4 ≤ E64 := by
    rw [hE4_def, hE64_def]
    have h_ratio : Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) =
        Real.exp ((15 : ℝ) / 64 * Real.sqrt n) *
          Real.exp (-((1 : ℝ) / 4 * Real.sqrt n)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h_ratio]
    have h_pos4 : 0 < Real.exp (-((1 : ℝ) / 4 * Real.sqrt n)) := Real.exp_pos _
    have h_8_le : (8 : ℝ) ≤ Real.exp ((15 : ℝ) / 64 * Real.sqrt n) := by
      have h_log8_lt : Real.log 8 < 7 := by
        have := Real.log_two_lt_d9
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; linarith
      have h_arg_large : Real.log 8 ≤ (15 : ℝ) / 64 * Real.sqrt n := by
        have h_sqrt_ge : (10 : ℝ) ^ 6 ≤ Real.sqrt n := hsqrtn_ge
        nlinarith
      have := Real.exp_log (show (0 : ℝ) < 8 by norm_num)
      calc (8 : ℝ) = Real.exp (Real.log 8) := this.symm
        _ ≤ Real.exp ((15 : ℝ) / 64 * Real.sqrt n) := Real.exp_le_exp.mpr h_arg_large
    nlinarith [h_8_le, h_pos4]
  -- slack exp(-n/512) ≤ (1/8)·E64.  Need 8·exp(-n/512) ≤ exp(-√n/64), i.e. 8 ≤ exp(n/512 - √n/64).
  have h_En8_le_E64 : (8 : ℝ) * Real.exp (-(n : ℝ) / 512) ≤ E64 := by
    rw [hE64_def]
    have h_ratio : Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) =
        Real.exp ((n : ℝ) / 512 - (1 : ℝ) / 64 * Real.sqrt n) *
          Real.exp (-(n : ℝ) / 512) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h_ratio]
    have h_pos : 0 < Real.exp (-(n : ℝ) / 512) := Real.exp_pos _
    have h_8_le : (8 : ℝ) ≤ Real.exp ((n : ℝ) / 512 - (1 : ℝ) / 64 * Real.sqrt n) := by
      have h_log8_lt : Real.log 8 < 7 := by
        have := Real.log_two_lt_d9
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; linarith
      have h_arg_large : Real.log 8 ≤ (n : ℝ) / 512 - (1 : ℝ) / 64 * Real.sqrt n := by
        have h_sqrt_ge : (10 : ℝ) ^ 6 ≤ Real.sqrt n := hsqrtn_ge
        -- n/512 - √n/64 = (√n)²/512 - √n/64 ≥ huge (since √n ≥ 10^6).
        nlinarith [hsqrt_sq, hsqrtn_pos, h_sqrt_ge]
      have := Real.exp_log (show (0 : ℝ) < 8 by norm_num)
      calc (8 : ℝ) = Real.exp (Real.log 8) := this.symm
        _ ≤ Real.exp ((n : ℝ) / 512 - (1 : ℝ) / 64 * Real.sqrt n) := Real.exp_le_exp.mpr h_arg_large
    nlinarith [h_8_le, h_pos]
  -- slack exp(-√n/2) ≤ (1/8)·E64.  Need 8·exp(-√n/2) ≤ exp(-√n/64), i.e. 8 ≤ exp(√n·31/64).
  have h_E2_le_E64 : (8 : ℝ) * Real.exp (-((1 : ℝ) / 2 * Real.sqrt n)) ≤ E64 := by
    rw [hE64_def]
    have h_ratio : Real.exp (-((1 : ℝ) / 64 * Real.sqrt n)) =
        Real.exp ((31 : ℝ) / 64 * Real.sqrt n) *
          Real.exp (-((1 : ℝ) / 2 * Real.sqrt n)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h_ratio]
    have h_pos : 0 < Real.exp (-((1 : ℝ) / 2 * Real.sqrt n)) := Real.exp_pos _
    have h_8_le : (8 : ℝ) ≤ Real.exp ((31 : ℝ) / 64 * Real.sqrt n) := by
      have h_log8_lt : Real.log 8 < 7 := by
        have := Real.log_two_lt_d9
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; linarith
      have h_arg_large : Real.log 8 ≤ (31 : ℝ) / 64 * Real.sqrt n := by
        have h_sqrt_ge : (10 : ℝ) ^ 6 ≤ Real.sqrt n := hsqrtn_ge
        nlinarith
      have := Real.exp_log (show (0 : ℝ) < 8 by norm_num)
      calc (8 : ℝ) = Real.exp (Real.log 8) := this.symm
        _ ≤ Real.exp ((31 : ℝ) / 64 * Real.sqrt n) := Real.exp_le_exp.mpr h_arg_large
    nlinarith [h_8_le, h_pos]
  -- 4·T_III ≤ (1/2)·E64  (from h_LC : T_III ≤ (1/8)·E64).
  -- Assemble: 4·(T_I+T_II+T_III) + exp(-n/512) + exp(-√n/2)
  --   ≤ 4·(1/4)·E4 + 4·(1/8)·E4 + 4·(1/8)·E64 + (1/8)E64 + (1/8)E64
  --   = (3/2)·E4 + (1/2)·E64 + (1/4)·E64
  --   ≤ (3/16)·E64 + (3/4)·E64 ≤ E64 = exp(-√n/64).
  linarith [h_HT, h_HA, h_LC, h_E4_le_E64, h_En8_le_E64, h_E2_le_E64,
            h_altSum_nonneg, hE4_pos, hE64_pos]
