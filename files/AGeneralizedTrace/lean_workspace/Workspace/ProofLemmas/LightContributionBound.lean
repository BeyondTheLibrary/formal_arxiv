import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.SublemmaPerSummandBoundEnvelope
import Workspace.ProofLemmas.LightEnvelopeBound
import Workspace.PriorWork.AltRSumLightAtypicalBound

set_option maxHeartbeats 4000000

open Classical

theorem LightContributionBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), (320 : ℝ) / Real.sqrt n ≤ δ → δ ≤ 1 / 2 →
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
      let P_L : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)))
      ∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|
        ≤ (1 : ℝ) / 8 * Real.exp (-(Real.sqrt n / 64)) := by
  intro n hn hmod δ hδ_lb hδ_ub
  -- Unfold all let-bindings
  simp only
  set c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)) with hc'_def
  set α : ℝ := c' * Real.sqrt n with hα_def
  set n_h : ℕ := n / 2 with hn_h_def
  -- Define the helpers
  set S_er : ℤ → ℕ → ℝ := fun r j =>
        α * Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
            (r + ((n : ℤ) / 4) + (j : ℤ)) with hS_er_def
  set widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
        ∏ j ∈ Finset.Icc 1 (n / 2),
          (if j ∈ x then S_er r j else (1 - S_er r j)) with hwidetildeMu_def
  set envelopeW : Finset ℕ → ℝ := fun ℓ =>
        ∑ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          ∏ j ∈ ℓ,
            Workspace.Types.AlternatingSumExpression.ellFactor n α r (j - 1) with henvelopeW_def
  set P_L : Finset (Finset ℕ) :=
        ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
          Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
          ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
            widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2))) with hP_L_def
  -- positivity facts
  have h_sqrt_n_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have h_n_pos : (0 : ℝ) < n := by
    have h1 : (10 ^ 12 : ℕ) ≤ n := hn
    have h2 : (0 : ℕ) < n := Nat.lt_of_lt_of_le (by norm_num : (0 : ℕ) < 10 ^ 12) h1
    exact_mod_cast h2
  have hn_ge : (10 ^ 12 : ℝ) ≤ n := by exact_mod_cast hn
  have h_sqrt_n_ge : (10 ^ 6 : ℝ) ≤ Real.sqrt n := by
    have h_sq : (10 ^ 6 : ℝ) ^ 2 ≤ (n : ℝ) := by
      have : ((10 : ℝ) ^ 6) ^ 2 = 10 ^ 12 := by ring
      rw [this]; exact hn_ge
    have h_pos : (0 : ℝ) ≤ 10 ^ 6 := by norm_num
    calc (10 ^ 6 : ℝ) = Real.sqrt ((10 ^ 6) ^ 2) := by
            rw [Real.sqrt_sq h_pos]
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt h_sq
  -- n/16 ≤ n/2+1 (for the inner Ico-split).
  have h_n16_le : n / 16 ≤ n / 2 + 1 := by
    have h1 : n / 16 ≤ n / 2 := Nat.div_le_div_left (by norm_num) (by norm_num)
    omega
  -- Per-ℓ rebracketing of the full inner z-double-sum into typical + atypical.
  have h_inner_decomp : ∀ ℓ : Finset ℕ,
      (∑ zMinus ∈ Finset.range (n / 2 + 1),
          ∑ zPlus ∈ Finset.range (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          +
          ((∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            +
           (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)) := by
    intro ℓ
    simp only [Finset.range_eq_Ico]
    rw [← Finset.sum_Ico_consecutive (fun zMinus =>
          ∑ zPlus ∈ Finset.Ico 0 (n / 2 + 1),
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          (Nat.zero_le _) h_n16_le]
    have h_inner_split :
        (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico 0 (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          = (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                ∑ zPlus ∈ Finset.Ico 0 (n / 16),
                  |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            + (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro zMinus _
      rw [← Finset.sum_Ico_consecutive (fun zPlus =>
            |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            (Nat.zero_le _) h_n16_le]
    rw [h_inner_split]
    ring
  -- Sum the rebracketing over ℓ ∈ P_L:
  have h_split_sum :
      (∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.range (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        = (∑ ℓ ∈ P_L,
              ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          + (∑ ℓ ∈ P_L,
              ((∑ zMinus ∈ Finset.range (n / 16),
                  ∑ zPlus ∈ Finset.range (n / 2 + 1),
                    |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
                +
               (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
                  ∑ zPlus ∈ Finset.range (n / 16),
                    |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ℓ _
    exact h_inner_decomp ℓ
  rw [h_split_sum]
  -- ===== TYPICAL PART (HONEST envelope route, F88) =====
  -- Per-ℓ honest bound: ∑_{z typ}|altRSum| ≤ √(2/(πn))·envelopeW(ℓ).
  have hPerSummand := Workspace.ProofLemmas.SublemmaPerSummandBoundEnvelope n hn hmod δ hδ_lb hδ_ub
  simp only at hPerSummand
  -- Envelope mass bound: ∑_{ℓ∈P_L} envelopeW(ℓ) ≤ n·e^{-√n/32}.
  have hLightEnv := LightEnvelopeBound n hn hmod
  simp only at hLightEnv
  -- subset / sameParity properties of P_L
  have h_PL_subset : ∀ ℓ ∈ P_L, ℓ ⊆ Finset.Icc 1 (n / 2) := by
    intro ℓ hℓ
    rw [hP_L_def] at hℓ
    simp only [Finset.mem_filter, Finset.mem_powerset] at hℓ
    exact hℓ.1
  have h_PL_sameParity : ∀ ℓ ∈ P_L,
      Workspace.Types.AlternatingSumExpression.sameParity ℓ := by
    intro ℓ hℓ
    rw [hP_L_def] at hℓ
    simp only [Finset.mem_filter, Finset.mem_powerset] at hℓ
    exact hℓ.2.1
  -- √(2/(πn)) ≥ 0.
  set sq : ℝ := Real.sqrt (2 / (Real.pi * (n / 2 : ℕ))) with hsq_def
  have hsq_nn : (0 : ℝ) ≤ sq := Real.sqrt_nonneg _
  -- Step 1: ∑_ℓ ∑_{z typ}|altRSum| ≤ ∑_ℓ √(2/(πn))·envelopeW(ℓ) = √(2/(πn))·(∑_ℓ envelopeW).
  have h_typ_step1 :
      (∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        ≤ ∑ ℓ ∈ P_L, sq * envelopeW ℓ := by
    apply Finset.sum_le_sum
    intro ℓ hℓ
    exact hPerSummand ℓ (h_PL_subset ℓ hℓ) (h_PL_sameParity ℓ hℓ)
  have h_factor :
      ∑ ℓ ∈ P_L, sq * envelopeW ℓ = sq * (∑ ℓ ∈ P_L, envelopeW ℓ) := by
    rw [Finset.mul_sum]
  -- √(2/(πn)) ≤ √n  (since 2/(πn) ≤ n ⟺ 2 ≤ π n², true).
  have hsq_le_sqrtn : sq ≤ Real.sqrt n := by
    rw [hsq_def]
    apply Real.sqrt_le_sqrt
    have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
    have hnh1 : (1 : ℕ) ≤ n / 2 := by omega
    have hnh1' : (1 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hnh1
    have hnh_pos : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by linarith
    rw [div_le_iff₀ (by positivity)]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by nlinarith [hn_ge]
    have hpi_pos : (0 : ℝ) < Real.pi := by linarith
    nlinarith [h_n_pos, hn_ge, hpi, hn1, hnh1', hnh_pos, hpi_pos,
      mul_pos h_n_pos hnh_pos, mul_pos (mul_pos h_n_pos hpi_pos) hnh_pos,
      mul_le_mul (le_of_lt hpi) hnh1' (by norm_num) hpi_pos.le]
  -- Typical numeric assembly: √(2/(πn))·(∑env)·  ≤ (1/16) e^{-√n/64}.
  have h_typical_bound :
      (∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64)) := by
    -- Step A: ≤ √(2/(πn))·(n·e^{-√n/32})  ≤ √n·n·e^{-√n/32}.
    have hstepA : (∑ ℓ ∈ P_L,
          ∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
        ≤ sq * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32))) := by
      calc _ ≤ ∑ ℓ ∈ P_L, sq * envelopeW ℓ := h_typ_step1
        _ = sq * (∑ ℓ ∈ P_L, envelopeW ℓ) := h_factor
        _ ≤ sq * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32))) :=
            mul_le_mul_of_nonneg_left hLightEnv hsq_nn
    -- Step B: sq·(n·e^{-√n/32}) ≤ √n·(n·e^{-√n/32}) ≤ √n·n·e^{-√n/32}.
    have hne_nn : (0 : ℝ) ≤ (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := by positivity
    have hstepB : sq * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32)))
        ≤ Real.sqrt n * (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := by
      have := mul_le_mul_of_nonneg_right hsq_le_sqrtn hne_nn
      calc sq * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32)))
          ≤ Real.sqrt n * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32))) := this
        _ = Real.sqrt n * (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := by ring
    -- Step C: √n·n·e^{-√n/32} ≤ (1/16) e^{-√n/64}.
    --   ⟺ 16·√n·n ≤ e^{√n/64}.  With n = (√n)², √n·n = (√n)³.
    have hfinal : Real.sqrt n * (n : ℝ) * Real.exp (-(Real.sqrt n / 32))
        ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64)) := by
      rw [show (1:ℝ)/16 * Real.exp (-(Real.sqrt n / 64))
              = Real.exp (-(Real.sqrt n / 64)) / 16 from by ring]
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      have h_eq : -(Real.sqrt n / 64)
          = (-(Real.sqrt n / 32)) + (Real.sqrt n / 64) := by ring
      rw [h_eq, Real.exp_add (-(Real.sqrt n / 32)) (Real.sqrt n / 64)]
      have hexp_neg_pos : 0 < Real.exp (-(Real.sqrt n / 32)) := Real.exp_pos _
      set t : ℝ := Real.sqrt n with ht_def
      have h_n_eq : (n:ℝ) = t^2 := by rw [ht_def, pow_two, Real.mul_self_sqrt h_n_pos.le]
      have ht_pos : (0:ℝ) < t := by rw [ht_def]; exact Real.sqrt_pos.mpr h_n_pos
      have ht_ge : (10:ℝ)^6 ≤ t := by rw [ht_def]; exact h_sqrt_n_ge
      -- Need: t·t²·e^{-t/32}·16 ≤ e^{-t/32}·e^{t/64}, i.e. 16·t³ ≤ e^{t/64}.
      rw [h_n_eq]
      have hexp_split : Real.exp (-(t / 32)) * Real.exp (t / 64)
          = Real.exp (-(t / 32)) * Real.exp (t / 64) := rfl
      -- 16·t³ ≤ e^{t/64}.
      have h_main : (16 : ℝ) * t^3 ≤ Real.exp (t / 64) := by
        set y : ℝ := t / 64 with hy_def
        have h_y_nonneg : 0 ≤ y := by rw [hy_def]; positivity
        have h_cubic : y ^ 7 / (Nat.factorial 7 : ℝ) ≤ Real.exp y :=
          Real.pow_div_factorial_le_exp y h_y_nonneg 7
        have h_fact7 : (Nat.factorial 7 : ℝ) = 5040 := by norm_num [Nat.factorial]
        rw [h_fact7] at h_cubic
        have ht3 : (10:ℝ)^18 ≤ t^3 := by
          calc (10:ℝ)^18 = ((10:ℝ)^6)^3 := by ring
            _ ≤ t^3 := by gcongr
        have h_intermediate : (16 : ℝ) * t^3 ≤ y ^ 7 / 5040 := by
          rw [hy_def]
          nlinarith [ht3, ht_pos, pow_pos ht_pos 3, pow_pos ht_pos 7,
            pow_pos ht_pos 4, mul_pos (pow_pos ht_pos 3) (pow_pos ht_pos 4)]
        linarith [h_cubic, h_intermediate]
      -- Assemble: t·(t²)·e^{-t/32}·16 ≤ e^{-t/32}·e^{t/64}.
      calc t * t ^ 2 * Real.exp (-(t / 32)) * 16
          = (16 * t^3) * Real.exp (-(t / 32)) := by ring
        _ ≤ Real.exp (t / 64) * Real.exp (-(t / 32)) :=
            mul_le_mul_of_nonneg_right h_main hexp_neg_pos.le
        _ = Real.exp (-(t / 32)) * Real.exp (t / 64) := by ring
    calc _ ≤ sq * ((n : ℝ) * Real.exp (-(Real.sqrt n / 32))) := hstepA
      _ ≤ Real.sqrt n * (n : ℝ) * Real.exp (-(Real.sqrt n / 32)) := hstepB
      _ ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64)) := hfinal
  -- ===== ATYPICAL PART =====
  -- Atypical light bound gives (1/16)·e^{-√n/4}, which is ≤ (1/16)·e^{-√n/64}.
  have h_atypical_bound :
      (∑ ℓ ∈ P_L,
          ((∑ zMinus ∈ Finset.range (n / 16),
              ∑ zPlus ∈ Finset.range (n / 2 + 1),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
            +
           (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
              ∑ zPlus ∈ Finset.range (n / 16),
                |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)))
        ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64)) := by
    have hat := AltRSumLightAtypicalBound n hn hmod δ hδ_lb hδ_ub
    simp only at hat
    -- relax e^{-√n/4} ≤ e^{-√n/64}.
    have hrelax : (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 4))
        ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have : (0 : ℝ) ≤ Real.sqrt n := h_sqrt_n_nonneg
      linarith [this]
    exact hat.trans hrelax
  -- Assemble: typical + atypical ≤ (1/16 + 1/16) e^{-√n/64} = (1/8) e^{-√n/64}.
  have h_final_eq : (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64))
      + (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 64))
      = (1 : ℝ) / 8 * Real.exp (-(Real.sqrt n / 64)) := by ring
  linarith [h_typical_bound, h_atypical_bound, h_final_eq]
