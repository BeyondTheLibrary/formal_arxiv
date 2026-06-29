import Mathlib

open Real

theorem PinskerTwoPointBound :
    ∀ (p q : ℝ), 0 < p → p < 1 → 0 < q → q < 1 →
      (p - q) ^ 2 ≤
        (1 / 2) * (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q))) := by
  intro p q hp0 hp1 hq0 hq1
  -- Define F t := t * log(t/q) + (1-t) * log((1-t)/(1-q)) - 2*(t-q)^2
  set F : ℝ → ℝ :=
    fun t => t * Real.log (t / q) + (1 - t) * Real.log ((1 - t) / (1 - q))
              - 2 * (t - q) ^ 2 with hFdef
  -- The goal rearranges to F p ≥ 0
  suffices h : F p ≥ 0 by
    simp only [hFdef, ge_iff_le, sub_nonneg] at h
    linarith
  -- Define F' (the derivative function):
  set F' : ℝ → ℝ :=
    fun t => Real.log t - Real.log q - Real.log (1 - t) + Real.log (1 - q) - 4 * (t - q) with hF'def
  -- Define F'' (the second derivative function):
  set F'' : ℝ → ℝ := fun t => 1 / t + 1 / (1 - t) - 4 with hF''def
  -- Step 1: For t ∈ Set.Ioo 0 1, HasDerivAt F (F' t) t.
  have hF_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F (F' t) t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1mt : (0:ℝ) < 1 - t := by linarith
    have hq1mq : (0:ℝ) < 1 - q := by linarith
    -- derivative of t * log(t/q)
    have d1 : HasDerivAt (fun s : ℝ => s * Real.log (s / q))
        (Real.log t - Real.log q + 1) t := by
      have hlog_div : HasDerivAt (fun s : ℝ => Real.log (s / q)) (1 / t) t := by
        have hsq : HasDerivAt (fun s : ℝ => s / q) (1 / q) t := by
          simpa using (hasDerivAt_id t).div_const q
        have hne : t / q ≠ 0 := div_ne_zero ht0.ne' hq0.ne'
        have hc : HasDerivAt (Real.log ∘ (fun s : ℝ => s / q)) ((t / q)⁻¹ * (1 / q)) t :=
          (Real.hasDerivAt_log hne).comp t hsq
        have hfun : (Real.log ∘ (fun s : ℝ => s / q)) = (fun s : ℝ => Real.log (s / q)) := rfl
        rw [hfun] at hc
        have hsimp : (t / q)⁻¹ * (1 / q) = 1 / t := by field_simp
        rw [hsimp] at hc
        exact hc
      have hmul : HasDerivAt (fun s : ℝ => s * Real.log (s / q))
            (1 * Real.log (t / q) + t * (1 / t)) t :=
        (hasDerivAt_id t).mul hlog_div
      have hsimp : 1 * Real.log (t / q) + t * (1 / t) = Real.log t - Real.log q + 1 := by
        rw [Real.log_div ht0.ne' hq0.ne']
        field_simp
      rw [hsimp] at hmul
      exact hmul
    -- derivative of (1-t) * log((1-t)/(1-q))
    have d2 : HasDerivAt (fun s : ℝ => (1 - s) * Real.log ((1 - s) / (1 - q)))
        (-(Real.log (1 - t) - Real.log (1 - q) + 1)) t := by
      have hg_deriv : HasDerivAt (fun u : ℝ => u * Real.log (u / (1 - q)))
          (Real.log (1 - t) - Real.log (1 - q) + 1) (1 - t) := by
        have hlog_div : HasDerivAt (fun u : ℝ => Real.log (u / (1 - q))) (1 / (1 - t)) (1 - t) := by
          have hsq : HasDerivAt (fun u : ℝ => u / (1 - q)) (1 / (1 - q)) (1 - t) := by
            simpa using (hasDerivAt_id (1-t)).div_const (1 - q)
          have hne : (1 - t) / (1 - q) ≠ 0 := div_ne_zero h1mt.ne' hq1mq.ne'
          have hc : HasDerivAt (Real.log ∘ (fun u : ℝ => u / (1 - q)))
              (((1 - t) / (1 - q))⁻¹ * (1 / (1 - q))) (1 - t) :=
            (Real.hasDerivAt_log hne).comp (1 - t) hsq
          have hfun : (Real.log ∘ (fun u : ℝ => u / (1 - q)))
                       = (fun u : ℝ => Real.log (u / (1 - q))) := rfl
          rw [hfun] at hc
          have hsimp : ((1 - t) / (1 - q))⁻¹ * (1 / (1 - q)) = 1 / (1 - t) := by field_simp
          rw [hsimp] at hc
          exact hc
        have hmul : HasDerivAt (fun u : ℝ => u * Real.log (u / (1 - q)))
              (1 * Real.log ((1 - t) / (1 - q)) + (1 - t) * (1 / (1 - t))) (1 - t) :=
          (hasDerivAt_id (1 - t)).mul hlog_div
        have hsimp : 1 * Real.log ((1 - t) / (1 - q)) + (1 - t) * (1 / (1 - t))
            = Real.log (1 - t) - Real.log (1 - q) + 1 := by
          rw [Real.log_div h1mt.ne' hq1mq.ne']
          field_simp
        rw [hsimp] at hmul
        exact hmul
      have hu : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
      have hcomp := hg_deriv.comp t hu
      -- (Real.log (1 - t) - Real.log (1 - q) + 1) * (-1) =
      --   -(Real.log (1 - t) - Real.log (1 - q) + 1)
      have hsimp : (Real.log (1 - t) - Real.log (1 - q) + 1) * (-1)
          = -(Real.log (1 - t) - Real.log (1 - q) + 1) := by ring
      simpa [hsimp] using hcomp
    -- derivative of 2 * (t - q)^2 = 4 * (t - q)
    have d3 : HasDerivAt (fun s : ℝ => 2 * (s - q) ^ 2) (4 * (t - q)) t := by
      have h1 : HasDerivAt (fun s : ℝ => (s - q) ^ 2) (2 * (t - q)) t := by
        have := ((hasDerivAt_id t).sub_const q).pow 2
        simpa [pow_succ, pow_zero, one_mul] using this
      have h2 := h1.const_mul 2
      convert h2 using 1
      ring
    have hsum := (d1.add d2).sub d3
    have hsimp : (Real.log t - Real.log q + 1) + -(Real.log (1 - t) - Real.log (1 - q) + 1)
                 - 4 * (t - q)
        = Real.log t - Real.log q - Real.log (1 - t) + Real.log (1 - q) - 4 * (t - q) := by ring
    rw [hsimp] at hsum
    exact hsum
  -- Step 2: For t ∈ Set.Ioo 0 1, HasDerivAt F' (F'' t) t.
  have hF'_deriv : ∀ t ∈ Set.Ioo (0:ℝ) 1, HasDerivAt F' (F'' t) t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1mt : (0:ℝ) < 1 - t := by linarith
    have d_logt : HasDerivAt (fun s : ℝ => Real.log s) (1/t) t := by
      simpa [one_div] using Real.hasDerivAt_log ht0.ne'
    have d_neglogq : HasDerivAt (fun _ : ℝ => -Real.log q) 0 t := hasDerivAt_const t _
    have d_log1mt : HasDerivAt (fun s : ℝ => Real.log (1 - s)) (-1 / (1 - t)) t := by
      have hu : HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
        simpa using (hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)
      have hne : (1:ℝ) - t ≠ 0 := h1mt.ne'
      have hl : HasDerivAt Real.log ((1 - t)⁻¹) (1 - t) := Real.hasDerivAt_log hne
      have hc := hl.comp t hu
      have hsimp : (1 - t)⁻¹ * (-1) = -1 / (1 - t) := by field_simp
      simpa [hsimp] using hc
    have d_neglog1mt : HasDerivAt (fun s : ℝ => -Real.log (1 - s)) (1 / (1 - t)) t := by
      have := d_log1mt.neg
      have hsimp : -((-1) / (1 - t)) = 1 / (1 - t) := by field_simp
      simpa [hsimp] using this
    have d_log1mq : HasDerivAt (fun _ : ℝ => Real.log (1 - q)) 0 t := hasDerivAt_const t _
    have d_lin : HasDerivAt (fun s : ℝ => -(4 * (s - q))) (-4) t := by
      have h1 : HasDerivAt (fun s : ℝ => 4 * (s - q)) 4 t := by
        have := ((hasDerivAt_id t).sub_const q).const_mul 4
        simpa using this
      simpa using h1.neg
    -- Sum: F'(t) = log t - log q - log(1-t) + log(1-q) - 4(t-q)
    --   = log t + (-log q) + (-log(1-t)) + log(1-q) + (-(4*(t-q)))
    -- The derivatives: 1/t + 0 + 1/(1-t) + 0 + (-4)
    -- Combine using add, then convert to F' as a function.
    have hcomb : HasDerivAt
        (fun s : ℝ => Real.log s + (-Real.log q) + (-Real.log (1 - s))
                      + Real.log (1 - q) + (-(4 * (s - q))))
        (1/t + 0 + 1/(1-t) + 0 + (-4)) t := by
      exact ((((d_logt.add d_neglogq).add d_neglog1mt).add d_log1mq).add d_lin)
    have hfun_eq : (fun s : ℝ => Real.log s + (-Real.log q) + (-Real.log (1 - s)) +
                                 Real.log (1 - q) + (-(4 * (s - q))))
                    = F' := by
      funext s
      simp only [hF'def]
      ring
    rw [hfun_eq] at hcomb
    have hd_simp : (1/t + 0 + 1/(1-t) + 0 + (-4)) = F'' t := by
      simp only [hF''def]
      ring
    rw [hd_simp] at hcomb
    exact hcomb
  -- Step 3: F''(t) ≥ 0 on (0,1)
  have hF''_nonneg : ∀ t ∈ Set.Ioo (0:ℝ) 1, 0 ≤ F'' t := by
    intro t ht
    obtain ⟨ht0, ht1⟩ := ht
    have h1mt : (0:ℝ) < 1 - t := by linarith
    have hprod : 0 < t * (1 - t) := mul_pos ht0 h1mt
    have hprod_le : t * (1 - t) ≤ 1/4 := by nlinarith [sq_nonneg (t - 1/2)]
    simp only [hF''def]
    have heq : (1/t + 1/(1-t)) = 1 / (t * (1-t)) := by
      have : 1 / t + 1 / (1 - t) = ((1 - t) + t) / (t * (1 - t)) := by
        field_simp
      rw [this]
      congr 1
      ring
    have hsum : 1 / t + 1 / (1 - t) - 4 = 1 / (t * (1 - t)) - 4 := by
      rw [heq]
    rw [hsum]
    have h4 : (4:ℝ) ≤ 1 / (t * (1 - t)) := by
      rw [le_div_iff₀ hprod]
      nlinarith
    linarith
  -- Step 4: F is convex on (0,1)
  have hF_convex : ConvexOn ℝ (Set.Ioo (0:ℝ) 1) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo 0 1)
    · intro t ht
      exact (hF_deriv t ht).continuousAt.continuousWithinAt
    · intro t ht
      have htio : t ∈ Set.Ioo (0:ℝ) 1 := by
        simpa [interior_Ioo] using ht
      exact (hF_deriv t htio).hasDerivWithinAt
    · intro t ht
      have htio : t ∈ Set.Ioo (0:ℝ) 1 := by
        simpa [interior_Ioo] using ht
      exact (hF'_deriv t htio).hasDerivWithinAt
    · intro t ht
      have htio : t ∈ Set.Ioo (0:ℝ) 1 := by
        simpa [interior_Ioo] using ht
      exact hF''_nonneg t htio
  -- Step 5: F(q) = 0
  have hFq : F q = 0 := by
    simp only [hFdef]
    have h1 : q / q = 1 := div_self hq0.ne'
    have h2 : (1 - q) / (1 - q) = 1 := div_self (by linarith : (1:ℝ) - q ≠ 0)
    rw [h1, h2, Real.log_one]
    ring
  -- Step 6: F'(q) = 0
  have hF'q : F' q = 0 := by
    simp only [hF'def]
    ring
  -- Step 7: Apply convexity. We use cases on p vs q.
  rcases lt_trichotomy p q with hlt | heq | hgt
  · -- p < q
    have hpio : p ∈ Set.Ioo (0:ℝ) 1 := ⟨hp0, hp1⟩
    have hqio : q ∈ Set.Ioo (0:ℝ) 1 := ⟨hq0, hq1⟩
    have hslope := ConvexOn.slope_le_of_hasDerivAt hF_convex hpio hqio hlt (hF_deriv q hqio)
    rw [slope_def_field] at hslope
    rw [hFq] at hslope
    rw [hF'q] at hslope
    have hqp : 0 < q - p := by linarith
    have hnum : 0 - F p ≤ 0 := by
      rw [div_le_iff₀ hqp] at hslope
      linarith
    linarith
  · rw [heq, hFq]
  · -- p > q
    have hpio : p ∈ Set.Ioo (0:ℝ) 1 := ⟨hp0, hp1⟩
    have hqio : q ∈ Set.Ioo (0:ℝ) 1 := ⟨hq0, hq1⟩
    have hslope := ConvexOn.le_slope_of_hasDerivAt hF_convex hqio hpio hgt (hF_deriv q hqio)
    rw [slope_def_field] at hslope
    rw [hFq] at hslope
    rw [hF'q] at hslope
    have hpq : 0 < p - q := by linarith
    rw [le_div_iff₀ hpq] at hslope
    linarith
