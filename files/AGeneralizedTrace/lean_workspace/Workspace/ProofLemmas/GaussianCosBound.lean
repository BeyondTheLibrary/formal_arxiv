import Mathlib

open Real Set

/-- Helper: on `[0, π/2]`, the function `t ↦ cos t · exp (t^2/2)` is antitone. -/
private lemma h_antitone :
    AntitoneOn (fun t : ℝ => Real.cos t * Real.exp (t ^ 2 / 2)) (Set.Icc (0 : ℝ) (Real.pi / 2)) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
  · -- Continuity
    exact ContinuousOn.mul Real.continuous_cos.continuousOn
      (Real.continuous_exp.comp ((continuous_pow 2).div_const 2)).continuousOn
  · -- Has derivative within the interior
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => Real.cos t)
        (-Real.sin t) t := Real.hasDerivAt_cos t
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
      have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t ^ 1) t := hasDerivAt_pow 2 t
      have hd : HasDerivAt (fun t : ℝ => t ^ 2 / 2) (2 * t ^ 1 / 2) t := hp.div_const 2
      convert hd using 1
      ring
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (t ^ 2 / 2))
        (Real.exp (t ^ 2 / 2) * t) t := by
      have := h2.exp
      simpa using this
    have h4 : HasDerivAt (fun t : ℝ => Real.cos t * Real.exp (t ^ 2 / 2))
        (-Real.sin t * Real.exp (t ^ 2 / 2) +
         Real.cos t * (Real.exp (t ^ 2 / 2) * t)) t := h1.mul h3
    exact h4.hasDerivWithinAt
  · -- Derivative is nonpositive on interior
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨ht0, ht1⟩ := ht
    have hcos_pos : 0 < Real.cos t := by
      apply Real.cos_pos_of_mem_Ioo
      refine ⟨?_, ht1⟩
      linarith [Real.pi_pos]
    have h_tan : t ≤ Real.tan t := Real.le_tan ht0.le ht1
    have h_tcos : t * Real.cos t ≤ Real.sin t := by
      have hmul := mul_le_mul_of_nonneg_right h_tan hcos_pos.le
      rw [Real.tan_eq_sin_div_cos] at hmul
      rw [div_mul_cancel₀ _ hcos_pos.ne'] at hmul
      exact hmul
    have hexp_pos : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
    nlinarith [h_tcos, hexp_pos]

/-- Main lemma proved on `[0, π/2]`. -/
private lemma gaussian_cos_bound_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ Real.pi / 2) :
    Real.cos t ≤ Real.exp (-(t ^ 2 / 2)) := by
  have hmono : Real.cos t * Real.exp (t ^ 2 / 2) ≤
               Real.cos 0 * Real.exp (0 ^ 2 / 2) := by
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
    exact h_antitone ⟨le_refl 0, hpi⟩ ⟨ht0, ht2⟩ ht0
  rw [Real.cos_zero] at hmono
  have h0sq : (0 : ℝ) ^ 2 / 2 = 0 := by ring
  rw [h0sq, Real.exp_zero, one_mul] at hmono
  -- hmono : cos t * exp(t²/2) ≤ 1
  have hexp_pos : 0 < Real.exp (t ^ 2 / 2) := Real.exp_pos _
  -- exp(-(t²/2)) = 1 / exp(t²/2)
  rw [show -(t ^ 2 / 2) = -(t ^ 2 / 2) from rfl]
  have : Real.exp (-(t ^ 2 / 2)) = 1 / Real.exp (t ^ 2 / 2) := by
    rw [Real.exp_neg, one_div]
  rw [this]
  rw [le_div_iff₀ hexp_pos]
  linarith [hmono]

theorem GaussianCosBound :
    ∀ (t : ℝ), -Real.pi / 2 ≤ t → t ≤ Real.pi / 2 →
      Real.cos t ≤ Real.exp (-(t ^ 2 / 2)) := by
  intro t ht1 ht2
  rcases le_or_gt 0 t with h | h
  · exact gaussian_cos_bound_nonneg t h ht2
  · have h1 : 0 ≤ -t := by linarith
    have h2 : -t ≤ Real.pi / 2 := by linarith
    have hkey := gaussian_cos_bound_nonneg (-t) h1 h2
    rw [Real.cos_neg] at hkey
    have heq : (-t) ^ 2 = t ^ 2 := by ring
    rw [heq] at hkey
    exact hkey
