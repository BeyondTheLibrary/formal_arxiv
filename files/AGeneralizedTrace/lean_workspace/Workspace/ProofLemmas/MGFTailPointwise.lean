import Mathlib

open MeasureTheory

/--
**Pointwise tail bound from MGF (extremal-density inequality).**

Let `h : ℝ → ℝ` be non-negative and non-increasing on `[1, ∞)`, and assume
`exp(t · ·) * h` is integrable over `[1, ∞)` with
`∫_{u ≥ 1} exp(t · u) · h(u) du ≤ 1`. Then for every `t > 0` and every
`η ≥ 1`,
`h(η) ≤ t / (exp(t · η) - exp(t))`.
-/
theorem MGFTailPointwise :
    ∀ (h : ℝ → ℝ),
      (∀ x : ℝ, 0 ≤ h x) →
      (∀ η₁ η₂ : ℝ, 1 ≤ η₁ → η₁ ≤ η₂ → h η₂ ≤ h η₁) →
      ∀ (t : ℝ), 0 < t →
        MeasureTheory.IntegrableOn
            (fun u : ℝ => Real.exp (t * u) * h u) (Set.Ici (1 : ℝ)) →
        (∫ u in Set.Ici (1 : ℝ), Real.exp (t * u) * h u) ≤ 1 →
        ∀ η : ℝ, 1 < η →
          h η ≤ t / (Real.exp (t * η) - Real.exp t) := by
  intro h h_nn h_mono t ht hint hint_le η hη_gt
  set D : ℝ := Real.exp (t * η) - Real.exp t with hD_def
  have hexp_strict : Real.exp t < Real.exp (t * η) := by
    apply Real.exp_lt_exp.mpr
    have : t * 1 < t * η := mul_lt_mul_of_pos_left hη_gt ht
    linarith
  have hD_pos : 0 < D := by rw [hD_def]; linarith
  -- Step 1: ∫_1^η exp(t·u) du = D / t
  have hderiv : ∀ u : ℝ,
      HasDerivAt (fun y : ℝ => Real.exp (t * y) / t) (Real.exp (t * u)) u := by
    intro u
    have h1 : HasDerivAt (fun y : ℝ => t * y) t u := by
      simpa using (hasDerivAt_id u).const_mul t
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (t * y))
        (Real.exp (t * u) * t) u := (Real.hasDerivAt_exp (t * u)).comp u h1
    have h3 : HasDerivAt (fun y : ℝ => Real.exp (t * y) / t)
        (Real.exp (t * u) * t / t) u := h2.div_const t
    have ht_ne : t ≠ 0 := ne_of_gt ht
    rw [mul_div_assoc, div_self ht_ne, mul_one] at h3
    exact h3
  have hii_exp : IntervalIntegrable (fun u : ℝ => Real.exp (t * u))
      MeasureTheory.volume 1 η := by
    apply Continuous.intervalIntegrable
    exact Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have h_int_exp_eq : ∫ u in (1 : ℝ)..η, Real.exp (t * u) = D / t := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun u _ => hderiv u) hii_exp, hD_def]
    field_simp
  -- Step 2: Integrability on Icc 1 η for the product function
  have h_int_on_Icc : IntegrableOn
      (fun u : ℝ => Real.exp (t * u) * h u)
      (Set.Icc 1 η) MeasureTheory.volume := by
    apply hint.mono_set
    intro u hu
    exact hu.1
  -- Step 3: ∫_1^η h(η) · exp(t·u) du ≤ ∫_1^η exp(t·u) · h(u) du
  have hη_le : (1 : ℝ) ≤ η := le_of_lt hη_gt
  have h_const_int : IntervalIntegrable (fun u : ℝ => h η * Real.exp (t * u))
      MeasureTheory.volume 1 η := hii_exp.const_mul (h η)
  have h_prod_int : IntervalIntegrable (fun u : ℝ => Real.exp (t * u) * h u)
      MeasureTheory.volume 1 η := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hη_le]
    apply h_int_on_Icc.mono_set
    exact Set.Ioc_subset_Icc_self
  have h_pointwise : ∀ u ∈ Set.Icc (1 : ℝ) η,
      h η * Real.exp (t * u) ≤ Real.exp (t * u) * h u := by
    intro u hu
    rw [mul_comm (h η)]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact h_mono u η hu.1 hu.2
  have h_int_const_le :
      ∫ u in (1 : ℝ)..η, h η * Real.exp (t * u) ≤
        ∫ u in (1 : ℝ)..η, Real.exp (t * u) * h u :=
    intervalIntegral.integral_mono_on hη_le h_const_int h_prod_int h_pointwise
  -- Step 4: ∫_1^η h(η) · exp(t·u) du = h(η) · D / t
  have h_const_int_eq : ∫ u in (1 : ℝ)..η, h η * Real.exp (t * u) =
      h η * (D / t) := by
    rw [intervalIntegral.integral_const_mul, h_int_exp_eq]
  -- Step 5: ∫_1^η exp(t·u) · h(u) du ≤ ∫_{[1,∞)} exp(t·u) · h(u) du
  have h_nonneg_ae : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Ici (1 : ℝ))]
      (fun u : ℝ => Real.exp (t * u) * h u) := by
    filter_upwards with u
    exact mul_nonneg (Real.exp_pos _).le (h_nn u)
  have h_subset_ae : Set.Ioc (1 : ℝ) η ≤ᵐ[MeasureTheory.volume]
      Set.Ici (1 : ℝ) := by
    apply Filter.Eventually.of_forall
    intro u hu
    exact le_of_lt hu.1
  have h_setint_le_total : (∫ u in Set.Ioc (1 : ℝ) η, Real.exp (t * u) * h u) ≤
      ∫ u in Set.Ici (1 : ℝ), Real.exp (t * u) * h u :=
    MeasureTheory.setIntegral_mono_set hint h_nonneg_ae h_subset_ae
  have h_interval_eq_setIoc : ∫ u in (1 : ℝ)..η, Real.exp (t * u) * h u =
      ∫ u in Set.Ioc (1 : ℝ) η, Real.exp (t * u) * h u :=
    intervalIntegral.integral_of_le hη_le
  -- Combine
  have h_total :
      h η * (D / t) ≤ 1 := by
    calc h η * (D / t)
        = ∫ u in (1 : ℝ)..η, h η * Real.exp (t * u) := h_const_int_eq.symm
      _ ≤ ∫ u in (1 : ℝ)..η, Real.exp (t * u) * h u := h_int_const_le
      _ = ∫ u in Set.Ioc (1 : ℝ) η, Real.exp (t * u) * h u :=
          h_interval_eq_setIoc
      _ ≤ ∫ u in Set.Ici (1 : ℝ), Real.exp (t * u) * h u :=
          h_setint_le_total
      _ ≤ 1 := hint_le
  -- Step 6: solve for h(η)
  -- h(η) * (D/t) ≤ 1, with D > 0 and t > 0, so D/t > 0.
  -- Hence h(η) ≤ t / D.
  have hDt_pos : 0 < D / t := div_pos hD_pos ht
  have h_final : h η ≤ 1 / (D / t) := by
    rw [le_div_iff₀ hDt_pos]
    linarith
  have hrewrite : 1 / (D / t) = t / D := by
    rw [one_div, inv_div]
  rw [hrewrite] at h_final
  -- The goal is h η ≤ t / (Real.exp (t * η) - Real.exp t), and D = exp(t*η) - exp(t)
  show h η ≤ t / (Real.exp (t * η) - Real.exp t)
  rw [hD_def] at h_final
  exact h_final
