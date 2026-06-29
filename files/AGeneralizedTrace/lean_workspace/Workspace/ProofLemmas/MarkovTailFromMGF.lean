import Mathlib

open MeasureTheory

theorem MarkovTailFromMGF :
    ∀ (f : ℝ → ℝ),
      (∀ η : ℝ, 0 ≤ f η) →
      MeasureTheory.Integrable f →
      ∀ (t : ℝ), 0 ≤ t → ∀ (a : ℝ), 0 ≤ a → ∀ (M : ℝ), 0 ≤ M →
        MeasureTheory.IntegrableOn
            (fun η : ℝ => Real.exp (t * η) * f η) (Set.Ici (0 : ℝ)) →
        (∫ η in Set.Ici (0 : ℝ), Real.exp (t * η) * f η) ≤ M →
        (∫ η in Set.Ici a, f η) ≤ M * Real.exp (-(t * a)) := by
  intro f hf_nn hf_int t ht_nn a ha_nn M hM_nn h_exp_int h_mgf
  -- Subset relation
  have h_a_subset_0 : Set.Ici a ⊆ Set.Ici (0 : ℝ) := Set.Ici_subset_Ici.mpr ha_nn
  -- Integrability on Set.Ici a
  have h_integrable_a : IntegrableOn (fun η => Real.exp (t * η) * f η) (Set.Ici a) :=
    h_exp_int.mono_set h_a_subset_0
  have hf_int_Icia : IntegrableOn f (Set.Ici a) := hf_int.integrableOn
  -- Step 1: pointwise bound
  have step_pointwise : ∀ η ∈ Set.Ici a,
      f η ≤ Real.exp (-(t * a)) * (Real.exp (t * η) * f η) := by
    intro η hη
    have hη_ge_a : a ≤ η := hη
    have h_exp_le : Real.exp (t * a) ≤ Real.exp (t * η) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hη_ge_a ht_nn)
    -- 1 ≤ exp(-(t·a)) · exp(t·η)
    have hpos : 0 < Real.exp (t * a) := Real.exp_pos _
    have h_one_le : 1 ≤ Real.exp (-(t * a)) * Real.exp (t * η) := by
      rw [Real.exp_neg]
      rw [inv_mul_eq_div]
      exact (one_le_div hpos).mpr h_exp_le
    calc f η = 1 * f η := (one_mul _).symm
      _ ≤ Real.exp (-(t * a)) * Real.exp (t * η) * f η :=
          mul_le_mul_of_nonneg_right h_one_le (hf_nn η)
      _ = Real.exp (-(t * a)) * (Real.exp (t * η) * f η) := by ring
  -- Step 2: ∫_{η ≥ a} f(η) ≤ exp(-(t*a)) · ∫_{η ≥ a} exp(t·η)·f(η)
  have step_integral :
      (∫ η in Set.Ici a, f η) ≤
        Real.exp (-(t * a)) * ∫ η in Set.Ici a, Real.exp (t * η) * f η := by
    have h_pull :
        Real.exp (-(t * a)) * (∫ η in Set.Ici a, Real.exp (t * η) * f η) =
          ∫ η in Set.Ici a, Real.exp (-(t * a)) * (Real.exp (t * η) * f η) :=
      (MeasureTheory.integral_const_mul _ _).symm
    rw [h_pull]
    apply MeasureTheory.setIntegral_mono_on
    · exact hf_int_Icia
    · exact h_integrable_a.const_mul _
    · exact measurableSet_Ici
    · exact step_pointwise
  -- Step 3: ∫_{η ≥ a} exp(t·η)·f(η) ≤ ∫_{η ≥ 0} exp(t·η)·f(η)
  have step_set :
      ∫ η in Set.Ici a, Real.exp (t * η) * f η ≤
        ∫ η in Set.Ici (0 : ℝ), Real.exp (t * η) * f η := by
    apply MeasureTheory.setIntegral_mono_set h_exp_int
    · exact Filter.Eventually.of_forall (fun η => mul_nonneg (Real.exp_pos _).le (hf_nn η))
    · exact Filter.Eventually.of_forall h_a_subset_0
  -- Combine
  have hexp_nn : 0 ≤ Real.exp (-(t * a)) := (Real.exp_pos _).le
  calc ∫ η in Set.Ici a, f η
      ≤ Real.exp (-(t * a)) * ∫ η in Set.Ici a, Real.exp (t * η) * f η := step_integral
    _ ≤ Real.exp (-(t * a)) * ∫ η in Set.Ici (0 : ℝ), Real.exp (t * η) * f η :=
        mul_le_mul_of_nonneg_left step_set hexp_nn
    _ ≤ Real.exp (-(t * a)) * M := mul_le_mul_of_nonneg_left h_mgf hexp_nn
    _ = M * Real.exp (-(t * a)) := mul_comm _ _
