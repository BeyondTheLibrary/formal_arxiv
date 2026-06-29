import Mathlib
open scoped Real
open MeasureTheory intervalIntegral
set_option maxHeartbeats 4000000
namespace PeriodicCircConvPeriodisation

theorem fold_hasSum (F : ℝ → ℝ) (hF : Integrable F) :
    HasSum (fun s : ℤ => ∫ η in (-Real.pi)..Real.pi, F (η + 2 * Real.pi * (s : ℝ)))
      (∫ x, F x) := by
  have hne : (2 * Real.pi) ≠ 0 := by positivity
  set g : ℝ → ℝ := fun x => (2 * Real.pi) * F (2 * Real.pi * x - Real.pi) with hg
  have h1 : Integrable (fun x => F (x - Real.pi)) := hF.comp_sub_right Real.pi
  have h2 : Integrable (fun x => F (2 * Real.pi * x - Real.pi)) := by
    have := h1.comp_mul_left' hne
    simpa using this
  have hgint : Integrable g := by
    simpa [hg, mul_comm] using h2.const_mul (2 * Real.pi)
  have hHS := MeasureTheory.Integrable.hasSum_intervalIntegral_comp_add_int hgint
  -- total integral
  have htot : (∫ x, g x) = ∫ x, F x := by
    have hcv : (∫ x, g x) = ∫ x, (2 * Real.pi) * F (2 * Real.pi * x - Real.pi) := by rfl
    rw [hcv]
    rw [MeasureTheory.integral_const_mul]
    have hcv2 : (∫ x, F (2 * Real.pi * x - Real.pi))
        = ∫ x, (fun y => F (y - Real.pi)) (2 * Real.pi * x) := by rfl
    rw [hcv2, MeasureTheory.Measure.integral_comp_mul_left (fun y => F (y - Real.pi)) (2 * Real.pi)]
    have hcv3 : (∫ y, F (y - Real.pi)) = ∫ x, F x :=
      MeasureTheory.integral_sub_right_eq_self F Real.pi
    rw [hcv3]
    rw [abs_of_pos (by positivity : (0:ℝ) < (2 * Real.pi)⁻¹)]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  -- summand rewrite
  have hsum_eq : (fun s : ℤ => ∫ x in (0:ℝ)..1, g (x + (s : ℝ)))
      = (fun s : ℤ => ∫ η in (-Real.pi)..Real.pi, F (η + 2 * Real.pi * (s : ℝ))) := by
    funext s
    have hstep : (∫ x in (0:ℝ)..1, g (x + (s : ℝ)))
        = ∫ x in (0:ℝ)..1, (fun y => (2 * Real.pi) * F (y - Real.pi))
            (2 * Real.pi * x + 2 * Real.pi * (s : ℝ)) := by
      apply intervalIntegral.integral_congr; intro x _
      simp only [hg]; ring_nf
    rw [hstep, intervalIntegral.integral_comp_mul_add
      (fun y => (2 * Real.pi) * F (y - Real.pi)) hne (2 * Real.pi * (s : ℝ))]
    rw [intervalIntegral.integral_const_mul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hne, one_mul]
    have e1 : (∫ x in (2 * Real.pi * 0 + 2 * Real.pi * (s : ℝ))..(2 * Real.pi * 1 + 2 * Real.pi * (s : ℝ)), F (x - Real.pi)) = ∫ x in (2 * Real.pi * 0 + 2 * Real.pi * (s : ℝ))..(2 * Real.pi * 1 + 2 * Real.pi * (s : ℝ)), (fun η => F (η + 2 * Real.pi * (s : ℝ))) (x - (Real.pi + 2 * Real.pi * (s : ℝ))) := by
      apply intervalIntegral.integral_congr; intro x _
      simp only; ring_nf
    rw [e1, intervalIntegral.integral_comp_sub_right
      (fun η => F (η + 2 * Real.pi * (s : ℝ))) (Real.pi + 2 * Real.pi * (s : ℝ))]
    congr 1 <;> ring
  rw [hsum_eq] at hHS
  rw [htot] at hHS
  exact hHS

theorem fold_tsum (F : ℝ → ℝ) (hF : Integrable F) :
    ∑' s : ℤ, (∫ η in (-Real.pi)..Real.pi, F (η + 2 * Real.pi * (s : ℝ))) = ∫ x, F x :=
  (fold_hasSum F hF).tsum_eq

/-- **Convolution symmetry on the whole line.** For any `f H : ℝ → ℝ` and shift `a`,
the linear-convolution integrand can be reflected:
`∫ η, f η * H (a - η) = ∫ u, f (a - u) * H u`.  Pure change of variables `u = a - η`
(translation- and reflection-invariance of Lebesgue measure); no integrability needed. -/
theorem conv_symm (f H : ℝ → ℝ) (a : ℝ) :
    (∫ η, f η * H (a - η)) = ∫ u, f (a - u) * H u := by
  have h := MeasureTheory.integral_sub_left_eq_self
    (fun u => f (a - u) * H u) (volume) a
  simpa using h

end PeriodicCircConvPeriodisation
