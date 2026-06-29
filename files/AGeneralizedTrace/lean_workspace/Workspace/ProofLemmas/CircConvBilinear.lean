import Mathlib
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.CircPowMultiplicity

open scoped Real
open MeasureTheory intervalIntegral CircConvInfra CircPowMultiplicity

set_option maxHeartbeats 4000000

/-!
# Bilinearity of circular / linear convolution over `tsum` (Lemma 7, Step 1)

`circConvR` and `linConv` are linear in each argument; this file lifts that
linearity through a `tsum` in the left argument (with explicit
summability/domination hypotheses), the form the multiplicity expansion needs.
-/

namespace CircConvBilinear

/-- **`circConvR` is linear over a `tsum` in the LEFT argument.**
Given a family `u : ℕ → ℝ → ℝ` whose per-term integrands are integrable on the
fundamental window and whose integrand-norm-integrals are summable,
`circConvR (∑'_a u_a) g ξ = ∑'_a circConvR (u_a) g ξ`. -/
theorem circConvR_tsum_left (u : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (ξ : ℝ)
    (hint : ∀ a, MeasureTheory.IntegrableOn
      (fun η => u a η * g (ξ - η)) (Set.Ioc (-Real.pi) Real.pi))
    (hsumm : Summable (fun a =>
      ∫ η in Set.Ioc (-Real.pi) Real.pi, ‖u a η * g (ξ - η)‖)) :
    circConvR (fun η => ∑' a, u a η) g ξ = ∑' a, circConvR (u a) g ξ := by
  unfold circConvR
  rw [tsum_mul_left]
  congr 1
  have hπ : (-Real.pi) ≤ Real.pi := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_of_le hπ]
  have hrhs : (∑' a, ∫ η in (-Real.pi)..Real.pi, u a η * g (ξ - η))
      = ∑' a, ∫ η in Set.Ioc (-Real.pi) Real.pi, u a η * g (ξ - η) := by
    apply tsum_congr; intro a; rw [intervalIntegral.integral_of_le hπ]
  rw [hrhs]
  -- Push the tsum into the product, then swap integral and tsum.
  rw [show (fun x => (fun η => ∑' a, u a η) x * g (ξ - x))
        = (fun x => ∑' a, u a x * g (ξ - x)) from by
    funext x; simp only; rw [← tsum_mul_right]]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm).symm

/-- **`linConv` is linear over a `tsum` in the LEFT argument.**
Same statement for the whole-line linear convolution `linConv u g ξ = ∫ η, u η * g(ξ-η)`. -/
theorem linConv_tsum_left (u : ℕ → ℝ → ℝ) (g : ℝ → ℝ) (ξ : ℝ)
    (hint : ∀ a, MeasureTheory.Integrable (fun η => u a η * g (ξ - η)))
    (hsumm : Summable (fun a => ∫ η, ‖u a η * g (ξ - η)‖)) :
    linConv (fun η => ∑' a, u a η) g ξ = ∑' a, linConv (u a) g ξ := by
  unfold linConv
  rw [show (fun η => (fun η => ∑' a, u a η) η * g (ξ - η))
        = (fun η => ∑' a, u a η * g (ξ - η)) from by
    funext η; simp only; rw [← tsum_mul_right]]
  exact (MeasureTheory.integral_tsum_of_summable_integral_norm hint hsumm).symm

/-- **Scalar pull-out for `circConvR` in the left argument.** -/
theorem circConvR_const_mul_left (c : ℝ) (f g : ℝ → ℝ) (ξ : ℝ) :
    circConvR (fun η => c * f η) g ξ = c * circConvR f g ξ := by
  unfold circConvR
  rw [show (fun η => c * f η * g (ξ - η)) = (fun η => c * (f η * g (ξ - η))) by
    funext η; ring]
  rw [intervalIntegral.integral_const_mul]
  ring

/-- **Scalar pull-out for `linConv` in the left argument.** -/
theorem linConv_const_mul_left (c : ℝ) (f g : ℝ → ℝ) (ξ : ℝ) :
    linConv (fun η => c * f η) g ξ = c * linConv f g ξ := by
  unfold linConv
  rw [show (fun η => c * f η * g (ξ - η)) = (fun η => c * (f η * g (ξ - η))) by
    funext η; ring]
  rw [MeasureTheory.integral_const_mul]

end CircConvBilinear
