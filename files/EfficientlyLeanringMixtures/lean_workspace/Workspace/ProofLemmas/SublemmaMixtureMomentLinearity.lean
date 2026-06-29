import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureRawMoments
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

set_option maxHeartbeats 400000

open MeasureTheory

theorem SublemmaMixtureMomentLinearity
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2) (i : ℕ) :
    Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F i
      = F.weight1 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp1 i
        + F.weight2 * Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian F.comp2 i := by
  -- Integrability of x^i * comp1.density x and x^i * comp2.density x
  have h_int1 : Integrable
      (fun x : ℝ => x ^ i * F.comp1.density x) volume :=
    Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian F.comp1 i
  have h_int2 : Integrable
      (fun x : ℝ => x ^ i * F.comp2.density x) volume :=
    Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian F.comp2 i
  -- Scalar multiples are also integrable
  have h_int1' : Integrable
      (fun x : ℝ => F.weight1 * (x ^ i * F.comp1.density x)) volume :=
    h_int1.const_mul F.weight1
  have h_int2' : Integrable
      (fun x : ℝ => F.weight2 * (x ^ i * F.comp2.density x)) volume :=
    h_int2.const_mul F.weight2
  -- Unfold rawMoment_ofMixture2
  unfold Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2
  unfold Workspace.Types.MixtureRawMoments.rawMoment_ofGaussian
  -- Rewrite the integrand: x^i * F.density x = w1 * (x^i * comp1.density x) + w2 * (x^i * comp2.density x)
  have h_pointwise : ∀ x : ℝ,
      x ^ i * F.density x
        = F.weight1 * (x ^ i * F.comp1.density x)
          + F.weight2 * (x ^ i * F.comp2.density x) := by
    intro x
    rw [Workspace.Types.GaussianMixture2.GaussianMixture2.density_eq]
    ring
  -- Use the pointwise identity to rewrite the integrand
  have h_eq : (fun x : ℝ => x ^ i * F.density x)
      = (fun x : ℝ => F.weight1 * (x ^ i * F.comp1.density x)
          + F.weight2 * (x ^ i * F.comp2.density x)) := by
    funext x
    exact h_pointwise x
  rw [h_eq]
  -- Split the integral
  rw [MeasureTheory.integral_add h_int1' h_int2']
  -- Pull out the constants
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
