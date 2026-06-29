import Mathlib

namespace Workspace.ProofLemmas

open scoped Real

/-- A finite formal-Gaussian sum (variances allowed to be ANY nonzero reals,
    including negative) is real-analytic on `ℝ`.  This is the abstract-form
    analyticity used in the §6.1 induction (the convolution / Hurwitz inputs
    need analyticity even for the negative-variance intermediate functions). -/
theorem abstract_formal_gaussian_analytic
    (n : ℕ) (a μ τ_sq : Fin n → ℝ) (hτ : ∀ i, τ_sq i ≠ 0) :
    AnalyticOnNhd ℝ
      (fun x => (Finset.univ : Finset (Fin n)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      Set.univ := by
  have hrw : (fun x => (Finset.univ : Finset (Fin n)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))))
      = (Finset.univ : Finset (Fin n)).sum
        (fun i => fun x => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) := by
    funext x
    rw [Finset.sum_apply]
  rw [hrw]
  apply Finset.analyticOnNhd_sum
  intro i _
  refine analyticOnNhd_const.mul ?_
  refine analyticOnNhd_rexp.comp ?_ (fun _ _ => Set.mem_univ _)
  have h2τ : (2 * τ_sq i) ≠ 0 := by
    simp [hτ i]
  apply AnalyticOnNhd.div_const
  apply AnalyticOnNhd.neg
  apply AnalyticOnNhd.pow
  exact analyticOnNhd_id.sub analyticOnNhd_const

end Workspace.ProofLemmas
