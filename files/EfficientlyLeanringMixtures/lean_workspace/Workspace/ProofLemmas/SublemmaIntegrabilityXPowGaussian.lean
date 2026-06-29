import Mathlib
import Workspace.Types.GaussianPDF

set_option maxHeartbeats 400000

namespace Workspace.ProofLemmas

open MeasureTheory ProbabilityTheory

/--
For every `GaussianPDF G` and every natural number `i`, the function
`fun x => x^i * G.density x` is Lebesgue-integrable on `ℝ`.
-/
theorem SublemmaIntegrabilityXPowGaussian
    (G : Workspace.Types.GaussianPDF.GaussianPDF) (i : ℕ) :
    MeasureTheory.Integrable
      (fun x : ℝ => x ^ i * G.density x) MeasureTheory.volume := by
  classical
  -- Set up NNReal variance and prove it's nonzero
  set v : NNReal := ⟨G.varSq, le_of_lt G.varSq_pos⟩ with hv_def
  have hv_pos : (0 : ℝ) < (v : ℝ) := by
    show (0 : ℝ) < G.varSq
    exact G.varSq_pos
  have hv_ne : v ≠ 0 := by
    intro h
    have : (v : ℝ) = 0 := by rw [h]; rfl
    linarith
  -- Rewrite g.density as gaussianPDFReal
  have hdens : (fun x : ℝ => x ^ i * G.density x) =
      (fun x : ℝ => x ^ i * gaussianPDFReal G.mean v x) := by
    funext x
    rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq_gaussianPDFReal]
  rw [hdens]
  -- Strategy: show Integrable (fun x => x^i) (gaussianReal G.mean v),
  -- then transfer to volume via integrable_withDensity_iff.
  have h_int_gr : Integrable (fun x : ℝ => x ^ i) (gaussianReal G.mean v) := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · -- i = 0: constant function is integrable on probability measure
      subst hi
      simp only [pow_zero]
      exact integrable_const 1
    · -- i ≥ 1: use MemLp.integrable_norm_pow with f = id, then identify ‖x‖^i = |x|^i
      have h_memLp : MemLp (id : ℝ → ℝ) ((i : ℕ) : ENNReal) (gaussianReal G.mean v) := by
        apply memLp_id_gaussianReal' ((i : ℕ) : ENNReal)
        exact ENNReal.natCast_ne_top i
      have h_norm_pow : Integrable (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ i)
          (gaussianReal G.mean v) := h_memLp.integrable_norm_pow hi.ne'
      -- ‖x‖ ^ i = |x|^i; we want x^i which is integrable iff |x|^i is
      have h_abs : Integrable (fun x : ℝ => |x| ^ i) (gaussianReal G.mean v) := by
        have : (fun x : ℝ => |x| ^ i) = (fun x : ℝ => ‖(id : ℝ → ℝ) x‖ ^ i) := by
          funext x
          simp [Real.norm_eq_abs]
        rw [this]
        exact h_norm_pow
      -- |x^i| = |x|^i, so Integrable x^i ↔ Integrable |x|^i
      refine (integrable_norm_iff ?_).mp ?_
      · -- measurability of x^i
        exact (Continuous.aestronglyMeasurable (by continuity))
      · -- ‖x^i‖ = |x|^i, integrable
        convert h_abs using 1
        funext x
        rw [Real.norm_eq_abs, abs_pow]
  -- Now use the fact that gaussianReal = withDensity to transfer integrability
  have hgr_eq : gaussianReal G.mean v =
      MeasureTheory.volume.withDensity (gaussianPDF G.mean v) :=
    gaussianReal_of_var_ne_zero G.mean hv_ne
  rw [hgr_eq] at h_int_gr
  -- Apply integrable_withDensity_iff
  have h_meas : Measurable (gaussianPDF G.mean v) := measurable_gaussianPDF G.mean v
  have h_lt_top : ∀ᵐ x ∂(MeasureTheory.volume : Measure ℝ),
      gaussianPDF G.mean v x < ⊤ := by
    filter_upwards with x using gaussianPDF_lt_top
  rw [MeasureTheory.integrable_withDensity_iff h_meas h_lt_top] at h_int_gr
  -- h_int_gr : Integrable (fun x => x^i * (gaussianPDF G.mean v x).toReal) volume
  -- Rewrite (gaussianPDF _ _ x).toReal as gaussianPDFReal _ _ x
  convert h_int_gr using 1
  funext x
  rw [toReal_gaussianPDF]

end Workspace.ProofLemmas
