import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Lemma5Case1PeakBoundAtMu1
import Workspace.ProofLemmas.Lemma5Case1OffPeakBoundAtMu1
import Workspace.ProofLemmas.Lemma5Case1DerivBoundOnDiff
import Workspace.ProofLemmas.Lemma35L1NormGeSetIntegral

set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas

open MeasureTheory

/-- Each `GaussianPDF` density is integrable on ℝ. -/
private lemma case1_density_integrable (G : Workspace.Types.GaussianPDF.GaussianPDF) :
    MeasureTheory.Integrable G.density MeasureTheory.volume := by
  have h : G.density = fun x => ProbabilityTheory.gaussianPDFReal G.mean
      ⟨G.varSq, le_of_lt G.varSq_pos⟩ x := by
    funext x; exact G.density_eq_gaussianPDFReal x
  rw [h]; exact ProbabilityTheory.integrable_gaussianPDFReal _ _

/-- A `GaussianMixture2` density is integrable on ℝ. -/
private lemma case1_mixture_integrable
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    MeasureTheory.Integrable F.density MeasureTheory.volume := by
  unfold Workspace.Types.GaussianMixture2.GaussianMixture2.density
  exact ((case1_density_integrable F.comp1).const_mul F.weight1).add
        ((case1_density_integrable F.comp2).const_mul F.weight2)

theorem Lemma5Case1Assembly :
    ∃ K5_1 : ℝ, 0 < K5_1 ∧
      ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
        0 < ε → ε ≤ 1 →
        Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
        -- WLOG: σ₁² is the minimum variance
        F.comp1.varSq ≤ F.comp2.varSq →
        F.comp1.varSq ≤ F'.comp1.varSq →
        F.comp1.varSq ≤ F'.comp2.varSq →
        -- Case 1 predicate
        (16 * ε ^ 10 ≤ F'.comp1.varSq - F.comp1.varSq ∨ 6 * ε ^ 5 ≤ |F'.comp1.mean - F.comp1.mean|) →
        (16 * ε ^ 10 ≤ F'.comp2.varSq - F.comp1.varSq ∨ 6 * ε ^ 5 ≤ |F'.comp2.mean - F.comp1.mean|) →
        ∃ α : ℝ,
          ∃ h₁ : α < min F.comp1.varSq F.comp2.varSq,
            ∃ h₂ : α < min F'.comp1.varSq F'.comp2.varSq,
              (-1 : ℝ) ≤ α
              ∧ ε ^ 12 ≤
                  min
                    (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp1.varSq
                         (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp2.varSq)
                    (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp1.varSq
                         (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp2.varSq)
              ∧ K5_1 * ε ^ 4 ≤
                  Workspace.Types.L1AndTVDistance.TVDistance
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) := by
  -- K5_1 := 9 / (512 * π). We'll show TV ≥ 9·ε²/(512·π) ≥ K5_1 · ε⁴ for ε ≤ 1.
  refine ⟨9 / (512 * Real.pi), ?_, ?_⟩
  · have hpi_pos : 0 < Real.pi := Real.pi_pos
    positivity
  intro F F' ε hε_pos hε_le_one hstd h12 h1'1 h1'2 hP1 hP2
  -- Define α := F.comp1.varSq - ε^12
  set α : ℝ := F.comp1.varSq - ε ^ 12 with hα_def
  -- Basic facts.
  have hε_nonneg : 0 ≤ ε := le_of_lt hε_pos
  have hε12_pos : 0 < ε ^ 12 := by positivity
  have hε12_le_one : ε ^ 12 ≤ 1 := by
    calc ε ^ 12 ≤ 1 ^ 12 := by apply pow_le_pow_left₀ hε_pos.le hε_le_one
      _ = 1 := one_pow _
  have hFc1_pos : 0 < F.comp1.varSq := F.comp1.varSq_pos
  -- h₁: α < min F.comp1.varSq F.comp2.varSq
  have hα_lt_Fc1 : α < F.comp1.varSq := by
    show F.comp1.varSq - ε ^ 12 < F.comp1.varSq; linarith
  have hα_lt_Fc2 : α < F.comp2.varSq := lt_of_lt_of_le hα_lt_Fc1 h12
  have h₁ : α < min F.comp1.varSq F.comp2.varSq := lt_min hα_lt_Fc1 hα_lt_Fc2
  have hα_lt_F'c1 : α < F'.comp1.varSq := lt_of_lt_of_le hα_lt_Fc1 h1'1
  have hα_lt_F'c2' : α < F'.comp2.varSq := lt_of_lt_of_le hα_lt_Fc1 h1'2
  have h₂ : α < min F'.comp1.varSq F'.comp2.varSq := lt_min hα_lt_F'c1 hα_lt_F'c2'
  refine ⟨α, h₁, h₂, ?_, ?_, ?_⟩
  · -- α ≥ -1
    rw [hα_def]
    have hFc1_nn : 0 ≤ F.comp1.varSq := hFc1_pos.le
    linarith
  · -- ε^12 ≤ min(...)
    simp only [Workspace.Types.MixtureDeconvolution.deconvMixture2_comp1_varSq,
               Workspace.Types.MixtureDeconvolution.deconvMixture2_comp2_varSq]
    rw [hα_def]
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> linarith
  · -- TV lower bound: 9/(512·π) · ε^4 ≤ TVDistance ...
    -- Names.
    set G := Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁ with hG_def
    set G' := Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂ with hG'_def
    set g : ℝ → ℝ := fun x => G.density x - G'.density x with hg_def
    -- Useful constants
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have h2pi_pos : 0 < 2 * Real.pi := by linarith
    have hsqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h2pi_pos
    have hsqrt_2pi_nn : 0 ≤ Real.sqrt (2 * Real.pi) := hsqrt_2pi_pos.le
    have hε5_pos : 0 < ε^5 := by positivity
    have hε6_pos : 0 < ε^6 := by positivity
    have hε7_pos : 0 < ε^7 := by positivity
    have hε12_pos' : 0 < ε^12 := by positivity
    -- ε ≤ F.weight1 from the ε-standard hypothesis.
    have hε_le_w1 : ε ≤ F.weight1 :=
      hstd.weights_bounded.1
    have hF'_w_sum : F'.weight1 + F'.weight2 = 1 := F'.weights_sum_one
    -- Peak bound at μ₁
    have h_peak_target : α < min F.comp1.varSq F.comp2.varSq := h₁
    -- Lemma5Case1PeakBoundAtMu1 needs F.comp1.varSq - ε^12 < min F.comp1.varSq F.comp2.varSq.
    have h_peak_arg : F.comp1.varSq - ε^12 < min F.comp1.varSq F.comp2.varSq := h₁
    have h_peak := Lemma5Case1PeakBoundAtMu1 F ε hε_pos hε_le_one hε_le_w1 h_peak_arg
    -- h_peak : F.weight1 / (√(2π) · ε^6) ≤ G.density F.comp1.mean
    -- Note G = deconvMixture2 F α h₁ = deconvMixture2 F (F.comp1.varSq - ε^12) h_peak_arg by hα_def.
    -- Off-peak bound: same for F'.
    have h_offpeak_arg : F.comp1.varSq - ε^12 < min F'.comp1.varSq F'.comp2.varSq := h₂
    have h_offpeak := Lemma5Case1OffPeakBoundAtMu1 F F' ε hε_pos hε_le_one hP1 hP2 h_offpeak_arg
    -- h_offpeak : G'.density F.comp1.mean ≤ (F'.weight1 + F'.weight2) / (4 · √(2π) · ε^5)
    -- Replace (F'.weight1 + F'.weight2) by 1.
    rw [hF'_w_sum] at h_offpeak
    -- h_offpeak : G'.density F.comp1.mean ≤ 1 / (4 · √(2π) · ε^5)
    -- Combine
    -- g(μ₁) = G.density μ₁ - G'.density μ₁ ≥ F.weight1/(√(2π)·ε^6) - 1/(4·√(2π)·ε^5)
    -- and using ε ≤ F.weight1, ε ≤ 1, get g(μ₁) ≥ 3/(4·√(2π)·ε^5).
    have h_g_mu1 : (3 : ℝ) / (4 * Real.sqrt (2 * Real.pi) * ε^5) ≤ g F.comp1.mean := by
      have hG_def_unfold : G = Workspace.Types.MixtureDeconvolution.deconvMixture2 F
                              (F.comp1.varSq - ε^12) h_peak_arg := by rfl
      have hG'_def_unfold : G' = Workspace.Types.MixtureDeconvolution.deconvMixture2 F'
                                  (F.comp1.varSq - ε^12) h_offpeak_arg := by rfl
      -- Rewrite h_peak in terms of G.
      have h_peak' : F.weight1 / (Real.sqrt (2 * Real.pi) * ε^6) ≤ G.density F.comp1.mean := by
        rw [hG_def_unfold]; exact h_peak
      have h_offpeak' : G'.density F.comp1.mean ≤ 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
        rw [hG'_def_unfold]; exact h_offpeak
      -- Bound F.weight1 ≥ ε, so F.weight1/(√(2π)·ε^6) ≥ ε/(√(2π)·ε^6) = 1/(√(2π)·ε^5).
      have hbase_denom_pos : 0 < Real.sqrt (2 * Real.pi) * ε^6 := by positivity
      have hbase_denom2_pos : 0 < Real.sqrt (2 * Real.pi) * ε^5 := by positivity
      have hbase4_denom_pos : 0 < 4 * Real.sqrt (2 * Real.pi) * ε^5 := by positivity
      have h_step1 : ε / (Real.sqrt (2 * Real.pi) * ε^6)
                       ≤ F.weight1 / (Real.sqrt (2 * Real.pi) * ε^6) := by
        apply div_le_div_of_nonneg_right hε_le_w1 hbase_denom_pos.le
      have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
      have hε5_ne : ε^5 ≠ 0 := ne_of_gt hε5_pos
      have hε6_ne : ε^6 ≠ 0 := ne_of_gt hε6_pos
      have h_step2 : ε / (Real.sqrt (2 * Real.pi) * ε^6)
                       = 1 / (Real.sqrt (2 * Real.pi) * ε^5) := by
        rw [div_eq_div_iff (ne_of_gt hbase_denom_pos) (ne_of_gt hbase_denom2_pos)]
        have : ε^6 = ε * ε^5 := by ring
        rw [this]; ring
      have h_step3 : (1 : ℝ) / (Real.sqrt (2 * Real.pi) * ε^5) - 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5)
                       = 3 / (4 * Real.sqrt (2 * Real.pi) * ε^5) := by
        field_simp
        ring
      -- g(μ₁) = G.density μ₁ - G'.density μ₁
      show 3 / (4 * Real.sqrt (2 * Real.pi) * ε^5) ≤ G.density F.comp1.mean - G'.density F.comp1.mean
      have hcombined : 1 / (Real.sqrt (2 * Real.pi) * ε^5) - 1 / (4 * Real.sqrt (2 * Real.pi) * ε^5)
                       ≤ G.density F.comp1.mean - G'.density F.comp1.mean := by
        have hL : 1 / (Real.sqrt (2 * Real.pi) * ε^5) ≤ G.density F.comp1.mean := by
          have := le_trans (le_of_eq h_step2.symm) h_step1
          linarith [h_peak']
        linarith [h_offpeak']
      linarith [h_step3, hcombined]
    -- Derivative bound on g.
    have h_deriv_pre :
        ε ^ 12 ≤
          min
            (min G.comp1.varSq G.comp2.varSq)
            (min G'.comp1.varSq G'.comp2.varSq) := by
      show ε ^ 12 ≤ min
        (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp1.varSq
             (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp2.varSq)
        (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp1.varSq
             (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp2.varSq)
      simp only [Workspace.Types.MixtureDeconvolution.deconvMixture2_comp1_varSq,
                 Workspace.Types.MixtureDeconvolution.deconvMixture2_comp2_varSq]
      rw [hα_def]
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> linarith
    obtain ⟨hg_diff, hg_deriv⟩ :=
      Lemma5Case1DerivBoundOnDiff F F' α ε hε_pos hε_le_one h₁ h₂ h_deriv_pre
    -- The function in hg_diff/hg_deriv has the SAME shape as our g, after unfolding via hG_def, hG'_def.
    -- We can lift them.
    have hg_diff' : Differentiable ℝ g := by
      have hg_eq : (fun x => (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).density x
                              - (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).density x) = g := rfl
      rw [← hg_eq]; exact hg_diff
    have hg_deriv' : ∀ x, |deriv g x| ≤ 4 / ε^12 := by
      intro x
      have hg_eq : (fun y => (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).density y
                              - (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).density y) = g := rfl
      have := hg_deriv x
      rw [hg_eq] at this
      exact this
    -- Lipschitz bound: |g(x) - g(μ₁)| ≤ (4/ε^12) · |x - μ₁|.
    have h_lip : ∀ x : ℝ, |g x - g F.comp1.mean| ≤ (4 / ε^12) * |x - F.comp1.mean| := by
      intro x
      have hC_nn : 0 ≤ 4 / ε^12 := by positivity
      have hcont :
          ∀ y ∈ (Set.univ : Set ℝ),
            HasDerivWithinAt g (deriv g y) (Set.univ : Set ℝ) y :=
        fun y _ => (hg_diff' y).hasDerivAt.hasDerivWithinAt
      have hbound :
          ∀ y ∈ (Set.univ : Set ℝ), ‖deriv g y‖ ≤ 4 / ε^12 :=
        fun y _ => by
          have := hg_deriv' y
          simpa [Real.norm_eq_abs] using this
      have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := g) (f' := deriv g) (s := (Set.univ : Set ℝ)) (C := 4/ε^12)
        hcont hbound convex_univ (Set.mem_univ F.comp1.mean) (Set.mem_univ x)
      simpa [Real.norm_eq_abs] using this
    -- Now define M and m.
    set M : ℝ := 3 / (4 * Real.sqrt (2 * Real.pi) * ε^5) with hM_def
    set m : ℝ := 4 / ε^12 with hm_def
    have hM_pos : 0 < M := by
      rw [hM_def]
      have : 0 < 4 * Real.sqrt (2 * Real.pi) * ε^5 := by positivity
      positivity
    have hm_pos : 0 < m := by rw [hm_def]; positivity
    -- r := M / (2 * m) = 3 ε^7 / (32 √(2π))
    set r : ℝ := M / (2 * m) with hr_def
    have hr_pos : 0 < r := by
      rw [hr_def]; positivity
    have hr_eq : r = 3 * ε^7 / (32 * Real.sqrt (2 * Real.pi)) := by
      rw [hr_def, hM_def, hm_def]
      have hsqrt_ne : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt hsqrt_2pi_pos
      have hε5_ne : ε^5 ≠ 0 := ne_of_gt hε5_pos
      have hε7_ne : ε^7 ≠ 0 := ne_of_gt hε7_pos
      have hε12_ne : ε^12 ≠ 0 := ne_of_gt hε12_pos
      have hε_pow : ε^12 = ε^7 * ε^5 := by ring
      field_simp
      ring
    -- Lower bound on g on Icc(μ₁ - r, μ₁ + r): g(x) ≥ M/2.
    have h_g_lower : ∀ x ∈ Set.Icc (F.comp1.mean - r) (F.comp1.mean + r), M / 2 ≤ g x := by
      intro x hx
      have hLip := h_lip x
      have h_abs_le : |x - F.comp1.mean| ≤ r := by
        have h1 : -r ≤ x - F.comp1.mean := by linarith [hx.1]
        have h2 : x - F.comp1.mean ≤ r := by linarith [hx.2]
        exact abs_le.mpr ⟨h1, h2⟩
      -- |g(x) - g(μ₁)| ≤ m · r = M/2
      have h_mr : m * r = M / 2 := by
        rw [hr_def]; field_simp
      have h_gap : |g x - g F.comp1.mean| ≤ M / 2 := by
        calc |g x - g F.comp1.mean| ≤ m * |x - F.comp1.mean| := by
              rw [hm_def]; exact hLip
          _ ≤ m * r := by
              apply mul_le_mul_of_nonneg_left h_abs_le hm_pos.le
          _ = M / 2 := h_mr
      -- So g(x) ≥ g(μ₁) - M/2 ≥ M - M/2 = M/2.
      have h_diff_lb : g F.comp1.mean - M / 2 ≤ g x := by
        have h1 := abs_sub_le_iff.mp h_gap
        linarith [h1.2]
      linarith [h_g_mu1]
    -- Integrate the lower bound over Icc(μ₁ - r, μ₁ + r).
    -- ∫_{Icc} (M/2) = (M/2) * (2r) = M·r
    have h_icc_meas : MeasurableSet (Set.Icc (F.comp1.mean - r) (F.comp1.mean + r)) :=
      measurableSet_Icc
    have h_icc_le : F.comp1.mean - r ≤ F.comp1.mean + r := by linarith
    have h_volume_icc :
        MeasureTheory.volume.real (Set.Icc (F.comp1.mean - r) (F.comp1.mean + r)) = 2 * r := by
      rw [Real.volume_real_Icc_of_le h_icc_le]; ring
    -- g is integrable (difference of two integrable mixture densities).
    have h_G_int : MeasureTheory.Integrable G.density MeasureTheory.volume :=
      case1_mixture_integrable G
    have h_G'_int : MeasureTheory.Integrable G'.density MeasureTheory.volume :=
      case1_mixture_integrable G'
    have h_g_int : MeasureTheory.Integrable g MeasureTheory.volume := by
      change MeasureTheory.Integrable (fun x => G.density x - G'.density x) MeasureTheory.volume
      exact h_G_int.sub h_G'_int
    have h_g_int_on : MeasureTheory.IntegrableOn g
                        (Set.Icc (F.comp1.mean - r) (F.comp1.mean + r))
                        MeasureTheory.volume := h_g_int.integrableOn
    -- (M/2) * volume.real (Icc) ≤ ∫_{Icc} g
    have h_volume_ne_top :
        MeasureTheory.volume (Set.Icc (F.comp1.mean - r) (F.comp1.mean + r)) ≠ ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have h_lb_int :
        M / 2 * MeasureTheory.volume.real (Set.Icc (F.comp1.mean - r) (F.comp1.mean + r))
          ≤ ∫ x in Set.Icc (F.comp1.mean - r) (F.comp1.mean + r), g x := by
      exact MeasureTheory.setIntegral_ge_of_const_le_real h_icc_meas h_volume_ne_top
              h_g_lower h_g_int_on
    rw [h_volume_icc] at h_lb_int
    -- (M/2) * (2r) = M * r
    have h_Mr : M / 2 * (2 * r) = M * r := by ring
    rw [h_Mr] at h_lb_int
    -- M * r = 9 ε² / (256 π)
    have h_Mr_eq : M * r = 9 * ε^2 / (256 * Real.pi) := by
      rw [hM_def, hr_eq]
      have hsqrt_sq : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi := by
        rw [← Real.sqrt_mul (le_of_lt h2pi_pos)]
        exact Real.sqrt_mul_self (le_of_lt h2pi_pos)
      have h_denom_ne : 4 * Real.sqrt (2 * Real.pi) * ε^5 ≠ 0 := by positivity
      have h_denom2_ne : 32 * Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
      have h_ε_pow : ε^5 * ε^7 = ε^12 := by ring
      have h_ε_pow' : ε^12 = ε^10 * ε^2 := by ring
      field_simp
      nlinarith [Real.sqrt_nonneg (2 * Real.pi), hsqrt_sq, Real.pi_pos,
                 sq_nonneg (Real.sqrt (2 * Real.pi)),
                 sq_nonneg ε, hε5_pos, hε7_pos]
    rw [h_Mr_eq] at h_lb_int
    -- ∫_{Icc} g ≤ ∫_{Icc} |g| ≤ L1Norm g (from Lemma35L1NormGeSetIntegral)
    have h_int_le_abs :
        ∫ x in Set.Icc (F.comp1.mean - r) (F.comp1.mean + r), g x
          ≤ ∫ x in Set.Icc (F.comp1.mean - r) (F.comp1.mean + r), |g x| := by
      apply MeasureTheory.integral_mono_ae h_g_int_on h_g_int_on.abs
      exact Filter.Eventually.of_forall (fun x => le_abs_self _)
    have h_abs_le_L1 :
        ∫ x in Set.Icc (F.comp1.mean - r) (F.comp1.mean + r), |g x|
          ≤ Workspace.Types.L1AndTVDistance.L1Norm g :=
      Lemma35L1NormGeSetIntegral g _ h_icc_meas h_g_int
    -- L1Norm g = L1NormMixtureDiff G G' = 2 * TVDistance G G'
    have hL1eq : Workspace.Types.L1AndTVDistance.L1Norm g
                 = Workspace.Types.L1AndTVDistance.L1NormMixtureDiff G G' := by
      rfl
    have hTVeq : Workspace.Types.L1AndTVDistance.TVDistance G G'
                 = (1/2) * Workspace.Types.L1AndTVDistance.L1NormMixtureDiff G G' := rfl
    -- Combine: 9·ε²/(256·π) ≤ ∫_{Icc} g ≤ L1Norm g = 2·TV
    have h_TV_lower :
        9 * ε^2 / (256 * Real.pi) ≤ 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' := by
      have h1 := h_lb_int
      have h2 := h_int_le_abs
      have h3 := h_abs_le_L1
      have h4 :
          Workspace.Types.L1AndTVDistance.L1Norm g
            = 2 * Workspace.Types.L1AndTVDistance.TVDistance G G' := by
        rw [hL1eq, hTVeq]; ring
      linarith
    -- So TV ≥ 9·ε²/(512·π)
    have h_TV_lower_final :
        9 * ε^2 / (512 * Real.pi) ≤ Workspace.Types.L1AndTVDistance.TVDistance G G' := by
      have hpipos : 0 < 256 * Real.pi := by positivity
      have h512pos : 0 < 512 * Real.pi := by positivity
      have h_relate : 9 * ε^2 / (256 * Real.pi) = 2 * (9 * ε^2 / (512 * Real.pi)) := by
        field_simp
        ring
      linarith [h_relate]
    -- Finally K5_1 * ε^4 = 9·ε⁴/(512·π) ≤ 9·ε²/(512·π) (since ε ≤ 1 ⇒ ε⁴ ≤ ε²) ≤ TV.
    have hε2_pos : 0 < ε^2 := by positivity
    have hε4_le_ε2 : ε^4 ≤ ε^2 := by
      have hε2_nn : 0 ≤ ε^2 := hε2_pos.le
      have h_eq : ε^4 = ε^2 * ε^2 := by ring
      rw [h_eq]
      have hε2_le_one : ε^2 ≤ 1 := by
        have h_eq2 : ε^2 = ε * ε := by ring
        rw [h_eq2]
        have := mul_le_mul hε_le_one hε_le_one hε_pos.le (by norm_num : (0:ℝ) ≤ 1)
        linarith
      nlinarith [hε2_pos]
    have h512_pos : (0 : ℝ) < 512 * Real.pi := by positivity
    have hKlow : 9 / (512 * Real.pi) * ε^4 ≤ 9 * ε^2 / (512 * Real.pi) := by
      rw [div_mul_eq_mul_div, mul_comm 9 (ε^4 : ℝ)]
      rw [show (9 * ε^2 / (512 * Real.pi) : ℝ) = ε^2 * 9 / (512 * Real.pi) by ring]
      apply div_le_div_of_nonneg_right _ h512_pos.le
      nlinarith [hε4_le_ε2]
    linarith

end Workspace.ProofLemmas
