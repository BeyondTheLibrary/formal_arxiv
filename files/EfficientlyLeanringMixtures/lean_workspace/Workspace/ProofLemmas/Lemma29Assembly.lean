import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.ProofLemmas.Lemma29ChangeOfVariablesTranslation
import Workspace.ProofLemmas.Lemma29SigmaAwareTailMomentStandardNormal
import Workspace.ProofLemmas.Lemma29BinomialAbsExpansionBound
import Workspace.ProofLemmas.SublemmaIntegrabilityXPowGaussian

open MeasureTheory Real
open Workspace.Types.GaussianPDF

set_option maxHeartbeats 16000000

namespace Workspace.ProofLemmas

/--
Lemma 29 (full statement, packaged as assembly). For every `μ ∈ ℝ`, every variance
`σ² ∈ (0, 1]`, every `ε ∈ (0, 1]`, and every integer `i ∈ {0, …, 6}`, assuming
`|μ| ≤ 1/ε`,

  `|∫_{|x| ≥ 2/ε} x^i · (1/√(2π σ²)) · exp(-(x-μ)²/(2σ²)) dx|
    ≤ K29 · (1/ε^i) · exp(-1/(2 ε²))`

for an absolute constant `K29 > 0`.
-/
theorem Lemma29Assembly :
    ∃ K_29 : ℝ, 0 < K_29 ∧
      ∀ (μ σSq ε : ℝ) (i : ℕ),
        0 < ε → ε ≤ 1 → 0 < σSq → σSq ≤ 1 → |μ| ≤ 1 / ε → i ≤ 6 →
        |∫ x in {x : ℝ | 2 / ε ≤ |x|},
            x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
                  * Real.exp (-((x - μ)^2) / (2 * σSq)) ∂MeasureTheory.volume|
        ≤ K_29 * (1 / ε ^ i) * Real.exp (-1 / (2 * ε^2)) := by
  obtain ⟨K27, hK27_pos, hK27⟩ := Lemma29SigmaAwareTailMomentStandardNormal
  refine ⟨2 ^ 7 * 100 * (K27 + 1), by positivity, ?_⟩
  intro μ σSq ε i hε_pos hε_le1 hσSq_pos hσSq_le1 hμ_bound hi_le6
  -- Basic positivity / inequalities
  have hε_inv_pos : 0 < 1 / ε := by positivity
  have hε_inv_ge_one : (1 : ℝ) ≤ 1 / ε := by rw [le_div_iff₀ hε_pos]; linarith
  have h_2πσ_pos : (0 : ℝ) < 2 * Real.pi * σSq := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi * σSq) := Real.sqrt_pos.mpr h_2πσ_pos
  have h_inv_sqrt_pos : 0 < 1 / Real.sqrt (2 * Real.pi * σSq) := by positivity
  have h_inv_sqrt_nonneg : 0 ≤ 1 / Real.sqrt (2 * Real.pi * σSq) := le_of_lt h_inv_sqrt_pos
  -- Step 1: Triangle inequality.
  apply abs_integral_le_integral_abs.trans
  -- Step 2: Push absolute value through product.
  have h_abs : ∀ x : ℝ, |x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
                            * Real.exp (-((x - μ)^2) / (2 * σSq))|
                      = |x|^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                              * Real.exp (-((x - μ)^2) / (2 * σSq)) := by
    intro x
    rw [abs_mul, abs_mul, abs_pow,
        abs_of_pos h_inv_sqrt_pos, abs_of_pos (Real.exp_pos _)]
  have h_measS : MeasurableSet {x : ℝ | 2 / ε ≤ |x|} := by
    have heq : {x : ℝ | 2 / ε ≤ |x|} = (fun x : ℝ => |x|) ⁻¹' (Set.Ici (2/ε)) := rfl
    rw [heq]
    exact measurable_norm measurableSet_Ici
  rw [show (∫ x in {x : ℝ | 2 / ε ≤ |x|},
              |x ^ i * (1 / Real.sqrt (2 * Real.pi * σSq))
                * Real.exp (-((x - μ)^2) / (2 * σSq))| ∂volume)
        = ∫ x in {x : ℝ | 2 / ε ≤ |x|},
              |x|^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                * Real.exp (-((x - μ)^2) / (2 * σSq)) ∂volume from
        MeasureTheory.setIntegral_congr_fun h_measS (fun x _ => h_abs x)]
  -- Step 3: Define g(u) = |u + μ|^i · (1/√(2πσ²)) · exp(-u²/(2σ²))
  --         and rewrite the integral.
  set g : ℝ → ℝ := fun u => |u + μ|^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                              * Real.exp (-(u^2) / (2 * σSq)) with hg_def
  have h_g_meas : Measurable g := by
    simp only [hg_def]
    refine Measurable.mul ?_ ?_
    · refine Measurable.mul ?_ measurable_const
      exact (measurable_id.add_const μ).norm.pow_const _
    · refine Measurable.exp ?_
      exact ((measurable_id.pow_const 2).neg.div_const _)
  have h_rewrite_as_g_shift : ∀ x : ℝ, |x|^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                                  * Real.exp (-((x - μ)^2) / (2 * σSq))
                                = g (x - μ) := by
    intro x
    simp only [hg_def]
    have hxμ : x - μ + μ = x := by ring
    rw [hxμ]
  rw [show (∫ x in {x : ℝ | 2 / ε ≤ |x|},
              |x|^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                * Real.exp (-((x - μ)^2) / (2 * σSq)) ∂volume)
        = ∫ x in {x : ℝ | 2 / ε ≤ |x|}, g (x - μ) ∂volume from
        MeasureTheory.setIntegral_congr_fun h_measS
          (fun x _ => h_rewrite_as_g_shift x)]
  -- Step 4: Change of variables u = x - μ via Lemma29ChangeOfVariablesTranslation.
  rw [Lemma29ChangeOfVariablesTranslation g μ {x : ℝ | 2 / ε ≤ |x|} h_g_meas h_measS]
  set T : Set ℝ := {u : ℝ | u + μ ∈ {x : ℝ | 2 / ε ≤ |x|}} with hT_def
  set T' : Set ℝ := {u : ℝ | 1 / ε ≤ |u|} with hT'_def
  have h_meas_T' : MeasurableSet T' := by
    have heq : T' = (fun u : ℝ => |u|) ⁻¹' (Set.Ici (1/ε)) := rfl
    rw [heq]
    exact measurable_norm measurableSet_Ici
  have h_meas_T : MeasurableSet T := by
    have : T = (fun u : ℝ => u + μ) ⁻¹' {x : ℝ | 2 / ε ≤ |x|} := rfl
    rw [this]
    exact (measurable_id.add_const μ) h_measS
  -- Set inclusion: T ⊆ T'.
  have h_set_inclusion : T ⊆ T' := by
    intro u hu
    simp only [hT_def, hT'_def, Set.mem_setOf_eq] at hu ⊢
    have h_tri : |u + μ| ≤ |u| + |μ| := abs_add_le u μ
    have h_two_inv : (2 : ℝ) / ε = 1/ε + 1/ε := by field_simp; ring
    linarith
  have h_g_nonneg : ∀ u : ℝ, 0 ≤ g u := by
    intro u
    simp only [hg_def]
    apply mul_nonneg (mul_nonneg (pow_nonneg (abs_nonneg _) _) h_inv_sqrt_nonneg)
    exact (Real.exp_pos _).le
  -- The remaining goal is: ∫ u in T, g u ∂volume ≤ K_29 * (1 / ε^i) * exp(-1/(2ε²)).
  ----------------------------------------------------------------------------
  -- Section A: integrability + basic estimates.
  ----------------------------------------------------------------------------
  -- Build a Gaussian PDF G centred at 0 with variance σSq.
  let G : Workspace.Types.GaussianPDF.GaussianPDF :=
    { mean := 0, varSq := σSq, varSq_pos := hσSq_pos }
  -- D(u) = (1/√(2πσSq)) · exp(-u²/(2σSq)) = G.density u (since G.mean = 0).
  have h_D_eq : ∀ u : ℝ,
      G.density u = (1 / Real.sqrt (2 * Real.pi * σSq)) * Real.exp (-u^2 / (2 * σSq)) := by
    intro u
    simp only [Workspace.Types.GaussianPDF.GaussianPDF.density_eq, G, sub_zero]
  -- Define D(u) for convenience.
  set D : ℝ → ℝ := fun u => (1 / Real.sqrt (2 * Real.pi * σSq))
                              * Real.exp (-(u^2) / (2 * σSq)) with hD_def
  have h_D_eq_G : ∀ u, D u = G.density u := by
    intro u; simp only [hD_def, h_D_eq u]
  have h_D_pos : ∀ u, 0 < D u := by
    intro u; simp only [hD_def]
    exact mul_pos h_inv_sqrt_pos (Real.exp_pos _)
  have h_D_nonneg : ∀ u, 0 ≤ D u := fun u => (h_D_pos u).le
  have h_D_even : ∀ u, D (-u) = D u := by
    intro u
    simp only [hD_def]
    congr 1
    ring_nf
  -- g(u) = |u + μ|^i · D(u)
  have h_g_as_D : ∀ u, g u = |u + μ|^i * D u := by
    intro u
    simp only [hg_def, hD_def]
    ring
  -- Pointwise bound: g(u) ≤ 2^i · (|u|^i + |μ|^i) · D(u).
  have h_g_pointwise_bound : ∀ u : ℝ,
      g u ≤ (2 : ℝ)^i * (|u|^i + |μ|^i) * D u := by
    intro u
    rw [h_g_as_D u]
    have h_binom : |u + μ|^i ≤ (2 : ℝ)^i * (|u|^i + |μ|^i) :=
      Lemma29BinomialAbsExpansionBound μ u i
    exact mul_le_mul_of_nonneg_right h_binom (h_D_nonneg u)
  -- Integrability of u ↦ u^j · D(u) on ℝ, via SublemmaIntegrabilityXPowGaussian.
  have h_int_xj_D : ∀ j : ℕ, Integrable (fun u : ℝ => u^j * D u) volume := by
    intro j
    have h := SublemmaIntegrabilityXPowGaussian G j
    have heq : (fun x : ℝ => x ^ j * G.density x) = (fun x : ℝ => x ^ j * D x) := by
      funext x; rw [h_D_eq_G x]
    rw [heq] at h
    exact h
  -- Integrability of u ↦ |u|^j · D(u) on ℝ.
  have h_int_absxj_D : ∀ j : ℕ, Integrable (fun u : ℝ => |u|^j * D u) volume := by
    intro j
    have h_eq : (fun u : ℝ => |u|^j * D u) = (fun u : ℝ => |u^j * D u|) := by
      funext u
      rw [abs_mul, abs_pow, abs_of_pos (h_D_pos u)]
    rw [h_eq]
    exact (h_int_xj_D j).abs
  -- Integrability of u ↦ D(u) on ℝ. (Specialise j = 0.)
  have h_int_D : Integrable D volume := by
    have := h_int_xj_D 0
    simpa using this
  ----------------------------------------------------------------------------
  -- Section B: g is integrable on ℝ (so trivially on T and T').
  ----------------------------------------------------------------------------
  -- g(u) ≤ G_bound(u) := 2^i · (|u|^i + |μ|^i) · D(u), which is integrable.
  have h_int_G_bound : Integrable
      (fun u : ℝ => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u) volume := by
    have h1 : Integrable (fun u : ℝ => |u|^i * D u) volume := h_int_absxj_D i
    have h2 : Integrable (fun u : ℝ => |μ|^i * D u) volume := h_int_D.const_mul (|μ|^i)
    have h_sum : Integrable (fun u : ℝ => |u|^i * D u + |μ|^i * D u) volume :=
      h1.add h2
    have h_rewrite : (fun u : ℝ => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u)
                   = fun u : ℝ => (2 : ℝ)^i * (|u|^i * D u + |μ|^i * D u) := by
      funext u; ring
    rw [h_rewrite]
    exact h_sum.const_mul ((2 : ℝ)^i)
  have h_int_g : Integrable g volume := by
    refine Integrable.mono' h_int_G_bound h_g_meas.aestronglyMeasurable ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (h_g_nonneg u)]
    exact h_g_pointwise_bound u
  have h_int_g_T' : IntegrableOn g T' volume := h_int_g.integrableOn
  have h_int_g_T : IntegrableOn g T volume := h_int_g.integrableOn
  have h_int_G_bound_T' : IntegrableOn (fun u : ℝ => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u) T' volume :=
    h_int_G_bound.integrableOn
  ----------------------------------------------------------------------------
  -- Section C: setIntegral_mono_set ∫_T g ≤ ∫_{T'} g, then pointwise bound.
  ----------------------------------------------------------------------------
  have h_step1 : ∫ u in T, g u ∂volume ≤ ∫ u in T', g u ∂volume := by
    apply MeasureTheory.setIntegral_mono_set h_int_g_T'
    · filter_upwards [self_mem_ae_restrict h_meas_T'] with u _
      exact h_g_nonneg u
    · exact Filter.Eventually.of_forall h_set_inclusion
  have h_step2 : ∫ u in T', g u ∂volume
               ≤ ∫ u in T', (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume := by
    apply MeasureTheory.setIntegral_mono_on h_int_g_T' h_int_G_bound_T' h_meas_T'
    intro u _
    exact h_g_pointwise_bound u
  ----------------------------------------------------------------------------
  -- Section D: split ∫_{T'} G_bound into ∫_{Ici(1/ε)} G_bound + ∫_{Iic(-1/ε)} G_bound.
  ----------------------------------------------------------------------------
  -- T' = Ici(1/ε) ∪ Iic(-1/ε), disjoint (the two sets share at most the boundary).
  -- |u| ≥ 1/ε iff u ≥ 1/ε ∨ u ≤ -1/ε.
  have h_T'_eq : T' = Set.Ici (1/ε) ∪ Set.Iic (-(1/ε)) := by
    ext u
    simp only [hT'_def, Set.mem_setOf_eq, Set.mem_union, Set.mem_Ici, Set.mem_Iic, abs_le]
    constructor
    · intro h
      rcases le_or_gt 0 u with hu | hu
      · left; rw [abs_of_nonneg hu] at h; exact h
      · right
        have habs : |u| = -u := abs_of_neg hu
        rw [habs] at h
        linarith
    · intro h
      rcases h with h | h
      · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ u)]; exact h
      · rw [abs_of_nonpos (by linarith : u ≤ 0)]; linarith
  have h_disjoint : Disjoint (Set.Ici (1/ε)) (Set.Iic (-(1/ε))) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Iic, Set.mem_empty_iff_false, iff_false]
    intro ⟨h1, h2⟩
    have : (1/ε) ≤ -(1/ε) := le_trans h1 h2
    linarith
  have h_meas_Iic : MeasurableSet (Set.Iic (-(1/ε)) : Set ℝ) := measurableSet_Iic
  have h_meas_Ici : MeasurableSet (Set.Ici (1/ε) : Set ℝ) := measurableSet_Ici
  -- Integrability on each half-line.
  have h_int_G_bound_Ici : IntegrableOn
      (fun u : ℝ => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u) (Set.Ici (1/ε)) volume :=
    h_int_G_bound.integrableOn
  have h_int_G_bound_Iic : IntegrableOn
      (fun u : ℝ => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u) (Set.Iic (-(1/ε))) volume :=
    h_int_G_bound.integrableOn
  have h_step3 : ∫ u in T', (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
               = (∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume)
               + ∫ u in Set.Iic (-(1/ε)), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume := by
    rw [h_T'_eq]
    exact MeasureTheory.setIntegral_union h_disjoint h_meas_Iic h_int_G_bound_Ici h_int_G_bound_Iic
  ----------------------------------------------------------------------------
  -- Section E: substitution v = -u on Iic(-(1/ε)).
  --   ∫_{Iic(-(1/ε))} F(u) du = ∫_{Ioi(1/ε)} F(-v) dv (via integral_comp_neg_Iic)
  --     = ∫_{Ici(1/ε)} F(-v) dv (since the boundary is a measure-zero point).
  -- We use F(u) = (2^i · (|u|^i + |μ|^i) * D(u)). Then F(-v) = F(v) because |·|^i
  -- and D are even.
  ----------------------------------------------------------------------------
  have h_GbF_even : ∀ v : ℝ, ((2 : ℝ)^i * (|(-v)|^i + |μ|^i) * D (-v))
                            = ((2 : ℝ)^i * (|v|^i + |μ|^i) * D v) := by
    intro v
    rw [abs_neg, h_D_even v]
  have h_step4_substitution :
      ∫ u in Set.Iic (-(1/ε)), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
      = ∫ v in Set.Ici (1/ε), (2 : ℝ)^i * (|v|^i + |μ|^i) * D v ∂volume := by
    -- Use integral_comp_neg_Iic: ∫ x in Iic c, f(-x) = ∫ x in Ioi (-c), f x.
    -- Set c = -(1/ε) and f(u) = G_bound(u) (= F u). Then f(-x) over Iic(-(1/ε))
    -- equals f(x) over Ioi(1/ε). Convert Ioi to Ici (zero-measure point).
    set F : ℝ → ℝ := fun u => (2 : ℝ)^i * (|u|^i + |μ|^i) * D u with hF_def
    have h_F_neg : ∀ v, F (-v) = F v := by
      intro v
      simp only [hF_def]
      exact h_GbF_even v
    -- ∫ u in Iic(-(1/ε)), F u du = ∫ u in Iic(-(1/ε)), F(-(-u)) du
    --                             = ∫ u in Iic(-(1/ε)), F(-u) du   (wrong direction)
    -- Actually we want: substitute u = -v.
    -- ∫ u in Iic(-(1/ε)), F u du = ∫ v in Ici(1/ε), F(-v) dv by change of variables.
    -- Use `integral_comp_neg_Iic` with c = -(1/ε) and function "F":
    --   ∫ x in Iic c, F(-x) dx = ∫ x in Ioi (-c), F x dx
    -- i.e. ∫ x in Iic (-(1/ε)), F(-x) dx = ∫ x in Ioi (1/ε), F x dx.
    -- We need the LHS to be `∫ u in Iic(-(1/ε)), F u du` (without the negation),
    -- so we rewrite F u = F(-(-u)) = F(-u') where u' = -u.
    -- Instead, use `integral_comp_neg_Ioi` form:
    --   ∫ x in Ioi c, F(-x) = ∫ x in Iic (-c), F x
    -- With c = 1/ε: ∫ x in Ioi (1/ε), F(-x) dx = ∫ x in Iic (-(1/ε)), F x dx.
    -- So ∫ u in Iic(-(1/ε)), F u du = ∫ x in Ioi (1/ε), F(-x) dx.
    -- And ∫ x in Ioi (1/ε), F(-x) dx = ∫ x in Ioi (1/ε), F x dx (by F_neg).
    -- And ∫ x in Ioi (1/ε), F x dx = ∫ x in Ici (1/ε), F x dx.
    have h1 : (∫ u in Set.Iic (-(1/ε)), F u ∂volume)
             = ∫ x in Set.Ioi (1/ε), F (-x) ∂volume := by
      rw [show (∫ u in Set.Iic (-(1/ε)), F u ∂volume) = (∫ u in Set.Iic (-(1/ε)), F u ∂volume) from rfl,
          ← integral_comp_neg_Ioi (1/ε) F]
    have h2 : (∫ x in Set.Ioi (1/ε), F (-x) ∂volume)
             = ∫ x in Set.Ioi (1/ε), F x ∂volume := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x _; exact h_F_neg x
    have h3 : (∫ x in Set.Ioi (1/ε), F x ∂volume)
             = ∫ x in Set.Ici (1/ε), F x ∂volume := by
      rw [← MeasureTheory.integral_Ici_eq_integral_Ioi]
    linarith [h1.symm, h2, h3.symm]
  -- Combine the two pieces:
  -- ∫_{T'} G_bound = 2 · ∫_{Ici(1/ε)} G_bound.
  have h_step5 : ∫ u in T', (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
              = 2 * ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume := by
    rw [h_step3, h_step4_substitution]; ring
  ----------------------------------------------------------------------------
  -- Section F: bound ∫_{Ici(1/ε)} G_bound via Lemma29SigmaAware (j=i and j=0).
  ----------------------------------------------------------------------------
  -- Split ∫_{Ici(1/ε)} G_bound = 2^i · (∫ |u|^i D + |μ|^i · ∫ D)
  --                            = 2^i · (∫ u^i D + |μ|^i · ∫ u^0 D)        (since u ≥ 0 on Ici(1/ε))
  -- We need: on Ici(1/ε), u ≥ 1/ε > 0, so |u| = u.
  have h_int_xi_D_Ici : IntegrableOn (fun u : ℝ => u^i * D u) (Set.Ici (1/ε)) volume :=
    (h_int_xj_D i).integrableOn
  have h_int_x0_D_Ici : IntegrableOn (fun u : ℝ => u^0 * D u) (Set.Ici (1/ε)) volume :=
    (h_int_xj_D 0).integrableOn
  have h_int_D_Ici : IntegrableOn D (Set.Ici (1/ε)) volume := h_int_D.integrableOn
  have h_int_absui_D_Ici : IntegrableOn (fun u : ℝ => |u|^i * D u) (Set.Ici (1/ε)) volume :=
    (h_int_absxj_D i).integrableOn
  have h_int_muD_Ici : IntegrableOn (fun u : ℝ => |μ|^i * D u) (Set.Ici (1/ε)) volume :=
    (h_int_D.const_mul (|μ|^i)).integrableOn
  -- The split:
  have h_split_Gbound : ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
                     = (2 : ℝ)^i * ((∫ u in Set.Ici (1/ε), |u|^i * D u ∂volume)
                                  + |μ|^i * ∫ u in Set.Ici (1/ε), D u ∂volume) := by
    have h_pt : ∀ u : ℝ, (2 : ℝ)^i * (|u|^i + |μ|^i) * D u
                       = (2 : ℝ)^i * (|u|^i * D u + |μ|^i * D u) := by
      intro u; ring
    rw [setIntegral_congr_fun h_meas_Ici (fun u _ => h_pt u)]
    rw [MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add h_int_absui_D_Ici h_int_muD_Ici]
    rw [MeasureTheory.integral_const_mul]
  -- On Ici(1/ε), |u|^i * D u = u^i * D u.
  have h_absui_eq_ui_on_Ici : ∀ u, u ∈ Set.Ici (1/ε) → |u|^i * D u = u^i * D u := by
    intro u hu
    have : (0 : ℝ) ≤ u := le_trans (le_of_lt hε_inv_pos) hu
    rw [abs_of_nonneg this]
  have h_int_eq_on_Ici : ∫ u in Set.Ici (1/ε), |u|^i * D u ∂volume
                      = ∫ u in Set.Ici (1/ε), u^i * D u ∂volume := by
    exact setIntegral_congr_fun h_meas_Ici h_absui_eq_ui_on_Ici
  -- Apply Lemma29SigmaAware with j = i: bounds ∫ u in Ici(1/ε), u^i * D u du.
  have hε_inv_pos' : (0 : ℝ) < 1/ε := hε_inv_pos
  have h_K27_xi : ∫ u in Set.Ici (1/ε), u^i * D u ∂volume
              ≤ K27 * (((1/ε)^i + Real.sqrt σSq^i + 1) / (1/ε))
                    * Real.exp (-(1/ε)^2 / (2 * σSq)) := by
    have h := hK27 σSq (1/ε) i hσSq_pos hσSq_le1 hε_inv_pos' hi_le6
    -- h has form: ∫ u in Ici (1/ε), u^i * (1/√(2πσSq)) * exp(-u²/(2σSq)) du ≤ ...
    -- Need to align u^i * D(u) with u^i * (1/√(2πσSq)) * exp(-u²/(2σSq)).
    have h_eq : (fun u : ℝ => u^i * (1 / Real.sqrt (2 * Real.pi * σSq))
                                * Real.exp (-u^2 / (2 * σSq)))
              = fun u : ℝ => u^i * D u := by
      funext u
      simp only [hD_def]
      ring
    rw [h_eq] at h
    exact h
  -- Apply Lemma29SigmaAware with j = 0: bounds ∫ u in Ici(1/ε), D u du.
  have h_K27_D : ∫ u in Set.Ici (1/ε), D u ∂volume
              ≤ K27 * (((1/ε)^0 + Real.sqrt σSq^0 + 1) / (1/ε))
                    * Real.exp (-(1/ε)^2 / (2 * σSq)) := by
    have h := hK27 σSq (1/ε) 0 hσSq_pos hσSq_le1 hε_inv_pos' (by omega)
    have h_eq : (fun u : ℝ => u^0 * (1 / Real.sqrt (2 * Real.pi * σSq))
                                * Real.exp (-u^2 / (2 * σSq)))
              = fun u : ℝ => D u := by
      funext u
      simp only [hD_def, pow_zero, one_mul]
    rw [h_eq] at h
    exact h
  ----------------------------------------------------------------------------
  -- Section G: algebraic simplifications. Combine bounds.
  ----------------------------------------------------------------------------
  -- Some inequalities:
  have hi_pow : (1 : ℝ) ≤ (1 / ε) ^ i := one_le_pow₀ hε_inv_ge_one
  have hε_inv_pow_pos : 0 < (1 / ε) ^ i := pow_pos hε_inv_pos i
  have hε_inv_pow_nonneg : 0 ≤ (1 / ε) ^ i := le_of_lt hε_inv_pow_pos
  have h_sigma_le_one : Real.sqrt σSq ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt hσSq_le1
  have h_sigma_nonneg : 0 ≤ Real.sqrt σSq := Real.sqrt_nonneg _
  have h_sigma_pow_le_one : Real.sqrt σSq ^ i ≤ 1 := by
    have : Real.sqrt σSq ^ i ≤ 1 ^ i := pow_le_pow_left₀ h_sigma_nonneg h_sigma_le_one i
    simpa using this
  have h_sigma_pow_nonneg : 0 ≤ Real.sqrt σSq ^ i := pow_nonneg h_sigma_nonneg i
  have h_mu_pow_bound : |μ|^i ≤ (1/ε)^i := pow_le_pow_left₀ (abs_nonneg _) hμ_bound i
  have h_mu_pow_nonneg : 0 ≤ |μ|^i := pow_nonneg (abs_nonneg _) i
  have h_2_pow_bound : (2 : ℝ) ^ i ≤ 2 ^ 6 := by
    apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hi_le6
  have h_2_pow_nonneg : (0 : ℝ) ≤ 2 ^ i := by positivity
  have h_2_pow_pos : (0 : ℝ) < 2 ^ i := by positivity
  have hε_sq_le : ε^2 ≤ 1 := by nlinarith
  have hε_sq_pos : 0 < ε^2 := by positivity
  have h_σε_sq_pos : 0 < σSq * ε^2 := by positivity
  -- exp(-(1/ε)²/(2σSq)) ≤ exp(-1/(2ε²)). (σSq ≤ 1 ⇒ 1/(2σSq ε²) ≥ 1/(2 ε²))
  have h_exp_bound : Real.exp (-(1/ε)^2 / (2 * σSq)) ≤ Real.exp (-1 / (2 * ε^2)) := by
    apply Real.exp_le_exp.mpr
    have h1 : (1/ε)^2 = 1 / ε^2 := by rw [div_pow, one_pow]
    rw [h1]
    -- Goal: -(1 / ε^2) / (2 * σSq) ≤ -1 / (2 * ε^2)
    -- = -(1 / (2 * σSq * ε^2)) ≤ -(1 / (2 * ε^2))
    -- = 1 / (2 * ε^2) ≤ 1 / (2 * σSq * ε^2)
    -- Since 2 * σSq * ε^2 ≤ 2 * ε^2 (σSq ≤ 1), and both positive.
    have hA : -(1 / ε^2) / (2 * σSq) = -(1 / (2 * σSq * ε^2)) := by field_simp
    have hB : -1 / (2 * ε^2) = -(1 / (2 * ε^2)) := by ring
    rw [hA, hB]
    apply neg_le_neg
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  -- E := exp(-1/(2 ε²))
  set E := Real.exp (-1 / (2 * ε^2)) with hE_def
  have hE_pos : 0 < E := Real.exp_pos _
  have hE_nonneg : 0 ≤ E := hE_pos.le
  -- ε > 0, ε ≤ 1 ⇒ ε · (1/ε)^i ≤ (1/ε)^i (since 1/ε ≥ 1)
  have h_ε_inv_pow : ε * (1/ε)^i ≤ (1/ε)^i := by
    have : ε ≤ 1 := hε_le1
    -- ε · (1/ε)^i ≤ 1 · (1/ε)^i = (1/ε)^i
    have : ε * (1/ε)^i ≤ 1 * (1/ε)^i := by
      apply mul_le_mul_of_nonneg_right this hε_inv_pow_nonneg
    linarith
  -- ε ≤ (1/ε)^i since (1/ε)^i ≥ 1 ≥ ε.
  have h_eps_le_inv_pow : ε ≤ (1/ε)^i := le_trans hε_le1 hi_pow
  -- Lemma29SigmaAware bound for j=i, simplified:
  --   K27 · (((1/ε)^i + √σSq^i + 1)/(1/ε)) · exp(...)
  --   = K27 · ε · ((1/ε)^i + √σSq^i + 1) · exp(...)
  --   ≤ K27 · ε · ((1/ε)^i + 1 + 1) · exp(...)        [√σSq^i ≤ 1]
  --   ≤ K27 · ε · 3·(1/ε)^i · exp(...)                [1 ≤ (1/ε)^i]
  --   ≤ K27 · 3 · (1/ε)^i · exp(-1/(2ε²))             [ε · (1/ε)^i ≤ (1/ε)^i, exp_bound]
  have h_K27_xi_simp : ∫ u in Set.Ici (1/ε), u^i * D u ∂volume
                    ≤ K27 * 3 * (1/ε)^i * E := by
    have h := h_K27_xi
    -- Step: simplify RHS upper bound
    have h_K27_nn : 0 ≤ K27 := hK27_pos.le
    have h_div_simp : ((1/ε)^i + Real.sqrt σSq^i + 1) / (1/ε)
                    = ε * ((1/ε)^i + Real.sqrt σSq^i + 1) := by
      rw [div_eq_mul_inv]
      have : (1/ε : ℝ)⁻¹ = ε := by field_simp
      rw [this]; ring
    rw [h_div_simp] at h
    -- Bound the bracket: ≤ (1/ε)^i + 1 + 1 ≤ 3 · (1/ε)^i.
    have hbra : (1/ε)^i + Real.sqrt σSq^i + 1 ≤ 3 * (1/ε)^i := by
      have h1 : Real.sqrt σSq^i ≤ 1 := h_sigma_pow_le_one
      have h2 : (1 : ℝ) ≤ (1/ε)^i := hi_pow
      linarith
    have hbra_nn : 0 ≤ (1/ε)^i + Real.sqrt σSq^i + 1 := by linarith [hi_pow, h_sigma_pow_nonneg]
    have hε_3_inv_pow : ε * ((1/ε)^i + Real.sqrt σSq^i + 1) ≤ ε * (3 * (1/ε)^i) := by
      apply mul_le_mul_of_nonneg_left hbra hε_pos.le
    have hε_inv_pow_factor : ε * (3 * (1/ε)^i) = 3 * (ε * (1/ε)^i) := by ring
    -- ε * (1/ε)^i ≤ (1/ε)^i (computed above)
    have h_ε_3_le : ε * (3 * (1/ε)^i) ≤ 3 * (1/ε)^i := by
      rw [hε_inv_pow_factor]; linarith [h_ε_inv_pow]
    have h_bra_final : ε * ((1/ε)^i + Real.sqrt σSq^i + 1) ≤ 3 * (1/ε)^i := by
      linarith
    -- Combine: K27 · (ε · bra) · exp(...) ≤ K27 · 3(1/ε)^i · E
    have h_exp_nn : 0 ≤ Real.exp (-(1/ε)^2 / (2 * σSq)) := (Real.exp_pos _).le
    have h_step_a : K27 * (ε * ((1/ε)^i + Real.sqrt σSq^i + 1))
                     * Real.exp (-(1/ε)^2 / (2 * σSq))
                  ≤ K27 * (3 * (1/ε)^i) * Real.exp (-(1/ε)^2 / (2 * σSq)) := by
      have h_left : K27 * (ε * ((1/ε)^i + Real.sqrt σSq^i + 1))
                  ≤ K27 * (3 * (1/ε)^i) := by
        apply mul_le_mul_of_nonneg_left h_bra_final h_K27_nn
      exact mul_le_mul_of_nonneg_right h_left h_exp_nn
    have h_step_b : K27 * (3 * (1/ε)^i) * Real.exp (-(1/ε)^2 / (2 * σSq))
                  ≤ K27 * (3 * (1/ε)^i) * E := by
      have h_nn : 0 ≤ K27 * (3 * (1/ε)^i) := by positivity
      exact mul_le_mul_of_nonneg_left h_exp_bound h_nn
    have h_total : K27 * (ε * ((1/ε)^i + Real.sqrt σSq^i + 1))
                     * Real.exp (-(1/ε)^2 / (2 * σSq))
                  ≤ K27 * 3 * (1/ε)^i * E := by
      have : K27 * (3 * (1/ε)^i) * E = K27 * 3 * (1/ε)^i * E := by ring
      linarith
    linarith [h, h_total]
  -- Lemma29SigmaAware bound for j=0, simplified:
  --   ≤ K27 · 3ε · exp(...) ≤ 3 K27 · ε · E ≤ 3 K27 · (1/ε)^i · E   (since ε ≤ (1/ε)^i)
  have h_K27_D_simp : ∫ u in Set.Ici (1/ε), D u ∂volume
                    ≤ K27 * 3 * (1/ε)^i * E := by
    have h := h_K27_D
    have h_K27_nn : 0 ≤ K27 := hK27_pos.le
    -- The j=0 case simplifies: (1/ε)^0 = 1, √σSq^0 = 1, sum = 3.
    have h_div_simp : ((1/ε)^0 + Real.sqrt σSq^0 + 1) / (1/ε) = ε * 3 := by
      simp only [pow_zero]
      rw [div_eq_mul_inv]
      have : (1/ε : ℝ)⁻¹ = ε := by field_simp
      rw [this]; ring
    rw [h_div_simp] at h
    -- K27 · ε · 3 · exp(...) ≤ K27 · 3 · ε · E ≤ K27 · 3 · (1/ε)^i · E
    have h_exp_nn : 0 ≤ Real.exp (-(1/ε)^2 / (2 * σSq)) := (Real.exp_pos _).le
    have h_step_b : K27 * (ε * 3) * Real.exp (-(1/ε)^2 / (2 * σSq))
                  ≤ K27 * (ε * 3) * E := by
      have h_nn : 0 ≤ K27 * (ε * 3) := by positivity
      exact mul_le_mul_of_nonneg_left h_exp_bound h_nn
    have h_step_c : K27 * (ε * 3) * E ≤ K27 * 3 * (1/ε)^i * E := by
      have hε_E_nn : 0 ≤ K27 * 3 * E := by positivity
      have h_ε_inv : ε ≤ (1/ε)^i := h_eps_le_inv_pow
      have h_K27_ε : K27 * (ε * 3) * E = K27 * 3 * ε * E := by ring
      rw [h_K27_ε]
      have : K27 * 3 * ε * E ≤ K27 * 3 * (1/ε)^i * E := by
        apply mul_le_mul_of_nonneg_right _ hE_nonneg
        apply mul_le_mul_of_nonneg_left h_ε_inv
        positivity
      linarith
    linarith [h, h_step_b, h_step_c]
  ----------------------------------------------------------------------------
  -- Section H: assemble.
  ----------------------------------------------------------------------------
  -- ∫_{Ici(1/ε)} G_bound = 2^i · (∫ u^i D + |μ|^i · ∫ D)
  --                    ≤ 2^i · (3 K27 (1/ε)^i E + |μ|^i · 3 K27 (1/ε)^i E)
  --                    ≤ 2^i · (3 K27 (1/ε)^i E + (1/ε)^i · 3 K27 (1/ε)^i E)
  -- But this gives (1/ε)^{2i}. We don't actually want that.
  -- Wait, the second term is |μ|^i · ∫ D, where ∫ D ≤ 3 K27 (1/ε)^i E (we BOUND ∫ D
  -- by that even though it's tighter). Hmm — that's wasteful. The tighter bound for
  -- ∫ D is `3 K27 · ε · E`, and then multiplying by |μ|^i ≤ (1/ε)^i gives
  -- `(1/ε)^i · ε · 3 K27 · E ≤ 3 K27 · (1/ε)^i · E` (since `ε(1/ε)^i ≤ (1/ε)^i`).
  -- Let me use the tighter ∫ D bound: K27 · 3 · ε · E.
  have h_K27_D_tight : ∫ u in Set.Ici (1/ε), D u ∂volume
                    ≤ K27 * 3 * ε * E := by
    have h := h_K27_D
    have h_K27_nn : 0 ≤ K27 := hK27_pos.le
    have h_div_simp : ((1/ε)^0 + Real.sqrt σSq^0 + 1) / (1/ε) = ε * 3 := by
      simp only [pow_zero]
      rw [div_eq_mul_inv]
      have : (1/ε : ℝ)⁻¹ = ε := by field_simp
      rw [this]; ring
    rw [h_div_simp] at h
    have h_exp_nn : 0 ≤ Real.exp (-(1/ε)^2 / (2 * σSq)) := (Real.exp_pos _).le
    have h_step_b : K27 * (ε * 3) * Real.exp (-(1/ε)^2 / (2 * σSq))
                  ≤ K27 * (ε * 3) * E := by
      have h_nn : 0 ≤ K27 * (ε * 3) := by positivity
      exact mul_le_mul_of_nonneg_left h_exp_bound h_nn
    have : K27 * (ε * 3) * E = K27 * 3 * ε * E := by ring
    linarith [h, h_step_b]
  -- Combine: 2^i · (∫ u^i D + |μ|^i · ∫ D)
  --       ≤ 2^i · (K27 · 3 · (1/ε)^i · E + |μ|^i · K27 · 3 · ε · E)
  --       ≤ 2^i · (K27 · 3 · (1/ε)^i · E + (1/ε)^i · K27 · 3 · ε · E)
  --       = 2^i · K27 · 3 · E · ((1/ε)^i + (1/ε)^i · ε)
  --       ≤ 2^i · K27 · 3 · E · ((1/ε)^i + (1/ε)^i)         [ε · (1/ε)^i ≤ (1/ε)^i]
  --       = 2^i · K27 · 6 · (1/ε)^i · E
  --       ≤ 2^6 · 6 · K27 · (1/ε)^i · E
  --       ≤ 2^7 · 100 · (K27 + 1) · (1/ε)^i · E.
  have h_step_final : ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
                    ≤ (2 : ℝ)^i * 6 * K27 * (1/ε)^i * E := by
    rw [h_split_Gbound, h_int_eq_on_Ici]
    -- 2^i · (A + |μ|^i · B) where A ≤ K27 · 3 · (1/ε)^i · E, B ≤ K27 · 3 · ε · E.
    have h_K27_nn : 0 ≤ K27 := hK27_pos.le
    -- A ≤ K27 · 3 · (1/ε)^i · E
    have hA : ∫ u in Set.Ici (1/ε), u^i * D u ∂volume ≤ K27 * 3 * (1/ε)^i * E := h_K27_xi_simp
    -- B ≤ K27 · 3 · ε · E
    have hB : ∫ u in Set.Ici (1/ε), D u ∂volume ≤ K27 * 3 * ε * E := h_K27_D_tight
    -- |μ|^i · B ≤ (1/ε)^i · K27 · 3 · ε · E
    have h_mu_B : |μ|^i * ∫ u in Set.Ici (1/ε), D u ∂volume ≤ |μ|^i * (K27 * 3 * ε * E) := by
      apply mul_le_mul_of_nonneg_left hB h_mu_pow_nonneg
    have h_mu_B2 : |μ|^i * (K27 * 3 * ε * E) ≤ (1/ε)^i * (K27 * 3 * ε * E) := by
      apply mul_le_mul_of_nonneg_right h_mu_pow_bound
      positivity
    -- A + |μ|^i · B ≤ K27 · 3 · (1/ε)^i · E + (1/ε)^i · K27 · 3 · ε · E
    have h_sum_bound : (∫ u in Set.Ici (1/ε), u^i * D u ∂volume)
                    + |μ|^i * ∫ u in Set.Ici (1/ε), D u ∂volume
                    ≤ K27 * 3 * (1/ε)^i * E + (1/ε)^i * (K27 * 3 * ε * E) := by
      linarith [hA, h_mu_B, h_mu_B2]
    -- 2^i · (A + |μ|^i · B) ≤ 2^i · (K27 · 3 · (1/ε)^i · E + (1/ε)^i · K27 · 3 · ε · E)
    have h_mul : (2 : ℝ)^i * ((∫ u in Set.Ici (1/ε), u^i * D u ∂volume)
                             + |μ|^i * ∫ u in Set.Ici (1/ε), D u ∂volume)
                ≤ (2 : ℝ)^i * (K27 * 3 * (1/ε)^i * E + (1/ε)^i * (K27 * 3 * ε * E)) := by
      apply mul_le_mul_of_nonneg_left h_sum_bound h_2_pow_nonneg
    -- (1/ε)^i · K27 · 3 · ε · E ≤ K27 · 3 · (1/ε)^i · E (since ε(1/ε)^i ≤ (1/ε)^i)
    have h_ε_part : (1/ε)^i * (K27 * 3 * ε * E) ≤ K27 * 3 * (1/ε)^i * E := by
      have h_factor : (1/ε)^i * (K27 * 3 * ε * E) = K27 * 3 * E * ((1/ε)^i * ε) := by ring
      rw [h_factor]
      have h_inner : (1/ε)^i * ε ≤ (1/ε)^i := by
        have : ε * (1/ε)^i ≤ (1/ε)^i := h_ε_inv_pow
        linarith [this, mul_comm ((1/ε)^i) ε]
      have h_K_E_pos : 0 ≤ K27 * 3 * E := by positivity
      have : K27 * 3 * E * ((1/ε)^i * ε) ≤ K27 * 3 * E * (1/ε)^i := by
        apply mul_le_mul_of_nonneg_left h_inner h_K_E_pos
      linarith [this]
    -- Total ≤ 2^i · 2 · K27 · 3 · (1/ε)^i · E = 2^i · 6 · K27 · (1/ε)^i · E.
    have h_final_sum : K27 * 3 * (1/ε)^i * E + (1/ε)^i * (K27 * 3 * ε * E)
                     ≤ 2 * (K27 * 3 * (1/ε)^i * E) := by linarith [h_ε_part]
    have h_2i_factor : (2 : ℝ)^i * (K27 * 3 * (1/ε)^i * E + (1/ε)^i * (K27 * 3 * ε * E))
                     ≤ (2 : ℝ)^i * (2 * (K27 * 3 * (1/ε)^i * E)) := by
      apply mul_le_mul_of_nonneg_left h_final_sum h_2_pow_nonneg
    have h_eq_final : (2 : ℝ)^i * (2 * (K27 * 3 * (1/ε)^i * E))
                    = (2 : ℝ)^i * 6 * K27 * (1/ε)^i * E := by ring
    linarith [h_mul, h_2i_factor, h_eq_final]
  -- Now: ∫_T g ≤ ∫_{T'} G_bound = 2 · ∫_{Ici(1/ε)} G_bound ≤ 2 · 2^i · 6 · K27 · (1/ε)^i · E
  --              = 12 · 2^i · K27 · (1/ε)^i · E.
  have h_final_bound : ∫ u in T, g u ∂volume
                     ≤ 2 * ((2 : ℝ)^i * 6 * K27 * (1/ε)^i * E) := by
    have hA : ∫ u in T, g u ∂volume ≤ ∫ u in T', g u ∂volume := h_step1
    have hB : ∫ u in T', g u ∂volume ≤ ∫ u in T', (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume := h_step2
    have hC : ∫ u in T', (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
            = 2 * ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume := h_step5
    have hD2 : ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
            ≤ (2 : ℝ)^i * 6 * K27 * (1/ε)^i * E := h_step_final
    have h_2_mul : 2 * ∫ u in Set.Ici (1/ε), (2 : ℝ)^i * (|u|^i + |μ|^i) * D u ∂volume
                 ≤ 2 * ((2 : ℝ)^i * 6 * K27 * (1/ε)^i * E) := by linarith
    linarith
  -- Final: bound by K_29 = 2^7 · 100 · (K27 + 1).
  -- Need: 12 · 2^i · K27 ≤ 2^7 · 100 · (K27 + 1).
  -- 12 · 2^i ≤ 12 · 2^6 = 768 ≤ 12800 = 2^7 · 100.
  -- And K27 ≤ K27 + 1 (trivially).
  have h_K27_pos' : 0 < K27 := hK27_pos
  have h_K27_le : K27 ≤ K27 + 1 := by linarith
  -- Goal:  ∫ u in T, g u ∂volume ≤ 2^7 * 100 * (K27 + 1) * (1 / ε ^ i) * E
  -- Note: (1 / ε)^i = 1 / ε^i.
  have h_inv_eq : (1 / ε)^i = 1 / ε^i := by rw [div_pow, one_pow]
  -- 2 · (2^i · 6 · K27 · (1/ε)^i · E) = 12 · 2^i · K27 · (1/ε)^i · E
  --                                  ≤ 2^7 · 100 · (K27 + 1) · (1/ε)^i · E
  have h_eps_inv_pow_nn : 0 ≤ (1 / ε)^i := hε_inv_pow_nonneg
  have h_final : 2 * ((2 : ℝ)^i * 6 * K27 * (1/ε)^i * E)
              ≤ 2^7 * 100 * (K27 + 1) * (1/ε)^i * E := by
    have h_rearrange1 : 2 * ((2 : ℝ)^i * 6 * K27 * (1/ε)^i * E)
                     = ((2 : ℝ)^i * 12 * K27) * ((1/ε)^i * E) := by ring
    have h_rearrange2 : (2 : ℝ)^7 * 100 * (K27 + 1) * (1/ε)^i * E
                     = ((2 : ℝ)^7 * 100 * (K27 + 1)) * ((1/ε)^i * E) := by ring
    rw [h_rearrange1, h_rearrange2]
    apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (1/ε)^i * E)
    -- (2^i · 12 · K27) ≤ 2^7 · 100 · (K27 + 1)
    -- 12 · 2^i ≤ 12 · 64 = 768 ≤ 12800 = 2^7 · 100
    have h_12_2i : 12 * (2 : ℝ)^i ≤ 12 * 64 := by
      have : (2 : ℝ)^i ≤ 64 := by
        have : (2 : ℝ)^i ≤ 2^6 := h_2_pow_bound
        have : (2 : ℝ)^6 = 64 := by norm_num
        linarith [h_2_pow_bound, this]
      linarith
    have h_768_le : (768 : ℝ) ≤ 12800 := by norm_num
    have h_12_2i_12800 : 12 * (2 : ℝ)^i ≤ 12800 := by linarith
    have h_eq1 : (2 : ℝ)^i * 12 * K27 = 12 * (2 : ℝ)^i * K27 := by ring
    have h_eq2 : (2 : ℝ)^7 * 100 = 12800 := by norm_num
    rw [h_eq1]
    -- Goal: 12 · 2^i · K27 ≤ 12800 · (K27 + 1)
    have h_a : 12 * (2 : ℝ)^i * K27 ≤ 12800 * K27 := by
      have : (12 * (2 : ℝ)^i) * K27 ≤ 12800 * K27 := by
        apply mul_le_mul_of_nonneg_right h_12_2i_12800 hK27_pos.le
      linarith
    have h_b : 12800 * K27 ≤ 12800 * (K27 + 1) := by
      apply mul_le_mul_of_nonneg_left h_K27_le (by norm_num : (0 : ℝ) ≤ 12800)
    have h_c : (2 : ℝ)^7 * 100 * (K27 + 1) = 12800 * (K27 + 1) := by
      have : (2 : ℝ)^7 * 100 = 12800 := h_eq2
      linarith
    linarith
  -- Now conclude.
  have : ∫ u in T, g u ∂volume ≤ 2^7 * 100 * (K27 + 1) * (1/ε)^i * E := by
    linarith
  -- The RHS in the goal uses `1 / ε^i`. Convert.
  rw [show ((1 : ℝ) / ε ^ i) = (1/ε)^i from by rw [div_pow, one_pow]]
  exact this

end Workspace.ProofLemmas
