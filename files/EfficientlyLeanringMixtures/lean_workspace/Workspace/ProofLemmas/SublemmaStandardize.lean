import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureRelabelEquiv
import Workspace.Types.MixtureRawMoments

set_option maxHeartbeats 1200000

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureRelabelEquiv
open Workspace.Types.MixtureRawMoments

/-- Density-scaling identity for a Gaussian: the rescaled component
`(μ/s, σ²/s²)` satisfies `density x = s · original.density(s·x)`. -/
private lemma gaussian_density_rescale
    (G : Workspace.Types.GaussianPDF.GaussianPDF) {s : ℝ} (hs : 0 < s)
    (Gt : Workspace.Types.GaussianPDF.GaussianPDF)
    (hμ : Gt.mean = G.mean / s) (hσ : Gt.varSq = G.varSq / s^2) :
    ∀ x : ℝ, Gt.density x = s * G.density (s * x) := by
  intro x
  rw [Workspace.Types.GaussianPDF.GaussianPDF.density_eq,
      Workspace.Types.GaussianPDF.GaussianPDF.density_eq, hμ, hσ]
  have hs_ne : s ≠ 0 := ne_of_gt hs
  have hs2_pos : 0 < s^2 := by positivity
  have hs2_ne : (s^2 : ℝ) ≠ 0 := ne_of_gt hs2_pos
  have hG_pos : 0 < G.varSq := G.varSq_pos
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hsq_pos' : 0 < 2 * Real.pi * G.varSq := by positivity
  -- Step 1: simplify the sqrt
  have step1 : Real.sqrt (2 * Real.pi * (G.varSq / s^2)) =
      Real.sqrt (2 * Real.pi * G.varSq) / s := by
    rw [show (2 * Real.pi * (G.varSq / s^2) : ℝ) = (2 * Real.pi * G.varSq) / s^2 by ring,
        Real.sqrt_div' _ (le_of_lt hs2_pos),
        Real.sqrt_sq hs.le]
  -- Step 2: simplify the exponent
  have step2 : -(x - G.mean / s) ^ 2 / (2 * (G.varSq / s^2)) =
      -(s * x - G.mean) ^ 2 / (2 * G.varSq) := by
    field_simp
  rw [step1, step2]
  -- Goal now:  1 / (√(2π·varSq) / s) * exp(...) = s * (1 / √(2π·varSq) * exp(...))
  -- Use field_simp / ring with sqrt > 0
  have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi * G.varSq) := Real.sqrt_pos.mpr hsq_pos'
  have hsqrt_ne : Real.sqrt (2 * Real.pi * G.varSq) ≠ 0 := ne_of_gt hsqrt_pos
  field_simp

theorem SublemmaStandardize
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (hw1  : 0 < F.weight1) (hw2  : 0 < F.weight2)
    (hw1' : 0 < F'.weight1) (hw2' : 0 < F'.weight2) :
    ∃ s : ℝ, 1 ≤ s ∧
      ∃ Ft Ft' : Workspace.Types.GaussianMixture2.GaussianMixture2,
        -- (a) variances of F̃, F̃' lie in (0, 1]
        (0 < Ft.comp1.varSq ∧ Ft.comp1.varSq ≤ 1 ∧
         0 < Ft.comp2.varSq ∧ Ft.comp2.varSq ≤ 1 ∧
         0 < Ft'.comp1.varSq ∧ Ft'.comp1.varSq ≤ 1 ∧
         0 < Ft'.comp2.varSq ∧ Ft'.comp2.varSq ≤ 1) ∧
        -- (b) non-degeneracy preserved as a bi-implication
        ((Ft.comp1.mean ≠ Ft.comp2.mean ∨ Ft.comp1.varSq ≠ Ft.comp2.varSq) ↔
         (F.comp1.mean ≠ F.comp2.mean ∨ F.comp1.varSq ≠ F.comp2.varSq)) ∧
        ((Ft'.comp1.mean ≠ Ft'.comp2.mean ∨ Ft'.comp1.varSq ≠ Ft'.comp2.varSq) ↔
         (F'.comp1.mean ≠ F'.comp2.mean ∨ F'.comp1.varSq ≠ F'.comp2.varSq)) ∧
        -- (c) weights preserved
        (Ft.weight1 = F.weight1 ∧ Ft.weight2 = F.weight2 ∧
         Ft'.weight1 = F'.weight1 ∧ Ft'.weight2 = F'.weight2) ∧
        -- (d) moment-scaling relation for i ∈ {0,...,6}
        (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ),
            s ^ i * Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 Ft i
              = Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F i) ∧
        (∀ i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ),
            s ^ i * Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 Ft' i
              = Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F' i) ∧
        -- (e) MixtureRelabelEquiv on standardized pair iff on original pair
        (Workspace.Types.MixtureRelabelEquiv.MixtureRelabelEquiv Ft Ft'
          ↔ Workspace.Types.MixtureRelabelEquiv.MixtureRelabelEquiv F F') := by
  have hσ1 : 0 < F.comp1.varSq := F.comp1.varSq_pos
  have hσ2 : 0 < F.comp2.varSq := F.comp2.varSq_pos
  have hσ1' : 0 < F'.comp1.varSq := F'.comp1.varSq_pos
  have hσ2' : 0 < F'.comp2.varSq := F'.comp2.varSq_pos
  set s : ℝ := max 1 (max (Real.sqrt F.comp1.varSq)
                (max (Real.sqrt F.comp2.varSq)
                  (max (Real.sqrt F'.comp1.varSq) (Real.sqrt F'.comp2.varSq)))) with hs_def
  have hs_ge_one : 1 ≤ s := le_max_left _ _
  have hs_pos : 0 < s := lt_of_lt_of_le one_pos hs_ge_one
  have hsq1 : Real.sqrt F.comp1.varSq ≤ s := by
    apply le_trans _ (le_max_right _ _)
    exact le_max_left _ _
  have hsq2 : Real.sqrt F.comp2.varSq ≤ s := by
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    exact le_max_left _ _
  have hsq1' : Real.sqrt F'.comp1.varSq ≤ s := by
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    exact le_max_left _ _
  have hsq2' : Real.sqrt F'.comp2.varSq ≤ s := by
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    apply le_trans _ (le_max_right _ _)
    exact le_max_right _ _
  have hs_sq_ge1 : F.comp1.varSq ≤ s^2 := by
    have : F.comp1.varSq = (Real.sqrt F.comp1.varSq)^2 := by
      rw [Real.sq_sqrt hσ1.le]
    rw [this]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq1 2
  have hs_sq_ge2 : F.comp2.varSq ≤ s^2 := by
    have : F.comp2.varSq = (Real.sqrt F.comp2.varSq)^2 := by
      rw [Real.sq_sqrt hσ2.le]
    rw [this]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq2 2
  have hs_sq_ge1' : F'.comp1.varSq ≤ s^2 := by
    have : F'.comp1.varSq = (Real.sqrt F'.comp1.varSq)^2 := by
      rw [Real.sq_sqrt hσ1'.le]
    rw [this]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq1' 2
  have hs_sq_ge2' : F'.comp2.varSq ≤ s^2 := by
    have : F'.comp2.varSq = (Real.sqrt F'.comp2.varSq)^2 := by
      rw [Real.sq_sqrt hσ2'.le]
    rw [this]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq2' 2
  have hs_sq_pos : 0 < s^2 := by positivity
  let comp1t : Workspace.Types.GaussianPDF.GaussianPDF :=
    { mean := F.comp1.mean / s
    , varSq := F.comp1.varSq / s^2
    , varSq_pos := div_pos hσ1 hs_sq_pos }
  let comp2t : Workspace.Types.GaussianPDF.GaussianPDF :=
    { mean := F.comp2.mean / s
    , varSq := F.comp2.varSq / s^2
    , varSq_pos := div_pos hσ2 hs_sq_pos }
  let comp1t' : Workspace.Types.GaussianPDF.GaussianPDF :=
    { mean := F'.comp1.mean / s
    , varSq := F'.comp1.varSq / s^2
    , varSq_pos := div_pos hσ1' hs_sq_pos }
  let comp2t' : Workspace.Types.GaussianPDF.GaussianPDF :=
    { mean := F'.comp2.mean / s
    , varSq := F'.comp2.varSq / s^2
    , varSq_pos := div_pos hσ2' hs_sq_pos }
  let Ft : Workspace.Types.GaussianMixture2.GaussianMixture2 :=
    { weight1 := F.weight1
    , weight2 := F.weight2
    , comp1 := comp1t
    , comp2 := comp2t
    , weight1_nonneg := F.weight1_nonneg
    , weight2_nonneg := F.weight2_nonneg
    , weights_sum_one := F.weights_sum_one }
  let Ft' : Workspace.Types.GaussianMixture2.GaussianMixture2 :=
    { weight1 := F'.weight1
    , weight2 := F'.weight2
    , comp1 := comp1t'
    , comp2 := comp2t'
    , weight1_nonneg := F'.weight1_nonneg
    , weight2_nonneg := F'.weight2_nonneg
    , weights_sum_one := F'.weights_sum_one }
  -- Key density-scaling identities for the four rescaled components
  have hd1 : ∀ x : ℝ, Ft.comp1.density x = s * F.comp1.density (s * x) :=
    gaussian_density_rescale F.comp1 hs_pos comp1t rfl rfl
  have hd2 : ∀ x : ℝ, Ft.comp2.density x = s * F.comp2.density (s * x) :=
    gaussian_density_rescale F.comp2 hs_pos comp2t rfl rfl
  have hd1' : ∀ x : ℝ, Ft'.comp1.density x = s * F'.comp1.density (s * x) :=
    gaussian_density_rescale F'.comp1 hs_pos comp1t' rfl rfl
  have hd2' : ∀ x : ℝ, Ft'.comp2.density x = s * F'.comp2.density (s * x) :=
    gaussian_density_rescale F'.comp2 hs_pos comp2t' rfl rfl
  -- The mixture-level density identity
  have hDens_Ft : ∀ x : ℝ, Ft.density x = s * F.density (s * x) := by
    intro x
    show Ft.weight1 * Ft.comp1.density x + Ft.weight2 * Ft.comp2.density x =
         s * (F.weight1 * F.comp1.density (s*x) + F.weight2 * F.comp2.density (s*x))
    rw [hd1, hd2]
    show F.weight1 * (s * F.comp1.density (s*x)) + F.weight2 * (s * F.comp2.density (s*x)) =
         s * (F.weight1 * F.comp1.density (s*x) + F.weight2 * F.comp2.density (s*x))
    ring
  have hDens_Ft' : ∀ x : ℝ, Ft'.density x = s * F'.density (s * x) := by
    intro x
    show Ft'.weight1 * Ft'.comp1.density x + Ft'.weight2 * Ft'.comp2.density x =
         s * (F'.weight1 * F'.comp1.density (s*x) + F'.weight2 * F'.comp2.density (s*x))
    rw [hd1', hd2']
    show F'.weight1 * (s * F'.comp1.density (s*x)) + F'.weight2 * (s * F'.comp2.density (s*x)) =
         s * (F'.weight1 * F'.comp1.density (s*x) + F'.weight2 * F'.comp2.density (s*x))
    ring
  -- Moment scaling lemma: s^i · M_i(Ft) = M_i(F) for any nat i
  have hMoment : ∀ (G Gt : Workspace.Types.GaussianMixture2.GaussianMixture2)
      (_ : ∀ x : ℝ, Gt.density x = s * G.density (s * x)) (i : ℕ),
      s^i * Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 Gt i =
        Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 G i := by
    intro G Gt hDens i
    rw [Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2_def,
        Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2_def]
    -- Rewrite the integrand using hDens
    have eq1 : (∫ x, x ^ i * Gt.density x ∂MeasureTheory.volume) =
               (∫ x, x ^ i * (s * G.density (s * x)) ∂MeasureTheory.volume) := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      simp only [hDens x]
    rw [eq1]
    -- Now ∫ x^i · s · G.density(s·x) dx = s · ∫ x^i · G.density(s·x) dx
    have eq2 : (∫ x, x ^ i * (s * G.density (s * x)) ∂MeasureTheory.volume) =
               s * ∫ x, x ^ i * G.density (s * x) ∂MeasureTheory.volume := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x; ring
    rw [eq2]
    -- Apply change of variable: ∫ g(s*x) dx = |s⁻¹| · ∫ g(y) dy with g(y) = (y/s)^i · G.density y
    -- so g(s*x) = (s*x/s)^i · G.density(s*x) = x^i · G.density(s*x)
    set g : ℝ → ℝ := fun y => (y / s)^i * G.density y with hg_def
    have hg_eval : ∀ x : ℝ, g (s * x) = x^i * G.density (s * x) := by
      intro x
      show (s * x / s)^i * G.density (s * x) = x^i * G.density (s * x)
      have hsx : (s * x) / s = x := by
        field_simp
      rw [hsx]
    have hgs : (∫ x, x ^ i * G.density (s * x) ∂MeasureTheory.volume) =
               ∫ x, g (s * x) ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      show x ^ i * G.density (s * x) = g (s * x)
      rw [hg_eval x]
    rw [hgs, MeasureTheory.Measure.integral_comp_mul_left g s]
    -- Now: s^i * (s * (|s⁻¹| · ∫ g(y) dy)) = ∫ y^i · G.density y dy
    -- We need: |s⁻¹| = 1/s (since s > 0)
    have habs : |s⁻¹| = s⁻¹ := abs_of_pos (inv_pos.mpr hs_pos)
    rw [habs]
    -- The integral of g: ∫ (y/s)^i · G.density y dy = (1/s^i) · ∫ y^i · G.density y dy
    have hgint : (∫ y, g y ∂MeasureTheory.volume) =
                 (1/s^i) * ∫ y, y^i * G.density y ∂MeasureTheory.volume := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      show g y = 1 / s^i * (y^i * G.density y)
      simp only [hg_def]
      rw [div_pow]
      ring
    rw [hgint]
    -- Now: s^i * (s * (s⁻¹ • ((1/s^i) * ∫ y^i · G.density y dy))) = ∫ y^i · G.density y dy
    rw [smul_eq_mul]
    have hsi_pos : (0:ℝ) < s^i := by positivity
    have hsi_ne : (s^i : ℝ) ≠ 0 := ne_of_gt hsi_pos
    have hs_ne : (s : ℝ) ≠ 0 := ne_of_gt hs_pos
    field_simp
  refine ⟨s, hs_ge_one, Ft, Ft', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact div_pos hσ1 hs_sq_pos
    · exact (div_le_one hs_sq_pos).mpr hs_sq_ge1
    · exact div_pos hσ2 hs_sq_pos
    · exact (div_le_one hs_sq_pos).mpr hs_sq_ge2
    · exact div_pos hσ1' hs_sq_pos
    · exact (div_le_one hs_sq_pos).mpr hs_sq_ge1'
    · exact div_pos hσ2' hs_sq_pos
    · exact (div_le_one hs_sq_pos).mpr hs_sq_ge2'
  · constructor
    · rintro (hμ | hσ)
      · left
        intro heq
        apply hμ
        show F.comp1.mean / s = F.comp2.mean / s
        rw [heq]
      · right
        intro heq
        apply hσ
        show F.comp1.varSq / s^2 = F.comp2.varSq / s^2
        rw [heq]
    · rintro (hμ | hσ)
      · left
        intro heq
        apply hμ
        have hh : F.comp1.mean / s = F.comp2.mean / s := heq
        exact (div_left_inj' hs_pos.ne').mp hh
      · right
        intro heq
        apply hσ
        have hh : F.comp1.varSq / s^2 = F.comp2.varSq / s^2 := heq
        exact (div_left_inj' hs_sq_pos.ne').mp hh
  · constructor
    · rintro (hμ | hσ)
      · left
        intro heq
        apply hμ
        show F'.comp1.mean / s = F'.comp2.mean / s
        rw [heq]
      · right
        intro heq
        apply hσ
        show F'.comp1.varSq / s^2 = F'.comp2.varSq / s^2
        rw [heq]
    · rintro (hμ | hσ)
      · left
        intro heq
        apply hμ
        have hh : F'.comp1.mean / s = F'.comp2.mean / s := heq
        exact (div_left_inj' hs_pos.ne').mp hh
      · right
        intro heq
        apply hσ
        have hh : F'.comp1.varSq / s^2 = F'.comp2.varSq / s^2 := heq
        exact (div_left_inj' hs_sq_pos.ne').mp hh
  · exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i _; exact hMoment F Ft hDens_Ft i
  · intro i _; exact hMoment F' Ft' hDens_Ft' i
  · constructor
    · rintro (⟨hw1eq, hw2eq, hμ1eq, hσ1eq, hμ2eq, hσ2eq⟩ |
              ⟨hw1eq, hw2eq, hμ1eq, hσ1eq, hμ2eq, hσ2eq⟩)
      · left
        refine ⟨hw1eq, hw2eq, ?_, ?_, ?_, ?_⟩
        · exact (div_left_inj' hs_pos.ne').mp hμ1eq
        · exact (div_left_inj' hs_sq_pos.ne').mp hσ1eq
        · exact (div_left_inj' hs_pos.ne').mp hμ2eq
        · exact (div_left_inj' hs_sq_pos.ne').mp hσ2eq
      · right
        refine ⟨hw1eq, hw2eq, ?_, ?_, ?_, ?_⟩
        · exact (div_left_inj' hs_pos.ne').mp hμ1eq
        · exact (div_left_inj' hs_sq_pos.ne').mp hσ1eq
        · exact (div_left_inj' hs_pos.ne').mp hμ2eq
        · exact (div_left_inj' hs_sq_pos.ne').mp hσ2eq
    · rintro (⟨hw1eq, hw2eq, hμ1eq, hσ1eq, hμ2eq, hσ2eq⟩ |
              ⟨hw1eq, hw2eq, hμ1eq, hσ1eq, hμ2eq, hσ2eq⟩)
      · left
        refine ⟨hw1eq, hw2eq, ?_, ?_, ?_, ?_⟩
        · show F.comp1.mean / s = F'.comp1.mean / s
          rw [hμ1eq]
        · show F.comp1.varSq / s^2 = F'.comp1.varSq / s^2
          rw [hσ1eq]
        · show F.comp2.mean / s = F'.comp2.mean / s
          rw [hμ2eq]
        · show F.comp2.varSq / s^2 = F'.comp2.varSq / s^2
          rw [hσ2eq]
      · right
        refine ⟨hw1eq, hw2eq, ?_, ?_, ?_, ?_⟩
        · show F.comp1.mean / s = F'.comp2.mean / s
          rw [hμ1eq]
        · show F.comp1.varSq / s^2 = F'.comp2.varSq / s^2
          rw [hσ1eq]
        · show F.comp2.mean / s = F'.comp1.mean / s
          rw [hμ2eq]
        · show F.comp2.varSq / s^2 = F'.comp1.varSq / s^2
          rw [hσ2eq]

end Workspace.ProofLemmas
