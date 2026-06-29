import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureRawMoments
import Workspace.Types.L1AndTVDistance
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureRelabelEquiv
import Workspace.Types.MixtureDeconvolution
import Workspace.ProofLemmas.Lemma5DeconvolutionTVGap
import Workspace.ProofLemmas.Lemma6DeconvolutionPreservesMoments
import Workspace.ProofLemmas.Lemma9MomentGap
import Workspace.ProofLemmas.SublemmaStandardize

set_option maxHeartbeats 1600000

namespace Workspace.MainTheorem

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.MixtureRawMoments
open Workspace.Types.L1AndTVDistance
open Workspace.Types.EpsilonStandardPair
open Workspace.Types.MixtureRelabelEquiv
open Workspace.Types.MixtureDeconvolution

/--
**Theorem 4 (Moitra--Valiant, Polynomially Robust Identifiability).**
-/
theorem theorem_4_polynomially_robust_identifiability :
    ∃ c : ℝ, 0 < c ∧
      ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
        0 < ε → ε < c →
        Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
        ∃ i ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
            |Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F i
              - Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F' i|
              ≥ ε ^ 67 := by
  obtain ⟨K5, ε_max, hK5_pos, hε_max_pos, hL5⟩ := Workspace.ProofLemmas.Lemma5DeconvolutionTVGap.Lemma5DeconvolutionTVGap
  obtain ⟨K9, hK9_pos, hL9⟩ := Workspace.ProofLemmas.Lemma9MomentGap.Lemma9MomentGap
  -- Lemma 9 is now in threshold form: instantiate at the fixed L¹ constant K = 2·K5
  -- to obtain a K-dependent threshold ε_max9.
  have h2K5_pos : 0 < 2 * K5 := by linarith
  obtain ⟨ε_max9, hε_max9_pos, hL9'⟩ := hL9 (2 * K5) h2K5_pos
  refine ⟨min (min (K9 * K5 / 17280) ε_max) ε_max9, by
    refine lt_min (lt_min ?_ hε_max_pos) hε_max9_pos
    positivity, ?_⟩
  intro F F' ε hε_pos hε_lt h_std
  have hε_le_ε_max : ε ≤ ε_max :=
    le_of_lt (lt_of_lt_of_le hε_lt (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hε_le_ε_max9 : ε ≤ ε_max9 :=
    le_of_lt (lt_of_lt_of_le hε_lt (min_le_right _ _))
  obtain ⟨α, h1, h2, hα_ge, hvar_lb, hTV_lb⟩ := hL5 F F' ε hε_pos hε_le_ε_max h_std
  -- Fα, Fα' are the deconvolved mixtures.
  set Fα : GaussianMixture2 := deconvMixture2 F α h1 with hFα_def
  set Fα' : GaussianMixture2 := deconvMixture2 F' α h2 with hFα'_def
  -- Convert TV lower bound to L1 lower bound.
  have hL1_lb : (2 * K5) * ε ^ 4 ≤ L1NormMixtureDiff Fα Fα' := by
    have hTV_eq : TVDistance Fα Fα' = (1/2) * L1NormMixtureDiff Fα Fα' := rfl
    rw [hTV_eq] at hTV_lb
    linarith
  -- Apply Lemma 9 to get a moment-gap on the deconvolved mixtures.
  obtain ⟨i₀, hi₀_mem, hM_lb⟩ :=
    hL9' F F' ε α h1 h2 hε_pos hε_le_ε_max9 h_std hvar_lb hα_ge hL1_lb
  -- Variance upper bounds for Lemma 6.
  have hF_comp1_var : F.comp1.varSq ≤ 1 := h_std.means_and_vars_bounded.1.1
  have hF_comp2_var : F.comp2.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.1
  have hF'_comp1_var : F'.comp1.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.2.1
  have hF'_comp2_var : F'.comp2.varSq ≤ 1 := h_std.means_and_vars_bounded.1.2.2.2
  have h_var_upper :
      F.comp1.varSq ≤ 1 ∧ F.comp2.varSq ≤ 1 ∧
      F'.comp1.varSq ≤ 1 ∧ F'.comp2.varSq ≤ 1 :=
    ⟨hF_comp1_var, hF_comp2_var, hF'_comp1_var, hF'_comp2_var⟩
  -- Apply Lemma 6 with k = 6.
  have hL6 := Workspace.ProofLemmas.Lemma6DeconvolutionPreservesMoments
                F F' α h1 h2 hα_ge h_var_upper 6 (by norm_num)
  -- Express i₀ as (i₀ - 1) + 1.
  have hi₀_pos : 1 ≤ i₀ := by fin_cases hi₀_mem <;> norm_num
  have hi₀_le : i₀ ≤ 6 := by fin_cases hi₀_mem <;> norm_num
  set j₀ : ℕ := i₀ - 1 with hj₀_def
  have hj₀_range : j₀ ∈ Finset.range 6 := by
    rw [Finset.mem_range]
    omega
  have hi₀_eq : i₀ = j₀ + 1 := by omega
  -- f6_dec j = |M_{j+1}(Fα) - M_{j+1}(Fα')|; f6 j = |M_{j+1}(F) - M_{j+1}(F')|.
  set f6_dec : ℕ → ℝ := fun i =>
      |rawMoment_ofMixture2 Fα (i + 1) - rawMoment_ofMixture2 Fα' (i + 1)| with hf6_dec_def
  set f6 : ℕ → ℝ := fun i =>
      |rawMoment_ofMixture2 F (i + 1) - rawMoment_ofMixture2 F' (i + 1)| with hf6_def
  have h_f6_dec_nn : ∀ i ∈ Finset.range 6, 0 ≤ f6_dec i := by
    intro i _; exact abs_nonneg _
  -- Single-term bound: f6_dec j₀ ≤ Σ f6_dec.
  have h_single_le : f6_dec j₀ ≤ (Finset.range 6).sum f6_dec :=
    Finset.single_le_sum (f := f6_dec) (s := Finset.range 6) h_f6_dec_nn hj₀_range
  -- f6_dec j₀ = |M_{i₀}(Fα) - M_{i₀}(Fα')|.
  have hj₀_eq : f6_dec j₀ = |rawMoment_ofMixture2 Fα i₀ - rawMoment_ofMixture2 Fα' i₀| := by
    show |rawMoment_ofMixture2 Fα (j₀ + 1) - rawMoment_ofMixture2 Fα' (j₀ + 1)|
        = |rawMoment_ofMixture2 Fα i₀ - rawMoment_ofMixture2 Fα' i₀|
    rw [← hi₀_eq]
  -- So K9 * (2 K5) * ε^66 ≤ Σ f6_dec.
  have h_chain1 : K9 * (2 * K5) * ε ^ 66 ≤ (Finset.range 6).sum f6_dec := by
    rw [← hj₀_eq] at hM_lb
    exact le_trans hM_lb h_single_le
  -- Show (6 : ℝ) * 2^6 * doubleFactorial 5 = 5760.
  have h_const : ((6 : ℕ) : ℝ) * (2 : ℝ)^6 * (Nat.doubleFactorial (6 - 1) : ℝ) = 5760 := by
    norm_num [Nat.doubleFactorial]
  -- hL6 says Σ f6_dec ≤ (6 * 2^6 * doubleFactorial 5) * Σ f6, i.e., ≤ 5760 * Σ f6.
  have hL6' : (Finset.range 6).sum f6_dec ≤ 5760 * (Finset.range 6).sum f6 := by
    have hL6_rewritten :
        (Finset.range 6).sum f6_dec ≤
          ((6 : ℕ) : ℝ) * (2 : ℝ)^6 * (Nat.doubleFactorial (6 - 1) : ℝ) *
          (Finset.range 6).sum f6 := hL6
    rw [h_const] at hL6_rewritten
    exact hL6_rewritten
  have h_chain2 : K9 * (2 * K5) * ε ^ 66 ≤ 5760 * (Finset.range 6).sum f6 :=
    le_trans h_chain1 hL6'
  -- Divide both sides by 5760: K9 * K5 / 2880 * ε^66 ≤ Σ f6.
  have h_sum_lb : K9 * K5 / 2880 * ε ^ 66 ≤ (Finset.range 6).sum f6 := by linarith
  -- Pigeonhole: ∃ j ∈ range 6 with K9 K5 ε^66 / 17280 ≤ f6 j.
  have h_ex : ∃ j ∈ Finset.range 6, K9 * K5 * ε ^ 66 / 17280 ≤ f6 j := by
    by_contra h_neg
    push_neg at h_neg
    have h_sum_lt : (Finset.range 6).sum f6 < 6 * (K9 * K5 * ε ^ 66 / 17280) := by
      have h_card : (Finset.range 6).card = 6 := Finset.card_range 6
      calc (Finset.range 6).sum f6
          < (Finset.range 6).sum (fun _ => K9 * K5 * ε ^ 66 / 17280) := by
            apply Finset.sum_lt_sum_of_nonempty
            · exact Finset.nonempty_range_iff.mpr (by norm_num)
            · intro j hj; exact h_neg j hj
        _ = 6 * (K9 * K5 * ε ^ 66 / 17280) := by
            rw [Finset.sum_const, h_card]; ring
    linarith
  obtain ⟨j, hj_range, hj_bound⟩ := h_ex
  have hj_lt : j < 6 := Finset.mem_range.mp hj_range
  refine ⟨j + 1, ?_, ?_⟩
  · -- j + 1 ∈ {1,2,3,4,5,6}
    interval_cases j <;> decide
  · -- |M_{j+1}(F) - M_{j+1}(F')| ≥ ε^67
    have h_ε67 : ε ^ 67 ≤ K9 * K5 * ε ^ 66 / 17280 := by
      have hε66_pos : 0 < ε ^ 66 := by positivity
      have hε_le_c : ε ≤ K9 * K5 / 17280 :=
        le_of_lt (lt_of_lt_of_le hε_lt (le_trans (min_le_left _ _) (min_le_left _ _)))
      have step : ε * ε ^ 66 ≤ (K9 * K5 / 17280) * ε ^ 66 :=
        mul_le_mul_of_nonneg_right hε_le_c (le_of_lt hε66_pos)
      have hpow : ε ^ 67 = ε * ε ^ 66 := by ring
      rw [hpow]
      linarith
    have h_total : ε ^ 67 ≤ f6 j := le_trans h_ε67 hj_bound
    show |rawMoment_ofMixture2 F (j + 1) - rawMoment_ofMixture2 F' (j + 1)| ≥ ε ^ 67
    exact h_total

/--
**Six-moments-suffice (qualitative limit).**
-/
theorem six_moments_suffice
    (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2)
    (hw1 : 0 < F.weight1) (hw2 : 0 < F.weight2)
    (hw1' : 0 < F'.weight1) (hw2' : 0 < F'.weight2)
    (hF_nondeg : F.comp1.mean ≠ F.comp2.mean ∨ F.comp1.varSq ≠ F.comp2.varSq)
    (hF'_nondeg : F'.comp1.mean ≠ F'.comp2.mean ∨ F'.comp1.varSq ≠ F'.comp2.varSq)
    (h_moments : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
        Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F i
          = Workspace.Types.MixtureRawMoments.rawMoment_ofMixture2 F' i) :
    Workspace.Types.MixtureRelabelEquiv.MixtureRelabelEquiv F F' := by
  -- Standardize.
  obtain ⟨s, hs_ge_one, Ft, Ft', hvars, hndF, hndF', hweq, hmom_F, hmom_F', hequiv⟩ :=
    Workspace.ProofLemmas.SublemmaStandardize F F' hw1 hw2 hw1' hw2'
  rw [← hequiv]
  have hs_pos : 0 < s := by linarith
  have hmoments_Ft : ∀ i ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ),
      rawMoment_ofMixture2 Ft i = rawMoment_ofMixture2 Ft' i := by
    intro i hi
    have hi' : i ∈ ({0, 1, 2, 3, 4, 5, 6} : Finset ℕ) := by
      fin_cases hi <;> decide
    have eF := hmom_F i hi'
    have eF' := hmom_F' i hi'
    have hsi_pos : 0 < s ^ i := by positivity
    have key : s ^ i * rawMoment_ofMixture2 Ft i = s ^ i * rawMoment_ofMixture2 Ft' i := by
      rw [eF, eF']
      exact h_moments i hi
    exact mul_left_cancel₀ (ne_of_gt hsi_pos) key
  have hFt_nondeg : Ft.comp1.mean ≠ Ft.comp2.mean ∨ Ft.comp1.varSq ≠ Ft.comp2.varSq :=
    hndF.mpr hF_nondeg
  have hFt'_nondeg : Ft'.comp1.mean ≠ Ft'.comp2.mean ∨ Ft'.comp1.varSq ≠ Ft'.comp2.varSq :=
    hndF'.mpr hF'_nondeg
  have hwt1 : 0 < Ft.weight1 := by rw [hweq.1]; exact hw1
  have hwt2 : 0 < Ft.weight2 := by rw [hweq.2.1]; exact hw2
  have hwt1' : 0 < Ft'.weight1 := by rw [hweq.2.2.1]; exact hw1'
  have hwt2' : 0 < Ft'.weight2 := by rw [hweq.2.2.2]; exact hw2'
  obtain ⟨hv1_pos, hv1_le, hv2_pos, hv2_le, hv3_pos, hv3_le, hv4_pos, hv4_le⟩ := hvars
  by_contra h_neq
  obtain ⟨c, hc_pos, hT4⟩ := theorem_4_polynomially_robust_identifiability
  -- δ₁: min weight.
  let δ₁ : ℝ := min (min Ft.weight1 Ft.weight2) (min Ft'.weight1 Ft'.weight2)
  have hδ₁_pos : 0 < δ₁ := by
    refine lt_min (lt_min hwt1 hwt2) (lt_min hwt1' hwt2')
  -- δ₂: max |mean|, at least 1.
  let δ₂ : ℝ := max (max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                          (max |Ft'.comp1.mean| |Ft'.comp2.mean|)) 1
  have hδ₂_ge_1 : 1 ≤ δ₂ := le_max_right _ _
  have hδ₂_pos : 0 < δ₂ := lt_of_lt_of_le zero_lt_one hδ₂_ge_1
  have hδ₂_ge_m1 : |Ft.comp1.mean| ≤ δ₂ := by
    have h1 : |Ft.comp1.mean| ≤ max |Ft.comp1.mean| |Ft.comp2.mean| := le_max_left _ _
    have h2 : max |Ft.comp1.mean| |Ft.comp2.mean| ≤
              max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) := le_max_left _ _
    have h3 : max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) ≤ δ₂ := le_max_left _ _
    linarith
  have hδ₂_ge_m2 : |Ft.comp2.mean| ≤ δ₂ := by
    have h1 : |Ft.comp2.mean| ≤ max |Ft.comp1.mean| |Ft.comp2.mean| := le_max_right _ _
    have h2 : max |Ft.comp1.mean| |Ft.comp2.mean| ≤
              max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) := le_max_left _ _
    have h3 : max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) ≤ δ₂ := le_max_left _ _
    linarith
  have hδ₂_ge_m3 : |Ft'.comp1.mean| ≤ δ₂ := by
    have h1 : |Ft'.comp1.mean| ≤ max |Ft'.comp1.mean| |Ft'.comp2.mean| := le_max_left _ _
    have h2 : max |Ft'.comp1.mean| |Ft'.comp2.mean| ≤
              max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) := le_max_right _ _
    have h3 : max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) ≤ δ₂ := le_max_left _ _
    linarith
  have hδ₂_ge_m4 : |Ft'.comp2.mean| ≤ δ₂ := by
    have h1 : |Ft'.comp2.mean| ≤ max |Ft'.comp1.mean| |Ft'.comp2.mean| := le_max_right _ _
    have h2 : max |Ft'.comp1.mean| |Ft'.comp2.mean| ≤
              max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) := le_max_right _ _
    have h3 : max (max |Ft.comp1.mean| |Ft.comp2.mean|)
                  (max |Ft'.comp1.mean| |Ft'.comp2.mean|) ≤ δ₂ := le_max_left _ _
    linarith
  let δ₃F : ℝ := |Ft.comp1.mean - Ft.comp2.mean| + |Ft.comp1.varSq - Ft.comp2.varSq|
  have hδ₃F_pos : 0 < δ₃F := by
    rcases hFt_nondeg with hmne | hvne
    · have h1 : 0 < |Ft.comp1.mean - Ft.comp2.mean| := abs_pos.mpr (sub_ne_zero_of_ne hmne)
      have h2 : 0 ≤ |Ft.comp1.varSq - Ft.comp2.varSq| := abs_nonneg _
      show 0 < |Ft.comp1.mean - Ft.comp2.mean| + |Ft.comp1.varSq - Ft.comp2.varSq|
      linarith
    · have h1 : 0 ≤ |Ft.comp1.mean - Ft.comp2.mean| := abs_nonneg _
      have h2 : 0 < |Ft.comp1.varSq - Ft.comp2.varSq| := abs_pos.mpr (sub_ne_zero_of_ne hvne)
      show 0 < |Ft.comp1.mean - Ft.comp2.mean| + |Ft.comp1.varSq - Ft.comp2.varSq|
      linarith
  let δ₃F' : ℝ := |Ft'.comp1.mean - Ft'.comp2.mean| + |Ft'.comp1.varSq - Ft'.comp2.varSq|
  have hδ₃F'_pos : 0 < δ₃F' := by
    rcases hFt'_nondeg with hmne | hvne
    · have h1 : 0 < |Ft'.comp1.mean - Ft'.comp2.mean| := abs_pos.mpr (sub_ne_zero_of_ne hmne)
      have h2 : 0 ≤ |Ft'.comp1.varSq - Ft'.comp2.varSq| := abs_nonneg _
      show 0 < |Ft'.comp1.mean - Ft'.comp2.mean| + |Ft'.comp1.varSq - Ft'.comp2.varSq|
      linarith
    · have h1 : 0 ≤ |Ft'.comp1.mean - Ft'.comp2.mean| := abs_nonneg _
      have h2 : 0 < |Ft'.comp1.varSq - Ft'.comp2.varSq| := abs_pos.mpr (sub_ne_zero_of_ne hvne)
      show 0 < |Ft'.comp1.mean - Ft'.comp2.mean| + |Ft'.comp1.varSq - Ft'.comp2.varSq|
      linarith
  let d_id : ℝ := (|Ft.weight1 - Ft'.weight1| + |Ft.comp1.mean - Ft'.comp1.mean|
                    + |Ft.comp1.varSq - Ft'.comp1.varSq|)
                  + (|Ft.weight2 - Ft'.weight2| + |Ft.comp2.mean - Ft'.comp2.mean|
                      + |Ft.comp2.varSq - Ft'.comp2.varSq|)
  let d_swap : ℝ := (|Ft.weight1 - Ft'.weight2| + |Ft.comp1.mean - Ft'.comp2.mean|
                      + |Ft.comp1.varSq - Ft'.comp2.varSq|)
                    + (|Ft.weight2 - Ft'.weight1| + |Ft.comp2.mean - Ft'.comp1.mean|
                        + |Ft.comp2.varSq - Ft'.comp1.varSq|)
  have h_not_id : ¬ (Ft.weight1 = Ft'.weight1 ∧ Ft.weight2 = Ft'.weight2 ∧
                     Ft.comp1.mean = Ft'.comp1.mean ∧ Ft.comp1.varSq = Ft'.comp1.varSq ∧
                     Ft.comp2.mean = Ft'.comp2.mean ∧ Ft.comp2.varSq = Ft'.comp2.varSq) := fun h => h_neq (Or.inl h)
  have h_not_swap : ¬ (Ft.weight1 = Ft'.weight2 ∧ Ft.weight2 = Ft'.weight1 ∧
                       Ft.comp1.mean = Ft'.comp2.mean ∧ Ft.comp1.varSq = Ft'.comp2.varSq ∧
                       Ft.comp2.mean = Ft'.comp1.mean ∧ Ft.comp2.varSq = Ft'.comp1.varSq) := fun h => h_neq (Or.inr h)
  have hd_id_pos : 0 < d_id := by
    by_contra h_le
    push_neg at h_le
    have ha1 : 0 ≤ |Ft.weight1 - Ft'.weight1| := abs_nonneg _
    have ha2 : 0 ≤ |Ft.comp1.mean - Ft'.comp1.mean| := abs_nonneg _
    have ha3 : 0 ≤ |Ft.comp1.varSq - Ft'.comp1.varSq| := abs_nonneg _
    have ha4 : 0 ≤ |Ft.weight2 - Ft'.weight2| := abs_nonneg _
    have ha5 : 0 ≤ |Ft.comp2.mean - Ft'.comp2.mean| := abs_nonneg _
    have ha6 : 0 ≤ |Ft.comp2.varSq - Ft'.comp2.varSq| := abs_nonneg _
    have hd_id_nn : 0 ≤ d_id := by
      show 0 ≤ (|Ft.weight1 - Ft'.weight1| + |Ft.comp1.mean - Ft'.comp1.mean|
                + |Ft.comp1.varSq - Ft'.comp1.varSq|)
                + (|Ft.weight2 - Ft'.weight2| + |Ft.comp2.mean - Ft'.comp2.mean|
                + |Ft.comp2.varSq - Ft'.comp2.varSq|)
      linarith
    have h_zero : d_id = 0 := le_antisymm h_le hd_id_nn
    have h_d_eq : (|Ft.weight1 - Ft'.weight1| + |Ft.comp1.mean - Ft'.comp1.mean|
                    + |Ft.comp1.varSq - Ft'.comp1.varSq|)
                  + (|Ft.weight2 - Ft'.weight2| + |Ft.comp2.mean - Ft'.comp2.mean|
                  + |Ft.comp2.varSq - Ft'.comp2.varSq|) = 0 := h_zero
    have h1 : |Ft.weight1 - Ft'.weight1| = 0 := by linarith
    have h2 : |Ft.comp1.mean - Ft'.comp1.mean| = 0 := by linarith
    have h3 : |Ft.comp1.varSq - Ft'.comp1.varSq| = 0 := by linarith
    have h4 : |Ft.weight2 - Ft'.weight2| = 0 := by linarith
    have h5 : |Ft.comp2.mean - Ft'.comp2.mean| = 0 := by linarith
    have h6 : |Ft.comp2.varSq - Ft'.comp2.varSq| = 0 := by linarith
    have e1 : Ft.weight1 = Ft'.weight1 := sub_eq_zero.mp (abs_eq_zero.mp h1)
    have e2 : Ft.comp1.mean = Ft'.comp1.mean := sub_eq_zero.mp (abs_eq_zero.mp h2)
    have e3 : Ft.comp1.varSq = Ft'.comp1.varSq := sub_eq_zero.mp (abs_eq_zero.mp h3)
    have e4 : Ft.weight2 = Ft'.weight2 := sub_eq_zero.mp (abs_eq_zero.mp h4)
    have e5 : Ft.comp2.mean = Ft'.comp2.mean := sub_eq_zero.mp (abs_eq_zero.mp h5)
    have e6 : Ft.comp2.varSq = Ft'.comp2.varSq := sub_eq_zero.mp (abs_eq_zero.mp h6)
    exact h_not_id ⟨e1, e4, e2, e3, e5, e6⟩
  have hd_swap_pos : 0 < d_swap := by
    by_contra h_le
    push_neg at h_le
    have ha1 : 0 ≤ |Ft.weight1 - Ft'.weight2| := abs_nonneg _
    have ha2 : 0 ≤ |Ft.comp1.mean - Ft'.comp2.mean| := abs_nonneg _
    have ha3 : 0 ≤ |Ft.comp1.varSq - Ft'.comp2.varSq| := abs_nonneg _
    have ha4 : 0 ≤ |Ft.weight2 - Ft'.weight1| := abs_nonneg _
    have ha5 : 0 ≤ |Ft.comp2.mean - Ft'.comp1.mean| := abs_nonneg _
    have ha6 : 0 ≤ |Ft.comp2.varSq - Ft'.comp1.varSq| := abs_nonneg _
    have hd_swap_nn : 0 ≤ d_swap := by
      show 0 ≤ (|Ft.weight1 - Ft'.weight2| + |Ft.comp1.mean - Ft'.comp2.mean|
                + |Ft.comp1.varSq - Ft'.comp2.varSq|)
                + (|Ft.weight2 - Ft'.weight1| + |Ft.comp2.mean - Ft'.comp1.mean|
                + |Ft.comp2.varSq - Ft'.comp1.varSq|)
      linarith
    have h_zero : d_swap = 0 := le_antisymm h_le hd_swap_nn
    have h_d_eq : (|Ft.weight1 - Ft'.weight2| + |Ft.comp1.mean - Ft'.comp2.mean|
                    + |Ft.comp1.varSq - Ft'.comp2.varSq|)
                  + (|Ft.weight2 - Ft'.weight1| + |Ft.comp2.mean - Ft'.comp1.mean|
                  + |Ft.comp2.varSq - Ft'.comp1.varSq|) = 0 := h_zero
    have h1 : |Ft.weight1 - Ft'.weight2| = 0 := by linarith
    have h2 : |Ft.comp1.mean - Ft'.comp2.mean| = 0 := by linarith
    have h3 : |Ft.comp1.varSq - Ft'.comp2.varSq| = 0 := by linarith
    have h4 : |Ft.weight2 - Ft'.weight1| = 0 := by linarith
    have h5 : |Ft.comp2.mean - Ft'.comp1.mean| = 0 := by linarith
    have h6 : |Ft.comp2.varSq - Ft'.comp1.varSq| = 0 := by linarith
    have e1 : Ft.weight1 = Ft'.weight2 := sub_eq_zero.mp (abs_eq_zero.mp h1)
    have e2 : Ft.comp1.mean = Ft'.comp2.mean := sub_eq_zero.mp (abs_eq_zero.mp h2)
    have e3 : Ft.comp1.varSq = Ft'.comp2.varSq := sub_eq_zero.mp (abs_eq_zero.mp h3)
    have e4 : Ft.weight2 = Ft'.weight1 := sub_eq_zero.mp (abs_eq_zero.mp h4)
    have e5 : Ft.comp2.mean = Ft'.comp1.mean := sub_eq_zero.mp (abs_eq_zero.mp h5)
    have e6 : Ft.comp2.varSq = Ft'.comp1.varSq := sub_eq_zero.mp (abs_eq_zero.mp h6)
    exact h_not_swap ⟨e1, e4, e2, e3, e5, e6⟩
  let δ₄ : ℝ := min d_id d_swap
  have hδ₄_pos : 0 < δ₄ := lt_min hd_id_pos hd_swap_pos
  let ε : ℝ :=
    min (c / 2) (min δ₁ (min δ₃F (min δ₃F' (min δ₄ (1 / δ₂)))))
  have h_inv_δ₂_pos : 0 < 1 / δ₂ := by positivity
  have hε_pos : 0 < ε := by
    refine lt_min (by linarith) ?_
    refine lt_min hδ₁_pos ?_
    refine lt_min hδ₃F_pos ?_
    refine lt_min hδ₃F'_pos ?_
    exact lt_min hδ₄_pos h_inv_δ₂_pos
  have hε_le_chalf : ε ≤ c / 2 := min_le_left _ _
  have hε_lt_c : ε < c := by linarith
  have hε_rest : ε ≤ min δ₁ (min δ₃F (min δ₃F' (min δ₄ (1 / δ₂)))) := min_le_right _ _
  have hε_le_δ₁ : ε ≤ δ₁ := le_trans hε_rest (min_le_left _ _)
  have hε_le_δ₃F : ε ≤ δ₃F :=
    le_trans hε_rest (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_le_δ₃F' : ε ≤ δ₃F' :=
    le_trans hε_rest (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε_le_δ₄ : ε ≤ δ₄ :=
    le_trans hε_rest (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε_le_inv : ε ≤ 1 / δ₂ :=
    le_trans hε_rest (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  -- Build EpsilonStandardPair Ft Ft' ε.
  have hε_le_w1 : ε ≤ Ft.weight1 :=
    le_trans hε_le_δ₁ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε_le_w2 : ε ≤ Ft.weight2 :=
    le_trans hε_le_δ₁ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε_le_w1' : ε ≤ Ft'.weight1 :=
    le_trans hε_le_δ₁ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_le_w2' : ε ≤ Ft'.weight2 :=
    le_trans hε_le_δ₁ (le_trans (min_le_right _ _) (min_le_right _ _))
  -- |μ| ≤ 1/ε.
  have h_main : ε * δ₂ ≤ 1 := by
    have : ε * δ₂ ≤ (1 / δ₂) * δ₂ :=
      mul_le_mul_of_nonneg_right hε_le_inv (le_of_lt hδ₂_pos)
    have h_simp : (1 / δ₂) * δ₂ = 1 := by field_simp
    linarith
  have h_one_div : ∀ μ, |μ| ≤ δ₂ → |μ| ≤ 1 / ε := by
    intro μ hμ
    rw [le_div_iff₀ hε_pos]
    calc |μ| * ε ≤ δ₂ * ε := mul_le_mul_of_nonneg_right hμ (le_of_lt hε_pos)
      _ = ε * δ₂ := by ring
      _ ≤ 1 := h_main
  have h_std : EpsilonStandardPair Ft Ft' ε := by
    refine EpsilonStandardPair.mk' ⟨hε_le_w1, hε_le_w2, hε_le_w1', hε_le_w2'⟩ ?_ ?_ ?_
    · refine ⟨⟨hv1_le, hv2_le, hv3_le, hv4_le⟩, ?_, ?_, ?_, ?_⟩
      · exact h_one_div _ hδ₂_ge_m1
      · exact h_one_div _ hδ₂_ge_m2
      · exact h_one_div _ hδ₂_ge_m3
      · exact h_one_div _ hδ₂_ge_m4
    · refine ⟨?_, ?_⟩
      · show |Ft.comp1.mean - Ft.comp2.mean| + |Ft.comp1.varSq - Ft.comp2.varSq| ≥ ε
        exact hε_le_δ₃F
      · show |Ft'.comp1.mean - Ft'.comp2.mean| + |Ft'.comp1.varSq - Ft'.comp2.varSq| ≥ ε
        exact hε_le_δ₃F'
    · have hδ₄_le_id : δ₄ ≤ d_id := min_le_left _ _
      have hδ₄_le_swap : δ₄ ≤ d_swap := min_le_right _ _
      have hε_le_id : ε ≤ d_id := le_trans hε_le_δ₄ hδ₄_le_id
      have hε_le_swap : ε ≤ d_swap := le_trans hε_le_δ₄ hδ₄_le_swap
      exact le_min hε_le_id hε_le_swap
  obtain ⟨i₀, hi₀_mem, hM_gap⟩ := hT4 Ft Ft' ε hε_pos hε_lt_c h_std
  have h_eq : rawMoment_ofMixture2 Ft i₀ = rawMoment_ofMixture2 Ft' i₀ :=
    hmoments_Ft i₀ hi₀_mem
  have h_abs_zero : |rawMoment_ofMixture2 Ft i₀ - rawMoment_ofMixture2 Ft' i₀| = 0 := by
    rw [h_eq, sub_self, abs_zero]
  rw [h_abs_zero] at hM_gap
  have hε67_pos : 0 < ε ^ 67 := pow_pos hε_pos 67
  linarith

end Workspace.MainTheorem
