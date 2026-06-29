import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.EpsilonStandardPair
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.L1AndTVDistance
import Workspace.ProofLemmas.Lemma5Case1Assembly
import Workspace.ProofLemmas.Lemma5Case2aAssembly
import Workspace.ProofLemmas.Lemma5Case2bAssembly

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Lemma5DeconvolutionTVGap

open Workspace.Types.GaussianPDF
open Workspace.Types.GaussianMixture2
open Workspace.Types.EpsilonStandardPair
open Workspace.Types.MixtureDeconvolution
open Workspace.Types.L1AndTVDistance

/-- Swap the two components of a `GaussianMixture2`. -/
private noncomputable def swapMix
    (F : Workspace.Types.GaussianMixture2.GaussianMixture2) :
    Workspace.Types.GaussianMixture2.GaussianMixture2 where
  weight1 := F.weight2
  weight2 := F.weight1
  comp1 := F.comp2
  comp2 := F.comp1
  weight1_nonneg := F.weight2_nonneg
  weight2_nonneg := F.weight1_nonneg
  weights_sum_one := by
    have := F.weights_sum_one
    linarith

@[simp] private lemma swapMix_weight1 (F : GaussianMixture2) :
    (swapMix F).weight1 = F.weight2 := rfl
@[simp] private lemma swapMix_weight2 (F : GaussianMixture2) :
    (swapMix F).weight2 = F.weight1 := rfl
@[simp] private lemma swapMix_comp1 (F : GaussianMixture2) :
    (swapMix F).comp1 = F.comp2 := rfl
@[simp] private lemma swapMix_comp2 (F : GaussianMixture2) :
    (swapMix F).comp2 = F.comp1 := rfl

/-- EpsilonStandardPair is preserved under swapping the components of F. -/
private lemma epsStd_swap_left
    {F F' : GaussianMixture2} {ε : ℝ}
    (h : EpsilonStandardPair F F' ε) :
    EpsilonStandardPair (swapMix F) F' ε := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨h.weights_bounded.2.1, h.weights_bounded.1,
           h.weights_bounded.2.2.1, h.weights_bounded.2.2.2⟩
  · exact ⟨⟨h.means_and_vars_bounded.1.2.1, h.means_and_vars_bounded.1.1,
            h.means_and_vars_bounded.1.2.2.1, h.means_and_vars_bounded.1.2.2.2⟩,
           h.means_and_vars_bounded.2.2.1, h.means_and_vars_bounded.2.1,
           h.means_and_vars_bounded.2.2.2.1, h.means_and_vars_bounded.2.2.2.2⟩
  · refine ⟨?_, h.intra_separation.2⟩
    have := h.intra_separation.1
    show |F.comp2.mean - F.comp1.mean| + |F.comp2.varSq - F.comp1.varSq| ≥ ε
    rw [abs_sub_comm F.comp2.mean F.comp1.mean, abs_sub_comm F.comp2.varSq F.comp1.varSq]
    exact this
  · have hInter := h.inter_separation
    have e1 : ((|(swapMix F).weight1 - F'.weight1| + |(swapMix F).comp1.mean - F'.comp1.mean|
                + |(swapMix F).comp1.varSq - F'.comp1.varSq|)
              + (|(swapMix F).weight2 - F'.weight2| + |(swapMix F).comp2.mean - F'.comp2.mean|
                + |(swapMix F).comp2.varSq - F'.comp2.varSq|))
            = (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                + |F.comp2.varSq - F'.comp1.varSq|)
              + (|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
                + |F.comp1.varSq - F'.comp2.varSq|) := by
      simp only [swapMix_weight1, swapMix_weight2, swapMix_comp1, swapMix_comp2]
    have e2 : ((|(swapMix F).weight1 - F'.weight2| + |(swapMix F).comp1.mean - F'.comp2.mean|
                + |(swapMix F).comp1.varSq - F'.comp2.varSq|)
              + (|(swapMix F).weight2 - F'.weight1| + |(swapMix F).comp2.mean - F'.comp1.mean|
                + |(swapMix F).comp2.varSq - F'.comp1.varSq|))
            = (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                + |F.comp2.varSq - F'.comp2.varSq|)
              + (|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
                + |F.comp1.varSq - F'.comp1.varSq|) := by
      simp only [swapMix_weight1, swapMix_weight2, swapMix_comp1, swapMix_comp2]
    rw [e1, e2]
    rw [show (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                + |F.comp2.varSq - F'.comp1.varSq|)
              + (|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
                + |F.comp1.varSq - F'.comp2.varSq|)
            = (|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
                + |F.comp1.varSq - F'.comp2.varSq|)
              + (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                + |F.comp2.varSq - F'.comp1.varSq|) from by ring,
        show (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                + |F.comp2.varSq - F'.comp2.varSq|)
              + (|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
                + |F.comp1.varSq - F'.comp1.varSq|)
            = (|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
                + |F.comp1.varSq - F'.comp1.varSq|)
              + (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                + |F.comp2.varSq - F'.comp2.varSq|) from by ring,
        min_comm]
    exact hInter

/-- EpsilonStandardPair is preserved under swapping F and F'. -/
private lemma epsStd_FF'_swap
    {F F' : GaussianMixture2} {ε : ℝ}
    (h : EpsilonStandardPair F F' ε) :
    EpsilonStandardPair F' F ε := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨h.weights_bounded.2.2.1, h.weights_bounded.2.2.2,
           h.weights_bounded.1, h.weights_bounded.2.1⟩
  · exact ⟨⟨h.means_and_vars_bounded.1.2.2.1, h.means_and_vars_bounded.1.2.2.2,
            h.means_and_vars_bounded.1.1, h.means_and_vars_bounded.1.2.1⟩,
           h.means_and_vars_bounded.2.2.2.1, h.means_and_vars_bounded.2.2.2.2,
           h.means_and_vars_bounded.2.1, h.means_and_vars_bounded.2.2.1⟩
  · exact ⟨h.intra_separation.2, h.intra_separation.1⟩
  · have hInter := h.inter_separation
    have e1 : (|F'.weight1 - F.weight1| + |F'.comp1.mean - F.comp1.mean|
                + |F'.comp1.varSq - F.comp1.varSq|)
              + (|F'.weight2 - F.weight2| + |F'.comp2.mean - F.comp2.mean|
                + |F'.comp2.varSq - F.comp2.varSq|)
            = (|F.weight1 - F'.weight1| + |F.comp1.mean - F'.comp1.mean|
                + |F.comp1.varSq - F'.comp1.varSq|)
              + (|F.weight2 - F'.weight2| + |F.comp2.mean - F'.comp2.mean|
                + |F.comp2.varSq - F'.comp2.varSq|) := by
      rw [abs_sub_comm F'.weight1 F.weight1, abs_sub_comm F'.comp1.mean F.comp1.mean,
          abs_sub_comm F'.comp1.varSq F.comp1.varSq, abs_sub_comm F'.weight2 F.weight2,
          abs_sub_comm F'.comp2.mean F.comp2.mean, abs_sub_comm F'.comp2.varSq F.comp2.varSq]
    have e2 : (|F'.weight1 - F.weight2| + |F'.comp1.mean - F.comp2.mean|
                + |F'.comp1.varSq - F.comp2.varSq|)
              + (|F'.weight2 - F.weight1| + |F'.comp2.mean - F.comp1.mean|
                + |F'.comp2.varSq - F.comp1.varSq|)
            = (|F.weight1 - F'.weight2| + |F.comp1.mean - F'.comp2.mean|
                + |F.comp1.varSq - F'.comp2.varSq|)
              + (|F.weight2 - F'.weight1| + |F.comp2.mean - F'.comp1.mean|
                + |F.comp2.varSq - F'.comp1.varSq|) := by
      rw [abs_sub_comm F'.weight1 F.weight2, abs_sub_comm F'.comp1.mean F.comp2.mean,
          abs_sub_comm F'.comp1.varSq F.comp2.varSq, abs_sub_comm F'.weight2 F.weight1,
          abs_sub_comm F'.comp2.mean F.comp1.mean, abs_sub_comm F'.comp2.varSq F.comp1.varSq]
      ring
    rw [e1, e2]
    exact hInter

/-- TVDistance is symmetric. -/
private lemma TVDistance_symm (F G : GaussianMixture2) :
    TVDistance F G = TVDistance G F := by
  unfold TVDistance L1NormMixtureDiff L1Norm
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [abs_sub_comm]

/-- The density of `deconvMixture2 (swapMix F) α h_sw` equals the density of
`deconvMixture2 F α h` pointwise. -/
private lemma deconv_swapMix_density_eq
    (F : GaussianMixture2) (α : ℝ)
    (h_sw : α < min (swapMix F).comp1.varSq (swapMix F).comp2.varSq)
    (h : α < min F.comp1.varSq F.comp2.varSq) (x : ℝ) :
    (deconvMixture2 (swapMix F) α h_sw).density x
      = (deconvMixture2 F α h).density x := by
  -- The density of a GaussianPDF depends only on mean and varSq.
  -- After unfolding everything, both sides give the same formula.
  simp only [GaussianMixture2.density_eq, GaussianPDF.density_eq,
             deconvMixture2_weight1, deconvMixture2_weight2]
  -- After simp, both sides will be a sum of two terms.
  -- We need to show: (weights, mean, varSq) match after rearrangement.
  show F.weight2 * ((1 / Real.sqrt (2 * Real.pi * (deconvMixture2 (swapMix F) α h_sw).comp1.varSq))
          * Real.exp (-(x - (deconvMixture2 (swapMix F) α h_sw).comp1.mean) ^ 2
                      / (2 * (deconvMixture2 (swapMix F) α h_sw).comp1.varSq))) +
       F.weight1 * ((1 / Real.sqrt (2 * Real.pi * (deconvMixture2 (swapMix F) α h_sw).comp2.varSq))
          * Real.exp (-(x - (deconvMixture2 (swapMix F) α h_sw).comp2.mean) ^ 2
                      / (2 * (deconvMixture2 (swapMix F) α h_sw).comp2.varSq))) =
       F.weight1 * ((1 / Real.sqrt (2 * Real.pi * (deconvMixture2 F α h).comp1.varSq))
          * Real.exp (-(x - (deconvMixture2 F α h).comp1.mean) ^ 2
                      / (2 * (deconvMixture2 F α h).comp1.varSq))) +
       F.weight2 * ((1 / Real.sqrt (2 * Real.pi * (deconvMixture2 F α h).comp2.varSq))
          * Real.exp (-(x - (deconvMixture2 F α h).comp2.mean) ^ 2
                      / (2 * (deconvMixture2 F α h).comp2.varSq)))
  simp only [deconvMixture2_comp1_mean, deconvMixture2_comp1_varSq,
             deconvMixture2_comp2_mean, deconvMixture2_comp2_varSq,
             swapMix_weight1, swapMix_weight2, swapMix_comp1, swapMix_comp2]
  ring

/-- TVDistance is invariant under swapping the components of the first deconvolved mixture. -/
private lemma TVDistance_deconv_swapMix_left
    (F : GaussianMixture2) (α : ℝ)
    (h_sw : α < min (swapMix F).comp1.varSq (swapMix F).comp2.varSq)
    (h : α < min F.comp1.varSq F.comp2.varSq)
    (G : GaussianMixture2) :
    TVDistance (deconvMixture2 (swapMix F) α h_sw) G
    = TVDistance (deconvMixture2 F α h) G := by
  unfold TVDistance L1NormMixtureDiff L1Norm
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [deconv_swapMix_density_eq F α h_sw h x]

/-- TVDistance is invariant under swapping the components of the second deconvolved mixture. -/
private lemma TVDistance_deconv_swapMix_right
    (G : GaussianMixture2)
    (F : GaussianMixture2) (α : ℝ)
    (h_sw : α < min (swapMix F).comp1.varSq (swapMix F).comp2.varSq)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    TVDistance G (deconvMixture2 (swapMix F) α h_sw)
    = TVDistance G (deconvMixture2 F α h) := by
  rw [TVDistance_symm, TVDistance_deconv_swapMix_left F α h_sw h G, TVDistance_symm]

/-- The min of variances after deconv is invariant under swapMix. -/
private lemma deconv_swapMix_var_min
    (F : GaussianMixture2) (α : ℝ)
    (h_sw : α < min (swapMix F).comp1.varSq (swapMix F).comp2.varSq)
    (h : α < min F.comp1.varSq F.comp2.varSq) :
    min (deconvMixture2 (swapMix F) α h_sw).comp1.varSq
        (deconvMixture2 (swapMix F) α h_sw).comp2.varSq
    = min (deconvMixture2 F α h).comp1.varSq
          (deconvMixture2 F α h).comp2.varSq := by
  simp only [deconvMixture2_comp1_varSq, deconvMixture2_comp2_varSq,
             swapMix_comp1, swapMix_comp2]
  exact min_comm _ _

private lemma min_swapMix
    (F : GaussianMixture2) :
    min (swapMix F).comp1.varSq (swapMix F).comp2.varSq
      = min F.comp1.varSq F.comp2.varSq := by
  simp only [swapMix_comp1, swapMix_comp2]
  exact min_comm _ _

/-- Lemma 5 of Moitra--Valiant: existence of a deconvolution parameter `α`
that simultaneously gives an `Ω(ε^4)` TV gap (conditional on the three
measure-theoretic prior-work hypotheses), keeps every constituent variance
`≥ ε^{12}`, and satisfies `α ≥ -1`. The theorem now exposes a smallness
witness `ε_max > 0` (from the ε-absorption in the variance Taylor step). -/
theorem Lemma5DeconvolutionTVGap :
    ∃ K₅ ε_max : ℝ, 0 < K₅ ∧ 0 < ε_max ∧
      ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (ε : ℝ),
        0 < ε → ε ≤ ε_max →
        Workspace.Types.EpsilonStandardPair.EpsilonStandardPair F F' ε →
        ∃ α : ℝ,
          ∃ h₁ : α < min F.comp1.varSq F.comp2.varSq,
            ∃ h₂ : α < min F'.comp1.varSq F'.comp2.varSq,
              (-1 : ℝ) ≤ α
              ∧ ε ^ 12 ≤
                  min
                    (min
                      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp1.varSq
                      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁).comp2.varSq)
                    (min
                      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp1.varSq
                      (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂).comp2.varSq)
              ∧ K₅ * ε ^ 4 ≤
                  Workspace.Types.L1AndTVDistance.TVDistance
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h₁)
                    (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h₂) := by
  -- Extract constants from the 3 Case lemmas
  obtain ⟨K1, hK1_pos, hCase1⟩ := Lemma5Case1Assembly
  obtain ⟨K2a, ε_max_a, hK2a_pos, hε_max_a_pos, hCase2a⟩ := Lemma5Case2aAssembly
  obtain ⟨K2b, ε_max_b, hK2b_pos, hε_max_b_pos, hCase2b⟩ := Lemma5Case2bAssembly
  refine ⟨min (min K1 K2a) K2b, min 1 (min ε_max_a ε_max_b), ?_, ?_, ?_⟩
  · exact lt_min (lt_min hK1_pos hK2a_pos) hK2b_pos
  · exact lt_min one_pos (lt_min hε_max_a_pos hε_max_b_pos)
  intro F F' ε hε_pos hε_le_max h_std
  set K₅ := min (min K1 K2a) K2b with hK₅_def
  have hε_le_one : ε ≤ 1 := le_trans hε_le_max (min_le_left _ _)
  have hε_le_a : ε ≤ ε_max_a :=
    le_trans hε_le_max (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε_le_b : ε ≤ ε_max_b :=
    le_trans hε_le_max (le_trans (min_le_right _ _) (min_le_right _ _))
  have hK5_le_K1 : K₅ ≤ K1 := (min_le_left _ _).trans (min_le_left _ _)
  have hK5_le_K2a : K₅ ≤ K2a := (min_le_left _ _).trans (min_le_right _ _)
  have hK5_le_K2b : K₅ ≤ K2b := min_le_right _ _
  have hε4_nn : 0 ≤ ε ^ 4 := by positivity
  -- Build the "core" claim: when G.comp1 is the min of all four variances,
  -- we get the bound via Cases 1/2a/2b dispatch.
  have core : ∀ (G G' : GaussianMixture2),
      EpsilonStandardPair G G' ε →
      G.comp1.varSq ≤ G.comp2.varSq →
      G.comp1.varSq ≤ G'.comp1.varSq →
      G.comp1.varSq ≤ G'.comp2.varSq →
      ∃ α : ℝ,
        ∃ h₁ : α < min G.comp1.varSq G.comp2.varSq,
          ∃ h₂ : α < min G'.comp1.varSq G'.comp2.varSq,
            (-1 : ℝ) ≤ α
            ∧ ε ^ 12 ≤
                min
                  (min (deconvMixture2 G α h₁).comp1.varSq
                       (deconvMixture2 G α h₁).comp2.varSq)
                  (min (deconvMixture2 G' α h₂).comp1.varSq
                       (deconvMixture2 G' α h₂).comp2.varSq)
            ∧ K₅ * ε ^ 4 ≤
                TVDistance (deconvMixture2 G α h₁) (deconvMixture2 G' α h₂) := by
    intro G G' hstd h12 h1'1 h1'2
    -- Dispatch on whether P(1) holds (Case 1 condition for index 1 of G')
    by_cases hP1 : 16 * ε ^ 10 ≤ G'.comp1.varSq - G.comp1.varSq ∨
                   6 * ε ^ 5 ≤ |G'.comp1.mean - G.comp1.mean|
    · -- P(1) holds. Now dispatch on whether P(2) holds.
      by_cases hP2 : 16 * ε ^ 10 ≤ G'.comp2.varSq - G.comp1.varSq ∨
                     6 * ε ^ 5 ≤ |G'.comp2.mean - G.comp1.mean|
      · -- Both P(1) and P(2) hold: Case 1.
        obtain ⟨α, h₁, h₂, hα_ge, hvar, htv⟩ :=
          hCase1 G G' ε hε_pos hε_le_one hstd h12 h1'1 h1'2 hP1 hP2
        refine ⟨α, h₁, h₂, hα_ge, hvar, ?_⟩
        calc K₅ * ε ^ 4
            ≤ K1 * ε ^ 4 := mul_le_mul_of_nonneg_right hK5_le_K1 hε4_nn
          _ ≤ _ := htv
      · -- P(1) holds but P(2) fails: "bad" index is 2 in G'. Use swapMix G'.
        push_neg at hP2
        obtain ⟨hVarP2, hMuP2⟩ := hP2
        have hstd_sw : EpsilonStandardPair G (swapMix G') ε := by
          have h1 : EpsilonStandardPair G' G ε := epsStd_FF'_swap hstd
          have h2 : EpsilonStandardPair (swapMix G') G ε := epsStd_swap_left h1
          exact epsStd_FF'_swap h2
        have h1'1_sw : G.comp1.varSq ≤ (swapMix G').comp1.varSq := by
          show G.comp1.varSq ≤ G'.comp2.varSq; exact h1'2
        have h1'2_sw : G.comp1.varSq ≤ (swapMix G').comp2.varSq := by
          show G.comp1.varSq ≤ G'.comp1.varSq; exact h1'1
        have hVar_sw : (swapMix G').comp1.varSq - G.comp1.varSq < 16 * ε ^ 10 := by
          show G'.comp2.varSq - G.comp1.varSq < 16 * ε ^ 10; exact hVarP2
        have hMu_sw : |(swapMix G').comp1.mean - G.comp1.mean| < 6 * ε ^ 5 := by
          show |G'.comp2.mean - G.comp1.mean| < 6 * ε ^ 5; exact hMuP2
        -- Dispatch Case 2a vs Case 2b on |G.weight1 - (swapMix G').weight1|
        by_cases hW : ε ^ 2 ≤ |G.weight1 - (swapMix G').weight1|
        · -- Case 2a (using swap of G')
          obtain ⟨α, h₁, h₂_sw, hα_ge, hvar_sw, htv_sw⟩ :=
            hCase2a G (swapMix G') ε hε_pos hε_le_one hε_le_a hstd_sw h12 h1'1_sw h1'2_sw
              hVar_sw hMu_sw hW
          have h₂ : α < min G'.comp1.varSq G'.comp2.varSq := by
            have heq : min (swapMix G').comp1.varSq (swapMix G').comp2.varSq
                       = min G'.comp1.varSq G'.comp2.varSq := min_swapMix G'
            rw [← heq]; exact h₂_sw
          refine ⟨α, h₁, h₂, hα_ge, ?_, ?_⟩
          · -- Variance lower bound
            rw [deconv_swapMix_var_min G' α h₂_sw h₂] at hvar_sw
            exact hvar_sw
          · -- TV bound
            calc K₅ * ε ^ 4
                ≤ K2a * ε ^ 4 := mul_le_mul_of_nonneg_right hK5_le_K2a hε4_nn
              _ ≤ TVDistance (deconvMixture2 G α h₁) (deconvMixture2 (swapMix G') α h₂_sw) := htv_sw
              _ = TVDistance (deconvMixture2 G α h₁) (deconvMixture2 G' α h₂) :=
                  TVDistance_deconv_swapMix_right (deconvMixture2 G α h₁) G' α h₂_sw h₂
        · -- Case 2b (using swap of G')
          push_neg at hW
          obtain ⟨α, h₁, h₂_sw, hα_ge, hvar_sw, htv_sw⟩ :=
            hCase2b G (swapMix G') ε hε_pos hε_le_one hε_le_b hstd_sw h12 h1'1_sw h1'2_sw
              hVar_sw hMu_sw hW
          have h₂ : α < min G'.comp1.varSq G'.comp2.varSq := by
            have heq : min (swapMix G').comp1.varSq (swapMix G').comp2.varSq
                       = min G'.comp1.varSq G'.comp2.varSq := min_swapMix G'
            rw [← heq]; exact h₂_sw
          refine ⟨α, h₁, h₂, hα_ge, ?_, ?_⟩
          · rw [deconv_swapMix_var_min G' α h₂_sw h₂] at hvar_sw
            exact hvar_sw
          · calc K₅ * ε ^ 4
                ≤ K2b * ε ^ 4 := mul_le_mul_of_nonneg_right hK5_le_K2b hε4_nn
              _ ≤ TVDistance (deconvMixture2 G α h₁) (deconvMixture2 (swapMix G') α h₂_sw) := htv_sw
              _ = TVDistance (deconvMixture2 G α h₁) (deconvMixture2 G' α h₂) :=
                  TVDistance_deconv_swapMix_right (deconvMixture2 G α h₁) G' α h₂_sw h₂
    · -- P(1) fails: "bad" index is 1 in G'. No swap needed.
      push_neg at hP1
      obtain ⟨hVarP1, hMuP1⟩ := hP1
      by_cases hW : ε ^ 2 ≤ |G.weight1 - G'.weight1|
      · -- Case 2a
        obtain ⟨α, h₁, h₂, hα_ge, hvar, htv⟩ :=
          hCase2a G G' ε hε_pos hε_le_one hε_le_a hstd h12 h1'1 h1'2 hVarP1 hMuP1 hW
        refine ⟨α, h₁, h₂, hα_ge, hvar, ?_⟩
        calc K₅ * ε ^ 4
            ≤ K2a * ε ^ 4 := mul_le_mul_of_nonneg_right hK5_le_K2a hε4_nn
          _ ≤ _ := htv
      · -- Case 2b
        push_neg at hW
        obtain ⟨α, h₁, h₂, hα_ge, hvar, htv⟩ :=
          hCase2b G G' ε hε_pos hε_le_one hε_le_b hstd h12 h1'1 h1'2 hVarP1 hMuP1 hW
        refine ⟨α, h₁, h₂, hα_ge, hvar, ?_⟩
        calc K₅ * ε ^ 4
            ≤ K2b * ε ^ 4 := mul_le_mul_of_nonneg_right hK5_le_K2b hε4_nn
          _ ≤ _ := htv
  -- Now case-split on which of the 4 variances is the smallest.
  -- Case A: F.comp1 is the min (direct)
  by_cases hCaseA : F.comp1.varSq ≤ min F.comp2.varSq (min F'.comp1.varSq F'.comp2.varSq)
  · have h12 : F.comp1.varSq ≤ F.comp2.varSq := le_trans hCaseA (min_le_left _ _)
    have h1'1 : F.comp1.varSq ≤ F'.comp1.varSq :=
      le_trans (le_trans hCaseA (min_le_right _ _)) (min_le_left _ _)
    have h1'2 : F.comp1.varSq ≤ F'.comp2.varSq :=
      le_trans (le_trans hCaseA (min_le_right _ _)) (min_le_right _ _)
    exact core F F' h_std h12 h1'1 h1'2
  · push_neg at hCaseA
    -- Case B: F.comp2 is the min — swap components of F
    by_cases hCaseB : F.comp2.varSq ≤ min F.comp1.varSq (min F'.comp1.varSq F'.comp2.varSq)
    · -- Apply core to (swapMix F, F')
      have hstd_swF : EpsilonStandardPair (swapMix F) F' ε := epsStd_swap_left h_std
      have h12_sw : (swapMix F).comp1.varSq ≤ (swapMix F).comp2.varSq := by
        show F.comp2.varSq ≤ F.comp1.varSq
        exact le_trans hCaseB (min_le_left _ _)
      have h1'1_sw : (swapMix F).comp1.varSq ≤ F'.comp1.varSq := by
        show F.comp2.varSq ≤ F'.comp1.varSq
        exact le_trans (le_trans hCaseB (min_le_right _ _)) (min_le_left _ _)
      have h1'2_sw : (swapMix F).comp1.varSq ≤ F'.comp2.varSq := by
        show F.comp2.varSq ≤ F'.comp2.varSq
        exact le_trans (le_trans hCaseB (min_le_right _ _)) (min_le_right _ _)
      obtain ⟨α, h₁_sw, h₂, hα_ge, hvar_sw, htv_sw⟩ :=
        core (swapMix F) F' hstd_swF h12_sw h1'1_sw h1'2_sw
      have h₁ : α < min F.comp1.varSq F.comp2.varSq := by
        have heq : min (swapMix F).comp1.varSq (swapMix F).comp2.varSq
                   = min F.comp1.varSq F.comp2.varSq := min_swapMix F
        rw [← heq]; exact h₁_sw
      refine ⟨α, h₁, h₂, hα_ge, ?_, ?_⟩
      · -- Variance lower bound: deconv (swapMix F) has same min variance as deconv F
        rw [deconv_swapMix_var_min F α h₁_sw h₁] at hvar_sw
        exact hvar_sw
      · -- TV bound: transfer via TVDistance_deconv_swapMix_left
        calc K₅ * ε ^ 4
            ≤ TVDistance (deconvMixture2 (swapMix F) α h₁_sw) (deconvMixture2 F' α h₂) := htv_sw
          _ = TVDistance (deconvMixture2 F α h₁) (deconvMixture2 F' α h₂) :=
              TVDistance_deconv_swapMix_left F α h₁_sw h₁ (deconvMixture2 F' α h₂)
    · push_neg at hCaseB
      -- Cases C & D: F'.comp1 or F'.comp2 is the min. Swap F ↔ F'.
      by_cases hCaseC : F'.comp1.varSq ≤ min F'.comp2.varSq (min F.comp1.varSq F.comp2.varSq)
      · -- Apply core to (F', F) — then we need to symmetrize
        have hstd_FF' : EpsilonStandardPair F' F ε := epsStd_FF'_swap h_std
        have h12_FF' : F'.comp1.varSq ≤ F'.comp2.varSq := le_trans hCaseC (min_le_left _ _)
        have h1'1_FF' : F'.comp1.varSq ≤ F.comp1.varSq :=
          le_trans (le_trans hCaseC (min_le_right _ _)) (min_le_left _ _)
        have h1'2_FF' : F'.comp1.varSq ≤ F.comp2.varSq :=
          le_trans (le_trans hCaseC (min_le_right _ _)) (min_le_right _ _)
        obtain ⟨α, h₂', h₁', hα_ge, hvar', htv'⟩ :=
          core F' F hstd_FF' h12_FF' h1'1_FF' h1'2_FF'
        refine ⟨α, h₁', h₂', hα_ge, ?_, ?_⟩
        · -- hvar' uses (deconvMixture2 F' α h₂', deconvMixture2 F α h₁'),
          -- we need (deconvMixture2 F α h₁', deconvMixture2 F' α h₂'). Min is commutative.
          rw [min_comm]; exact hvar'
        · -- TV bound: TVDistance is symmetric
          rw [TVDistance_symm]; exact htv'
      · push_neg at hCaseC
        -- Case D: F'.comp2 is the min. Swap both F ↔ F' AND swap components of F'.
        -- After F↔F' swap, we get (F', F). F'.comp2 is min, so we need to swap-comp of F'.
        -- That is, apply core to (swapMix F', F).
        have hstd_FF' : EpsilonStandardPair F' F ε := epsStd_FF'_swap h_std
        have hstd_swF'_F : EpsilonStandardPair (swapMix F') F ε := epsStd_swap_left hstd_FF'
        -- We need: F'.comp2 is the min of all four variances.
        -- (swapMix F').comp1 = F'.comp2 is the min.
        -- From hCaseA, hCaseB, hCaseC fails, F'.comp2 must be the min.
        have h_min_F'2 : F'.comp2.varSq ≤ min F'.comp1.varSq (min F.comp1.varSq F.comp2.varSq) := by
          -- We have:
          -- hCaseA: min F.comp2.varSq (min F'.comp1.varSq F'.comp2.varSq) < F.comp1.varSq
          -- hCaseB: min F.comp1.varSq (min F'.comp1.varSq F'.comp2.varSq) < F.comp2.varSq
          -- hCaseC: min F'.comp2.varSq (min F.comp1.varSq F.comp2.varSq) < F'.comp1.varSq
          -- Need: F'.comp2.varSq ≤ F'.comp1, F.comp1, F.comp2.
          rcases le_or_gt F'.comp2.varSq F'.comp1.varSq with hA | hA
          · rcases le_or_gt F'.comp2.varSq F.comp1.varSq with hB | hB
            · rcases le_or_gt F'.comp2.varSq F.comp2.varSq with hC | hC
              · exact le_min hA (le_min hB hC)
              · -- F'.comp2 > F.comp2. Use hCaseB:
                -- min F.comp1 (min F'.comp1 F'.comp2) < F.comp2
                -- F.comp1 > F.comp2 (from hCaseA via min_le_left of inner contradicts...
                -- Actually let's just be careful.
                exfalso
                have hmin1 : min F'.comp1.varSq F'.comp2.varSq = F'.comp2.varSq :=
                  min_eq_right hA
                rw [hmin1] at hCaseA hCaseB
                -- hCaseA : min F.comp2 F'.comp2 < F.comp1
                -- hCaseB : min F.comp1 F'.comp2 < F.comp2
                -- hC : F.comp2 < F'.comp2 so min F.comp2 F'.comp2 = F.comp2
                rw [min_eq_left (le_of_lt hC)] at hCaseA
                -- hCaseA : F.comp2 < F.comp1
                -- Now hCaseB : min F.comp1 F'.comp2 < F.comp2
                -- F'.comp2 > F.comp2 (hC), F.comp1 > F.comp2 (hCaseA)
                -- so min F.comp1 F'.comp2 > F.comp2, contradiction with hCaseB.
                have : F.comp2.varSq < min F.comp1.varSq F'.comp2.varSq := lt_min hCaseA hC
                linarith
            · -- F'.comp2 > F.comp1. Use hCaseA:
              -- min F.comp2 (min F'.comp1 F'.comp2) < F.comp1
              -- min F'.comp1 F'.comp2 = F'.comp2 (since hA), > F.comp1 (hB).
              -- So min F.comp2 F'.comp2 < F.comp1, but F'.comp2 > F.comp1.
              -- Hence min F.comp2 F'.comp2 = F.comp2 (and F.comp2 < F.comp1).
              -- Now hCaseB : min F.comp1 (min F'.comp1 F'.comp2) < F.comp2
              -- min F'.comp1 F'.comp2 = F'.comp2 > F.comp1 (hB),
              -- so min F.comp1 F'.comp2 = F.comp1.
              -- hCaseB : F.comp1 < F.comp2, contradicting F.comp2 < F.comp1.
              exfalso
              have hmin1 : min F'.comp1.varSq F'.comp2.varSq = F'.comp2.varSq :=
                min_eq_right hA
              rw [hmin1] at hCaseA hCaseB
              rw [min_eq_left (le_of_lt hB)] at hCaseB
              -- hCaseB : F.comp1 < F.comp2
              -- hCaseA : min F.comp2 F'.comp2 < F.comp1
              -- F'.comp2 > F.comp1, F.comp2 > F.comp1, so min > F.comp1
              have hL : F.comp1.varSq < min F.comp2.varSq F'.comp2.varSq := lt_min hCaseB hB
              linarith
          · -- F'.comp1 < F'.comp2. Use hCaseC:
            -- min F'.comp2 (min F.comp1 F.comp2) < F'.comp1
            -- F'.comp2 > F'.comp1, so min F'.comp2 X < F'.comp1 < F'.comp2 needs X part:
            -- min F'.comp2 (min F.comp1 F.comp2) = min F.comp1 F.comp2 (if < F'.comp2)
            -- or = F'.comp2 (otherwise). Since result < F'.comp1 < F'.comp2, must be first case.
            -- So min F.comp1 F.comp2 < F'.comp1.
            -- Use hCaseA, hCaseB:
            -- hCaseA : min F.comp2 (min F'.comp1 F'.comp2) < F.comp1
            --   min F'.comp1 F'.comp2 = F'.comp1 (since hA), so min F.comp2 F'.comp1 < F.comp1
            -- hCaseB : min F.comp1 (min F'.comp1 F'.comp2) < F.comp2
            --   = min F.comp1 F'.comp1 < F.comp2
            -- Combine: min F.comp1 F.comp2 < F'.comp1 means F.comp1 < F'.comp1 or F.comp2 < F'.comp1.
            -- Sub-case (i): F.comp1 < F'.comp1.
            --   hCaseB : min F.comp1 F'.comp1 < F.comp2 → F.comp1 < F.comp2.
            --   hCaseA : min F.comp2 F'.comp1 < F.comp1. F.comp2 > F.comp1, F'.comp1 > F.comp1,
            --     so min > F.comp1, contradiction.
            -- Sub-case (ii): F.comp2 < F'.comp1.
            --   hCaseA : min F.comp2 F'.comp1 < F.comp1 → F.comp2 < F.comp1.
            --   hCaseB : min F.comp1 F'.comp1 < F.comp2. F.comp1 > F.comp2, F'.comp1 > F.comp2,
            --     so min > F.comp2, contradiction.
            exfalso
            have hmin1 : min F'.comp1.varSq F'.comp2.varSq = F'.comp1.varSq :=
              min_eq_left (le_of_lt hA)
            rw [hmin1] at hCaseA hCaseB
            rcases le_or_gt F'.comp2.varSq (min F.comp1.varSq F.comp2.varSq) with hM | hM
            · rw [min_eq_left hM] at hCaseC
              -- hCaseC : F'.comp2 < F'.comp1, contradicting hA
              linarith
            · rw [min_eq_right (le_of_lt hM)] at hCaseC
              -- hCaseC : min F.comp1 F.comp2 < F'.comp1
              rcases le_or_gt F.comp1.varSq F.comp2.varSq with hN | hN
              · rw [min_eq_left hN] at hCaseC
                -- hCaseC : F.comp1 < F'.comp1
                rw [min_eq_left (le_of_lt hCaseC)] at hCaseB
                -- hCaseB : F.comp1 < F.comp2
                have : F.comp1.varSq < min F.comp2.varSq F'.comp1.varSq := lt_min hCaseB hCaseC
                linarith
              · rw [min_eq_right (le_of_lt hN)] at hCaseC
                -- hCaseC : F.comp2 < F'.comp1
                rw [min_eq_left (le_of_lt hCaseC)] at hCaseA
                -- hCaseA : F.comp2 < F.comp1
                have : F.comp2.varSq < min F.comp1.varSq F'.comp1.varSq := lt_min hCaseA hCaseC
                linarith
        have h12_swF' : (swapMix F').comp1.varSq ≤ (swapMix F').comp2.varSq := by
          show F'.comp2.varSq ≤ F'.comp1.varSq
          exact le_trans h_min_F'2 (min_le_left _ _)
        have h1'1_swF' : (swapMix F').comp1.varSq ≤ F.comp1.varSq := by
          show F'.comp2.varSq ≤ F.comp1.varSq
          exact le_trans (le_trans h_min_F'2 (min_le_right _ _)) (min_le_left _ _)
        have h1'2_swF' : (swapMix F').comp1.varSq ≤ F.comp2.varSq := by
          show F'.comp2.varSq ≤ F.comp2.varSq
          exact le_trans (le_trans h_min_F'2 (min_le_right _ _)) (min_le_right _ _)
        obtain ⟨α, h₂_sw, h₁, hα_ge, hvar_sw, htv_sw⟩ :=
          core (swapMix F') F hstd_swF'_F h12_swF' h1'1_swF' h1'2_swF'
        have h₂ : α < min F'.comp1.varSq F'.comp2.varSq := by
          have heq : min (swapMix F').comp1.varSq (swapMix F').comp2.varSq
                     = min F'.comp1.varSq F'.comp2.varSq := min_swapMix F'
          rw [← heq]; exact h₂_sw
        refine ⟨α, h₁, h₂, hα_ge, ?_, ?_⟩
        · -- hvar_sw : ε^12 ≤ min (min (deconv (swap F'))) (min (deconv F))
          -- We want   : ε^12 ≤ min (min (deconv F)) (min (deconv F'))
          rw [deconv_swapMix_var_min F' α h₂_sw h₂] at hvar_sw
          rw [min_comm]; exact hvar_sw
        · -- htv_sw : K₅ ε^4 ≤ TVDistance (deconv (swapMix F')) (deconv F)
          -- We want : K₅ ε^4 ≤ TVDistance (deconv F) (deconv F')
          calc K₅ * ε ^ 4
              ≤ TVDistance (deconvMixture2 (swapMix F') α h₂_sw) (deconvMixture2 F α h₁) := htv_sw
            _ = TVDistance (deconvMixture2 F' α h₂) (deconvMixture2 F α h₁) :=
                TVDistance_deconv_swapMix_left F' α h₂_sw h₂ (deconvMixture2 F α h₁)
            _ = TVDistance (deconvMixture2 F α h₁) (deconvMixture2 F' α h₂) := TVDistance_symm _ _

end Workspace.ProofLemmas.Lemma5DeconvolutionTVGap
