import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.GaussianMixture2
import Workspace.Types.MixtureDeconvolution
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.DerivativeBoundOfSignedCombination
import Workspace.ProofLemmas.MixtureDifferenceAsSignedCombination

set_option maxHeartbeats 800000

namespace Workspace.ProofLemmas

theorem Lemma5Case1DerivBoundOnDiff :
    ∀ (F F' : Workspace.Types.GaussianMixture2.GaussianMixture2) (α ε : ℝ),
      0 < ε → ε ≤ 1 →
      ∀ (h_F : α < min F.comp1.varSq F.comp2.varSq)
        (h_F' : α < min F'.comp1.varSq F'.comp2.varSq),
      ε ^ 12 ≤
        min
          (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp1.varSq
               (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).comp2.varSq)
          (min (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp1.varSq
               (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').comp2.varSq) →
      Differentiable ℝ (fun x =>
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).density x
        - (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').density x)
      ∧ ∀ x : ℝ, |deriv (fun y =>
        (Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F).density y
        - (Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F').density y) x| ≤ 4 / ε ^ 12
    := by
  intro F F' α ε hε_pos hε_le1 h_F h_F' h_var_min
  -- Names for the deconvolved mixtures.
  set G := Workspace.Types.MixtureDeconvolution.deconvMixture2 F α h_F with hG_def
  set G' := Workspace.Types.MixtureDeconvolution.deconvMixture2 F' α h_F' with hG'_def
  -- Step 1: Get S from MixtureDifferenceAsSignedCombination.
  obtain ⟨S, hS_len, hS_dens, hS_comp⟩ := MixtureDifferenceAsSignedCombination G G'
  -- Step 2: Show ε ≤ 2^(1/12). Use ε ≤ 1 ≤ 2^(1/12).
  have hε_pow : ε ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) := by
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((1 : ℝ) / 12) := by
      have h2pos : (0 : ℝ) < 2 := by norm_num
      have h12_le : (1 : ℝ) ≤ 2 := by norm_num
      have hexp_nn : (0 : ℝ) ≤ 1 / 12 := by norm_num
      exact Real.one_le_rpow h12_le hexp_nn
    linarith
  -- Step 3: components length ≤ 4
  have h_len_le : S.components.length ≤ 4 := by rw [hS_len]
  -- Step 4: weight bounds via weights_sum_one and nonneg
  have hG_w1_le : G.weight1 ≤ 1 := by
    have h1 := G.weight1_nonneg
    have h2 := G.weight2_nonneg
    have hs := G.weights_sum_one
    linarith
  have hG_w2_le : G.weight2 ≤ 1 := by
    have h1 := G.weight1_nonneg
    have h2 := G.weight2_nonneg
    have hs := G.weights_sum_one
    linarith
  have hG'_w1_le : G'.weight1 ≤ 1 := by
    have h1 := G'.weight1_nonneg
    have h2 := G'.weight2_nonneg
    have hs := G'.weights_sum_one
    linarith
  have hG'_w2_le : G'.weight2 ≤ 1 := by
    have h1 := G'.weight1_nonneg
    have h2 := G'.weight2_nonneg
    have hs := G'.weights_sum_one
    linarith
  -- Variance bounds from h_var_min.
  have hG_v1 : ε ^ 12 ≤ G.comp1.varSq := by
    have := h_var_min
    have h_left : ε ^ 12 ≤ min G.comp1.varSq G.comp2.varSq :=
      le_trans this (min_le_left _ _)
    exact le_trans h_left (min_le_left _ _)
  have hG_v2 : ε ^ 12 ≤ G.comp2.varSq := by
    have h_left : ε ^ 12 ≤ min G.comp1.varSq G.comp2.varSq :=
      le_trans h_var_min (min_le_left _ _)
    exact le_trans h_left (min_le_right _ _)
  have hG'_v1 : ε ^ 12 ≤ G'.comp1.varSq := by
    have h_right : ε ^ 12 ≤ min G'.comp1.varSq G'.comp2.varSq :=
      le_trans h_var_min (min_le_right _ _)
    exact le_trans h_right (min_le_left _ _)
  have hG'_v2 : ε ^ 12 ≤ G'.comp2.varSq := by
    have h_right : ε ^ 12 ≤ min G'.comp1.varSq G'.comp2.varSq :=
      le_trans h_var_min (min_le_right _ _)
    exact le_trans h_right (min_le_right _ _)
  -- Component bounds
  have h_comp_bound : ∀ p ∈ S.components, |p.fst| ≤ 1 ∧ ε^12 ≤ p.snd.varSq := by
    intro p hp
    rw [hS_comp] at hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨?_, hG_v1⟩
      exact abs_le.mpr ⟨by linarith [G.weight1_nonneg], hG_w1_le⟩
    · refine ⟨?_, hG_v2⟩
      exact abs_le.mpr ⟨by linarith [G.weight2_nonneg], hG_w2_le⟩
    · refine ⟨?_, hG'_v1⟩
      rw [abs_neg]
      exact abs_le.mpr ⟨by linarith [G'.weight1_nonneg], hG'_w1_le⟩
    · refine ⟨?_, hG'_v2⟩
      rw [abs_neg]
      exact abs_le.mpr ⟨by linarith [G'.weight2_nonneg], hG'_w2_le⟩
  -- Apply DerivativeBoundOfSignedCombination
  obtain ⟨hS_diff, hS_deriv⟩ :=
    DerivativeBoundOfSignedCombination S ε hε_pos hε_pow h_len_le h_comp_bound
  -- The function in the goal equals S.density pointwise.
  have h_eq : (fun x => G.density x - G'.density x) = S.density := by
    funext x; exact (hS_dens x).symm
  refine ⟨?_, ?_⟩
  · rw [h_eq]; exact hS_diff
  · intro x
    rw [h_eq]
    exact hS_deriv x

end Workspace.ProofLemmas
