import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianConvolution
import Workspace.Types.MixtureDeconvolution
import Workspace.ProofLemmas.Prop7AnalyticityOfMixture
import Workspace.ProofLemmas.Prop7AddGaussianAddsAtMostTwoZeros
import Workspace.ProofLemmas.Prop7ConvolutionRecoversOriginalDensity
import Workspace.ProofLemmas.SublemmaFormalGaussianIHExtension
import Workspace.PriorWork.HummelGidasZeroCount

namespace Workspace.ProofLemmas

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination
open Workspace.Types.ZeroCount

/-! ## Prop7Induction as a corollary of `SublemmaFormalGaussianIHExtension`.

The strengthened IH (`SublemmaFormalGaussianIHExtension`) bounds the zero
count of `Σ_i a_i · exp(-(x-μ_i)²/(2 τ_i²))` for ANY nonzero distinct
real `τ_i²`. The user-facing `Prop7Induction` is the specialization to
all `τ_i² > 0`, with `a_i := S.components[i].fst · (1/√(2π·varSq_i))`
absorbing the Gaussian normalization. -/

theorem Prop7Induction :
    ∀ (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination),
      let k := S.components.length
      1 ≤ k →
      (S.components.map (fun p => p.snd.varSq)).Nodup →
      (∃ p ∈ S.components, p.fst ≠ 0) →
      Workspace.Types.ZeroCount.hasAtMostNZeros S.density (2 * (k - 1)) := by
  intro S
  simp only
  intro hk_le hnodup hnonzero
  set k := S.components.length with hk_def
  -- Define the abstract-Gaussian data from S.
  let comp : Fin k → ℝ × GaussianPDF := fun i => S.components[i.val]'i.isLt
  let τ_sq : Fin k → ℝ := fun i => (comp i).2.varSq
  let μ : Fin k → ℝ := fun i => (comp i).2.mean
  let a : Fin k → ℝ := fun i =>
    (comp i).1 * (1 / Real.sqrt (2 * Real.pi * (comp i).2.varSq))
  have h_varSq_pos : ∀ i : Fin k, 0 < τ_sq i := fun i => (comp i).2.varSq_pos
  have h_τ_nonzero : ∀ i : Fin k, τ_sq i ≠ 0 :=
    fun i => ne_of_gt (h_varSq_pos i)
  -- Distinctness of τ_sq from Nodup.
  have h_τ_distinct : ∀ i j : Fin k, i ≠ j → τ_sq i ≠ τ_sq j := by
    intro i j hij habs
    apply hij
    have hi_lt : i.val < (S.components.map (fun p => p.snd.varSq)).length := by
      simp [hk_def]; exact i.isLt
    have hj_lt : j.val < (S.components.map (fun p => p.snd.varSq)).length := by
      simp [hk_def]; exact j.isLt
    have h_idx_i :
        (S.components.map (fun p => p.snd.varSq))[i.val]'hi_lt = τ_sq i := by
      simp [comp, τ_sq, List.getElem_map]
    have h_idx_j :
        (S.components.map (fun p => p.snd.varSq))[j.val]'hj_lt = τ_sq j := by
      simp [comp, τ_sq, List.getElem_map]
    have heq : (S.components.map (fun p => p.snd.varSq))[i.val]'hi_lt =
               (S.components.map (fun p => p.snd.varSq))[j.val]'hj_lt := by
      rw [h_idx_i, h_idx_j, habs]
    have hval_eq : i.val = j.val :=
      (List.Nodup.getElem_inj_iff hnodup).mp heq
    exact Fin.ext hval_eq
  -- Nonzero coefficient: ∃ i, a i ≠ 0 from ∃ p ∈ components, p.fst ≠ 0.
  have h_a_nonzero : ∃ i : Fin k, a i ≠ 0 := by
    obtain ⟨p, hp_mem, hp_ne⟩ := hnonzero
    obtain ⟨n, hn_lt, hn_eq⟩ := List.getElem_of_mem hp_mem
    refine ⟨⟨n, hn_lt⟩, ?_⟩
    have hcomp : comp ⟨n, hn_lt⟩ = p := hn_eq
    show (comp ⟨n, hn_lt⟩).1 *
        (1 / Real.sqrt (2 * Real.pi * (comp ⟨n, hn_lt⟩).2.varSq)) ≠ 0
    rw [hcomp]
    refine mul_ne_zero hp_ne ?_
    apply div_ne_zero one_ne_zero
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
    exact mul_pos h2pi p.2.varSq_pos
  -- Apply SublemmaFormalGaussianIHExtension.
  have h_extension :=
    SublemmaFormalGaussianIHExtension k hk_le a μ τ_sq
      h_varSq_pos h_τ_distinct h_a_nonzero
  -- Show S.density equals the abstract sum pointwise, hence as a function.
  have h_density_eq : S.density =
      fun x => (Finset.univ : Finset (Fin k)).sum
        (fun i => a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))) := by
    funext x
    rw [SignedGaussianCombination.density_eq]
    -- LHS: (S.components.map fun p => p.1 * p.2.density x).sum.
    -- Use Fin.sum_univ_fun_getElem with l = S.components and f = (fun p => p.1 * p.2.density x).
    rw [← Fin.sum_univ_fun_getElem S.components (fun p => p.1 * p.2.density x)]
    -- Goal: ∑ i : Fin S.components.length, (S.components[i].1 * S.components[i].2.density x)
    --     = ∑ i : Fin k, a i * Real.exp (-(x - μ i)^2 / (2 * τ_sq i))
    -- Since k := S.components.length, both sums have the same index type. Use sum_congr.
    apply Finset.sum_congr rfl
    intro i _
    -- For each i, show S.components[i].1 * S.components[i].2.density x = a i * exp(...).
    have hci : S.components[i.val]'i.isLt = comp i := rfl
    rw [show S.components[i.val] = comp i from hci]
    rw [GaussianPDF.density_eq]
    simp only [a, μ, τ_sq]
    ring
  rw [h_density_eq]
  exact h_extension

end Workspace.ProofLemmas
