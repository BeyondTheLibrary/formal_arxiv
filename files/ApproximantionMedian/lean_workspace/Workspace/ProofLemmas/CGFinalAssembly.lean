import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGEvenAugmentReduction
import Workspace.ProofLemmas.CGTranslationScaleNormalize
import Workspace.ProofLemmas.CGNormalizedCoreInequality
import Workspace.ProofLemmas.MedianOfConstant
import Workspace.ProofLemmas.LqNormZeroIffEqZero

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ConsistencyTheorem

namespace Workspace.ProofLemmas.CGFinalAssembly

/-- **CGFinalAssembly** — the proof of Theorem 3 (consistency guarantee of
`CMP(c)`), assembled from the consistency sub-lemmas.

This is the body of `Workspace.ConsistencyTheorem.consistency_guarantee`; the
root statement file sets `consistency_guarantee := CGFinalAssembly`.

Pipeline (proof_nlp.md §1.2, §7):
* `CGEvenAugmentReduction` reduces to the case `n + ⌊cn⌋` even (and discharges
  `n = 0`) by duplicating the augmented instance.
* In the even case we split on `optSocialCost 2 P = 0`:
  - `OPT = 0`: every report equals the optimal facility, the augmented instance
    is the constant `fstar`, its median is `fstar`, so `SC(P,m) = 0 ≤ CG c · 0`.
  - `OPT > 0`: `CGTranslationScaleNormalize` (its `h_norm` premise instantiated
    with the strict-`f>0` core `CGNormalizedCoreInequality_fpos`) gives the bound,
    using the general-position hypothesis `∀ j, fstar j ≠ m j` to certify that the
    reflected/normalized optimum is strictly positive coordinate-wise.

The general-position hypothesis is the paper's standing normalization
(`approx.tex` line 9); see `consistency_guarantee`'s docstring. -/
theorem CGFinalAssembly :
    ∀ (c : ℝ), 0 ≤ c → c < 1 →
      ∀ {n d : ℕ}, 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P : Fin n → Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P fstar (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        socialCost 2 P m ≤ CG c * optSocialCost 2 P := by
  intro c hc0 hc1 n d hd hcn P fstar hopt m hmed hgp
  -- Reduce to the even case via CGEvenAugmentReduction.  Its `h_even` premise is
  -- the even-`n` bound, which we discharge below; the rest of its arguments are
  -- the present instance data.
  refine Workspace.ProofLemmas.CGEvenAugmentReduction.CGEvenAugmentReduction
    c hc0 hc1 ?_ hcn hd P fstar hopt m hmed hgp
  -- Goal: the `h_even` closure (general instance, `n' + ⌊cn'⌋` even).
  intro n' d' hne' hcn' hd' P' fstar' hopt' m' hmed' hgp'
  classical
  -- Split on whether OPT' = 0.
  by_cases hOPT0 : optSocialCost 2 P' = 0
  · -- Trivial branch: OPT' = 0 ⇒ every report = fstar' ⇒ augmented instance is
    -- constant fstar' ⇒ m' = fstar' ⇒ SC(P',m') = 0 = CG c · 0.
    have hq2 : (1 : ℝ) ≤ 2 := by norm_num
    -- SC(P', fstar') = 0.
    have hsc0 : socialCost 2 P' fstar' = 0 := by rw [hopt', hOPT0]
    -- Each report equals fstar'.
    have hP_eq : ∀ i : Fin n', (fun j => P' i j) = fstar' := by
      intro i
      have hsum : ∑ i, lqNorm 2 (fun j => P' i j - fstar' j) = 0 := by
        have : socialCost 2 P' fstar' = ∑ i, lqNorm 2 (fun j => P' i j - fstar' j) := rfl
        rw [this] at hsc0; exact hsc0
      have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n')),
          0 ≤ lqNorm 2 (fun j => P' i j - fstar' j) := fun i _ => lqNorm_nonneg hq2 _
      have hterm : lqNorm 2 (fun j => P' i j - fstar' j) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
      have hzero : (fun j => P' i j - fstar' j) = 0 :=
        (LqNormZeroIffEqZero 2 hq2 hd' _).mp hterm
      funext j
      have := congr_fun hzero j
      simp only [Pi.zero_apply] at this
      linarith
    -- The augmented instance is the constant fstar'.
    have haug_const :
        augment P' fstar' (⌊c * (n' : ℝ)⌋₊)
          = (fun (_ : Fin (n' + ⌊c * (n' : ℝ)⌋₊)) (j : Fin d') => fstar' j) := by
      funext i j
      unfold augment
      refine Fin.addCases ?_ ?_ i
      · intro a
        simp only [Fin.addCases_left]
        have := congr_fun (hP_eq a) j
        simpa using this
      · intro a
        simp only [Fin.addCases_right]
    -- Median of a constant is that constant, provided the augmented size ≥ 1.
    -- If the augmented size is 0 then n' = 0 and SC(P', m') is the empty sum.
    by_cases hsize : 1 ≤ n' + ⌊c * (n' : ℝ)⌋₊
    · have hmed_const :
          IsCoordinateMedian m'
            (fun (_ : Fin (n' + ⌊c * (n' : ℝ)⌋₊)) (j : Fin d') => fstar' j) := by
        rw [← haug_const]; exact hmed'
      have hm_eq : m' = fstar' := MedianOfConstant hsize fstar' m' hmed_const
      have hscm0 : socialCost 2 P' m' = 0 := by
        rw [hm_eq]; exact hsc0
      rw [hscm0, hOPT0, mul_zero]
    · -- Augmented size 0 ⇒ n' = 0 ⇒ SC(P', m') = 0 (empty sum of agents).
      have hn'0 : n' = 0 := by omega
      subst hn'0
      have hscm0 : socialCost 2 P' m' = 0 := by
        show ∑ i, lqNorm 2 (fun j => P' i j - m' j) = 0
        exact Fin.sum_univ_zero _
      rw [hscm0, hOPT0, mul_zero]
  · -- Generic branch: OPT' > 0.
    have hOPT_pos : 0 < optSocialCost 2 P' :=
      lt_of_le_of_ne (optSocialCost_nonneg (by norm_num) P') (Ne.symm hOPT0)
    -- n' > 0 (else OPT' = 0).
    have hn'_pos : 0 < n' := by
      by_contra hcon
      push_neg at hcon
      interval_cases n'
      · -- n' = 0 ⇒ optSocialCost 2 P' = 0, contradicting hOPT_pos.
        have : optSocialCost 2 P' = 0 := by
          apply le_antisymm
          · have hle := optSocialCost_le_socialCost (show (1:ℝ) ≤ 2 by norm_num) P' (fun _ => 0)
            have : socialCost 2 P' (fun _ => 0) = 0 := by
              show ∑ i, lqNorm 2 (fun j => P' i j - (fun _ => (0:ℝ)) j) = 0
              exact Fin.sum_univ_zero _
            rw [this] at hle; exact hle
          · exact optSocialCost_nonneg (by norm_num) P'
        exact absurd this hOPT0
    -- Apply CGTranslationScaleNormalize with the strict-f>0 core as h_norm.
    exact Workspace.ProofLemmas.CGTranslationScaleNormalize.CGTranslationScaleNormalize
      c hc0 hc1
      (Workspace.ProofLemmas.CGNormalizedCoreInequality.CGNormalizedCoreInequality_fpos c hc0 hc1)
      hn'_pos hne' hd' hcn' P' fstar' hopt' hOPT_pos m' hmed' hgp'

end Workspace.ProofLemmas.CGFinalAssembly
