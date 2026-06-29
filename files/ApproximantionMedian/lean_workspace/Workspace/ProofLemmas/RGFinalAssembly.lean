import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.RGEvenAugmentReduction
import Workspace.ProofLemmas.RGTranslationScaleNormalize
import Workspace.ProofLemmas.RGNormalizedCoreInequality
import Workspace.ProofLemmas.LqNormZeroIffEqZero

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem

namespace Workspace.ProofLemmas.RGFinalAssembly

/-- **Strict-majority coordinate median.**  In the OPT = 0 robustness branch the
pred-augmented instance is `fstar'` on the `n'` original agents and `pred'` on the
`⌊cn'⌋` appended copies.  When `n' > (n' + ⌊cn'⌋)/2` (i.e. the original agents form a
STRICT majority, which holds because `⌊cn'⌋ < n'`), any coordinate-wise median `m'`
must agree with `fstar'` on every coordinate: if `m' j < fstar' j` then all `n'`
original agents lie strictly above `m' j`, forcing the `>`-filter card `≥ n' > N/2`,
contradicting the median condition (symmetric for `m' j > fstar' j`).  This is the one
genuine difference from the consistency assembly, where the augmented instance is a
true constant and `MedianOfConstant` applies directly. -/
private lemma strictMajority_median_eq {n' d' k : ℕ}
    (hmaj : (n' + k) / 2 < n')
    (cst : Fin d' → ℝ) (pred' : Fin d' → ℝ) (m' : Fin d' → ℝ)
    (hmed : IsCoordinateMedian m'
      (Workspace.ConsistencyTheorem.augment
        (fun (_ : Fin n') (j : Fin d') => cst j) pred' k)) :
    m' = cst := by
  classical
  funext j
  obtain ⟨hlt, hgt⟩ := hmed j
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmlt | hmgt
  · -- m' j < cst j : every original agent (left summand) lies strictly above m' j.
    have hsub : n' ≤
        (Finset.univ.filter
          (fun i : Fin (n' + k) =>
            (Workspace.ConsistencyTheorem.augment
              (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) i j > m' j)).card := by
      have hcard :
          (Finset.univ : Finset (Fin n')).card ≤
          (Finset.univ.filter
            (fun i : Fin (n' + k) =>
              (Workspace.ConsistencyTheorem.augment
                (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) i j > m' j)).card := by
        refine Finset.card_le_card_of_injOn (fun i => Fin.castAdd k i) ?_ ?_
        · intro i _
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          show (Workspace.ConsistencyTheorem.augment
            (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) (Fin.castAdd k i) j > m' j
          unfold Workspace.ConsistencyTheorem.augment
          rw [Fin.addCases_left]
          exact hmlt
        · intro a _ b _ hab
          exact Fin.castAdd_injective _ _ hab
      simpa using hcard
    have : n' ≤ (n' + k) / 2 := le_trans hsub hgt
    omega
  · -- m' j > cst j : every original agent (left summand) lies strictly below m' j.
    have hsub : n' ≤
        (Finset.univ.filter
          (fun i : Fin (n' + k) =>
            (Workspace.ConsistencyTheorem.augment
              (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) i j < m' j)).card := by
      have hcard :
          (Finset.univ : Finset (Fin n')).card ≤
          (Finset.univ.filter
            (fun i : Fin (n' + k) =>
              (Workspace.ConsistencyTheorem.augment
                (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) i j < m' j)).card := by
        refine Finset.card_le_card_of_injOn (fun i => Fin.castAdd k i) ?_ ?_
        · intro i _
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
          show (Workspace.ConsistencyTheorem.augment
            (fun (_ : Fin n') (j : Fin d') => cst j) pred' k) (Fin.castAdd k i) j < m' j
          unfold Workspace.ConsistencyTheorem.augment
          rw [Fin.addCases_left]
          exact hmgt
        · intro a _ b _ hab
          exact Fin.castAdd_injective _ _ hab
      simpa using hcard
    have : n' ≤ (n' + k) / 2 := le_trans hsub hlt
    omega

/-- **RGFinalAssembly** — the proof of Theorem 4 (robustness guarantee of
`CMP(c)`), assembled from the robustness sub-lemmas.

This is the body of `Workspace.RobustnessTheorem.robustness_guarantee`; the
root statement file sets `robustness_guarantee := RGFinalAssembly`.

Pipeline (faithful `c → −c` / `fstar → pred` mirror of `CGFinalAssembly`):
* `RGEvenAugmentReduction` reduces to the case `n + ⌊cn⌋` even (and discharges
  `n = 0`) by duplicating the pred-augmented instance.
* In the even case we split on `optSocialCost 2 P = 0`:
  - `OPT = 0`: every report equals the optimal facility `fstar'`, so the
    pred-augmented instance is `fstar'` on the `n'` agents and `pred'` on the
    `⌊cn'⌋` appended copies.  Because `⌊cn'⌋ < n'`, the original agents form a
    STRICT majority on every coordinate, so any median `m'` equals `fstar'`
    (`strictMajority_median_eq`).  Then `SC(P',m') = SC(P',fstar') = 0 ≤ RG c · 0`.
  - `OPT > 0`: `RGTranslationScaleNormalize` (its `h_norm` premise instantiated
    with the strict-`f>0` core `RGNormalizedCoreInequality_fpos`) gives the bound,
    using the general-position hypotheses `∀ j, fstar j ≠ m j` and `∀ j, pred j ≠ m j`.

The general-position hypotheses are the paper's standing normalization; see
`robustness_guarantee`'s docstring. -/
theorem RGFinalAssembly :
    ∀ (c : ℝ), 0 ≤ c → c < 1 →
      ∀ {n d : ℕ}, 1 ≤ d →
      (⌊c * (n : ℝ)⌋₊ : ℝ) = c * (n : ℝ) →
      ∀ (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (fstar : Fin d → ℝ),
        socialCost 2 P fstar = optSocialCost 2 P →
      ∀ (m : Fin d → ℝ),
        IsCoordinateMedian m (augment P pred (⌊c * (n : ℝ)⌋₊)) →
        (∀ j, fstar j ≠ m j) →
        (∀ j, pred j ≠ m j) →
        socialCost 2 P m ≤ RG c * optSocialCost 2 P := by
  intro c hc0 hc1 n d hd hcn P pred fstar hopt m hmed hgp hgp_pred
  -- Reduce to the even case via RGEvenAugmentReduction.  Its `h_even` premise is
  -- the even-`n` bound, which we discharge below; the rest of its arguments are
  -- the present instance data.
  refine Workspace.ProofLemmas.RGEvenAugmentReduction.RGEvenAugmentReduction
    c hc0 hc1 ?_ hcn hd P pred fstar hopt m hmed hgp hgp_pred
  -- Goal: the `h_even` closure (general instance, `n' + ⌊cn'⌋` even).
  intro n' d' hne' hcn' hd' P' pred' fstar' hopt' m' hmed' hgp' hgp_pred'
  classical
  -- Split on whether OPT' = 0.
  by_cases hOPT0 : optSocialCost 2 P' = 0
  · -- Trivial branch: OPT' = 0 ⇒ every report = fstar'.  The pred-augmented
    -- instance is `fstar'` on agents + `pred'` on the appended copies; the strict
    -- majority of agents forces m' = fstar', whence SC(P',m') = 0 = RG c · 0.
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
    -- The pred-augmented instance is `fstar'` on agents + `pred'` on the copies.
    have haug_eq :
        augment P' pred' (⌊c * (n' : ℝ)⌋₊)
          = augment (fun (_ : Fin n') (j : Fin d') => fstar' j) pred' (⌊c * (n' : ℝ)⌋₊) := by
      funext i j
      unfold augment
      refine Fin.addCases ?_ ?_ i
      · intro a
        simp only [Fin.addCases_left]
        have := congr_fun (hP_eq a) j
        simpa using this
      · intro a
        simp only [Fin.addCases_right]
    -- n' > 0 (else OPT' is the empty-agent cost, which is 0 — fine — but we need the
    -- strict-majority argument; handle n' = 0 separately).
    by_cases hn'0 : n' = 0
    · subst hn'0
      have hscm0 : socialCost 2 P' m' = 0 := by
        show ∑ i, lqNorm 2 (fun j => P' i j - m' j) = 0
        exact Fin.sum_univ_zero _
      rw [hscm0, hOPT0, mul_zero]
    · have hn'_pos : 0 < n' := Nat.pos_of_ne_zero hn'0
      -- ⌊cn'⌋ < n', so the original agents form a strict majority.
      have hk_lt : ⌊c * (n' : ℝ)⌋₊ < n' := by
        have hreal : (⌊c * (n' : ℝ)⌋₊ : ℝ) < (n' : ℝ) := by
          rw [hcn']
          calc c * (n' : ℝ) < 1 * (n' : ℝ) := by
                apply mul_lt_mul_of_pos_right hc1
                exact_mod_cast hn'_pos
            _ = (n' : ℝ) := by ring
        exact_mod_cast hreal
      have hmaj : (n' + ⌊c * (n' : ℝ)⌋₊) / 2 < n' := by omega
      -- The median equals fstar'.
      have hmed_cst :
          IsCoordinateMedian m'
            (augment (fun (_ : Fin n') (j : Fin d') => fstar' j) pred' (⌊c * (n' : ℝ)⌋₊)) := by
        rw [← haug_eq]; exact hmed'
      have hm_eq : m' = fstar' :=
        strictMajority_median_eq hmaj fstar' pred' m' hmed_cst
      have hscm0 : socialCost 2 P' m' = 0 := by
        rw [hm_eq]; exact hsc0
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
    -- Apply RGTranslationScaleNormalize with the strict-f>0 core as h_norm.
    exact Workspace.ProofLemmas.RGTranslationScaleNormalize.RGTranslationScaleNormalize
      c hc0 hc1
      (Workspace.ProofLemmas.RGNormalizedCoreInequality.RGNormalizedCoreInequality_fpos c hc0 hc1)
      hn'_pos hne' hd' hcn' P' pred' fstar' hopt' hOPT_pos m' hmed' hgp' hgp_pred'

end Workspace.ProofLemmas.RGFinalAssembly
