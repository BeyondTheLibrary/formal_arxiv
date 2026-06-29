import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Workspace.Types.FractionalCover
import Workspace.Lemmas.Lemma_PowBoundFromRatio

open BigOperators

namespace Workspace.Lemmas.FinalBound

open Workspace.Types.FractionalCover

/-- final_bound theorem: the upper bound from cost assumption.

**Source**: @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../../../arXiv-2412.03540v1.tex, Section 4, Proof of Theorem 1.2)
-/
theorem final_bound {X : Type} [Fintype X] [DecidableEq X]
    (c_sel : ℝ) (t : ℕ) (p : ℝ) (ℋ : Set (Finset X))
    (cov : FractionalCover X ℋ)
    (s : ℕ) (q q' : ℝ)
    (_hq : q = (c_sel / 100000) * p / Real.log t)
    (_hq' : q' = 16 * s * q)
    (_hs : s = Nat.ceil (Real.log (2 * t) / Real.log 2))
    (h_cost : ∑ W : Finset X, cov.w W * p ^ W.card ≤ 1 / 2)
    (hq'_le : q' ≤ p / 6) (hq'_pos : 0 ≤ q') (hp_nonneg : 0 ≤ p) :
    ∑ W : Finset X, cov.w W * q' ^ W.card ≤ (1 / 12 : ℝ) := by
  -- Pointwise bound: cov.w W * q'^|W| ≤ (1/6) * (cov.w W * p^|W|)
  have h_term : ∀ W : Finset X,
      cov.w W * q' ^ W.card ≤ (1 / 6) * (cov.w W * p ^ W.card) := by
    intro W
    by_cases hW : W = ∅
    · -- Empty case: cov.w ∅ = 0
      rw [hW, cov.w_empty]
      simp
    · -- Nonempty case: apply pow_bound_from_ratio
      have hk : W.card ≥ 1 :=
        Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hW)
      have hpow := Workspace.Lemmas.PowBoundFromRatio.pow_bound_from_ratio
                     hp_nonneg hq'_pos hq'_le hk
      have hwnn := cov.nonneg W
      have hpk : (0 : ℝ) ≤ p ^ W.card := pow_nonneg hp_nonneg _
      nlinarith [hwnn, hpow, hpk]
  -- Sum the pointwise bound
  calc ∑ W : Finset X, cov.w W * q' ^ W.card
      ≤ ∑ W : Finset X, (1 / 6) * (cov.w W * p ^ W.card) :=
        Finset.sum_le_sum (fun W _ => h_term W)
    _ = (1 / 6) * ∑ W : Finset X, cov.w W * p ^ W.card := by
        rw [← Finset.mul_sum]
    _ ≤ (1 / 6) * (1 / 2) := by
        have h6 : (0 : ℝ) ≤ 1 / 6 := by norm_num
        nlinarith [h_cost]
    _ = 1 / 12 := by norm_num

end Workspace.Lemmas.FinalBound
