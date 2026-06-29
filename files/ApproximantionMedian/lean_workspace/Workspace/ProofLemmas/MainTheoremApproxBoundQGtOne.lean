import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.MainTheoremTrivialCases
import Workspace.ProofLemmas.TranslationScaleNormalize
import Workspace.ProofLemmas.ReductionToEvenN
import Workspace.ProofLemmas.MainTheoremApproxBoundQEqOne
import Workspace.ProofLemmas.NormalizedCoreInequality

open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ProofLemmas.UBDef

theorem MainTheoremApproxBoundQGtOne
    (q : ℝ) (hq : 1 < q) {n d : ℕ} (hd : 1 ≤ d)
    (P : Fin n → Fin d → ℝ) (m : Fin d → ℝ)
    (hm : IsCoordinateMedian m P) :
    socialCost q P m ≤ UB q * optSocialCost q P := by
  -- Top-level structural reduction:
  --   Outer: reduce general n to even n via ReductionToEvenN.
  --   Inner: case-split on q' = 1 (use MainTheoremApproxBoundQEqOne) versus q' > 1;
  --          for q' > 1, dispatch the trivial subcase (optSocialCost = 0) via
  --          MainTheoremTrivialCases, else apply TranslationScaleNormalize, with
  --          NormalizedCoreInequality supplying the normalized-core hypothesis.
  apply ReductionToEvenN ?_ q hq.le hd P m hm
  intro q' hq' n' d' hn'_pos hn'_even hd' P' m' hm'
  rcases eq_or_lt_of_le hq' with hq1 | hq1
  · -- q' = 1
    rw [← hq1]
    exact MainTheoremApproxBoundQEqOne hd' P' m' hm'
  · -- q' > 1
    by_cases hopt0 : optSocialCost q' P' = 0
    · exact MainTheoremTrivialCases q' (le_of_lt hq1) hd' P' m' hm' (Or.inr hopt0)
    have hopt_nn : 0 ≤ optSocialCost q' P' := optSocialCost_nonneg hq' P'
    have hopt_pos : 0 < optSocialCost q' P' := lt_of_le_of_ne hopt_nn (Ne.symm hopt0)
    exact TranslationScaleNormalize NormalizedCoreInequality
      q' hq1 hn'_pos hn'_even hd' P' m' hm' hopt_pos
