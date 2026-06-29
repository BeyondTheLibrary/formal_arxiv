import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.UBLimitThree
import Workspace.ProofLemmas.UBTwo
import Workspace.ProofLemmas.MainTheoremApproxBoundQEqOne
import Workspace.ProofLemmas.MainTheoremApproxBoundQGtOne

open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ProofLemmas.UBDef

theorem MainTheoremFinalAssembly :
    ∃ UB' : ℝ → ℝ,
      UB' 1 = 1 ∧
      Filter.Tendsto UB' Filter.atTop (nhds 3) ∧
      UB' 2 = Real.sqrt (6 * Real.sqrt 3 - 8) ∧
      ∀ (q : ℝ), 1 ≤ q →
        ∀ {n d : ℕ}, 1 ≤ d →
        ∀ (P : Fin n → Fin d → ℝ),
        ∀ (m : Fin d → ℝ), IsCoordinateMedian m P →
          socialCost q P m ≤ UB' q * optSocialCost q P := by
  refine ⟨UB, UBDef.2, UBLimitThree, UBTwo, ?_⟩
  intro q hq n d hd P m hm
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · -- hq1 : 1 = q
    rw [← hq1]
    exact MainTheoremApproxBoundQEqOne hd P m hm
  · exact MainTheoremApproxBoundQGtOne q hq1 hd P m hm
