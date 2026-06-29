import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.MainTheoremFinalAssembly

open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost

namespace Workspace.MainTheorem

/-- **Main Theorem (Approximation guarantees of the coordinate-wise Median
Mechanism in `ℝ^d`).**

There exists a function `UB : ℝ → ℝ` (whose values for `q ≥ 1` are the
quantitatively-meaningful approximation factors) such that:

1. **(Approximation guarantee.)** For every `q ≥ 1`, every dimension
   `d ≥ 1`, every number of agents `n` (`n` is allowed to be `0`, in which
   case the bound is vacuous since both sides are `0`), every placement
   `P : Fin n → Fin d → ℝ`, and every coordinate-wise median `m` of `P`,
   `socialCost q P m ≤ UB q * optSocialCost q P`.
2. **(Base case.)** `UB 1 = 1`.
3. **(Limit at infinity.)** `UB q → 3` as `q → +∞`.
4. **(Euclidean case.)** `UB 2 = √(6√3 − 8)`. -/
theorem main_theorem :
    ∃ UB : ℝ → ℝ,
      UB 1 = 1 ∧
      Filter.Tendsto UB Filter.atTop (nhds 3) ∧
      UB 2 = Real.sqrt (6 * Real.sqrt 3 - 8) ∧
      ∀ (q : ℝ), 1 ≤ q →
        ∀ {n d : ℕ}, 1 ≤ d →
        ∀ (P : Fin n → Fin d → ℝ),
        ∀ (m : Fin d → ℝ), IsCoordinateMedian m P →
          socialCost q P m ≤ UB q * optSocialCost q P
    := MainTheoremFinalAssembly

end Workspace.MainTheorem
