import Mathlib
import Workspace.Types.ProbVec

open Workspace.Types.ProbVec

namespace Workspace.Types.LInfDistance

/--
The ℓ∞ (supremum) distance between two probability vectors of the same length.

For `S, S' : ProbVec n`, we set
`LInfDistance S S' := max_{i : Fin n} |S.p i - S'.p i|`
when `n > 0`, and `0` when `n = 0` (the max over an empty set is vacuously `0`).

The result is always a non-negative real (see `LInfDistance_nonneg`).
-/
def LInfDistance : {n : ℕ} → (S S' : ProbVec n) → ℝ
  | 0, _, _ => 0
  | (n+1), S, S' =>
      (Finset.univ : Finset (Fin (n+1))).sup'
        Finset.univ_nonempty
        (fun i => |S.p i - S'.p i|)

end Workspace.Types.LInfDistance
