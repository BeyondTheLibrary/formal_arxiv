import Mathlib
import Workspace.Types.ProbVec

namespace Workspace.Types.L1Distance

open Workspace.Types.ProbVec

/--
The ℓ¹ distance between two length-`n` probability vectors:
`L1Distance S S' = ∑_{i : Fin n} |S.p i - S'.p i|`.

This is a non-negative real number (see `l1Distance_nonneg`).
-/
def L1Distance {n : ℕ} (S S' : ProbVec n) : ℝ :=
  Finset.univ.sum (fun i : Fin n => |S.p i - S'.p i|)

end Workspace.Types.L1Distance
