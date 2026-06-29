import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian

namespace Workspace.ConsistencyTheorem

/-- The closed-form consistency bound `CG(c)` for the `CMP(c)` mechanism at
`q = 2` (Euclidean L₂), from Theorem 3 of Gravin & Jia.

For `c < 1/2`:
`CG(c) = √(4·√(2c+3)·c + 6·√(2c+3) − 10c − 8) / (c + 1)`.

For `c ≥ 1/2`:
`CG(c) = √(2 / (c + 1))`.

(The `^{1/2}` in the paper is rendered with `Real.sqrt`.) -/
noncomputable def CG (c : ℝ) : ℝ :=
  if c < 1 / 2 then
    Real.sqrt (4 * Real.sqrt (2 * c + 3) * c + 6 * Real.sqrt (2 * c + 3) - 10 * c - 8) / (c + 1)
  else
    Real.sqrt (2 / (c + 1))

/-- The `CMP(c)`-augmented instance: the original `n` agent reports `P`
augmented with `k` copies of the prediction `pred`. Indices `< n` return the
corresponding original report `P i`; indices `≥ n` (the last `k`) return `pred`.

Modeling choice: the index split uses `Fin.addCases`, so for
`i : Fin (n + k)` the result is `P` on the `Fin n` summand and the constant
`pred` on the `Fin k` summand. This matches "append `k` copies of `pred`". -/
def augment {n d : ℕ} (P : Fin n → Fin d → ℝ) (pred : Fin d → ℝ) (k : ℕ) :
    Fin (n + k) → Fin d → ℝ :=
  Fin.addCases (fun i => P i) (fun _ => pred)

end Workspace.ConsistencyTheorem
