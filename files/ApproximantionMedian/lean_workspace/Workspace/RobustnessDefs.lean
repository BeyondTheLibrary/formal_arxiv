import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem

namespace Workspace.RobustnessTheorem

/-- The closed-form robustness bound `RG(c)` for the `CMP(c)` mechanism at
`q = 2` (Euclidean L₂), from Theorem 4 of Gravin & Jia.

`RG(c) = 1/λ₂ = √(−4·√(3−2c)·c + 6·√(3−2c) + 10c − 8) / (1 − c)`,  `c ∈ [0,1)`.

Unlike consistency's `CG(c)`, the robustness `RG(c)` has a **single branch**
across the whole interval `c ∈ [0,1)`: the interior root
`a₂' = (2−c−√(3−2c))/2 ≤ (1+c)/2` for every `c ∈ [0,1)`, so the boundary case
`a₂ = (1+c)/2` never binds (appendix.tex lines 310–311). There is NO `if c < 1/2`
split here, in contrast to the two-branch `CG`.

(The `^{1/2}` in the paper is rendered with `Real.sqrt`.) -/
noncomputable def RG (c : ℝ) : ℝ :=
  Real.sqrt (-4 * Real.sqrt (3 - 2 * c) * c + 6 * Real.sqrt (3 - 2 * c) + 10 * c - 8) / (1 - c)

end Workspace.RobustnessTheorem
