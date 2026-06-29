import Mathlib
import Workspace.Types.Bracket
import Workspace.Types.MatComplexity

namespace Workspace.Types.Lambda

open Workspace.Types.BoolMat
open Workspace.Types.Bracket
open Workspace.Types.MatComplexity

/-- The three-rung potential `Λ_M(p,x,y)` (Section 4.3).

For a Boolean matrix `M`, a positive integer `p`, and reals `x, y`, the
potential is the minimum over `j ∈ {0, 1, 2}` of

  `j + DSet ([M]_{p, x, y / 2^j})`,

i.e. the smaller of three rungs whose column densities are `y`, `y/2`, and
`y/4`:

* `j = 0`: `0 + DSet (bracket M p x y)`,
* `j = 1`: `1 + DSet (bracket M p x (y / 2))`,
* `j = 2`: `2 + DSet (bracket M p x (y / 4))`.

`DSet` is noncomputable, so `Λ` is marked `noncomputable`. -/
noncomputable def Lambda (M : BoolMat) (p : ℕ) (x y : ℝ) : ℕ :=
  min (DSet (bracket M p x y))
      (min (1 + DSet (bracket M p x (y / 2)))
           (2 + DSet (bracket M p x (y / 4))))

end Workspace.Types.Lambda
