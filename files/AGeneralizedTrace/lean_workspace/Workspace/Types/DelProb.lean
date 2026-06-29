import Mathlib

namespace Workspace.Types.DelProb

/-- A deletion probability δ: a real number strictly between 0 and 1.
Parameterises the deletion channel. Endpoints are excluded (0 = no-deletion
case, 1 = erases everything). -/
structure DelProb where
  /-- The underlying real value. -/
  val : ℝ
  /-- The value is strictly positive. -/
  pos : 0 < val
  /-- The value is strictly less than 1. -/
  lt_one : val < 1

end Workspace.Types.DelProb
