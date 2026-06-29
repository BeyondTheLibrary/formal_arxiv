import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith

namespace Workspace.Lemmas.CSelFact

theorem c_sel_fact : (1 : ℝ) ≤ 100 * Real.log 2 := by
  have h := Real.log_two_gt_d9
  linarith

end Workspace.Lemmas.CSelFact
