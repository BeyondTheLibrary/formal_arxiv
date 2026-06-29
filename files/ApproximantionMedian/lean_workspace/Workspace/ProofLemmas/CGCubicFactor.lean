import Mathlib

namespace Workspace.ProofLemmas.CGCubicFactor

/-- **CGCubicFactor** (appendix.tex 190–196). The cubic factorization underlying
the interior critical point: for all real `t` and `c`,
`2t³ − (3+c)t + (1+c) = (t − 1)(2t² + 2t − (1+c))`. Pure polynomial identity. -/
theorem CGCubicFactor (t c : ℝ) :
    2 * t ^ 3 - (3 + c) * t + (1 + c) = (t - 1) * (2 * t ^ 2 + 2 * t - (1 + c)) := by
  ring

end Workspace.ProofLemmas.CGCubicFactor
