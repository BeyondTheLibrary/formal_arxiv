import Mathlib

namespace Workspace.ProofLemmas.RGCubicFactor

/-- **RGCubicFactor** (appendix.tex 287–293; `c → −c` image of `CGCubicFactor`).
The cubic factorization underlying the interior critical point of the robustness
profile: for all real `t` and `c`,
`2t³ − (3−c)t + (1−c) = (t − 1)(2t² + 2t − (1−c))`. Pure polynomial identity. -/
theorem RGCubicFactor (t c : ℝ) :
    2 * t ^ 3 - (3 - c) * t + (1 - c) = (t - 1) * (2 * t ^ 2 + 2 * t - (1 - c)) := by
  ring

end Workspace.ProofLemmas.RGCubicFactor
