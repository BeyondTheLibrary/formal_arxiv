import Mathlib
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.CGABranchComparison

open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.CGABranchComparison

namespace Workspace.ProofLemmas.CGDeltaLambdaHighBranch

/-- **CGDeltaLambdaHighBranch** (prediction.tex line 92; appendix.tex 215–220).
For `c ∈ [1/2, 1)`, with `a₁ = (1-c)/2` (so the term `(1−2a₁−c)/(1+c)` vanishes
since `1 − 2a₁ − c = 0`), the value `δ₁²` obtained from `u₁(a₁) = 0` is
`δ₁² = a₁/(1−a₁) = ((1-c)/2)/((1+c)/2) = (1-c)/(1+c)`, and the resulting
`λ₁ = (1 + δ₁²)^{-1/2} = (2/(1+c))^{-1/2} = √((c+1)/2)`, so
`1/λ₁ = √(2/(c+1)) = CG c`.

We state: on this branch the closed-form `lambda1 c` (defined as `√((c+1)/2)`)
satisfies the chain of equalities
`δ₁² = (1-c)/(1+c)`, `lambda1 c = (1 + δ₁²)^{-1/2} = √((c+1)/2)`, and
`1 / lambda1 c = CG c`. -/
theorem CGDeltaLambdaHighBranch (c : ℝ) (hc_lo : 1 / 2 ≤ c) (hc_hi : c < 1) :
    let a1v : ℝ := (1 - c) / 2
    let d1sq : ℝ := a1v / (1 - a1v)
    (d1sq = (1 - c) / (1 + c)) ∧
    (lambda1 c = (1 + d1sq) ^ (-(1 : ℝ) / 2)) ∧
    (lambda1 c = Real.sqrt ((c + 1) / 2)) ∧
    (1 / lambda1 c = Workspace.ConsistencyTheorem.CG c) := by
  have hc1 : (0 : ℝ) < 1 - c := by linarith
  have hc2 : (0 : ℝ) < 1 + c := by linarith
  have hcn : ¬ (c < 1 / 2) := by linarith
  have hlam : lambda1 c = Real.sqrt ((c + 1) / 2) := by
    unfold lambda1; rw [if_neg hcn]
  have hcg : Workspace.ConsistencyTheorem.CG c = Real.sqrt (2 / (c + 1)) := by
    unfold Workspace.ConsistencyTheorem.CG; rw [if_neg hcn]
  intro a1v d1sq
  have hd1 : d1sq = (1 - c) / (1 + c) := by
    show ((1 - c) / 2) / (1 - (1 - c) / 2) = (1 - c) / (1 + c)
    rw [div_eq_div_iff (by nlinarith) (by linarith)]
    ring
  refine ⟨hd1, ?_, hlam, ?_⟩
  · -- lambda1 c = (1 + d1sq) ^ (-1/2)
    have hsum : (1 : ℝ) + d1sq = 2 / (1 + c) := by
      rw [hd1]; field_simp; ring
    rw [hlam, hsum]
    have h2c : (0 : ℝ) < 2 / (1 + c) := by positivity
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg (le_of_lt h2c),
      ← Real.sqrt_eq_rpow, ← Real.sqrt_inv]
    congr 1
    rw [inv_div]
    ring
  · -- 1 / lambda1 c = CG c
    rw [hlam, hcg, one_div, ← Real.sqrt_inv]
    congr 1
    rw [inv_div]

end Workspace.ProofLemmas.CGDeltaLambdaHighBranch
