import Mathlib
import Workspace.Types.LqNorm

open Workspace.Types.LqNorm

theorem LqNormSubReverseTriangle {q : ℝ} (hq : 1 ≤ q) {d : ℕ} (x y : Fin d → ℝ) :
    lqNorm q x - lqNorm q y ≤ lqNorm q (fun j => x j - y j) := by
  -- Apply the Minkowski inequality `Real.Lp_add_le` to f = x - y, g = y.
  -- That gives: lqNorm q ((x-y)+y) ≤ lqNorm q (x-y) + lqNorm q y, i.e.
  --            lqNorm q x ≤ lqNorm q (x-y) + lqNorm q y.
  have hMink := Real.Lp_add_le (Finset.univ : Finset (Fin d))
    (fun j => x j - y j) (fun j => y j) hq
  -- Rewrite `(x j - y j) + y j` as `x j` inside the LHS sum.
  have hxeq : (∑ j, |(x j - y j) + y j| ^ q) = (∑ j, |x j| ^ q) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    have : (x j - y j) + y j = x j := by ring
    rw [this]
  rw [hxeq] at hMink
  -- Now hMink : (∑ j, |x j|^q)^(1/q) ≤ (∑ j, |x j - y j|^q)^(1/q) + (∑ j, |y j|^q)^(1/q)
  -- These are exactly lqNorm q x, lqNorm q (fun j => x j - y j), and lqNorm q y.
  unfold lqNorm
  linarith
