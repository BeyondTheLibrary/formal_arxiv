import Mathlib

namespace Workspace.Types.LowerBoundConstants

/--
`LowerBoundConstants` bundles the six absolute constants appearing in the
main theorem:

* `cDelta`, `cInf`, `c1`, `cC1`, `cTv` — strictly positive real constants
  (corresponding to the paper's `c_delta`, `c_inf`, `c_1`, `C_1`, `c_tv`).
* `n0` — a natural number threshold (the paper's `n_0`) above which the
  theorem's conclusion holds.

The structure also carries positivity proofs for the five real constants
and the ordering `c1 ≤ cC1`, ensuring that the range `[c1 · √n, C_1 · √n]`
used in the main theorem is non-empty.

Field-name mapping (spec → Lean):
* `c_delta` → `cDelta`
* `c_inf`   → `cInf`
* `c_1`     → `c1`
* `C_1`     → `cC1`
* `c_tv`    → `cTv`
* `n_0`     → `n0`
-/
structure LowerBoundConstants where
  /-- The constant `c_delta` from the paper (strictly positive). -/
  cDelta : ℝ
  /-- The constant `c_inf` from the paper (strictly positive). -/
  cInf : ℝ
  /-- The lower constant `c_1` in the range `[c_1 √n, C_1 √n]`
  (strictly positive). -/
  c1 : ℝ
  /-- The upper constant `C_1` in the range `[c_1 √n, C_1 √n]`
  (strictly positive). -/
  cC1 : ℝ
  /-- The constant `c_tv` from the paper (strictly positive). -/
  cTv : ℝ
  /-- The threshold `n_0` above which the theorem's conclusion holds. -/
  n0 : ℕ
  /-- Positivity of `c_delta`. -/
  cDelta_pos : 0 < cDelta
  /-- Positivity of `c_inf`. -/
  cInf_pos : 0 < cInf
  /-- Positivity of `c_1`. -/
  c1_pos : 0 < c1
  /-- Positivity of `C_1`. -/
  cC1_pos : 0 < cC1
  /-- Positivity of `c_tv`. -/
  cTv_pos : 0 < cTv
  /-- `c_1 ≤ C_1`, so that `[c_1 √n, C_1 √n]` is non-empty. -/
  c1_le_cC1 : c1 ≤ cC1

end Workspace.Types.LowerBoundConstants
