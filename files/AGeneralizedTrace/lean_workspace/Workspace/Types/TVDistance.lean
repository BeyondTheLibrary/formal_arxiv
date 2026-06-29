import Mathlib
import Workspace.Types.Trace

open Workspace.Types.Trace

namespace Workspace.Types.TVDistance

/--
The total-variation distance between two PMFs on `Trace n`.

`TVDistance μ ν = (1/2) · ∑' τ, |μ(τ) - ν(τ)|`

The sum is a `tsum` over the countable type `Trace n` (a subtype of `List Bool`,
which is countable). The PMF values live in `ℝ≥0∞`; we convert to `ℝ` via
`ENNReal.toReal` before taking the absolute value of the difference.
-/
noncomputable def TVDistance {n : ℕ} (μ ν : PMF (Trace n)) : ℝ :=
  (1 / 2 : ℝ) * ∑' τ : Trace n, |(μ τ).toReal - (ν τ).toReal|

end Workspace.Types.TVDistance
