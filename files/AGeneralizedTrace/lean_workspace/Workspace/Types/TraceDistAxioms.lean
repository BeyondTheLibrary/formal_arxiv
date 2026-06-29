import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.Types.LowerBoundConstants
import Workspace.Types.LowerBoundWitness

namespace Workspace.Types.TraceDistAxioms

open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.TraceDist
open Workspace.Types.TVDistance

/--
Existence of a deletion-rate `δ` with `val = 1/2`.

A `DelProb` with value exactly `1/2` exists: it satisfies the open-interval
constraints `0 < 1/2 < 1`. This is purely structural; the lemma is here for
notational convenience so that downstream proofs can produce a
canonical "half" witness without re-proving positivity each time.
-/
noncomputable def halfDelProb : DelProb :=
  { val := (1 : ℝ) / 2
    pos := by norm_num
    lt_one := by norm_num }

lemma halfDelProb_val : halfDelProb.val = (1 : ℝ) / 2 := rfl

-- (The non-paper axiom `pad_preserves_tv` and the zero-padding reduction it
-- supported were removed in F90: `MainTheorem` now constructs the witness
-- directly for `n ≡ 1 (mod 8)` — a faithful specialization of the paper's
-- odd-`n` construction — so no padding step is needed.)

end Workspace.Types.TraceDistAxioms
