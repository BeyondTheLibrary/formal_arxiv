import Mathlib
import Workspace.Types.BoolMat
import Workspace.Types.Interlace
import Workspace.Types.AlternatingGame

open Workspace.Types.BoolMat Workspace.Types.Interlace Workspace.Types.AlternatingGame

namespace Workspace.ProofLemmas

private abbrev Q : ℕ := 255 * 2 ^ (10000 - 8)

theorem DimRecurrence (i : ℕ) :
    (phi Q (i + 1)).m = ((phi Q i).n) ^ Q ∧ (phi Q (i + 1)).n = (phi Q i).m * Q := by
  constructor <;> rfl

end Workspace.ProofLemmas
