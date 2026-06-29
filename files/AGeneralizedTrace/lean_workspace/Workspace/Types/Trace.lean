import Mathlib

namespace Workspace.Types.Trace

/--
A `Trace n` represents a finite binary string of length at most `n`,
the observable output of the deletion-channel (trace-generation) process.
-/
structure Trace (n : ℕ) where
  /-- The underlying list of Booleans forming the trace. -/
  bits : List Bool
  /-- Proof that the length of the underlying bit list does not exceed the bound `n`. -/
  length_le : bits.length ≤ n

end Workspace.Types.Trace
