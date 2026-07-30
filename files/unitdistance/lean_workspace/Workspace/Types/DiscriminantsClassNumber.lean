import Mathlib

set_option maxHeartbeats 400000

open NumberField

namespace Workspace.Types.DiscriminantsClassNumber

/-!
Number-field invariants: root discriminant, class number, and the relative
discriminant ideal of a finite extension of number fields.  Definitions only,
a thin layer over Mathlib.
-/

/-- The root discriminant of a number field `K`:
`rd(K) = |D_K|^(1/[K:ℚ])`, a nonnegative real number, where `D_K = NumberField.discr K`
is the absolute discriminant and `[K:ℚ] = Module.finrank ℚ K`. -/
noncomputable def rootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (|(NumberField.discr K : ℝ)|) ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))

/-- The class number `h(K)` of a number field `K`, i.e. the cardinality of the
ideal class group of `𝓞 K`.  Re-exposed from Mathlib's `NumberField.classNumber`. -/
noncomputable def classNumber (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.classNumber K

end Workspace.Types.DiscriminantsClassNumber
