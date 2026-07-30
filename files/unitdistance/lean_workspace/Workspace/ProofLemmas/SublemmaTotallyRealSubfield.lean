import Mathlib

open NumberField

theorem SublemmaTotallyRealSubfield :
    ∀ (A B : IntermediateField ℚ ℂ) [NumberField ↥A] [NumberField ↥B],
      A ≤ B → NumberField.IsTotallyReal ↥B → NumberField.IsTotallyReal ↥A := by
  intro A B _ _ h hB
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ↥A ↥B := by infer_instance
  exact NumberField.IsTotallyReal.of_algebra ↥A ↥B
