import Mathlib

/-- **Tower degree multiplicativity.** For `F, M : IntermediateField ℚ ℂ` with `F ≤ M`,
`F` a number field, `M/ℚ` finite, and the inclusion algebra structure (so that
`algebraMap ↥F ↥M` is the subfield inclusion), the degrees multiply in the tower
`ℚ ⊆ F ⊆ M`: `Module.finrank ℚ ↥M = Module.finrank ↥F ↥M * Module.finrank ℚ ↥F`. -/
theorem SublemmaTowerDegree (F M : IntermediateField ℚ ℂ) (hFM : F ≤ M)
    [NumberField ↥F] [FiniteDimensional ℚ ↥M]
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Module.finrank ℚ ↥M = Module.finrank ↥F ↥M * Module.finrank ℚ ↥F := by
  haveI : FiniteDimensional ℚ ↥F := inferInstance
  haveI : FiniteDimensional ↥F ↥M := Module.Finite.right ℚ ↥F ↥M
  rw [mul_comm, Module.finrank_mul_finrank ℚ ↥F ↥M]
