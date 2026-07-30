import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by a Dirichlet character `χ` of modulus `m` is Galois
(indeed abelian) over `ℚ`. -/
theorem SublemmaCutOutFieldGalois (m : ℕ+) (χ : DirichletCharacter ℂ (m : ℕ)) :
    IsGalois ℚ ↥(cutOutField m χ) := by
  set H := (χ.toUnitHom.comp (galToUnits m).toMonoidHom).ker with hH
  haveI hg : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup _
  have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(cutOutField m χ) :=
    IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)
  exact IsGalois.of_algEquiv e
