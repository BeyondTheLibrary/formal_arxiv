import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaCyclicCubicSubfieldNormal (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) :
    IsGalois ℚ ↥(cyclicCubicSubfield r hr hr3) := by
  unfold cyclicCubicSubfield
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom) with hH
  -- The Galois group is abelian (iso to `(ZMod r)ˣ`), so every subgroup is normal.
  haveI hnormal : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hcomm : g * a * g⁻¹ = a := by
      apply (galToUnits r).injective
      rw [map_mul, map_mul, map_inv]
      rw [mul_comm (galToUnits r g) (galToUnits r a), mul_assoc, mul_inv_cancel, mul_one]
    rwa [hcomm]
  have hgal : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup H
  -- transfer across `lift = map val`
  have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ]
      ↥(IntermediateField.lift (IntermediateField.fixedField H)) :=
    IntermediateField.equivMap (IntermediateField.fixedField H) (cyclotomicField' r).val
  exact (AlgEquiv.transfer_galois e).mp hgal
