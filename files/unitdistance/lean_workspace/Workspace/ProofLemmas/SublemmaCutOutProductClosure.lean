import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by a product character `χ * χ'` is contained in the compositum
of the fields cut out by the factors: `cutOutField D (χ * χ') ≤ cutOutField D χ ⊔ cutOutField D χ'`.
This holds because `ker (χ * χ') ⊇ ker χ ∩ ker χ'`, and the fixed-field (Galois)
correspondence is antitone with `fixedField (H₁ ⊓ H₂) = fixedField H₁ ⊔ fixedField H₂`. -/
theorem SublemmaCutOutProductClosure
    (D : ℕ+) (χ χ' : DirichletCharacter ℂ (D : ℕ)) :
    cutOutField D (χ * χ') ≤ cutOutField D χ ⊔ cutOutField D χ' := by
  haveI : FiniteDimensional ℚ (cyclotomicField' D) := inferInstance
  -- General Galois-correspondence fact: if `Ha ⊓ Hb ≤ Hc` then
  -- `fixedField Hc ≤ fixedField Ha ⊔ fixedField Hb`.
  have core : ∀ (Ha Hb Hc : Subgroup (cyclotomicField' D ≃ₐ[ℚ] cyclotomicField' D)),
      Ha ⊓ Hb ≤ Hc →
      IntermediateField.fixedField Hc ≤
        IntermediateField.fixedField Ha ⊔ IntermediateField.fixedField Hb := by
    intro Ha Hb Hc hc
    set B := IntermediateField.fixedField Ha ⊔ IntermediateField.fixedField Hb with hB
    rw [← IsGalois.fixedField_fixingSubgroup B]
    apply IntermediateField.fixedField_antitone
    refine le_trans ?_ hc
    apply le_inf
    · have h1 : IntermediateField.fixedField Ha ≤ B := le_sup_left
      have := IntermediateField.fixingSubgroup_antitone h1
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
    · have h2 : IntermediateField.fixedField Hb ≤ B := le_sup_right
      have := IntermediateField.fixingSubgroup_antitone h2
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
  -- Kernel containment: `ker χ ⊓ ker χ' ≤ ker (χ * χ')`.
  have hker : (χ.toUnitHom.comp (galToUnits D).toMonoidHom).ker ⊓
      (χ'.toUnitHom.comp (galToUnits D).toMonoidHom).ker ≤
      ((χ * χ').toUnitHom.comp (galToUnits D).toMonoidHom).ker := by
    intro g hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulChar.toUnitHom_eq,
        MulChar.equivToUnitHom_mul_apply]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulChar.toUnitHom_eq] at h1 h2
    rw [h1, h2, one_mul]
  -- Monotonicity of `IntermediateField.lift` (`lift E = map K.val E`).
  have lift_mono : ∀ {A B : IntermediateField ℚ ↥(cyclotomicField' D)}, A ≤ B →
      IntermediateField.lift A ≤ IntermediateField.lift B := by
    intro A B h
    exact IntermediateField.map_mono (cyclotomicField' D).val h
  -- Assemble.
  simp only [cutOutField]
  rw [← IntermediateField.lift_sup]
  apply lift_mono
  exact core _ _ _ hker
