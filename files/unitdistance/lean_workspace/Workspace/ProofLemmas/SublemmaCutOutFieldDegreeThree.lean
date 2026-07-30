import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.DirichletCharacterRangeCardEqOrder

open Workspace.Types.CyclotomicCharacterFields
open scoped NumberField

set_option maxHeartbeats 800000

theorem SublemmaCutOutFieldDegreeThree (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    (n : ℕ) (hchi : orderOf chi = n) :
    Module.finrank ℚ ↥(cutOutField D chi) = n := by
  rw [← hchi]
  set K := cyclotomicField' D with hK
  set φ := chi.toUnitHom.comp (galToUnits D).toMonoidHom with hφ
  set H := φ.ker with hH
  -- lift preserves degree over ℚ
  have hlift : Module.finrank ℚ ↥(cutOutField D chi) =
      Module.finrank ℚ ↥(IntermediateField.fixedField H) := by
    have e := IntermediateField.equivMap (IntermediateField.fixedField H) (K.val)
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  rw [hlift]
  -- fixed field degree = index of H
  have hidx : Module.finrank ℚ ↥(IntermediateField.fixedField H) = H.index := by
    have hcard : Module.finrank ↥(IntermediateField.fixedField H) K = Nat.card ↥H :=
      IntermediateField.finrank_fixedField_eq_card H
    have htower : Module.finrank ℚ ↥(IntermediateField.fixedField H) *
        Module.finrank ↥(IntermediateField.fixedField H) K = Module.finrank ℚ K :=
      Module.finrank_mul_finrank ℚ ↥(IntermediateField.fixedField H) K
    have hgal : Module.finrank ℚ K = Nat.card (K ≃ₐ[ℚ] K) :=
      (IsGalois.card_aut_eq_finrank ℚ K).symm
    have hcmi : Nat.card ↥H * H.index = Nat.card (K ≃ₐ[ℚ] K) := Subgroup.card_mul_index H
    rw [hcard, hgal] at htower
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    have hfin : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H =
        H.index * Nat.card ↥H := by rw [htower, ← hcmi, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos hfin
  rw [hidx, Subgroup.index_ker]
  -- goal: Nat.card ↥φ.range = orderOf chi
  have hsurj : Function.Surjective (galToUnits D).toMonoidHom := (galToUnits D).surjective
  have hrange : φ.range = chi.toUnitHom.range := by
    ext x
    simp only [hφ, MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩; obtain ⟨a, rfl⟩ := hsurj b; exact ⟨a, rfl⟩
  rw [hrange]
  exact DirichletCharacterRangeCardEqOrder chi
