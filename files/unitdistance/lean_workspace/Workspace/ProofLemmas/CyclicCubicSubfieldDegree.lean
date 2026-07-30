-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the cyclic cubic subfield of Q(zeta_r) has degree 3 over Q.
--   Proof: the cyclic cubic subfield is `lift (fixedField H)` with
--   `H = comap galToUnits ((powMonoidHom 3).range)` inside `Gal(Q(zeta_r)/Q) ≃ (ZMod r)ˣ`.
--   `finrank Q (lift E) = finrank Q E` (via `IntermediateField.equivMap`), which equals `H.index`
--   (finite-Galois tower + `finrank_fixedField_eq_card` + `card_aut_eq_finrank` + `card_mul_index`),
--   and `H.index = (powMonoidHom 3).range.index = gcd (card (ZMod r)ˣ) 3 = gcd (r-1) 3 = 3`
--   using `Subgroup.index_comap_of_surjective` and `IsCyclic.index_powMonoidHom_range`
--   (with `ZMod.isCyclic_units_prime`).
import Mathlib
import Workspace.Types.CyclotomicCharacterFields

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CyclicCubicSubfieldDegree (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3) = 3 := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom) with hH
  -- Step 1: transfer degree from `cyclicCubicSubfield = lift (fixedField H)` down to `fixedField H`.
  have key : Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3)
      = Module.finrank ℚ ↥(IntermediateField.fixedField H) := by
    have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(cyclicCubicSubfield r hr hr3) :=
      IntermediateField.equivMap (IntermediateField.fixedField H) (cyclotomicField' r).val
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  rw [key]
  -- Step 2: finrank ℚ ↥(fixedField H) = H.index
  have hindex : Module.finrank ℚ ↥(IntermediateField.fixedField H) = H.index := by
    have h1 : Module.finrank ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
        = Nat.card ↥H := IntermediateField.finrank_fixedField_eq_card H
    have h2 : Module.finrank ℚ ↥(IntermediateField.fixedField H)
        * Module.finrank ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
        = Module.finrank ℚ ↥(cyclotomicField' r) :=
      Module.finrank_mul_finrank ℚ ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
    have h3 : Nat.card (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r)
        = Module.finrank ℚ ↥(cyclotomicField' r) :=
      IsGalois.card_aut_eq_finrank ℚ ↥(cyclotomicField' r)
    have h4 : Nat.card ↥H * H.index
        = Nat.card (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) := Subgroup.card_mul_index H
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    have hL : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H
        = Module.finrank ℚ ↥(cyclotomicField' r) := by rw [← h1]; exact h2
    have hR : Nat.card ↥H * H.index = Module.finrank ℚ ↥(cyclotomicField' r) := by
      rw [h4, h3]
    have hcomb : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H
        = H.index * Nat.card ↥H := by
      rw [mul_comm H.index]; exact hL.trans hR.symm
    exact Nat.eq_of_mul_eq_mul_right hpos hcomb
  rw [hindex]
  -- Step 3+4: H.index = (powMonoidHom 3).range.index = gcd (card units) 3 = 3
  haveI : IsCyclic (ZMod (r : ℕ))ˣ := ZMod.isCyclic_units_prime hr
  have hsurj : Function.Surjective (galToUnits r).toMonoidHom := (galToUnits r).surjective
  rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range]
  have h3 : 3 ∣ Nat.card (ZMod (r : ℕ))ˣ := by
    have hc : Nat.card (ZMod (r : ℕ))ˣ = (r : ℕ) - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hr]
    rw [hc]; omega
  rw [Nat.gcd_eq_right h3]
