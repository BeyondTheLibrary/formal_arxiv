-- Cited from: Def A.11(i) / Washington, Introduction to Cyclotomic Fields, Ch.3, Thm 3.11: for a prime r ≡ 1 (mod 3), the field cut out by an order-3 Dirichlet character of conductor r equals THE unique cyclic cubic subfield of ℚ(ζ_r).
-- Both fields are the fixed field (lifted to ℂ) of an
-- index-3 subgroup of Gal(ℚ(ζ_r)/ℚ) ≃ (ℤ/rℤ)ˣ; via `galToUnits` the problem reduces to a
-- subgroup identity in the finite cyclic group (ℤ/rℤ)ˣ (order r-1, divisible by 3):
--   ker(ψ.toUnitHom) = range(x ↦ x^3).
-- The cubes are contained in the kernel (ψ has order 3), and both subgroups have index 3
-- (`Subgroup.index_ker` + `DirichletCharacterRangeCardEqOrder`, resp.
-- `IsCyclic.index_powMonoidHom_range`), hence equal cardinality, hence equal.
import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.DirichletCharacterRangeCardEqOrder

open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CutOutFieldEqCyclicCubic
    (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : orderOf ψ = 3) :
    cutOutField r ψ = cyclicCubicSubfield r hr hr3 := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  have hcardU : Nat.card (ZMod (r : ℕ))ˣ = (r : ℕ) - 1 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units (r : ℕ)
  have hdvd : 3 ∣ Nat.card (ZMod (r : ℕ))ˣ := by
    rw [hcardU]; have hr2 : 2 ≤ (r : ℕ) := hr.two_le; omega
  have hQindex :
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range.index = 3 := by
    rw [IsCyclic.index_powMonoidHom_range (ZMod (r : ℕ))ˣ 3, Nat.gcd_eq_right hdvd]
  have hfindex : ψ.toUnitHom.ker.index = 3 := by
    rw [Subgroup.index_ker, DirichletCharacterRangeCardEqOrder ψ, hψ]
  have hf3 : ψ.toUnitHom ^ 3 = 1 := by
    have hbridge : ψ.toUnitHom = MulChar.mulEquivToUnitHom ψ := by
      rw [MulChar.toUnitHom_eq, MulChar.mulEquivToUnitHom_apply]
    rw [hbridge, ← map_pow]
    have hp : ψ ^ 3 = 1 := by rw [← hψ]; exact pow_orderOf_eq_one ψ
    rw [hp, map_one]
  have hle :
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range ≤ ψ.toUnitHom.ker := by
    rintro _ ⟨x, rfl⟩
    simp only [MonoidHom.mem_ker]
    rw [powMonoidHom_apply, map_pow, ← MonoidHom.pow_apply, hf3, MonoidHom.one_apply]
  have hcardeq :
      Nat.card ψ.toUnitHom.ker ≤
        Nat.card (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range := by
    have hcQ := Subgroup.card_mul_index
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    have hcK := Subgroup.card_mul_index ψ.toUnitHom.ker
    rw [hQindex] at hcQ
    rw [hfindex] at hcK
    omega
  have hcore :
      ψ.toUnitHom.ker = (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range :=
    (Subgroup.eq_of_le_of_card_ge hle hcardeq).symm
  have hsub : (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker
      = ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
          (galToUnits r).toMonoidHom := by
    rw [← MonoidHom.comap_ker, hcore]
  exact congrArg (fun H => IntermediateField.lift (IntermediateField.fixedField H)) hsub
