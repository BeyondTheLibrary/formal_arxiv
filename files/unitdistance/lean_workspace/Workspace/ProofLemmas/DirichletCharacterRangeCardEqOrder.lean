import Mathlib

set_option maxHeartbeats 800000

theorem DirichletCharacterRangeCardEqOrder {N : ℕ} (chi : DirichletCharacter ℂ N) :
    Nat.card ↥(chi.toUnitHom.range) = orderOf chi := by
  set f := chi.toUnitHom with hf
  -- `f` corresponds to `chi` under the multiplicative equiv `mulEquivToUnitHom`
  have hfm : f = MulChar.mulEquivToUnitHom chi := by
    rw [hf, MulChar.toUnitHom_eq, MulChar.mulEquivToUnitHom_apply]
  have hbridge : ∀ k, f ^ k = 1 ↔ chi ^ k = 1 := by
    intro k
    rw [hfm, ← map_pow]
    constructor
    · intro h
      have : MulChar.mulEquivToUnitHom (chi ^ k) = MulChar.mulEquivToUnitHom 1 := by
        rw [map_one]; exact h
      exact MulChar.mulEquivToUnitHom.injective this
    · intro h; rw [h, map_one]
  have horder : orderOf f = orderOf chi := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hbridge (orderOf chi)).mpr (pow_orderOf_eq_one chi))
    · exact orderOf_dvd_of_pow_eq_one ((hbridge (orderOf f)).mp (pow_orderOf_eq_one f))
  rw [← horder]
  -- `Nat.card (range) = orderOf f`, via exponent of the cyclic image
  haveI : Finite ↥(f.range) :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective f)
  haveI : IsCyclic ↥(f.range) := inferInstance
  have hcard : Nat.card ↥(f.range) = Monoid.exponent ↥(f.range) :=
    IsCyclic.exponent_eq_card.symm
  rw [hcard]
  apply Nat.dvd_antisymm
  · -- exponent of the range divides orderOf f
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, u, rfl⟩
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← MonoidHom.pow_apply f (orderOf f) u, pow_orderOf_eq_one, MonoidHom.one_apply]
  · -- orderOf f divides the exponent of the range
    apply orderOf_dvd_of_pow_eq_one
    apply MonoidHom.ext
    intro u
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have hmem : f u ∈ f.range := ⟨u, rfl⟩
    have h := Monoid.pow_exponent_eq_one (⟨f u, hmem⟩ : ↥(f.range))
    have h2 : ((⟨f u, hmem⟩ : ↥(f.range)) : ℂˣ) ^ Monoid.exponent ↥(f.range) = 1 := by
      rw [← SubmonoidClass.coe_pow, h, OneMemClass.coe_one]
    exact h2
