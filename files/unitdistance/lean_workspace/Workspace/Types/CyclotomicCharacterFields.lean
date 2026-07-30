import Mathlib

/-!
# Cyclotomic fields, Dirichlet characters and cut-out fields

Concrete model (inside `ℂ`) of cyclotomic fields together with the canonical
Galois-to-units isomorphism, the subfield cut out by a Dirichlet character, the
cyclic cubic subfield of `ℚ(ζ_r)` for `r ≡ 1 (mod 3)`, and the character group
of an abelian subfield of `ℂ`.

All the number fields are realised as `IntermediateField ℚ ℂ`, so that composita
of the fields for different moduli make sense inside the fixed ambient field `ℂ`.
-/

open Complex IsCyclotomicExtension

namespace Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 400000

/-- For `m : ℕ+`, the natural-number underlying value is nonzero. -/
instance instNeZeroPNatVal (m : ℕ+) : NeZero (m : ℕ) := ⟨m.pos.ne'⟩

/-- The chosen primitive `m`-th root of unity `exp (2πi/m)` inside `ℂ`. -/
noncomputable def zetaC (m : ℕ+) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / (m : ℕ))

/-- `zetaC m` is a primitive `m`-th root of unity. -/
theorem isPrimitiveRoot_zetaC (m : ℕ+) : IsPrimitiveRoot (zetaC m) (m : ℕ) :=
  Complex.isPrimitiveRoot_exp (m : ℕ) m.pos.ne'

/-- The `m`-th cyclotomic field, realised concretely as the subfield of `ℂ`
generated over `ℚ` by the primitive root of unity `zetaC m = exp (2πi/m)`. -/
noncomputable def cyclotomicField' (m : ℕ+) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {zetaC m}

/-- `cyclotomicField' m` really is an `m`-th cyclotomic extension of `ℚ`. -/
noncomputable instance instIsCyclotomic (m : ℕ+) :
    IsCyclotomicExtension {(m : ℕ)} ℚ (cyclotomicField' m) := by
  have hζ : IsPrimitiveRoot (zetaC m) (m : ℕ) := isPrimitiveRoot_zetaC m
  have halg : IsAlgebraic ℚ (zetaC m) := ((hζ.isIntegral m.pos).tower_top).isAlgebraic
  change IsCyclotomicExtension {(m : ℕ)} ℚ (cyclotomicField' m).toSubalgebra
  rw [cyclotomicField', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

/-- `cyclotomicField' m` is a number field. -/
noncomputable instance instNumberField (m : ℕ+) :
    NumberField (cyclotomicField' m) :=
  IsCyclotomicExtension.numberField {(m : ℕ)} ℚ (cyclotomicField' m)

/-- `cyclotomicField' m / ℚ` is Galois. -/
noncomputable instance instIsGalois (m : ℕ+) :
    IsGalois ℚ (cyclotomicField' m) :=
  IsCyclotomicExtension.isGalois {(m : ℕ)} ℚ (cyclotomicField' m)

/-- The canonical isomorphism `Gal(ℚ(ζ_m)/ℚ) ≃* (ℤ/mℤ)ˣ` sending `σ` to the class
`a` such that `σ ζ = ζ ^ a`. -/
noncomputable def galToUnits (m : ℕ+) :
    (cyclotomicField' m ≃ₐ[ℚ] cyclotomicField' m) ≃* (ZMod (m : ℕ))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod (m : ℕ) (cyclotomicField' m)

/-- The subfield of `ℂ` cut out by a Dirichlet character `χ` of modulus `m`: the
fixed field of the kernel of the composite
`Gal(ℚ(ζ_m)/ℚ) ≃ (ℤ/mℤ)ˣ --χ--> ℂˣ`. -/
noncomputable def cutOutField (m : ℕ+) (chi : DirichletCharacter ℂ (m : ℕ)) :
    IntermediateField ℚ ℂ :=
  IntermediateField.lift
    (IntermediateField.fixedField
      ((chi.toUnitHom.comp (galToUnits m).toMonoidHom).ker))

/-- The unique cyclic cubic subfield of `ℚ(ζ_r)` for a prime `r ≡ 1 (mod 3)`,
defined as the fixed field of the unique index-`3` subgroup of
`Gal(ℚ(ζ_r)/ℚ) ≃ (ℤ/rℤ)ˣ`, namely the subgroup of cubes (its preimage under
`galToUnits`). -/
noncomputable def cyclicCubicSubfield (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) : IntermediateField ℚ ℂ :=
  IntermediateField.lift
    (IntermediateField.fixedField
      (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
        (galToUnits r).toMonoidHom))

end Workspace.Types.CyclotomicCharacterFields
