import Mathlib

open scoped NumberField
open Polynomial

set_option maxHeartbeats 800000

/-- **Normal closure over ℚ of `E(i)`.** Given a finite Galois extension `E/F` of number fields
with `[Algebra ℚ E]` and `[IsScalarTower ℚ F E]`, adjoining a root `i` of `X² + 1` and taking the
normal closure over `ℚ` yields a number field `N` such that:
* `N` is finite Galois over `ℚ` (`IsGalois ℚ N`, `NumberField N`);
* `N` contains a copy of `E` (hence of `F`): `[Algebra E N]` with `[IsScalarTower ℚ E N]`;
* `N` contains a copy of `ℚ(i)`: `∃ x : N, x ^ 2 = -1`.

Because `E`, `F`, and `ℚ(i)` are realised as genuine subfields of the single object `N`, every
splitting statement in the descent is computed for the same objects appearing in the goal. -/
theorem SublemmaFieldNormalClosure
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [Algebra ℚ E] [IsScalarTower ℚ F E] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : IsGalois ℚ N)
      (_ : Algebra E N) (_ : IsScalarTower ℚ E N),
      ∃ x : N, x ^ 2 = -1 := by
  -- Ambient algebraic closure of ℚ, which is Galois over ℚ.
  haveI hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGal : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  -- Realise `E` as a subfield of the algebraic closure.
  let φ : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  -- A square root `i` of `-1`.
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  have hiint : IsIntegral ℚ i := ⟨X ^ 2 + 1, by monicity!, by simp [hi]⟩
  -- `M = E(i)` as an intermediate field, finite over ℚ.
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := φ.fieldRange ⊔ IntermediateField.adjoin ℚ {i}
  have hEfin : FiniteDimensional ℚ ↥(φ.fieldRange) :=
    (AlgEquiv.ofInjective φ hφinj).toLinearEquiv.finiteDimensional
  have hifin : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {i}) :=
    IntermediateField.adjoin.finiteDimensional hiint
  haveI : FiniteDimensional ℚ ↥M := IntermediateField.finiteDimensional_sup _ _
  -- The normal closure `N` of `M` over ℚ: finite Galois number field.
  set N := IntermediateField.normalClosure ℚ (↥M) (AlgebraicClosure ℚ) with hN
  haveI hNGal : IsGalois ℚ ↥N := IsGalois.normalClosure ℚ (↥M) (AlgebraicClosure ℚ)
  haveI hNfin : FiniteDimensional ℚ ↥N := inferInstance
  haveI hNF : NumberField ↥N := NumberField.of_module_finite ℚ _
  -- `M ≤ N`, so `E`'s image and `i` both lie in `N`.
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  have hrangeN : φ.fieldRange ≤ N := le_trans le_sup_left hMN
  -- Bundle `Algebra E N` from the embedding `E ≃ φ(E) ⊆ N`.
  let e : E ≃ₐ[ℚ] ↥(φ.fieldRange) := AlgEquiv.ofInjective φ hφinj
  let ψ : E →ₐ[ℚ] ↥N := (IntermediateField.inclusion hrangeN).comp e.toAlgHom
  letI algEN : Algebra E ↥N := ψ.toRingHom.toAlgebra
  haveI hst : IsScalarTower ℚ E ↥N :=
    IsScalarTower.of_algebraMap_eq (fun q => (ψ.commutes q).symm)
  -- `i ∈ N`.
  have hiM : i ∈ M := by
    have hle : IntermediateField.adjoin ℚ {i} ≤ M := le_sup_right
    exact hle (IntermediateField.mem_adjoin_simple_self ℚ i)
  have hiN : i ∈ N := hMN hiM
  refine ⟨↥N, inferInstance, hNF, hNGal, algEN, hst, ⟨i, hiN⟩, ?_⟩
  apply Subtype.ext
  push_cast
  simpa using hi
