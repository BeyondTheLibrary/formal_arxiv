import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.ProPGroup
import Workspace.Types.FrobeniusSplitting

/-!
# The maximal everywhere-unramified pro-`p` extension `F^{ur,p}` (Definition A.3)

Working inside a fixed algebraic closure `AlgebraicClosure F` of a number field `F`, we single
out the *defining family* of intermediate fields `E` (`F ≤ E ≤ AlgebraicClosure F`) that are

* finite-dimensional over `F`,
* Galois over `F`,
* everywhere unramified over `F` (`SplittingRamification.EverywhereUnramified`),
* with Galois group `Gal(E/F)` a finite `p`-group (`IsPGroup p`).

`maxUnramifiedProPExt p F` is the compositum (supremum in `IntermediateField F (AlgebraicClosure F)`)
of this family. Its Galois group `galUr p F = Gal(F^{ur,p}/F)` carries the Krull topology
(Mathlib's `krullTopology`, an instance, so `Group` and `TopologicalSpace` fire automatically).

The type also provides the fixed-field construction `fixedFieldOf` (used to extract the finite tower
layers `F_j`), the restriction homomorphisms `restrictTo` to finite Galois subextensions, and the
re-exposed Frobenius-representative predicate `IsFrobeniusRepAt` (via `FrobeniusSplitting`, applied
to `Ω = F^{ur,p}`).

That `galUr p F` is pro-`p`, and that its open-normal quotients correspond to the finite
everywhere-unramified `p`-group extensions, are *theorem statements* to be formalized elsewhere;
this file contains definitions only.
-/

set_option maxHeartbeats 400000

open scoped NumberField

namespace Workspace.Types.UnramifiedProPExtension

variable (p : ℕ) (F : Type*) [Field F] [NumberField F]

/-- The defining property of the family: an intermediate field `E` of `AlgebraicClosure F` over `F`
is a **finite Galois everywhere-unramified `p`-group subextension** when it is finite-dimensional
over `F`, Galois over `F`, everywhere unramified over `F`, and has `Gal(E/F)` a `p`-group.

The `NumberField ↥E` instance needed to state everywhere-unramifiedness is derived from finite
dimensionality of `E` over the number field `F`. -/
def IsFiniteUnramifiedProPExt (E : IntermediateField F (AlgebraicClosure F)) : Prop :=
  ∃ hfd : FiniteDimensional F E,
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    IsGalois F E ∧
      Workspace.Types.SplittingRamification.EverywhereUnramified F (E : Type _) ∧
        IsPGroup p (E ≃ₐ[F] E)

/-- The **maximal everywhere-unramified pro-`p` extension** `F^{ur,p}` of `F`: the compositum
(supremum) of all finite Galois everywhere-unramified `p`-group subextensions of
`AlgebraicClosure F` over `F`. -/
noncomputable def maxUnramifiedProPExt : IntermediateField F (AlgebraicClosure F) :=
  sSup {E | IsFiniteUnramifiedProPExt p F E}

/-- The **Galois group** `Gal(F^{ur,p}/F)` of the maximal everywhere-unramified pro-`p` extension.
As an `abbrev` it inherits the `Group` instance (`AlgEquiv.aut`) and the Krull `TopologicalSpace`
instance (`krullTopology`), together with whatever profinite instances Mathlib provides for the
Krull topology on algebraic Galois groups. -/
noncomputable abbrev galUr : Type _ :=
  (maxUnramifiedProPExt p F) ≃ₐ[F] (maxUnramifiedProPExt p F)

/-- The **fixed field** of a subgroup `H` of `galUr p F`, as an intermediate field of `F^{ur,p}/F`.
For an open normal subgroup this is a finite layer `F_H` of the tower, finite Galois over `F`. -/
noncomputable def fixedFieldOf (H : Subgroup (galUr p F)) :
    IntermediateField F (maxUnramifiedProPExt p F) :=
  IntermediateField.fixedField H

/-- A finite prime `q` of `F` has a **Frobenius representative** `σ` in `galUr p F` when `σ` is a
Frobenius representative for the extension `Ω = F^{ur,p}` at `q`, i.e. a compatible system of
Frobenii restricting to a Frobenius element on every finite Galois layer. -/
def IsFrobeniusRepAt (σ : galUr p F) (q : Ideal (𝓞 F)) : Prop :=
  Workspace.Types.FrobeniusSplitting.IsFrobeniusRepAt σ q

end Workspace.Types.UnramifiedProPExtension
