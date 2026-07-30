import Mathlib
import Workspace.Types.UnramifiedProPExtension

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension

/-- **SublemmaFixedFieldKernel** (infinite Galois correspondence, kernel form).

Let `G = galUr 3 F` be the Galois group of the maximal everywhere-unramified pro-`3`
extension of the number field `F`, and let `H : Subgroup G` be open and normal.  Put
`E := fixedFieldOf 3 F H`.  Then the kernel of the restriction homomorphism
`AlgEquiv.restrictNormalHom ↥E : G →* (↥E ≃ₐ[F] ↥E)` is exactly `H`.

Equivalently, for every `σ : G`, `σ ∈ H ↔ restrictNormalHom ↥E σ = 1`; in particular
`σ ∈ H → restrictNormalHom ↥E σ = 1`.

The `[Normal F ↥E]` instance is what makes `restrictNormalHom ↥E` available; it is the
Lean-level manifestation of `H` being normal (the fixed field of a normal subgroup is a
normal subextension). -/
theorem SublemmaFixedFieldKernel
    (F : Type*) [Field F] [NumberField F]
    (H : Subgroup (galUr 3 F))
    (hopen : IsOpen (H : Set (galUr 3 F)))
    (hnormal : H.Normal)
    [Normal F (fixedFieldOf 3 F H : Type _)] :
    MonoidHom.ker (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F H : Type _)) = H := by
  -- The ambient extension `F^{ur,3}/F` is Galois: it is the supremum of finite Galois
  -- (everywhere-unramified `3`-group) subextensions, hence normal; separability is
  -- automatic in characteristic zero.
  haveI hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    have hn : ∀ i : {E // E ∈ {E | IsFiniteUnramifiedProPExt 3 F E}},
        Normal F ↥(i : IntermediateField F (AlgebraicClosure F)) := by
      rintro ⟨E, hE⟩
      obtain ⟨hfd, hgal, _, _⟩ := hE
      letI := hfd
      letI : NumberField (E : Type _) :=
        NumberField.of_module_finite (K := F) (L := (E : Type _))
      exact hgal.to_normal
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    exact IntermediateField.normal_iSup F (AlgebraicClosure F) (h := hn)
  haveI : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  -- Fundamental theorem of infinite Galois theory, kernel form:
  -- `(restrictNormalHom E).ker = E.fixingSubgroup`.
  rw [IntermediateField.restrictNormalHom_ker]
  -- `H` is open, hence closed; the Krull-topology Galois correspondence gives
  -- `fixingSubgroup (fixedField H) = H` for the closed subgroup `H`.
  let H' : ClosedSubgroup (galUr 3 F) := ⟨H, Subgroup.isClosed_of_isOpen H hopen⟩
  have hcorr := InfiniteGalois.fixingSubgroup_fixedField H'
  simpa [fixedFieldOf, H'] using hcorr
