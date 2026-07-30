import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.SublemmaUnramifiedTransport

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem SublemmaMPrimeRealization (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (F M : IntermediateField ℚ ℂ) [NumberField ↥F] [NumberField ↥M]
    (hFM : F ≤ M) [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M]
    [FiniteDimensional ↥F ↥M] [IsGalois ↥F ↥M]
    (hunr : EverywhereUnramified ↥F ↥M)
    (hiso : Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3)))) :
    ∃ M' : IntermediateField ↥F (AlgebraicClosure ↥F),
      IsFiniteUnramifiedProPExt 3 ↥F M' ∧
      Nonempty ((M' ≃ₐ[↥F] M') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3)) := by
  haveI : Algebra.IsAlgebraic ↥F ↥M := inferInstance
  -- Embed M into AlgebraicClosure F
  let f : ↥M →ₐ[↥F] AlgebraicClosure ↥F := IsAlgClosed.lift
  have hf : Function.Injective f := f.toRingHom.injective
  let M' : IntermediateField ↥F (AlgebraicClosure ↥F) := f.fieldRange
  let e : ↥M ≃ₐ[↥F] ↥M' := AlgEquiv.ofInjective f hf
  -- Transport structure along e
  haveI hfd : FiniteDimensional ↥F ↥M' := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI hst : IsScalarTower ℚ ↥F ↥M' := inferInstance
  haveI hnf : NumberField ↥M' := NumberField.of_module_finite (K := ↥F) (L := ↥M')
  refine ⟨M', ⟨hfd, ?_, ?_, ?_⟩, ?_⟩
  · -- IsGalois
    exact (AlgEquiv.transfer_galois e).mp inferInstance
  · -- EverywhereUnramified, via SublemmaUnramifiedTransport
    exact (SublemmaUnramifiedTransport e).mp hunr
  · -- IsPGroup 3 of the Galois group of M'
    have hp : IsPGroup 3 (Fin (ℓ - 1) → Multiplicative (ZMod 3)) := by
      apply IsPGroup.of_card (n := ℓ - 1)
      simp [Nat.card_eq_fintype_card, Fintype.card_pi]
    have hpM : IsPGroup 3 (↥M ≃ₐ[↥F] ↥M) := hp.of_equiv hiso.some.symm
    exact hpM.of_equiv (AlgEquiv.autCongr e)
  · -- final MulEquiv onto Multiplicative (Fin (ℓ-1) → ZMod 3)
    exact ⟨((AlgEquiv.autCongr e).symm.trans hiso.some).trans
      (MulEquiv.funMultiplicative (Fin (ℓ - 1)) (ZMod 3)).symm⟩
