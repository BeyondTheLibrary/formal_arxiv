import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.Types.SplittingRamification
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.SublemmaFirstEllPrimes
import Workspace.ProofLemmas.SublemmaCubicCharacterOfConductorR
import Workspace.ProofLemmas.SublemmaChangeLevelPreservesConductorAndOrder
import Workspace.ProofLemmas.SublemmaCharacterProductOrderConductor
import Workspace.ProofLemmas.SublemmaCutOutFieldCubicChar
import Workspace.ProofLemmas.SublemmaFsubsetM
import Workspace.ProofLemmas.SublemmaTotallyRealSubfield
import Workspace.ProofLemmas.SublemmaCutOutFieldGalois
import Workspace.ProofLemmas.SublemmaNoZeta3
import Workspace.ProofLemmas.SublemmaGalMFElementaryAbelianIso
import Workspace.ProofLemmas.SublemmaMPrimeRealization
import Workspace.ProofLemmas.Prop32CyclotomicBase
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000

theorem Prop38BaseFieldConstruction :
    ∀ (ℓ : ℕ), 2 ≤ ℓ →
      ∃ (r : Fin ℓ → ℕ+),
        StrictMono r ∧
        ∃ (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1),
          (∀ p : ℕ, p.Prime → p % 3 = 1 → (¬ ∃ i, (r i : ℕ) = p) → ∀ i, (r i : ℕ) < p) ∧
          ∃ (D : ℕ+), (D : ℕ) = ∏ i, (r i : ℕ) ∧
            ∃ (chi : DirichletCharacter ℂ (D : ℕ)),
              orderOf chi = 3 ∧
              DirichletCharacter.conductor chi = (D : ℕ) ∧
              ∃ (F M : IntermediateField ℚ ℂ),
                F = cutOutField D chi ∧
                M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) ∧
                F ≤ M ∧
                ∃ (nfF : NumberField ↥F) (nfM : NumberField ↥M) (algFM : Algebra ↥F ↥M),
                  letI := nfF
                  letI := nfM
                  letI := algFM
                  IsScalarTower ℚ ↥F ↥M ∧
                  NumberField.IsTotallyReal ↥F ∧
                  IsGalois ℚ ↥F ∧
                  Module.finrank ℚ ↥F = 3 ∧
                  (¬ ∃ x : ↥F, IsPrimitiveRoot x 3) ∧
                  EverywhereUnramified ↥F ↥M ∧
                  Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) ∧
                  (NumberField.discr ↥F).natAbs = (D : ℕ) ^ 2 ∧
                  ∃ (M' : IntermediateField ↥F (AlgebraicClosure ↥F)),
                    IsFiniteUnramifiedProPExt 3 ↥F M' ∧
                    Nonempty ((M' ≃ₐ[↥F] M') ≃*
                      Multiplicative (Fin (ℓ - 1) → ZMod 3)) := by
  intro ℓ hℓ
  -- Step 1: primes and modulus D
  obtain ⟨r, hmono, hp, hm, hmin⟩ := SublemmaFirstEllPrimes ℓ
  have hdist : Function.Injective r := hmono.injective
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (r i : ℕ) (r j : ℕ) := by
    intro i j hij
    have hne : (r i : ℕ) ≠ (r j : ℕ) := fun h => hij (hdist (PNat.coe_injective h))
    exact (Nat.coprime_primes (hp i) (hp j)).mpr hne
  set D : ℕ+ := ∏ i, r i with hDdef
  have hDcoe : (D : ℕ) = ∏ i, (r i : ℕ) := by rw [hDdef]; push_cast; rfl
  have hD1 : 1 < (D : ℕ) := by
    rw [hDcoe]
    have hi0 : (r (⟨0, by omega⟩ : Fin ℓ) : ℕ) ∣ ∏ i, (r i : ℕ) :=
      Finset.dvd_prod_of_mem (fun i => (r i : ℕ)) (Finset.mem_univ (⟨0, by omega⟩ : Fin ℓ))
    have hpos : 0 < ∏ i, (r i : ℕ) := Finset.prod_pos (fun i _ => (hp i).pos)
    have hle := Nat.le_of_dvd hpos hi0
    have := (hp (⟨0, by omega⟩ : Fin ℓ)).one_lt
    omega
  have hrd : ∀ i, (r i : ℕ) ∣ (D : ℕ) := by
    intro i; rw [hDcoe]; exact Finset.dvd_prod_of_mem (fun j => (r j : ℕ)) (Finset.mem_univ i)
  -- Step 2: characters
  have hψexists : ∀ i, ∃ ψ : DirichletCharacter ℂ (r i : ℕ),
      orderOf ψ = 3 ∧ DirichletCharacter.conductor ψ = (r i : ℕ) :=
    fun i => SublemmaCubicCharacterOfConductorR (r i) (hp i) (hm i)
  choose ψ hψord hψcond using hψexists
  set χ : Fin ℓ → DirichletCharacter ℂ (D : ℕ) :=
    fun i => DirichletCharacter.changeLevel (hrd i) (ψ i) with hχdef
  have hχcond : ∀ i, DirichletCharacter.conductor (χ i) = (r i : ℕ) := by
    intro i
    have h := (SublemmaChangeLevelPreservesConductorAndOrder (D := (D : ℕ)) (ψ i) (hrd i)).1
    rw [hχdef]
    exact h.trans (hψcond i)
  have hχord : ∀ i, orderOf (χ i) = 3 := by
    intro i
    have h := (SublemmaChangeLevelPreservesConductorAndOrder (D := (D : ℕ)) (ψ i) (hrd i)).2
    rw [hχdef]
    exact h.trans (hψord i)
  obtain ⟨hchicond, hchiord⟩ :=
    SublemmaCharacterProductOrderConductor ℓ (D : ℕ) r χ hcop hχcond hχord hDcoe hD1
  -- Step 3: fields and instances
  refine ⟨r, hmono, hp, hm, hmin, D, hDcoe, ∏ i, χ i, hchiord, hchicond, ?_⟩
  set M : IntermediateField ℚ ℂ := ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) with hMdef
  set F : IntermediateField ℚ ℂ := cutOutField D (∏ i, χ i) with hFdef
  -- NumberField ↥M
  haveI hFinEach : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
    intro i
    apply FiniteDimensional.of_finrank_pos
    rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num
  haveI hMfin : FiniteDimensional ℚ ↥M := by
    rw [hMdef]; exact IntermediateField.finiteDimensional_iSup_of_finite
  letI nfM : NumberField ↥M := NumberField.of_module_finite ℚ ↥M
  -- F ≤ M
  have hFM : F ≤ M := by
    rw [hFdef, hMdef]
    exact SublemmaFsubsetM ℓ r D hp hm hrd ψ hψord χ (fun i => by rw [hχdef]) (∏ i, χ i) rfl
  -- NumberField ↥F
  haveI hFfin : FiniteDimensional ℚ ↥F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFM).toLinearMap
      (IntermediateField.inclusion_injective hFM)
  letI nfF : NumberField ↥F := NumberField.of_module_finite ℚ ↥F
  -- Algebra ↥F ↥M and scalar tower
  letI algFM : Algebra ↥F ↥M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  haveI htower : IsScalarTower ℚ ↥F ↥M := by
    apply IsScalarTower.of_algebraMap_eq; intro x; apply Subtype.ext; rfl
  -- M/ℚ Galois (each summand Galois, finite compositum)
  have hLgal : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
    intro i
    rw [← SublemmaCutOutFieldCubicChar (r i) (hp i) (hm i) (ψ i) (hψord i)]
    exact SublemmaCutOutFieldGalois (r i) (ψ i)
  haveI hMgal : IsGalois ℚ ↥M := by
    rw [hMdef]
    have hgal_finset : ∀ s : Finset (Fin ℓ),
        IsGalois ℚ ↥(⨆ i ∈ s, cyclicCubicSubfield (r i) (hp i) (hm i)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          rw [show (⨆ i ∈ (∅ : Finset (Fin ℓ)), cyclicCubicSubfield (r i) (hp i) (hm i)) = ⊥
              from by simp]
          exact isGalois_bot
      | insert a s hnm ihg =>
          rw [Finset.iSup_insert]
          exact @FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax
            ℚ ℂ _ _ _
            (cyclicCubicSubfield (r a) (hp a) (hm a))
            (⨆ i ∈ s, cyclicCubicSubfield (r i) (hp i) (hm i))
            (hLgal a) ihg
    have heq : (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
        = ⨆ i ∈ (Finset.univ : Finset (Fin ℓ)), cyclicCubicSubfield (r i) (hp i) (hm i) := by
      simp
    rw [heq]; exact hgal_finset Finset.univ
  -- Relative finite dimensionality and relative Galois
  haveI hFMfin : FiniteDimensional ↥F ↥M := FiniteDimensional.right ℚ ↥F ↥M
  haveI hFMgal : IsGalois ↥F ↥M := IsGalois.tower_top_of_isGalois ℚ ↥F ↥M
  -- Base-field properties
  have hMtr : NumberField.IsTotallyReal ↥M :=
    Prop32CyclotomicBase_totally_real ℓ (by omega) r hp hm hdist M hMdef
  have hFtr : NumberField.IsTotallyReal ↥F := SublemmaTotallyRealSubfield F M hFM hMtr
  have hFgal : IsGalois ℚ ↥F := by
    rw [hFdef]; exact SublemmaCutOutFieldGalois D (∏ i, χ i)
  have hFdeg : Module.finrank ℚ ↥F = 3 := by
    have hMdeg := Prop32CyclotomicBase_degree ℓ (by omega) r hp hm hdist M hMdef
    have hrel := Prop32CyclotomicBase_relative_degree ℓ (by omega) r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hFdef
    have hmul := Module.finrank_mul_finrank ℚ ↥F ↥M
    rw [hrel, hMdeg] at hmul
    have h3 : (3 : ℕ) ^ ℓ = 3 * 3 ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h3] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
  have hunr : EverywhereUnramified ↥F ↥M :=
    Prop32CyclotomicBase_unramified ℓ (by omega) r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hchicond hFdef
  have hiso : Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) :=
    SublemmaGalMFElementaryAbelianIso ℓ hℓ r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hFdef
  have hdisc : (NumberField.discr ↥F).natAbs = (D : ℕ) ^ 2 := by
    have h := Prop32CyclotomicBase_discriminant ℓ (by omega) r hp hm hdist F
      D hDcoe (∏ i, χ i) hchiord hchicond hFdef
    rw [hDcoe]; exact h
  have hmprime := SublemmaMPrimeRealization ℓ hℓ F M hFM hunr hiso
  exact ⟨F, M, rfl, rfl, hFM, nfF, nfM, algFM, htower, hFtr, hFgal, hFdeg,
    SublemmaNoZeta3 F hFtr, hunr, hiso, hdisc, hmprime⟩
