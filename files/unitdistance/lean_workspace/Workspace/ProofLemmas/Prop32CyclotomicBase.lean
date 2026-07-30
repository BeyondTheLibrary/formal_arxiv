import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.SplittingRamification
import Workspace.Types.UnramifiedProPExtension
import Workspace.ProofLemmas.CyclicCubicSubfieldTotallyReal
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree
import Workspace.ProofLemmas.CyclicCubicSubfieldConductor
import Workspace.ProofLemmas.ConductorMultiplicativeFamily
import Workspace.ProofLemmas.SublemmaCompositumTotallyReal
import Workspace.ProofLemmas.SublemmaCyclicCubicSubfieldNormal
import Workspace.ProofLemmas.SublemmaCompositumGalois
import Workspace.ProofLemmas.SublemmaCutOutFieldDegreeThree
import Workspace.ProofLemmas.SublemmaInfinitePlacesUnramifiedTotallyReal
import Workspace.ProofLemmas.SublemmaLinearDisjointFromDisjointRamification
import Workspace.ProofLemmas.SublemmaDegreeCompositumLinearlyDisjoint
import Workspace.ProofLemmas.SublemmaGaloisGroupCompositumProduct
import Workspace.ProofLemmas.SublemmaTowerDegree
import Workspace.ProofLemmas.CyclotomicTameDiscriminant
import Workspace.ProofLemmas.CompositumRamification
import Workspace.ProofLemmas.SublemmaTotallyRealSubfield
import Workspace.ProofLemmas.SublemmaCubicCharacterOfConductorR
import Workspace.ProofLemmas.SublemmaChangeLevelPreservesConductorAndOrder

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

theorem Prop32CyclotomicBase_totally_real (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M] :
    NumberField.IsTotallyReal ↥M := by
  subst hM
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  haveI hnf : ∀ i, NumberField ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := fun i => ⟨⟩
  haveI htr : ∀ i, NumberField.IsTotallyReal ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => CyclicCubicSubfieldTotallyReal (r i) (hp i) (hm i)
  exact SublemmaCompositumTotallyReal (fun i => cyclicCubicSubfield (r i) (hp i) (hm i))

theorem Prop32CyclotomicBase_degree (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :
    Module.finrank ℚ ↥M = 3 ^ ℓ := by
  subst hM
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  haveI hgi : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => SublemmaCyclicCubicSubfieldNormal (r i) (hp i) (hm i)
  obtain ⟨hindep, hdisj⟩ := SublemmaLinearDisjointFromDisjointRamification hℓ r hp hm hdist
  rw [SublemmaDegreeCompositumLinearlyDisjoint
    (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) hindep hdisj]
  simp only [CyclicCubicSubfieldDegree]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem Prop32CyclotomicBase_galois_elementary_abelian (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :
    (∀ σ τ : ↥M ≃ₐ[ℚ] ↥M, σ * τ = τ * σ) ∧ (∀ σ : ↥M ≃ₐ[ℚ] ↥M, σ ^ 3 = 1) := by
  subst hM
  haveI hgi : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => SublemmaCyclicCubicSubfieldNormal (r i) (hp i) (hm i)
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  obtain ⟨hindep, hdisj⟩ := SublemmaLinearDisjointFromDisjointRamification hℓ r hp hm hdist
  letI algi : ∀ i, Algebra ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => (IntermediateField.inclusion
      (le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i)).toRingHom.toAlgebra
  haveI towi : ∀ i, IsScalarTower ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion
        (le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i)).commutes x).symm)
  obtain ⟨e, -⟩ := SublemmaGaloisGroupCompositumProduct
    (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) hindep hdisj
  have hcard : ∀ i, Nat.card (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) = 3 := by
    intro i
    rw [IsGalois.card_aut_eq_finrank, CyclicCubicSubfieldDegree]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hcyc : ∀ i, IsCyclic (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) :=
    fun i => isCyclic_of_prime_card (hcard i)
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · apply e.injective
    rw [map_mul, map_mul]
    funext i
    simp only [Pi.mul_apply]
    letI : CommGroup (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) := IsCyclic.commGroup
    exact mul_comm _ _
  · apply e.injective
    rw [map_pow, map_one]
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← hcard i]
    exact pow_card_eq_one'

theorem Prop32CyclotomicBase_relative_degree (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M)
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Module.finrank ↥F ↥M = 3 ^ (ℓ - 1) := by
  have hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ :=
    Prop32CyclotomicBase_degree ℓ hℓ r hp hm hdist M hM
  have hFdeg : Module.finrank ℚ ↥F = 3 := by
    rw [hFcut]; exact SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  haveI hfdM : FiniteDimensional ℚ ↥M :=
    FiniteDimensional.of_finrank_pos (by rw [hMdeg]; positivity)
  haveI hfdF : FiniteDimensional ℚ ↥F :=
    FiniteDimensional.of_finrank_pos (by rw [hFdeg]; norm_num)
  haveI : NumberField ↥F := ⟨⟩
  have htower := SublemmaTowerDegree F M hFM
  rw [hMdeg, hFdeg] at htower
  have h3 : (3 : ℕ) ^ (ℓ - 1) * 3 = 3 ^ ℓ := by rw [← pow_succ, Nat.sub_add_cancel hℓ]
  rw [← h3] at htower
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) htower).symm

theorem Prop32CyclotomicBase_discriminant (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (F : IntermediateField ℚ ℂ) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hchi_cond : DirichletCharacter.conductor chi = (D : ℕ))
    (hFcut : F = cutOutField D chi) :
    (NumberField.discr ↥F).natAbs = (∏ i, (r i : ℕ)) ^ 2 := by
  -- Proved from the tame conductor–discriminant computation in
  -- `Workspace.ProofLemmas.CyclotomicTameDiscriminant` (inertia + the conductor of `chi`).
  subst hFcut
  have hsq : Squarefree (D : ℕ) := by
    rw [hD]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun i _ => (hp i).squarefree)
    intro i _ j _ hij
    show IsRelPrime ((r i : ℕ)) ((r j : ℕ))
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hdist (by exact_mod_cast h)))
  have hdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3 :=
    SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  rw [Workspace.ProofLemmas.CyclotomicTameDiscriminant.natAbs_discr_cutOutField D chi hsq
    hchi_cond hdeg, hD]

theorem Prop32CyclotomicBase_unramified (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M]
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hchi_cond : DirichletCharacter.conductor chi = (D : ℕ))
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    EverywhereUnramified ↥F ↥M := by
  subst hM
  subst hFcut
  -- `M/F` is unramified at the finite primes by the inertia computation of
  -- `Workspace.ProofLemmas.CompositumRamification` (`e = 3` at each `r i` both in `M` and in `F`).
  have hDF : (NumberField.discr ↥(cutOutField D chi)).natAbs = (D : ℕ) ^ 2 := by
    rw [Prop32CyclotomicBase_discriminant ℓ hℓ r hp hm hdist (cutOutField D chi) D hD chi
      hchi_ord hchi_cond rfl, hD]
  haveI hgalF : IsGalois ℚ ↥(cutOutField D chi) := SublemmaCutOutFieldGalois D chi
  have hFdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3 :=
    SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  have hMdeg : Module.finrank ℚ ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) = 3 ^ ℓ :=
    Prop32CyclotomicBase_degree ℓ hℓ r hp hm hdist _ rfl
  have hMD : (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) ≤ cyclotomicField' D := by
    refine iSup_le fun i => ?_
    refine (CyclicCubicSubfieldConductor (r i) (hp i) (hm i) D).mpr ?_
    rw [hD]
    exact Finset.dvd_prod_of_mem (fun i => (r i : ℕ)) (Finset.mem_univ i)
  have hfin : UnramifiedAtFinitePrimes ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Workspace.ProofLemmas.CompositumRamification.unramified_compositum ℓ hℓ r hp hm hdist
      _ rfl hMdeg ↥(cutOutField D chi) hFdeg D hD hDF hMD
  have hMtr : NumberField.IsTotallyReal ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Prop32CyclotomicBase_totally_real ℓ hℓ r hp hm hdist _ rfl
  have hFtr : NumberField.IsTotallyReal ↥(cutOutField D chi) :=
    SublemmaTotallyRealSubfield (cutOutField D chi)
      (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) hFM hMtr
  haveI : FiniteDimensional ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Module.Finite.right ℚ ↥(cutOutField D chi) ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
  haveI := hFtr
  haveI := hMtr
  have hinf : IsUnramifiedAtInfinitePlaces ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    SublemmaInfinitePlacesUnramifiedTotallyReal ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
  exact ⟨hfin, hinf⟩
