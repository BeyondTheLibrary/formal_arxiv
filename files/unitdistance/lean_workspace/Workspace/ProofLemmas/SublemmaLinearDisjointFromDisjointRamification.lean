import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.CyclicCubicSubfieldConductor
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree

set_option maxHeartbeats 1000000

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaLinearDisjointFromDisjointRamification {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → ℕ+) (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1)
    (hinj : Function.Injective r) :
    iSupIndep (fun i => (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra) ∧
      ∀ i, cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
          (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)) = ⊥ := by
  classical
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  have hdeg : ∀ i, Module.finrank ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) = 3 :=
    fun i => CyclicCubicSubfieldDegree (r i) (hp i) (hm i)
  -- CORE: each L i meets the compositum of the others trivially.
  have hbot : ∀ i, cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
      (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)) = ⊥ := by
    intro i
    set X := ⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j) with hXdef
    set N : ℕ+ := ∏ j ∈ Finset.univ.erase i, r j with hNdef
    have hNcoe : (N : ℕ) = ∏ j ∈ Finset.univ.erase i, (r j : ℕ) := by
      rw [hNdef]; exact Finset.PNat.coe_prod r (Finset.univ.erase i)
    -- the compositum of the L j (j ≠ i) sits inside ℚ(ζ_N).
    have hXle : X ≤ cyclotomicField' N := by
      rw [hXdef]
      refine iSup_le (fun j => iSup_le (fun hji => ?_))
      refine (CyclicCubicSubfieldConductor (r j) (hp j) (hm j) N).mpr ?_
      rw [hNcoe]
      exact Finset.dvd_prod_of_mem (fun j => (r j : ℕ))
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    -- degree of the intersection divides [L i : ℚ] = 3, so is 1 or 3.
    letI : Algebra ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X)
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
      (IntermediateField.inclusion inf_le_left).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X)
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
      IsScalarTower.of_algebraMap_eq (fun x =>
        ((IntermediateField.inclusion
          (inf_le_left : cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X ≤ _)).commutes x).symm)
    have htower := Module.finrank_mul_finrank ℚ
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X) ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
    rw [hdeg i] at htower
    have hdvd3 : Module.finrank ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X) ∣ 3 :=
      ⟨_, htower.symm⟩
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd3 with h1 | h3
    · exact IntermediateField.finrank_eq_one_iff.mp h1
    · exfalso
      have heq : cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X
          = cyclicCubicSubfield (r i) (hp i) (hm i) :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (by rw [h3, hdeg i])
      have hLiX : cyclicCubicSubfield (r i) (hp i) (hm i) ≤ X := heq ▸ inf_le_right
      have hri : (r i : ℕ) ∣ (N : ℕ) :=
        (CyclicCubicSubfieldConductor (r i) (hp i) (hm i) N).mp (le_trans hLiX hXle)
      rw [hNcoe] at hri
      obtain ⟨j, hjmem, hrij⟩ := (hp i).prime.exists_mem_finset_dvd hri
      have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
      have hrieq : (r i : ℕ) = (r j : ℕ) := (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hrij
      exact hji (hinj (PNat.coe_injective hrieq)).symm
  refine ⟨?_, hbot⟩
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra)
      ≤ (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra := by
    refine iSup_le (fun j => iSup_le (fun hji => ?_))
    exact IntermediateField.toSubalgebra_le_toSubalgebra.mpr
      (le_iSup_of_le j (le_iSup_of_le hji le_rfl))
  refine le_antisymm ?_ bot_le
  calc (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra ⊓
        (⨆ j, ⨆ (_ : j ≠ i), (cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra)
      ≤ (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra ⊓
        (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra :=
        inf_le_inf_left _ hle
    _ = (cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
        (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j))).toSubalgebra :=
        (IntermediateField.inf_toSubalgebra _ _).symm
    _ = (⊥ : IntermediateField ℚ ℂ).toSubalgebra := by rw [hbot i]
    _ = ⊥ := IntermediateField.bot_toSubalgebra
