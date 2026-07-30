import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.FrobeniusSplitting
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.SublemmaSplitInQiModFour
import Workspace.ProofLemmas.SublemmaSplitCompletelyFrobTrivial
import Workspace.ProofLemmas.SublemmaCompleteSplittingDescends
import Workspace.ProofLemmas.SublemmaFieldNormalClosure
import Workspace.ProofLemmas.SublemmaFrattiniQuotientField
import Workspace.ProofLemmas.SublemmaFrobRepExists
import Workspace.ProofLemmas.GalUrIsProP
import Workspace.ProofLemmas.ChebotarevManySplitPrimes
import Workspace.ProofLemmas.GalUrOpenNormalThreePowerIndex
import Workspace.ProofLemmas.ProPBurnsideBasis
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence
import Workspace.ProofLemmas.SublemmaSplittingTransitive
import Workspace.ProofLemmas.SublemmaTrivialFrobSplits

open scoped NumberField
open Polynomial
open Workspace.Types.SplittingRamification
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem Prop36ChebotarevApplication
    (F : Type) [Field F] [NumberField F]
    (hfg : TopFinitelyGenerated (galUr 3 F))
    (t : ℕ) (ht : 0 < t) (T : Finset ℕ) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧
      (∀ b, (q b).Prime ∧ q b ∉ T) ∧
      ∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) F ∧
        ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
          ∃ σ : galUr 3 F,
            Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 F σ v ∧
              σ ∈ frattiniOpen (galUr 3 F) := by
  classical
  -- Step 0: pro-3 structure of G = galUr 3 F
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  -- Step 1: Frattini quotient extension E := fixedFieldOf 3 F Φ
  obtain ⟨hΦopen, hΦnormal, ⟨kk, hkindex⟩, hEfd, hEgal, hker⟩ :=
    SublemmaFrattiniQuotientField F hpro hfg
  haveI hEfd' := hEfd
  haveI hEgal' := hEgal
  haveI hnfE : NumberField (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) :=
    NumberField.of_module_finite (K := F)
      (L := (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _))
  -- Step 2: N = normal closure of E(i) over ℚ.  Peel the instance telescope one
  -- existential at a time, registering each instance before elaborating the next.
  have hNC := SublemmaFieldNormalClosure F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _)
  obtain ⟨Nn, hNC⟩ := hNC
  obtain ⟨fN, hNC⟩ := hNC; letI := fN
  obtain ⟨nfN, hNC⟩ := hNC; letI := nfN
  obtain ⟨galQN, hNC⟩ := hNC; letI := galQN
  obtain ⟨algEN, hNC⟩ := hNC; letI := algEN
  obtain ⟨twQEN, hNC⟩ := hNC; letI := twQEN
  obtain ⟨ii, hii⟩ := hNC
  -- Step 3: Chebotarev on N
  obtain ⟨q, hqinj, hq⟩ := ChebotarevManySplitPrimes Nn T t
  refine ⟨q, hqinj, fun b => ⟨(hq b).1, (hq b).2.1⟩, ?_⟩
  intro b
  set qb := q b with hqb
  have hqbP : qb.Prime := (hq b).1
  have hqN : SplitsCompletelyRat qb Nn := (hq b).2.2
  -- descend N → E
  haveI hEN_fd : FiniteDimensional (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) Nn :=
    Module.Finite.right ℚ (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) Nn
  have hqE : SplitsCompletelyRat qb (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) :=
    SublemmaCompleteSplittingDescends Nn
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) qb hqN
  -- transitivity in F ⊆ E: property 2 and the per-prime splitting
  obtain ⟨hqF, hvall⟩ :=
    (SublemmaSplittingTransitive F
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) qb).mp hqE
  -- Property 1: q % 4 = 1 via ℚ(i)
  have hq4 : qb % 4 = 1 := by
    set Qi := IntermediateField.adjoin ℚ ({ii} : Set Nn) with hQi
    have hmem : ii ∈ Qi := IntermediateField.mem_adjoin_simple_self ℚ ii
    haveI hnfQi : NumberField (Qi : Type _) :=
      NumberField.of_module_finite (K := ℚ) (L := (Qi : Type _))
    haveI hQiN_fd : FiniteDimensional (Qi : Type _) Nn := Module.Finite.right ℚ (Qi : Type _) Nn
    have hwit : ∃ x : (Qi : Type _), x ^ 2 = -1 := by
      refine ⟨⟨ii, hmem⟩, ?_⟩; apply Subtype.ext; push_cast; exact hii
    have hdeg : Module.finrank ℚ (Qi : Type _) = 2 := by
      haveI : Algebra.IsIntegral ℚ Nn := Algebra.IsIntegral.of_finite ℚ Nn
      have hint : IsIntegral ℚ ii := Algebra.IsIntegral.isIntegral ii
      have hmonic : (X ^ 2 + 1 : ℚ[X]).Monic := by
        have h : (X ^ 2 + 1 : ℚ[X]) = X ^ 2 + C 1 := by simp
        rw [h]; exact monic_X_pow_add (by simp)
      have haeval : (Polynomial.aeval ii) (X ^ 2 + 1 : ℚ[X]) = 0 := by simp [hii]
      have hnd : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
      have hirr : Irreducible (X ^ 2 + 1 : ℚ[X]) := by
        by_contra hcon
        rw [Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff hmonic hnd] at hcon
        obtain ⟨c₁, c₂, hc0, hc1⟩ := hcon
        simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc0 hc1
        norm_num at hc0 hc1
        nlinarith [sq_nonneg c₁, sq_nonneg c₂]
      have hmin : minpoly ℚ ii = X ^ 2 + 1 :=
        (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm
      rw [IntermediateField.adjoin.finrank hint, hmin, hnd]
    have hqQi : SplitsCompletelyRat qb (Qi : Type _) :=
      SublemmaCompleteSplittingDescends Nn (Qi : Type _) qb hqN
    exact SublemmaSplitInQiModFour (Qi : Type _) hwit hdeg qb hqbP hqQi
  refine ⟨hq4, hqF, ?_⟩
  -- Property 3: Frobenius representative in Φ at each v ∣ q
  intro v hv
  have hvmem := hv
  simp only [Ideal.primesOver, Set.mem_setOf_eq] at hv
  obtain ⟨hvprime, hvlies⟩ := hv
  haveI := hvprime
  haveI := hvlies
  have hspanne : Ideal.span {(qb : ℤ)} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hqbP.ne_zero
  have hvne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanne v
  have hvsplit : SplitsCompletely (F := F)
      (M := (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _)) v := hvall v hvmem
  obtain ⟨σ, hσfrob⟩ := SublemmaFrobRepExists F v hvne hvprime
  have hφfrob := hσfrob (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)))
  have hφ1 := SublemmaSplitCompletelyFrobTrivial F
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) v hvne hvprime hvsplit _ hφfrob
  have hσΦ : σ ∈ frattiniOpen (galUr 3 F) := by
    rw [← hker]; exact MonoidHom.mem_ker.mpr hφ1
  exact ⟨σ, hσfrob, hσΦ⟩
