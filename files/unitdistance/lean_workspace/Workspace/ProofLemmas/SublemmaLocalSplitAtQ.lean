import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.LocalSplitGenerator
import Workspace.ProofLemmas.LocalSplitResidueFactors
import Workspace.ProofLemmas.LocalSplitConductorCoprime
import Workspace.ProofLemmas.LocalSplitKummerCount
import Workspace.ProofLemmas.LocalSplitInertiaFromIdentity

open scoped NumberField

open Polynomial

open Workspace.Types.AdmissibleDatum Workspace.Types.CMAdjoinI Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaLocalSplitAtQ (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L)) :
    (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2 ∧
      ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K),
        Ideal.ramificationIdx 𝔮 𝔓 = 1 ∧ Ideal.inertiaDeg 𝔮 𝔓 = 1 := by
  -- (2) inertiaDeg over ℚ = 1 from q_b splitting completely in L
  have hf : Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) 𝔮 = 1 :=
    ((d.hq_split b).2.2 𝔮 h𝔮).2
  -- (3) residue factorization
  obtain ⟨hcard_res, r, hr_sq, hr_ne, hr_factor⟩ := LocalSplitResidueFactors d b 𝔮 h𝔮 hf
  -- (1) generator ω
  obtain ⟨ω, hω_algsq, hω_int, hω_min, hω_gen⟩ := LocalSplitGenerator d
  have hω_sq : ω ^ 2 = -1 := by
    apply IsFractionRing.injective (𝓞 d.K) d.K
    rw [map_pow, map_neg, map_one]; exact hω_algsq
  -- (4) conductor coprime
  have hcop := LocalSplitConductorCoprime d ω hω_sq hω_min b 𝔮 h𝔮
  -- (5) count of primes over 𝔮 and ramification indices
  obtain ⟨hncard, hram⟩ :=
    LocalSplitKummerCount d b ω hω_sq hω_int hω_min hω_gen 𝔮 h𝔮 hcop ⟨r, hr_sq, hr_ne⟩
  -- degree [K : L] = 2
  have hdeg : Module.finrank d.L d.K = 2 := by
    set ω' := algebraMap (𝓞 d.K) d.K ω with hω'def
    have hω'sq : ω' ^ 2 = -1 := by rw [hω'def, ← map_pow, hω_sq, map_neg, map_one]
    have hω'int : IsIntegral d.L ω' := ⟨X ^ 2 + 1, by monicity!, by simp [hω'sq]⟩
    have hmin' : minpoly d.L ω' = X ^ 2 + 1 := by
      have hh := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 d.L) (S := 𝓞 d.K)
        d.L d.K hω_int
      rw [hω'def, hh, hω_min]
      simp [Polynomial.map_add, Polynomial.map_pow]
    have h1 := IntermediateField.adjoin.finrank hω'int
    rw [hmin', hω_gen, IntermediateField.finrank_top'] at h1
    rw [h1]
    compute_degree!
  -- (6) inertiaDeg = 1
  have hinertia := LocalSplitInertiaFromIdentity d b 𝔮 h𝔮 hncard hram hdeg
  exact ⟨hncard, fun 𝔓 h𝔓 => ⟨hram 𝔓 h𝔓, hinertia 𝔓 h𝔓⟩⟩
