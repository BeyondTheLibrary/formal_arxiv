import Mathlib
import Workspace.Types.AdmissibleDatum

open scoped NumberField
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 800000

theorem MultiplicityPrimeOverRationalPrime (d : AdmissibleDatum) (P : Ideal (𝓞 d.K))
    [hPp : P.IsPrime] (hPne : P ≠ ⊥) (b : Fin d.t)
    (hram : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
      Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1) :
    (P.LiesOver (Ideal.span {(d.q b : ℤ)}) →
        multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = 1) ∧
    (¬ P.LiesOver (Ideal.span {(d.q b : ℤ)}) →
        multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = 0) := by
  classical
  have hqZprime : Prime ((d.q b : ℤ)) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
  have hqZne : ((d.q b : ℤ)) ≠ 0 := hqZprime.ne_zero
  have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
  haveI hspan_prime : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hqZne).mpr hqZprime
  haveI hspan_max : (Ideal.span {(d.q b : ℤ)}).IsMaximal := hspan_prime.isMaximal hspan_ne
  have hinj : Function.Injective (algebraMap ℤ (𝓞 d.K)) := RingHom.injective_int _
  have hspaneq : Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}
      = Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapne : Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact hspan_ne
  have hbridge : multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)})
      = Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}))) := by
    rw [hspaneq]
    apply multiplicity_eq_of_emultiplicity_eq_some
    have h := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hPne hPp).irreducible hmapne
    rwa [normalize_eq] at h
  refine ⟨?_, ?_⟩
  · intro hlies
    rw [hbridge,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapne hPp hPne]
    exact hram P ⟨hPp, hlies⟩
  · intro hnlies
    rw [hbridge, Multiset.count_eq_zero]
    intro hmem
    apply hnlies
    exact ((Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hspan_ne).mpr hmem).2
