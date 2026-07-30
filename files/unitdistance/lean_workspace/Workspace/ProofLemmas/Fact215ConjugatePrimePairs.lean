import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.SplittingRamification
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaDegKQ
import Workspace.ProofLemmas.SublemmaLocalSplitAtQ
import Workspace.ProofLemmas.SublemmaDisjointCount

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.SplittingRamification
open Workspace.Types.CMAdjoinI

theorem Fact215ConjugatePrimePairs (d : AdmissibleDatum) :
    (∀ b, SplitsCompletelyRat (d.q b) d.K) ∧
      (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
        = 2 * d.t * deg d := by
  -- scalar tower ℤ → 𝓞 L → 𝓞 K (any two ℤ-algebras with a compatible map form a tower)
  haveI htower : IsScalarTower ℤ (𝓞 d.L) (𝓞 d.K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  -- degree identity [K:ℚ] = 2·deg d
  have hdeg : Module.finrank ℚ d.K = 2 * deg d := SublemmaDegKQ d
  -- Claim 1: each rational prime q_b splits completely in K.
  have hsplit : ∀ b, SplitsCompletelyRat (d.q b) d.K := by
    intro b
    -- span (q_b) in ℤ is a nonzero maximal ideal
    have hqZprime : Prime ((d.q b : ℤ)) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
    have hqZne : ((d.q b : ℤ)) ≠ 0 := hqZprime.ne_zero
    have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
    have hspan_prime : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hqZne).mpr hqZprime
    haveI hspan_max : (Ideal.span {(d.q b : ℤ)}).IsMaximal :=
      hspan_prime.isMaximal hspan_ne
    -- L-level complete splitting data
    obtain ⟨hqL_prime, hqL_count, hqL_ef⟩ := d.hq_split b
    -- Ramification/residue over q_b in K: each prime P over q_b has e = f = 1 (tower assembly)
    have hef : ∀ P ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
        Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) P = 1 ∧
          Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) P = 1 := by
      intro P hP
      obtain ⟨hPp, hPo⟩ := hP
      haveI := hPp
      haveI := hPo
      -- the prime 𝔮 = P ∩ 𝓞_L below P, a prime of 𝓞_L over q_b
      have h𝔮mem : P.under (𝓞 d.L) ∈
          Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L) :=
        ⟨inferInstance, inferInstance⟩
      obtain ⟨he_q, hf_q⟩ := hqL_ef _ h𝔮mem
      obtain ⟨_, hloc_ef⟩ := SublemmaLocalSplitAtQ d b (P.under (𝓞 d.L)) h𝔮mem
      have hPmem : P ∈ Ideal.primesOver (P.under (𝓞 d.L)) (𝓞 d.K) :=
        ⟨inferInstance, inferInstance⟩
      obtain ⟨he_P, hf_P⟩ := hloc_ef P hPmem
      -- 𝔮 is a nonzero prime of the Dedekind domain 𝓞_L, hence maximal
      haveI h𝔮max : (P.under (𝓞 d.L)).IsMaximal :=
        (h𝔮mem.1).isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne _)
      refine ⟨?_, ?_⟩
      · -- e(q_b, P) = e(q_b, 𝔮) · e(𝔮, P) = 1·1
        rw [Ideal.ramificationIdx_algebra_tower' (Ideal.span {(d.q b : ℤ)})
          (P.under (𝓞 d.L)) P, he_q, he_P]
      · -- f(q_b, P) = f(q_b, 𝔮) · f(𝔮, P) = 1·1
        rw [Ideal.inertiaDeg_algebra_tower (Ideal.span {(d.q b : ℤ)})
          (P.under (𝓞 d.L)) P, hf_q, hf_P]
    -- assemble SplitsCompletelyRat: prime, count, ramification
    refine ⟨d.hq_prime b, ?_, hef⟩
    -- Count: #primesOver(q_b, K) = [K:ℚ] via the fundamental identity ∑ e·f = [K:ℚ]
    rw [← IsDedekindDomain.coe_primesOverFinset hspan_ne (𝓞 d.K), Set.ncard_coe_finset,
      ← Ideal.sum_ramification_inertia (𝓞 d.K) ℚ d.K hspan_ne, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hPmem : P ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hspan_ne (𝓞 d.K)]
      exact Finset.mem_coe.mpr hP
    obtain ⟨he, hf⟩ := hef P hPmem
    rw [he, hf]
  -- Assemble the conjunction.
  refine ⟨hsplit, ?_⟩
  -- Count over all b: reduce to the disjoint-union sublemma via per-block counts.
  refine SublemmaDisjointCount d ?_
  intro b
  exact (hsplit b).2.1.trans hdeg
