import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.ConjQuotientValuationFormula

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

theorem QSquaredClearsConjQuotient (d : AdmissibleDatum)
    (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (bidx : Fin (d.t * deg d) → Fin d.t)
    (hfam :
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I))
    (η ε : Fin (d.t * deg d) → Bool)
    (α : d.K) (hα : α ≠ 0)
    (hgen : FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
      (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K) *
      (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    IsIntegral ℤ ((Dq d : d.K) * (α / conjAut d.h_adjoin α)) := by
  set u := α / conjAut d.h_adjoin α with hu_def
  have hform := ConjQuotientValuationFormula d P Pc bidx hfam η ε α hα hgen
  -- Crux: any prime `w` lying over `(q_b)` has `w.valuation Dq ≤ exp(-2)`, since `q_b² ∣ Dq`.
  have hcrux : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K)) (b : Fin d.t),
      w.asIdeal.LiesOver (Ideal.span {(d.q b : ℤ)}) →
      w.valuation d.K (Dq d : d.K) ≤ WithZero.exp (-2) := by
    intro w b hlo
    have hcast : (Dq d : d.K) = algebraMap (𝓞 d.K) d.K ((Dq d : ℕ) : 𝓞 d.K) := by
      rw [map_natCast]
    rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    -- Goal: `((Dq d : ℕ) : 𝓞 K) ∈ w.asIdeal ^ 2`.
    have hqmem : ((d.q b : ℕ) : 𝓞 d.K) ∈ w.asIdeal := by
      have hmem_int : (d.q b : ℤ) ∈ Ideal.under ℤ w.asIdeal := by
        rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
      have h2 : algebraMap ℤ (𝓞 d.K) (d.q b : ℤ) ∈ w.asIdeal := hmem_int
      simpa using h2
    have hQmem : ((Qprod d : ℕ) : 𝓞 d.K) ∈ w.asIdeal := by
      have hQ : ((Qprod d : ℕ) : 𝓞 d.K) = ∏ b', ((d.q b' : ℕ) : 𝓞 d.K) := by
        rw [show Qprod d = ∏ b', d.q b' from rfl]; push_cast; rfl
      rw [hQ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
      exact Ideal.mul_mem_right _ _ hqmem
    have hDqQ : ((Dq d : ℕ) : 𝓞 d.K) = ((Qprod d : ℕ) : 𝓞 d.K) ^ 2 := by
      rw [show Dq d = (Qprod d) ^ 2 from rfl]; push_cast; ring
    rw [hDqQ, pow_two, pow_two]
    exact Ideal.mul_mem_mul hQmem hQmem
  -- All adic valuations of `Dq · u` are `≤ 1`, so `Dq · u` is an algebraic integer.
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      v.valuation d.K ((Dq d : d.K) * u) ≤ 1 := by
    intro v
    rw [map_mul]
    by_cases hv : ∃ s, v = P s ∨ v = Pc s
    · obtain ⟨s, hs⟩ := hv
      have hbound_ε : ((ε s).toNat : ℤ) ≤ 1 ∧ 0 ≤ ((ε s).toNat : ℤ) := by
        rcases ε s <;> simp
      have hbound_η : ((η s).toNat : ℤ) ≤ 1 ∧ 0 ≤ ((η s).toNat : ℤ) := by
        rcases η s <;> simp
      rcases hs with hs | hs
      · subst hs
        rw [(hform.1 s).1]
        calc (P s).valuation d.K (Dq d : d.K)
                * WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))))
            ≤ WithZero.exp (-2)
                * WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) :=
              mul_le_mul_right' (hcrux (P s) (bidx s) (hfam.2.2.1 s).1) _
          _ = WithZero.exp (-2 + -(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) :=
              (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
          _ = 1 := WithZero.exp_zero
      · subst hs
        rw [(hform.1 s).2]
        calc (Pc s).valuation d.K (Dq d : d.K)
                * WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))
            ≤ WithZero.exp (-2)
                * WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))) :=
              mul_le_mul_right' (hcrux (Pc s) (bidx s) (hfam.2.2.1 s).2.1) _
          _ = WithZero.exp (-2 + 2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))) :=
              (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
          _ = 1 := WithZero.exp_zero
    · push_neg at hv
      rw [hform.2 v hv, mul_one]
      -- `Dq` is an integer, so its valuation is `≤ 1`.
      have hcast : (Dq d : d.K) = algebraMap (𝓞 d.K) d.K ((Dq d : ℕ) : 𝓞 d.K) := by
        rw [map_natCast]
      rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v _
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one d.K
      ((Dq d : d.K) * u) hval
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y
