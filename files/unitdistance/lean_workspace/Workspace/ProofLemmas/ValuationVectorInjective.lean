import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.ConjQuotientValuationFormula

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 4000000

theorem ValuationVectorInjective (d : AdmissibleDatum)
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
    (η : Fin (d.t * deg d) → Bool)
    (F : Finset (Fin (d.t * deg d) → Bool))
    (u : (Fin (d.t * deg d) → Bool) → d.K)
    (hu : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧ u ε = α / conjAut d.h_adjoin α ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
        (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
            FractionalIdeal (𝓞 d.K)⁰ d.K) *
        (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
            FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    Set.InjOn u ↑F := by
  intro ε₁ hε₁ ε₂ hε₂ heq
  obtain ⟨α₁, hα₁, huε₁, hgen₁⟩ := hu ε₁ (Finset.mem_coe.mp hε₁)
  obtain ⟨α₂, hα₂, huε₂, hgen₂⟩ := hu ε₂ (Finset.mem_coe.mp hε₂)
  funext s
  -- valuation of `u ε_i` at `P s`
  have hv₁ := ((ConjQuotientValuationFormula d P Pc bidx hfam η ε₁ α₁ hα₁ hgen₁).1 s).1
  have hv₂ := ((ConjQuotientValuationFormula d P Pc bidx hfam η ε₂ α₂ hα₂ hgen₂).1 s).1
  -- both valuations are `exp` of the corresponding integer exponent, and are equal
  have hchain :
      WithZero.exp (-(2 * (((ε₁ s).toNat : ℤ) - ((η s).toNat : ℤ))))
        = WithZero.exp (-(2 * (((ε₂ s).toNat : ℤ) - ((η s).toNat : ℤ)))) := by
    rw [← hv₁, ← hv₂, ← huε₁, ← huε₂, heq]
  -- injectivity of `exp` recovers the exponent, hence `ε₁ s = ε₂ s`
  have hE := WithZero.exp_inj.mp hchain
  have hnat : (ε₁ s).toNat = (ε₂ s).toNat := by omega
  rcases hb₁ : ε₁ s <;> rcases hb₂ : ε₂ s <;> simp_all
