import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.MultiplicityEqFractionalCount

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

/-- **Count-level `conjAut` transport (equation-(4) building block for Prop 2.2).** -/
theorem ConjAutSpanSingletonCountSwap (d : AdmissibleDatum)
    (P Pc : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (α : d.K) (hα : α ≠ 0)
    (htrans : ∀ I : Ideal (𝓞 d.K),
      multiplicity Pc.asIdeal
          (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
        = multiplicity P.asIdeal I) :
    FractionalIdeal.count d.K Pc
        (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α))
      = FractionalIdeal.count d.K P
        (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α) := by
  classical
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'
  -- naturality: algebraMap ∘ c' = conjAut ∘ algebraMap
  have hnat : ∀ x : 𝓞 d.K, algebraMap (𝓞 d.K) d.K (c' x)
      = conjAut d.h_adjoin (algebraMap (𝓞 d.K) d.K x) := by
    intro x
    simp [hc', NumberField.RingOfIntegers.mapAlgEquiv, NumberField.RingOfIntegers.mapAlgHom]
  -- write α = mk' a s0
  obtain ⟨⟨a, s0⟩, hα_eq⟩ := IsLocalization.mk'_surjective (𝓞 d.K)⁰ α
  have hαmk : α = IsLocalization.mk' d.K a s0 := hα_eq.symm
  have ha : a ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hαmk
    exact hα hαmk
  have hs0 : (s0 : 𝓞 d.K) ≠ 0 := nonZeroDivisors.ne_zero s0.prop
  -- c' preserves the denominator's nonzero-divisor membership
  have hmem : (c' (s0 : 𝓞 d.K)) ∈ (𝓞 d.K)⁰ := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact hs0 (c'.injective (by rw [h, map_zero]))
  set t0 : (𝓞 d.K)⁰ := ⟨c' (s0 : 𝓞 d.K), hmem⟩ with ht0
  have ht0coe : ((t0 : 𝓞 d.K)) = c' (s0 : 𝓞 d.K) := rfl
  -- conjAut α = mk' (c' a) t0
  have hconj : conjAut d.h_adjoin α = IsLocalization.mk' d.K (c' a) t0 := by
    rw [hαmk, IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ht0coe, map_div₀,
      hnat a, hnat (s0 : 𝓞 d.K)]
  -- c' a ≠ 0
  have hca : c' a ≠ 0 := fun h => ha (c'.injective (by rw [h, map_zero]))
  have hcs0 : c' (s0 : 𝓞 d.K) ≠ 0 := nonZeroDivisors.ne_zero hmem
  -- image ideals under c' are the span singletons of images
  have himgA : Ideal.map c' (Ideal.span ({a} : Set (𝓞 d.K))) = Ideal.span {c' a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have himgS : Ideal.map c' (Ideal.span ({(s0 : 𝓞 d.K)} : Set (𝓞 d.K)))
      = Ideal.span {c' (s0 : 𝓞 d.K)} := by
    rw [Ideal.map_span, Set.image_singleton]
  -- span-of-mk' decomposition
  have hspan : ∀ (b : 𝓞 d.K) (u : (𝓞 d.K)⁰),
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (IsLocalization.mk' d.K b u)
        = (↑(Ideal.span {b}) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(Ideal.span {(u : 𝓞 d.K)}) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro b u
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  -- generic count of coe J1 * (coe J2)⁻¹
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K)) (J1 J2 : Ideal (𝓞 d.K)),
      J1 ≠ ⊥ → J2 ≠ ⊥ →
      FractionalIdeal.count d.K v
          ((↑J1 : FractionalIdeal (𝓞 d.K)⁰ d.K) * (↑J2 : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹)
        = (multiplicity v.asIdeal J1 : ℤ) - (multiplicity v.asIdeal J2 : ℤ) := by
    intro v J1 J2 h1 h2
    rw [FractionalIdeal.count_mul d.K v (FractionalIdeal.coeIdeal_ne_zero.mpr h1)
          (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr h2)),
        FractionalIdeal.count_inv,
        ← MultiplicityEqFractionalCount d.K v J1 h1,
        ← MultiplicityEqFractionalCount d.K v J2 h2]
    ring
  -- nonzero ideals
  have hbaneA : Ideal.span ({a} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hbaneS : Ideal.span ({(s0 : 𝓞 d.K)} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hcaneA : Ideal.span ({c' a} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hcaneS : Ideal.span ({c' (s0 : 𝓞 d.K)} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  -- LHS
  rw [hconj, hspan (c' a) t0]
  show FractionalIdeal.count d.K Pc
      ((↑(Ideal.span {c' a}) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
        (↑(Ideal.span {(t0 : 𝓞 d.K)}) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) = _
  rw [ht0coe, key Pc (Ideal.span {c' a}) (Ideal.span {c' (s0 : 𝓞 d.K)}) hcaneA hcaneS]
  -- RHS
  conv_rhs => rw [hαmk, hspan a s0, key P (Ideal.span {a}) (Ideal.span {(s0 : 𝓞 d.K)}) hbaneA hbaneS]
  -- transport multiplicities: mult Pc (span{c' a}) = mult P (span{a}), etc.
  rw [← himgA, ← himgS, htrans (Ideal.span {a}), htrans (Ideal.span {(s0 : 𝓞 d.K)})]
