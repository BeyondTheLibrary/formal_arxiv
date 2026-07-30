import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI

open scoped NumberField
open Polynomial

open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 1000000

/-- **Coprimality of the conductor to a split prime `𝔮` (Local splitting, step 2).**

For an admissible datum `d`, let `ω : 𝓞 d.K` be an integral generator with `ω² = -1` and
minimal polynomial `X² + 1` over `𝓞 d.L` (the conclusion of `LocalSplitGenerator`, taken here
as hypotheses).  Let `b : Fin d.t`, so `q_b = d.q b` is an odd rational prime, and let `𝔮` be a
prime of `𝓞 d.L` lying over `(q_b)`.  Then the conductor `𝔣 = conductor (𝓞 d.L) ω` of the order
`𝓞 d.L[ω] ⊆ 𝓞 d.K` is coprime to `𝔮`: the pullback of `𝔣` to `𝓞 d.L` (its `comap` along the
ring-of-integers algebra map) together with `𝔮` generates the unit ideal.

Mathematically `2 ∈ 𝔣` (the different of `X² + 1` is `(2ω)`, discriminant `-4`), while `2 ∉ 𝔮`
because `𝔮` lies over the odd prime `q_b`; hence `𝔮` cannot contain the conductor pullback and
the two ideals are coprime. -/
theorem LocalSplitConductorCoprime
    (d : AdmissibleDatum)
    (ω : 𝓞 d.K)
    (hω_sq : ω ^ 2 = -1)
    (hω_min : minpoly (𝓞 d.L) ω = X ^ 2 + 1)
    (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L)) :
    (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ⊔ 𝔮 = ⊤ := by
  -- relative-extension instances
  have i3 : IsScalarTower (𝓞 d.L) d.L d.K :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [← IsScalarTower.algebraMap_apply])
  have i4 : IsScalarTower (𝓞 d.L) (𝓞 d.K) d.K :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [← IsScalarTower.algebraMap_apply])
  have i5 : IsIntegralClosure (𝓞 d.K) (𝓞 d.L) d.K :=
    NumberField.RingOfIntegers.instIsIntegralClosure d.L d.K
  have i8 : Module.IsTorsionFree (𝓞 d.L) (𝓞 d.K) := inferInstance
  -- ω as an element of the field d.K
  set ω' : d.K := algebraMap (𝓞 d.K) d.K ω with hω'def
  have hω'sq : ω' ^ 2 = -1 := by
    rw [hω'def, ← map_pow, hω_sq, map_neg, map_one]
  have hω'int : IsIntegral d.L ω' := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hω'sq]
  have hpoly : (aeval ω') (X ^ 2 + 1 : d.L[X]) = 0 := by simp [hω'sq]
  have hωint : IsIntegral (𝓞 d.L) ω := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hω_sq]
  -- minpoly of ω' over d.L is X²+1
  have hmin' : minpoly d.L ω' = X ^ 2 + 1 := by
    have := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 d.L) (S := 𝓞 d.K)
      d.L d.K hωint
    rw [hω'def, this, hω_min]
    simp [Polynomial.map_add, Polynomial.map_pow]
  -- ω' generates d.K over d.L
  obtain ⟨iota, hiota_sq, hiota_adj⟩ := d.h_adjoin
  have hfac : (ω' - iota) * (ω' + iota) = 0 := by
    have h2 : ω' ^ 2 - iota ^ 2 = 0 := by rw [hω'sq, hiota_sq]; ring
    linear_combination h2
  have hxIF : IntermediateField.adjoin d.L {ω'} = ⊤ := by
    rcases mul_eq_zero.mp hfac with h | h
    · have : ω' = iota := by linear_combination h
      rw [this, hiota_adj]
    · have hneg : ω' = -iota := by linear_combination h
      rw [hneg]
      apply top_le_iff.mp
      rw [← hiota_adj]
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      rw [hy]
      have : (-iota) ∈ IntermediateField.adjoin d.L {-iota} :=
        IntermediateField.mem_adjoin_simple_self d.L (-iota)
      simpa using neg_mem this
  have hx : Algebra.adjoin d.L {ω'} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hω'int, hxIF]
    exact IntermediateField.top_toSubalgebra
  -- conductor * different = span {2ω}  (Kummer–Dedekind / different of X²+1)
  have hcond := conductor_mul_differentIdeal (𝓞 d.L) d.L d.K ω hx
  rw [hω_min] at hcond
  have hd : derivative (X ^ 2 + 1 : (𝓞 d.L)[X]) = 2 * X := by
    simp only [derivative_add, derivative_X_pow, derivative_one, add_zero, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, map_ofNat]
  have hderiv : (aeval ω) (derivative (X ^ 2 + 1 : (𝓞 d.L)[X])) = 2 * ω := by
    rw [hd, map_mul, map_ofNat, aeval_X]
  rw [hderiv] at hcond
  -- 2ω ∈ conductor, hence 2 ∈ conductor
  have hspan_le : Ideal.span {2 * ω} ≤ conductor (𝓞 d.L) ω := by
    rw [← hcond]; exact Ideal.mul_le_right
  have h2ω : 2 * ω ∈ conductor (𝓞 d.L) ω :=
    hspan_le (Ideal.mem_span_singleton_self _)
  have h2 : (2 : 𝓞 d.K) ∈ conductor (𝓞 d.L) ω := by
    have hmul := Ideal.mul_mem_left (conductor (𝓞 d.L) ω) (-ω) h2ω
    have heq : (-ω) * (2 * ω) = (2 : 𝓞 d.K) := by linear_combination (-2 : 𝓞 d.K) * hω_sq
    rwa [heq] at hmul
  have h2comap : (2 : 𝓞 d.L) ∈ (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) := by
    rw [Ideal.mem_comap, map_ofNat]; exact h2
  -- 2 ∉ 𝔮 (𝔮 lies over the odd prime q_b)
  have hqdvd : ¬ (d.q b ∣ 2) := by
    intro hdvd
    have heq2 : d.q b = 2 := (Nat.prime_dvd_prime_iff_eq (d.hq_prime b) Nat.prime_two).mp hdvd
    have hm := d.hq_mod4 b
    rw [heq2] at hm; norm_num at hm
  have hinj : Function.Injective (algebraMap ℤ (𝓞 d.L)) := RingHom.injective_int _
  have h2not : (2 : 𝓞 d.L) ∉ 𝔮 := by
    intro hmem
    have h2int : (2 : ℤ) ∈ Ideal.under ℤ 𝔮 := by
      show algebraMap ℤ (𝓞 d.L) (2 : ℤ) ∈ 𝔮
      simpa using hmem
    rw [← h𝔮.2.over, Ideal.mem_span_singleton] at h2int
    have : d.q b ∣ 2 := by exact_mod_cast h2int
    exact hqdvd this
  -- 𝔮 is maximal (nonzero prime in a Dedekind domain)
  have hqne : 𝔮 ≠ ⊥ := by
    rintro rfl
    have hlo : Ideal.span {(d.q b : ℤ)} = ⊥ :=
      (h𝔮.2.over).trans (Ideal.comap_bot_of_injective _ hinj)
    have hq0 : (d.q b : ℤ) = 0 := (Ideal.span_singleton_eq_bot).mp hlo
    have hp := d.hq_prime b
    simp only [Nat.cast_eq_zero] at hq0
    rw [hq0] at hp
    exact Nat.not_prime_zero hp
  have hmax : 𝔮.IsMaximal := (h𝔮.1).isMaximal hqne
  -- combine: 2 ∈ pullback but 2 ∉ 𝔮, and 𝔮 maximal ⇒ sup = ⊤
  by_contra hne
  have hsub : (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ≤ 𝔮 := by
    have heqq := hmax.eq_of_le hne le_sup_right
    rw [heqq]; exact le_sup_left
  exact h2not (hsub h2comap)
