import Mathlib

/-!
# The exact different exponent, propagated down a tower

Mathlib knows two things about the different ideal of a number field:

* `pow_sub_one_dvd_differentIdeal` : `P ^ (e - 1) ∣ 𝔡`;
* `not_dvd_differentIdeal_iff` : `P ∤ 𝔡` exactly when `P` is unramified.

It does **not** know the tame value `v_P(𝔡) = e - 1` (that is a local computation with higher
ramification groups).  The point of this file is that one does not need it for *subfields of a field
whose different exponent is already known*: in a tower `ℚ ⊆ L ⊆ K` the two Mathlib lower bounds for
`𝔡_{K/L}` and `𝔡_{L/ℚ}` already add up to `e(P/p) - 1`, so if `v_P(𝔡_K) = e(P/p) - 1` then **both**
must be equalities and in particular `v_{P∩L}(𝔡_L) = e(P∩L/p) - 1`.

This is the "forced equality" trick; it turns the single computation for `ℚ(ζ_m)` into the tame
conductor–discriminant input for every subfield of `ℚ(ζ_m)`.
-/

open scoped NumberField

namespace Workspace.ProofLemmas.TameDifferent

set_option maxHeartbeats 1000000

section Tower

variable (L K : Type*) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

end Tower

/-- `e(P/p) ≤ [E:F]`. -/
theorem ramificationIdx_le_finrank (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E] [Algebra R E]
    [IsScalarTower R S E] [IsScalarTower R F E] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Ideal.ramificationIdx p P ≤ Module.finrank F E := by
  have hsum := Ideal.sum_ramification_inertia (R := R) S F E hp
  have hmem : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp S).mpr ⟨inferInstance, inferInstance⟩
  have hle : Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset p S,
          Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q :=
    Finset.single_le_sum (f := fun Q => Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hsum] at hle
  have hf : 1 ≤ Ideal.inertiaDeg p P := Ideal.inertiaDeg_pos p P
  nlinarith [hle, hf]

/-- If `e(P/p) = [E:F]` then `f(P/p) = 1`. -/
theorem inertiaDeg_eq_one_of_totally_ramified
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E] [Algebra R E]
    [IsScalarTower R S E] [IsScalarTower R F E] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (he : Ideal.ramificationIdx p P = Module.finrank F E) (hpos : 0 < Module.finrank F E) :
    Ideal.inertiaDeg p P = 1 := by
  have hsum := Ideal.sum_ramification_inertia (R := R) S F E hp
  have hmem : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp S).mpr ⟨inferInstance, inferInstance⟩
  have hle : Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset p S,
          Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q :=
    Finset.single_le_sum (f := fun Q => Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hsum, he] at hle
  have hf : 1 ≤ Ideal.inertiaDeg p P := Ideal.inertiaDeg_pos p P
  nlinarith [hle, hf, hpos]

section Subfield

variable (r : ℕ) [hr : Fact r.Prime]
variable (K : Type) [Field K] [NumberField K] [hcyc : IsCyclotomicExtension {r} ℚ K]
variable (L : Type) [Field L] [NumberField L] [Algebra L K]

theorem span_r_ne_bot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
  simp only [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast hr.out.ne_zero

instance span_r_isPrime : (Ideal.span {(r : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by exact_mod_cast hr.out.ne_zero)]
  exact Nat.prime_iff_prime_int.mp hr.out

instance span_r_isMaximal : (Ideal.span {(r : ℤ)}).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (span_r_ne_bot r)

/-- Every subfield of `ℚ(ζ_r)` is totally ramified at `r`. -/
theorem totally_ramified
    (P : Ideal (𝓞 K)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) (P.under (𝓞 L)) = Module.finrank ℚ L
      ∧ Ideal.ramificationIdx (P.under (𝓞 L)) P = Module.finrank L K := by
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional L K := Module.Finite.right ℚ L K
  haveI : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  set PL : Ideal (𝓞 L) := P.under (𝓞 L) with hPLdef
  haveI : PL.IsPrime := Ideal.IsPrime.under _ P
  haveI : PL.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [hPLdef, Ideal.under_under]
    exact hPl.over
  haveI : P.LiesOver PL := ⟨rfl⟩
  have hrbot := span_r_ne_bot r
  have hPLbot : PL ≠ ⊥ := by
    intro hcon
    exact hP (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 L) (S := 𝓞 K) (I := P) hcon)
  haveI : PL.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPLbot
  -- the ramification index upstairs
  have heK : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = r - 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime r K P
  -- degrees
  have hnK : Module.finrank ℚ K = r - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank (K := K) (k := r), Nat.totient_prime hr.out]
  have hdeg : Module.finrank ℚ L * Module.finrank L K = r - 1 := by
    rw [Module.finrank_mul_finrank ℚ L K, hnK]
  -- tower multiplicativity of `e`
  have hinjL : Function.Injective (algebraMap (𝓞 L) (𝓞 K)) :=
    FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 K)
  have hinjZ : Function.Injective (algebraMap ℤ (𝓞 K)) :=
    FaithfulSMul.algebraMap_injective ℤ (𝓞 K)
  have htower : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL * Ideal.ramificationIdx PL P := by
    refine Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 L) (T := 𝓞 K) ?_ ?_ ?_
    · exact (Ideal.map_eq_bot_iff_of_injective hinjL).not.mpr hPLbot
    · exact (Ideal.map_eq_bot_iff_of_injective hinjZ).not.mpr hrbot
    · exact Ideal.map_le_of_le_comap le_rfl
  -- both factors are bounded by the corresponding degrees
  have h1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL ≤ Module.finrank ℚ L :=
    ramificationIdx_le_finrank ℤ ℚ (𝓞 L) L _ hrbot PL
  have h2 : Ideal.ramificationIdx PL P ≤ Module.finrank L K :=
    ramificationIdx_le_finrank (𝓞 L) L (𝓞 K) K _ hPLbot P
  rw [heK] at htower
  set a := Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL with hadef
  set b := Ideal.ramificationIdx PL P with hbdef
  set A := Module.finrank ℚ L with hAdef
  set B := Module.finrank L K with hBdef
  have hApos : 0 < A := Module.finrank_pos
  have hBpos : 0 < B := Module.finrank_pos
  have hab : a * b = A * B := (hdeg.trans htower).symm
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.mul_zero] at hab
      exact absurd hab.symm (Nat.mul_ne_zero hApos.ne' hBpos.ne')
    · exact h
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, Nat.zero_mul] at hab
      exact absurd hab.symm (Nat.mul_ne_zero hApos.ne' hBpos.ne')
    · exact h
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hlt : a < A := lt_of_le_of_ne h1 hne
    have hcon : a * b < A * B :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hlt (le_refl b) hbpos)
        (Nat.mul_le_mul_left A h2)
    omega
  · by_contra hne
    have hlt : b < B := lt_of_le_of_ne h2 hne
    have hcon : a * b < A * B :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_le_of_lt h1 hlt hApos)
        (le_refl (A * B))
    omega

end Subfield

section Discr

/-- **Discriminant of a subfield of `ℚ(ζ_r)`.** -/
theorem natAbs_discr_subfield (r : ℕ) [hr : Fact r.Prime]
    (K : Type) [Field K] [NumberField K] [hcyc : IsCyclotomicExtension {r} ℚ K]
    (L : Type) [Field L] [NumberField L] [Algebra L K] :
    (NumberField.discr L).natAbs = r ^ (Module.finrank ℚ L - 1) := by
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional L K := Module.Finite.right ℚ L K
  haveI : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  have hrbot := span_r_ne_bot r
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr.out
  -- a prime of `𝓞 K` over `r`
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(r : ℤ)})
  haveI := hPmax
  haveI := hPlies
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    intro hcon
    subst hcon
    have : (Ideal.span {(r : ℤ)}) = ⊥ := by
      have := hPlies.over
      simpa using this
    exact hrbot this
  set PL : Ideal (𝓞 L) := P.under (𝓞 L) with hPLdef
  haveI : PL.IsPrime := Ideal.IsPrime.under _ P
  haveI : PL.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [hPLdef, Ideal.under_under]
    exact hPlies.over
  haveI : P.LiesOver PL := ⟨rfl⟩
  have hPLbot : PL ≠ ⊥ := by
    intro hcon
    exact hPbot (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 L) (S := 𝓞 K) (I := P) hcon)
  haveI : PL.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPLbot
  obtain ⟨he1, he2⟩ := totally_ramified r K L P hPbot
  set n := Module.finrank ℚ L with hn
  set m := Module.finrank L K with hm
  have hnpos : 0 < n := Module.finrank_pos
  have hmpos : 0 < m := Module.finrank_pos
  -- inertia degrees are `1`
  have hfK : Ideal.inertiaDeg (Ideal.span {(r : ℤ)}) P = 1 :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime r K P
  have hfL : Ideal.inertiaDeg (Ideal.span {(r : ℤ)}) PL = 1 :=
    inertiaDeg_eq_one_of_totally_ramified ℤ ℚ (𝓞 L) L _ hrbot PL he1 hnpos
  -- absolute norms
  have hNK : Ideal.absNorm P = r := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg P hrprime, hfK, pow_one, Int.natAbs_natCast]
  have hNL : Ideal.absNorm PL = r := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg PL hrprime, hfL, pow_one, Int.natAbs_natCast]
  -- lower bound
  have hlow : r ^ (n - 1) ∣ (NumberField.discr L).natAbs := by
    have h1 : PL ^ (n - 1) ∣ differentIdeal ℤ (𝓞 L) := by
      rw [← he1]
      exact pow_sub_one_dvd_differentIdeal ℤ PL _ hrbot
        (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    have h2 := map_dvd Ideal.absNorm h1
    rw [map_pow, hNL, NumberField.absNorm_differentIdeal L (𝓞 L)] at h2
    exact h2
  -- upper bound
  have hrel : (r : ℕ) ^ (m - 1) ∣ Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) := by
    have h1 : P ^ (m - 1) ∣ differentIdeal (𝓞 L) (𝓞 K) := by
      rw [← he2]
      exact pow_sub_one_dvd_differentIdeal (𝓞 L) P _ hPLbot
        (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    have h2 := map_dvd Ideal.absNorm h1
    rwa [map_pow, hNK] at h2
  have htow := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) K (𝓞 K)
  have hdiscK : (NumberField.discr K).natAbs = r ^ (r - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime r K]
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hnm : n * m = r - 1 := by
    rw [hn, hm, Module.finrank_mul_finrank ℚ L K,
      IsCyclotomicExtension.Rat.finrank (K := K) (k := r), Nat.totient_prime hr.out]
  set B := (NumberField.discr L).natAbs with hB
  obtain ⟨A', hA'⟩ := hrel
  rw [hdiscK, hA'] at htow
  have hdvd1 : r ^ (m - 1) * B ^ m ∣ r ^ (r - 2) := ⟨A', by rw [htow]; ring⟩
  have hr2 : 2 ≤ r := hr.out.two_le
  have hnm' : m * n = r - 1 := by rw [Nat.mul_comm]; exact hnm
  have hsub : m * (n - 1) = (r - 1) - m := by rw [Nat.mul_sub, Nat.mul_one, hnm']
  have hmle : m ≤ r - 1 := Nat.le_of_dvd (by omega) ⟨n, hnm'.symm⟩
  have hexp : r - 2 = (m - 1) + m * (n - 1) := by rw [hsub]; omega
  rw [hexp, pow_add] at hdvd1
  have hcancel : B ^ m ∣ r ^ (m * (n - 1)) :=
    (Nat.mul_dvd_mul_iff_left (pow_pos hr.out.pos (m - 1))).mp hdvd1
  have hcancel2 : B ^ m ∣ (r ^ (n - 1)) ^ m := by
    rw [← pow_mul, Nat.mul_comm]
    exact hcancel
  have hup : B ∣ r ^ (n - 1) := (Nat.pow_dvd_pow_iff hmpos.ne').mp hcancel2
  exact Nat.dvd_antisymm hup hlow

end Discr

end Workspace.ProofLemmas.TameDifferent
