import Mathlib

open scoped NumberField nonZeroDivisors

set_option maxHeartbeats 800000

/-- **Reconciliation of the integral multiplicity and the fractional-ideal count.** For a number
field `K`, a height-one prime `v` of `𝓞 K`, and a nonzero integral ideal `I`, the multiplicity of
`v.asIdeal` in `I` (as a natural number, cast to `ℤ`) equals Mathlib's signed adic count
`FractionalIdeal.count K v` of the coerced fractional ideal `↑I`. Both are computed from the same
normalized-factorization count of `I`. -/
theorem MultiplicityEqFractionalCount (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (multiplicity v.asIdeal I : ℤ)
      = FractionalIdeal.count K v (↑I : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hI0 : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hbridge : multiplicity v.asIdeal I
      = Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
    apply multiplicity_eq_of_emultiplicity_eq_some
    have h := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible hI0
    rwa [normalize_eq] at h
  rw [hbridge, FractionalIdeal.count_coe K v hI0,
      Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]
