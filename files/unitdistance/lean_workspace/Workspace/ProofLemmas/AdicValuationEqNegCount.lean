import Mathlib

open scoped NumberField nonZeroDivisors

set_option maxHeartbeats 800000

theorem AdicValuationEqNegCount (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  have hrs' : IsLocalization.mk' K r s = x := hrs
  have hs0 : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hrs'
    exact hx hrs'.symm
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ x
      = (↑(Ideal.span {r}) : FractionalIdeal (𝓞 K)⁰ K) *
        (↑(Ideal.span {(s : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs', IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  have hspanR : (Ideal.span {r} : Ideal (𝓞 K)) ≠ 0 :=
    fun hc => hr0 (Ideal.span_singleton_eq_bot.mp hc)
  have hspanS : (Ideal.span {(s : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 :=
    fun hc => hs0 (Ideal.span_singleton_eq_bot.mp hc)
  have hcr : (↑(Ideal.span {r}) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hspanR
  have hcs : (↑(Ideal.span {(s : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hspanS
  rw [← hrs', IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    v.intValuation_if_neg hr0, v.intValuation_if_neg hs0, hrs', hspan,
    FractionalIdeal.count_mul K v hcr (inv_ne_zero hcs),
    FractionalIdeal.count_inv, FractionalIdeal.count_coe K v hspanR,
    FractionalIdeal.count_coe K v hspanS]
  rw [← WithZero.exp_sub]
  congr 1
  ring
