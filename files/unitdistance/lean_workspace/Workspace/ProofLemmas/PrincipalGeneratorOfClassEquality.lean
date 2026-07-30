import Mathlib

open scoped NumberField nonZeroDivisors
open NumberField

set_option maxHeartbeats 4000000

theorem PrincipalGeneratorOfClassEquality
    (K : Type*) [Field K] [NumberField K]
    (A B : Ideal (𝓞 K)) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero hA⟩
        = ClassGroup.mk0 ⟨B, mem_nonZeroDivisors_of_ne_zero hB⟩) :
    ∃ α : K, α ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ α
        = (↑A : FractionalIdeal (𝓞 K)⁰ K) * (↑B : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hax : algebraMap (𝓞 K) K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx
  have hay : algebraMap (𝓞 K) K y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hy
  refine ⟨algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K x, div_ne_zero hay hax, ?_⟩
  have hcoe : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) *
        (↑A : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) *
        (↑B : FractionalIdeal (𝓞 K)⁰ K) := by
    have hh := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) hxy
    simpa only [FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton] using hh
  have hBne : (↑B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hB
  have haxne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hax
  have hsplit : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K x)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x))⁻¹ := by
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_inv]
  rw [hsplit, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff haxne hBne,
    mul_comm (↑A : FractionalIdeal (𝓞 K)⁰ K)]
  exact hcoe.symm
