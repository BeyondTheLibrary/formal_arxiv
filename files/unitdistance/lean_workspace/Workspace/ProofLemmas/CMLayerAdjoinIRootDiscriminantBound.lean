import Mathlib
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.CMAdjoinI
open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI

open Polynomial
open scoped ComplexConjugate

theorem CMLayerAdjoinIRootDiscriminantBound (L : Type) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (K : Type) [Field K] [NumberField K] [Algebra L K] (hadj : IsAdjoinI L K) :
    rootDiscriminant K ≤ 2 * rootDiscriminant L := by
  classical
  obtain ⟨iota, hsq, hadjeq⟩ := hadj
  -- `iota` is integral over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota ∉ L`, since `L` is totally real.
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- The minimal polynomial of `iota` over `L` is `X ^ 2 + 1`.
  have hmin : minpoly L iota = X ^ 2 + 1 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd; simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : L[X]).natDegree ≤ (minpoly L iota).natDegree := by
      have h2 : 2 ≤ (minpoly L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd hdeg).symm
  -- `[K : L] = 2`.
  have hrank2 : Module.finrank L K = 2 := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [hmin] at h1
    have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    rw [hnd] at h1
    have e : (IntermediateField.adjoin L {iota}) ≃ₐ[L] K :=
      (IntermediateField.equivOfEq hadjeq).trans IntermediateField.topEquiv
    have h3 : Module.finrank L (IntermediateField.adjoin L {iota}) = Module.finrank L K :=
      e.toLinearEquiv.finrank_eq
    rw [h3] at h1; exact h1
  haveI hfd : FiniteDimensional L K := by
    apply FiniteDimensional.of_finrank_pos; rw [hrank2]; norm_num
  haveI hmodfin : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  -- `iota` is integral over `ℤ`, hence an algebraic integer.
  have hintZ : IsIntegral ℤ iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  set xI : 𝓞 K := ⟨iota, hintZ⟩ with hxI
  have hxI_map : (algebraMap (𝓞 K) K) xI = iota := rfl
  -- `xI ^ 2 = -1` in `𝓞 K`.
  have hsqOK : (xI : 𝓞 K) ^ 2 = -1 := by
    apply IsFractionRing.injective (𝓞 K) K
    simp only [map_pow, hxI_map, hsq, map_neg, map_one]
  -- `xI` is integral over `𝓞 L`.
  have hintOL : IsIntegral (𝓞 L) xI := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqOK]
  -- Minimal polynomial of `xI` over `𝓞 L` is `X ^ 2 + 1`.
  have hminOL : minpoly (𝓞 L) xI = X ^ 2 + 1 := by
    have htr := minpoly.isIntegrallyClosed_eq_field_fractions L K hintOL
    rw [hxI_map, hmin] at htr
    have hinj : Function.Injective (Polynomial.map (algebraMap (𝓞 L) L)) :=
      Polynomial.map_injective _ (IsFractionRing.injective (𝓞 L) L)
    apply hinj
    rw [← htr]; simp
  -- `xI` generates `K` over `L`.
  have hx : Algebra.adjoin L {(algebraMap (𝓞 K) K) xI} = ⊤ := by
    rw [hxI_map, ← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hadjeq,
      IntermediateField.top_toSubalgebra]
  -- Conductor / different identity: `conductor · 𝔡 = span {2 · xI}`.
  have hcond := conductor_mul_differentIdeal (𝓞 L) L K xI hx
  rw [hminOL] at hcond
  have haeval : (aeval xI) (derivative (X ^ 2 + 1 : (𝓞 L)[X])) = 2 * xI := by
    simp [derivative_pow, map_ofNat]
  rw [haeval] at hcond
  -- Absolute norms.
  have hnorm : Ideal.absNorm (conductor (𝓞 L) xI) *
      Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) =
      Ideal.absNorm (Ideal.span {(2 * xI : 𝓞 K)}) := by
    rw [← map_mul, hcond]
  have hspan : Ideal.absNorm (Ideal.span {(2 * xI : 𝓞 K)}) =
      (Algebra.norm ℤ (2 * xI)).natAbs := Ideal.absNorm_span_singleton _
  -- `xI` is a unit (`xI · (-xI) = 1`).
  have hxIunit : IsUnit (xI : 𝓞 K) := by
    refine isUnit_of_mul_eq_one (-xI) ?_
    have h : xI * (-xI) = -(xI ^ 2) := by ring
    rw [h, hsqOK]; ring
  have hnormval : (Algebra.norm ℤ (2 * xI : 𝓞 K)).natAbs = 2 ^ (Module.finrank ℚ K) := by
    have h2 : Algebra.norm ℤ (2 : 𝓞 K) = 2 ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp]
      rw [Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K) 2,
        Module.finrank_eq_card_chooseBasisIndex]
    have hunit : IsUnit (Algebra.norm ℤ xI) := IsUnit.map (Algebra.norm ℤ) hxIunit
    have hu : (Algebra.norm ℤ xI).natAbs = 1 := by
      rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> rfl
    rw [map_mul, h2, Int.natAbs_mul, hu, mul_one, Int.natAbs_pow]
    rw [NumberField.RingOfIntegers.rank K]
    norm_num
  -- `𝔡`'s norm divides `2 ^ [K:ℚ]`, hence is `≤`.
  have hDdvd : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) ∣ 2 ^ Module.finrank ℚ K := by
    have h := dvd_mul_left (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)))
      (Ideal.absNorm (conductor (𝓞 L) xI))
    rw [hnorm, hspan, hnormval] at h
    exact h
  have hD : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) ≤ 2 ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (by positivity) hDdvd
  -- Tower formula for discriminants.
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    L (𝓞 L) K (𝓞 K)
  rw [hrank2] at htower
  -- Degrees.
  have hnm : Module.finrank ℚ L * 2 = Module.finrank ℚ K := by
    rw [← hrank2]; exact Module.finrank_mul_finrank ℚ L K
  have hm_pos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hn_pos : 0 < Module.finrank ℚ K := by omega
  -- Real abbreviations.
  set n := Module.finrank ℚ K with hn
  set m := Module.finrank ℚ L with hm
  have haL : (0 : ℝ) ≤ ((NumberField.discr L).natAbs : ℝ) := by positivity
  have hdiscK : |(NumberField.discr K : ℝ)| = ((NumberField.discr K).natAbs : ℝ) := by
    rw [Int.cast_natAbs, Int.cast_abs]
  have hdiscL : |(NumberField.discr L : ℝ)| = ((NumberField.discr L).natAbs : ℝ) := by
    rw [Int.cast_natAbs, Int.cast_abs]
  -- Relate `|D_K|` to `D · |D_L|²`.
  have htowerR : |(NumberField.discr K : ℝ)| =
      (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) : ℝ) * |(NumberField.discr L : ℝ)| ^ 2 := by
    rw [hdiscK, hdiscL]
    have := htower
    rw [this]
    push_cast
    ring
  -- Unfold root discriminants.
  simp only [rootDiscriminant, ← hn, ← hm]
  rw [htowerR, hdiscL]
  -- Now: `(D * aL²) ^ (1/n) ≤ 2 * aL ^ (1/m)`.
  set D : ℝ := (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) : ℝ) with hDdef
  set aL : ℝ := ((NumberField.discr L).natAbs : ℝ) with haLdef
  have hDnn : (0 : ℝ) ≤ D := by positivity
  have hDle : D ≤ (2 : ℝ) ^ n := by
    rw [hDdef]; exact_mod_cast hD
  have hbase_nn : (0 : ℝ) ≤ D * aL ^ 2 := by positivity
  have hexp_nn : (0 : ℝ) ≤ (1 : ℝ) / n := by positivity
  -- Step 1: monotonicity.
  have step1 : (D * aL ^ 2) ^ ((1 : ℝ) / n) ≤ ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) := by
    apply Real.rpow_le_rpow hbase_nn _ hexp_nn
    exact mul_le_mul_of_nonneg_right hDle (by positivity)
  -- Step 2: split the product.
  have step2 : ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) =
      ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) * (aL ^ 2) ^ ((1 : ℝ) / n) := by
    apply Real.mul_rpow (by positivity) (by positivity)
  -- Step 3: `(2^n)^(1/n) = 2`.
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have step3 : ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num)]
    rw [mul_one_div, div_self hnR, Real.rpow_one]
  -- Step 4: `(aL²)^(1/n) = aL^(1/m)`.
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have hnm_R : (n : ℝ) = (m : ℝ) * 2 := by exact_mod_cast hnm.symm
  have step4 : (aL ^ 2) ^ ((1 : ℝ) / n) = aL ^ ((1 : ℝ) / m) := by
    rw [← Real.rpow_natCast aL 2, ← Real.rpow_mul haL]
    congr 1
    push_cast
    rw [hnm_R]
    field_simp
  -- Combine.
  calc (D * aL ^ 2) ^ ((1 : ℝ) / n)
      ≤ ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) := step1
    _ = ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) * (aL ^ 2) ^ ((1 : ℝ) / n) := step2
    _ = 2 * aL ^ ((1 : ℝ) / m) := by rw [step3, step4]
