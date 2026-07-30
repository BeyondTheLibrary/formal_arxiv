import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI

open scoped NumberField
open scoped ComplexConjugate
open Polynomial
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

/-- **SublemmaDegKQ.** For an admissible datum `d` with totally real base field `L = d.L`
and CM extension `K = d.K = L(i)`, the degree of `K` over `ℚ` is twice the base-field
degree `f = deg d = dim_ℚ L`, i.e. `Module.finrank ℚ d.K = 2 * deg d`. -/
theorem SublemmaDegKQ (d : AdmissibleDatum) :
    Module.finrank ℚ d.K = 2 * deg d := by
  classical
  -- Abbreviations for the two fields.
  set L := d.L
  set K := d.K
  -- The generator `iota` of `K` over `L` with `iota ^ 2 = -1`.
  set iota := d.h_adjoin.choose with hi
  have hsq : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
  have hadj : IntermediateField.adjoin L {iota} = ⊤ := d.h_adjoin.choose_spec.2
  -- `iota` is integral over `L`, being a root of `X ^ 2 + 1`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota` does not lie in `L`, because `L` is totally real.
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
  -- The minimal polynomial of `iota` over `L` has degree exactly `2`.
  have hdeg2 : (minpoly L iota).natDegree = 2 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hnz : (X ^ 2 + 1 : L[X]) ≠ 0 := by
      intro hz
      have : (X ^ 2 + 1 : L[X]).natDegree = 0 := by rw [hz]; simp
      have h2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    have hle : (minpoly L iota).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hnz
      have h2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    have hge : 2 ≤ (minpoly L iota).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr hne
    omega
  -- Hence `[K : L] = 2`.
  have hKL : Module.finrank L K = 2 := by
    have hadjfr := IntermediateField.adjoin.finrank hint
    rw [hadj, IntermediateField.finrank_top'] at hadjfr
    rw [hadjfr, hdeg2]
  -- Tower law: `[K : ℚ] = [L : ℚ] * [K : L]`.
  have htower := Module.finrank_mul_finrank ℚ L K
  rw [hKL] at htower
  -- Conclude.
  rw [deg, ← htower]
  ring
