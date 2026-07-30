import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

open scoped NumberField
open scoped ComplexConjugate
open Workspace.Types.MinkowskiWindow Workspace.Types.CMAdjoinI

open Polynomial

namespace Workspace.ProofLemmas

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Step 1 (Lemma 2.6, norm-product identity).**  In the CM setting `K = L(i)`
(`hcm : IsAdjoinI L K`), for every nonzero algebraic integer `β ∈ 𝓞 K` the product of the
moduli of the images of `β` under the `f` selected complex embeddings equals the square root of
the absolute value of the field norm `N_{K/ℚ}(β)`, and this quantity is at least `1`:
`∏ r, ‖σ_r β‖ = √|N_{K/ℚ}(β)| ≥ 1`. -/
theorem SublemmaNormProduct (hcm : IsAdjoinI L K) (sel : EmbeddingSelection L K f)
    (β : 𝓞 K) (hβ : β ≠ 0) :
    (∏ r, ‖sel.sigma r (β : K)‖) = Real.sqrt (|Algebra.norm ℚ (β : K)|)
      ∧ 1 ≤ ∏ r, ‖sel.sigma r (β : K)‖ := by
  classical
  obtain ⟨iota, hsq, hadj⟩ := hcm
  -- Every complex embedding of `K` is non-real (it sends `iota` to `±i`).
  have hemb : ∀ φ : K →+* ℂ, ¬ NumberField.ComplexEmbedding.IsReal φ := by
    intro φ hφ
    have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
      (NumberField.ComplexEmbedding.isReal_iff).mp hφ
    have hI : (φ iota) ^ 2 = -1 := by rw [← map_pow, hsq, map_neg, map_one]
    have hconj : (starRingEnd ℂ) (φ iota) = φ iota := by
      have h2 := RingHom.congr_fun h1 iota
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hz2 : (φ iota) * (starRingEnd ℂ) (φ iota) = ((Complex.normSq (φ iota) : ℝ) : ℂ) :=
      Complex.mul_conj _
    rw [hconj, ← pow_two, hI] at hz2
    have hcast : Complex.normSq (φ iota) = -1 := by exact_mod_cast hz2.symm
    have hnn := Complex.normSq_nonneg (φ iota)
    linarith
  -- Hence `K` is totally complex.
  haveI htc : NumberField.IsTotallyComplex K := by
    apply NumberField.IsTotallyComplex.mk
    intro v
    rw [NumberField.InfinitePlace.isComplex_iff]
    exact hemb v.embedding
  -- `iota` is integral over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota ∉ L` because `L` is totally real.
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
  -- Minimal polynomial of `iota` over `L` is `X² + 1`, so `[K : L] = 2`.
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
  have hnd : (minpoly L iota).natDegree = 2 := by rw [hmin]; compute_degree!
  have hfinLK : Module.finrank L K = 2 := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [hnd, hadj, IntermediateField.finrank_top'] at h1
    exact h1
  -- `[L : ℚ] = f` from the bijection of restrictions.
  have hcard_emb : f = Fintype.card (L →+* ℂ) := by
    have := Fintype.card_of_bijective sel.restrict_bijective
    simpa using this
  have hfinL : Module.finrank ℚ L = f := by
    rw [← NumberField.Embeddings.card L ℂ, ← hcard_emb]
  have hfinK : Module.finrank ℚ K = 2 * f := by
    have htower := Module.finrank_mul_finrank ℚ L K
    rw [hfinL, hfinLK] at htower
    omega
  have hcardIP : Fintype.card (NumberField.InfinitePlace K) = f := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
    have hf2 := NumberField.IsTotallyComplex.finrank K
    rw [hfinK] at hf2
    omega
  -- The map `r ↦ mk (σ_r)` is a bijection `Fin f ≃ InfinitePlace K`.
  set W : Fin f → NumberField.InfinitePlace K :=
    fun r => NumberField.InfinitePlace.mk (sel.sigma r) with hW
  have hWinj : Function.Injective W := by
    intro r r' h
    rw [hW] at h
    simp only at h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have hrestr : (sel.sigma r).comp (algebraMap L K) = (sel.sigma r').comp (algebraMap L K) := by
      rcases h with h | h
      · rw [h]
      · ext x
        have hreal := sel.restrict_isReal r
        have hri : NumberField.ComplexEmbedding.conjugate ((sel.sigma r).comp (algebraMap L K))
            = (sel.sigma r).comp (algebraMap L K) :=
          (NumberField.ComplexEmbedding.isReal_iff).mp hreal
        have h2 := RingHom.congr_fun hri x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
        rw [← h]
        simp only [RingHom.comp_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        exact h2.symm
    exact sel.restrict_bijective.injective hrestr
  have hWbij : Function.Bijective W :=
    (Fintype.bijective_iff_injective_and_card W).mpr
      ⟨hWinj, by rw [Fintype.card_fin, hcardIP]⟩
  -- The product-of-moduli squared equals |N|.
  have e2 : ∏ r, (W r) (β : K) ^ (W r).mult = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [Function.Bijective.prod_comp hWbij (fun w => w (β : K) ^ w.mult)]
    exact NumberField.InfinitePlace.prod_eq_abs_norm _
  have e3 : ∏ r, ‖sel.sigma r (β : K)‖ ^ 2 = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [← e2]
    apply Finset.prod_congr rfl
    intro r _
    rw [hW]
    simp only [NumberField.InfinitePlace.apply, NumberField.IsTotallyComplex.mult_eq]
  have hnn : (0 : ℝ) ≤ ∏ r, ‖sel.sigma r (β : K)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hsq_eq : (∏ r, ‖sel.sigma r (β : K)‖) ^ 2 = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [← Finset.prod_pow]; exact e3
  have hpart1 : (∏ r, ‖sel.sigma r (β : K)‖) = Real.sqrt (|(↑(Algebra.norm ℚ (β : K)) : ℝ)|) := by
    rw [← Rat.cast_abs, ← hsq_eq, Real.sqrt_sq hnn]
  refine ⟨hpart1, ?_⟩
  rw [hpart1]
  -- `|N| ≥ 1` since `β` is a nonzero algebraic integer.
  have hNint : (Algebra.norm ℤ β) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hβ
  have hge1 : (1 : ℝ) ≤ |(↑(Algebra.norm ℚ (β : K)) : ℝ)| := by
    rw [← Rat.cast_abs]
    have h0 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hNint
    have hq : (1 : ℚ) ≤ |Algebra.norm ℚ (β : K)| := by
      rw [← Algebra.coe_norm_int β, ← Int.cast_abs]
      exact_mod_cast h0
    exact_mod_cast hq
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (|(↑(Algebra.norm ℚ (β : K)) : ℝ)|) := Real.sqrt_le_sqrt hge1

end MinkowskiLemmas

end Workspace.ProofLemmas
