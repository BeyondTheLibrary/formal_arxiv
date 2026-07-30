import Mathlib

open Polynomial
open scoped ComplexConjugate

namespace Workspace.Types.CMAdjoinI

set_option maxHeartbeats 400000

/-!
# CM-extension data `K = L(i)`

This file formalises the CM-extension data `K = L(i)` of a totally real number field `L`
(Definition A.4 / Definition 2.1).

* `IsAdjoinI L K` : the predicate that `K` is obtained from `L` by adjoining a square root
  of `-1` (a generator `iota` with `iota ^ 2 = -1` that generates `K` over `L`).
* `conjAut h` : the nontrivial `L`-automorphism `c` of `K`, the complex conjugation sending
  `iota` to `-iota`.
* `relNorm_KL h u` : the relative norm `u * c(u)` as an element of `K`.
-/

section Def

variable (L K : Type*) [Field L] [Field K] [Algebra L K]

/-- `IsAdjoinI L K` holds when `K` is obtained from the field `L` by adjoining a square root
`iota` of `-1`, i.e. there is an element `iota : K` with `iota ^ 2 = -1` generating `K` over
`L`. When `L` is totally real this forces `iota ∉ L`, so `[K : L] = 2` and `K` is a
totally imaginary (CM) field. -/
def IsAdjoinI : Prop :=
  ∃ iota : K, iota ^ 2 = -1 ∧ IntermediateField.adjoin L {iota} = ⊤

end Def

section ConjAut

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K]

/-- The nontrivial `L`-algebra automorphism `c` of `K = L(i)`: the unique element of
`Gal(K/L)` different from the identity, i.e. complex conjugation, sending the chosen square
root `iota` of `-1` to `-iota` while fixing `L`.  It is constructed as the algebra
homomorphism `K → K` determined by sending the generator `iota` to the other root `-iota`
of the minimal polynomial `X ^ 2 + 1`; this map is bijective because `K` is a finite
extension of `L`. -/
noncomputable def conjAut (h : IsAdjoinI L K) : K ≃ₐ[L] K := by
  classical
  set iota := h.choose with hi
  have hsq : iota ^ 2 = -1 := h.choose_spec.1
  have hadj : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  -- `iota` is integral over `L`, being a root of the monic polynomial `X ^ 2 + 1`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota` does not lie in (the image of) `L`, because `L` is totally real.
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
  -- Hence the minimal polynomial of `iota` over `L` is exactly `X ^ 2 + 1`.
  have hmin : minpoly L iota = X ^ 2 + 1 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : L[X]).natDegree ≤ (minpoly L iota).natDegree := by
      have h2 : 2 ≤ (minpoly L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      hdeg).symm
  -- `-iota` is a root of the minimal polynomial.
  have hroot : -iota ∈ (minpoly L iota).aroots K := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [hmin]
    simp [hsq]
  -- The algebra hom `L⟮iota⟯ →ₐ[L] K` sending the generator `iota` to `-iota`.
  let f : IntermediateField.adjoin L {iota} →ₐ[L] K :=
    (IntermediateField.algHomAdjoinIntegralEquiv L hint).symm ⟨-iota, hroot⟩
  -- Identify `L⟮iota⟯` with `K` via `IsAdjoinI`.
  let e : IntermediateField.adjoin L {iota} ≃ₐ[L] K :=
    (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
  let g : K →ₐ[L] K := f.comp e.symm.toAlgHom
  haveI hfd : FiniteDimensional L (IntermediateField.adjoin L {iota}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional L K := e.toLinearEquiv.finiteDimensional
  have hinj : Function.Injective g := g.toRingHom.injective
  refine AlgEquiv.ofBijective g ⟨hinj, ?_⟩
  have hsurj : Function.Surjective (g.toLinearMap) :=
    (LinearMap.injective_iff_surjective).mp hinj
  exact hsurj

/-- The relative norm `N_{K/L}(u) = u * c(u)` as an element of `K`, where `c = conjAut h`.
The paper uses the equation `u * c(u) = 1` in `K` to express that all archimedean absolute
values of a unit `u` are `1`. -/
noncomputable def relNorm_KL (h : IsAdjoinI L K) (u : K) : K := u * conjAut h u

end ConjAut

end Workspace.Types.CMAdjoinI
