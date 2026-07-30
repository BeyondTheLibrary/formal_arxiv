import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI

set_option maxHeartbeats 4000000

open scoped NumberField ComplexConjugate
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Polynomial

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeRankFull (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) = 2 * f := by
  -- `f = [L : ℚ]`.
  have hfL : f = Module.finrank ℚ L := by
    have h1 : Fintype.card (Fin f) = Fintype.card (L →+* ℂ) :=
      Fintype.card_of_bijective sel.restrict_bijective
    rw [Fintype.card_fin] at h1
    rw [h1, NumberField.Embeddings.card L ℂ]
  have hfpos : 0 < f := by rw [hfL]; exact Module.finrank_pos
  -- `[K : L] = 2`.
  obtain ⟨iota, hsq, hadj⟩ := hcm
  have hint : IsIntegral L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsq]⟩
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
  have hmin_deg : (minpoly L iota).natDegree = 2 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := minpoly.dvd L iota (by simp [hsq])
    have h2le : 2 ≤ (minpoly L iota).natDegree := (minpoly.two_le_natDegree_iff hint).mpr hne
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    have hle := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
    omega
  -- `FiniteDimensional L K` (for the tower).
  haveI hfdadj : FiniteDimensional L ↥(IntermediateField.adjoin L {iota}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI hfdK : FiniteDimensional L K := by
    have e : ↥(IntermediateField.adjoin L {iota}) ≃ₐ[L] K :=
      (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
    exact e.toLinearEquiv.finiteDimensional
  have hfrankKL : Module.finrank L K = 2 := by
    have h1 : Module.finrank L ↥(IntermediateField.adjoin L {iota}) = (minpoly L iota).natDegree :=
      IntermediateField.adjoin.finrank hint
    rw [hmin_deg, hadj, IntermediateField.finrank_top'] at h1
    exact h1
  -- `[K : ℚ] = 2f`.
  have hfrankQ : Module.finrank ℚ K = 2 * f := by
    have htower := Module.finrank_mul_finrank ℚ L K
    rw [← hfL, hfrankKL] at htower
    omega
  -- `latticeHom` is injective.
  have hcoord : ∀ (γ : 𝓞 K) (r : Fin f),
      latticeHom sel DD γ r = sel.sigma r (γ : K) * ((DD : ℂ))⁻¹ := by
    intro γ r
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hinj : Function.Injective (latticeHom sel DD) := by
    intro β β' hββ'
    have hDDne : (DD : ℂ)⁻¹ ≠ 0 := by
      apply inv_ne_zero
      exact_mod_cast (by omega : DD ≠ 0)
    obtain ⟨r0⟩ : Nonempty (Fin f) := ⟨⟨0, hfpos⟩⟩
    have h0 := congr_fun hββ' r0
    rw [hcoord β r0, hcoord β' r0] at h0
    have hσ : sel.sigma r0 (β : K) = sel.sigma r0 (β' : K) := mul_right_cancel₀ hDDne h0
    have hβK : (β : K) = (β' : K) := (sel.sigma r0).injective hσ
    exact NumberField.RingOfIntegers.coe_injective hβK
  -- Assemble the ℤ-rank chain.
  have hchain : Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule (lattice sel DD))
      = Module.finrank ℤ (𝓞 K) := by
    have e := AddMonoidHom.ofInjective hinj
    rw [show (AddSubgroup.toIntSubmodule (lattice sel DD) : Submodule ℤ (Fin f → ℂ)) =
        AddSubgroup.toIntSubmodule (latticeHom sel DD).range from rfl]
    exact (LinearEquiv.finrank_eq (AddEquiv.toIntLinearEquiv e)).symm
  rw [hchain, NumberField.RingOfIntegers.rank]
  exact hfrankQ

end MinkowskiLemmas
