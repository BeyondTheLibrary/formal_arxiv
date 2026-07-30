import Mathlib
import Workspace.Types.CMAdjoinI

open Polynomial
open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI

theorem SublemmaCMModelExists (L : Type) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K), IsAdjoinI L K := by
  -- -1 is not a square in L (L is totally real)
  have hnsq : ∀ a : L, a ^ 2 ≠ -1 := by
    intro a ha2
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
  -- X^2 + 1 is irreducible over L
  have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
  have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + 1 : L[X]) := by
    by_contra hcon
    rw [Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff hmonic hnd] at hcon
    obtain ⟨c₁, c₂, hc0, hc1⟩ := hcon
    have hcoeff0 : (X ^ 2 + 1 : L[X]).coeff 0 = 1 := by simp
    have hcoeff1 : (X ^ 2 + 1 : L[X]).coeff 1 = 0 := by simp [Polynomial.coeff_one]
    rw [hcoeff0] at hc0
    rw [hcoeff1] at hc1
    exact hnsq c₁ (by linear_combination c₁ * hc1.symm - hc0.symm)
  -- Construct K = L(i) = AdjoinRoot (X^2+1)
  haveI hfact : Fact (Irreducible (X ^ 2 + 1 : L[X])) := ⟨hirr⟩
  set K := AdjoinRoot (X ^ 2 + 1 : L[X]) with hKdef
  have hne : (X ^ 2 + 1 : L[X]) ≠ 0 := hmonic.ne_zero
  haveI : Module.Finite L K := Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  haveI : NumberField K := NumberField.of_module_finite L K
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  · -- IsAdjoinI L K
    refine ⟨AdjoinRoot.root (X ^ 2 + 1 : L[X]), ?_, ?_⟩
    · -- root ^ 2 = -1
      have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : L[X])
      simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
      linear_combination h
    · -- IntermediateField.adjoin L {root} = ⊤
      have htop : Algebra.adjoin L {AdjoinRoot.root (X ^ 2 + 1 : L[X])} = ⊤ :=
        AdjoinRoot.adjoinRoot_eq_top
      have hle := IntermediateField.algebra_adjoin_le_adjoin L
        {AdjoinRoot.root (X ^ 2 + 1 : L[X])}
      rw [htop] at hle
      have htopsub : (IntermediateField.adjoin L
          {AdjoinRoot.root (X ^ 2 + 1 : L[X])}).toSubalgebra = ⊤ :=
        top_le_iff.mp hle
      exact (IntermediateField.toSubalgebra_injective (by rw [htopsub]; rfl))
