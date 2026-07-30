import Mathlib
import Workspace.Types.CMAdjoinI

open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 2000000

theorem ConjIsComplexConjugationUnderEmbedding {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (σ : K →+* ℂ) (x : K) :
    σ (conjAut h x) = (starRingEnd ℂ) (σ x) := by
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqι]
  have halg : IsAlgebraic L iota := hint.isAlgebraic
  have hadjalg : Algebra.adjoin L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  -- The crux: `conjAut h` sends `iota` to `-iota`.
  have hci : conjAut h iota = -iota := by
    have hgen : ((IntermediateField.equivOfEq hadjι).trans
        IntermediateField.topEquiv).symm iota
        = IntermediateField.AdjoinSimple.gen L iota := by
      apply Subtype.ext
      simp [IntermediateField.AdjoinSimple.gen]
    unfold conjAut
    simp only [AlgEquiv.ofBijective_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe]
    erw [hgen, IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
  -- `L` totally real: `σ` restricted to `L` has real image.
  have hreal : ∀ l : L, (starRingEnd ℂ) (σ (algebraMap L K l)) = σ (algebraMap L K l) := by
    intro l
    have hr : NumberField.ComplexEmbedding.IsReal (σ.comp (algebraMap L K)) :=
      NumberField.IsTotallyReal.complexEmbedding_isReal _
    have he : NumberField.ComplexEmbedding.conjugate (σ.comp (algebraMap L K))
        = σ.comp (algebraMap L K) :=
      NumberField.ComplexEmbedding.isReal_iff.mp hr
    have := RingHom.congr_fun he l
    rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this
  -- Give `ℂ` the `L`-algebra structure induced by `σ|_L`.
  letI algLC : Algebra L ℂ := (σ.comp (algebraMap L K)).toAlgebra
  have halgmap : ∀ l : L, algebraMap L ℂ l = σ (algebraMap L K l) := fun _ => rfl
  -- Two `L`-algebra homs `K →ₐ[L] ℂ`: `σ ∘ conjAut h` and `conj ∘ σ`.
  let ψ₁ : K →ₐ[L] ℂ :=
    { σ.comp (conjAut h).toRingHom with
      commutes' := fun l => by
        show σ (conjAut h (algebraMap L K l)) = algebraMap L ℂ l
        rw [(conjAut h).commutes l]; exact (halgmap l).symm }
  let ψ₂ : K →ₐ[L] ℂ :=
    { (starRingEnd ℂ).comp σ with
      commutes' := fun l => by
        show (starRingEnd ℂ) (σ (algebraMap L K l)) = algebraMap L ℂ l
        rw [hreal l]; exact (halgmap l).symm }
  have hψ : ψ₁ = ψ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hadjalg
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    show σ (conjAut h iota) = (starRingEnd ℂ) (σ iota)
    rw [hci, map_neg]
    -- `σ iota` is purely imaginary (its square is `-1`), so `conj (σ iota) = -(σ iota)`.
    have hz2 : (σ iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
    have hre : (σ iota).re = 0 := by
      have h1 : ((σ iota) ^ 2).im = 0 := by rw [hz2]; simp
      have h2 : ((σ iota) ^ 2).re = -1 := by rw [hz2]; simp
      simp only [pow_two, Complex.mul_re, Complex.mul_im] at h1 h2
      nlinarith [sq_nonneg (σ iota).re, sq_nonneg (σ iota).im, h1, h2]
    apply Complex.ext
    · simp [Complex.conj_re, hre]
    · simp [Complex.conj_im]
  have := AlgHom.congr_fun hψ x
  simpa using this
