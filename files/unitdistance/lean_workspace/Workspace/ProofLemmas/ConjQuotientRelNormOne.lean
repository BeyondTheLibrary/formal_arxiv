import Mathlib
import Workspace.Types.CMAdjoinI

open scoped NumberField
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 2000000

theorem ConjQuotientRelNormOne {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (α : K) (hα : α ≠ 0) :
    relNorm_KL h (α / conjAut h α) = 1 := by
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  -- `iota` is integral, hence algebraic, over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqι]
  have halg : IsAlgebraic L iota := hint.isAlgebraic
  -- `conjAut h (iota)² = -1`, so `conjAut h iota = ± iota`.
  have hcι2 : (conjAut h iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
  have hcases : conjAut h iota = iota ∨ conjAut h iota = -iota := by
    have hfac : (conjAut h iota - iota) * (conjAut h iota + iota) = 0 := by
      have hz : (conjAut h iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
      linear_combination hz
    rcases mul_eq_zero.mp hfac with hh | hh
    · left; exact sub_eq_zero.mp hh
    · right; linear_combination hh
  -- `conjAut h` is an involution on the generator.
  have hinvι : conjAut h (conjAut h iota) = iota := by
    rcases hcases with hh | hh
    · rw [hh, hh]
    · rw [hh, map_neg, hh, neg_neg]
  -- Hence `conjAut h ∘ conjAut h = id`.
  have hadjalg : Algebra.adjoin L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  have hinv : ∀ y : K, conjAut h (conjAut h y) = y := by
    have hEq : ((conjAut h).toAlgHom.comp (conjAut h).toAlgHom) = AlgHom.id L K := by
      apply AlgHom.ext_of_adjoin_eq_top hadjalg
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinvι
    intro y
    have := AlgHom.congr_fun hEq y
    simpa using this
  -- `conjAut h α ≠ 0`.
  have hcαne : conjAut h α ≠ 0 := by
    intro hh
    exact hα ((conjAut h).injective (by rw [hh, map_zero]))
  -- Compute the relative norm.
  unfold relNorm_KL
  rw [map_div₀, hinv α]
  field_simp
