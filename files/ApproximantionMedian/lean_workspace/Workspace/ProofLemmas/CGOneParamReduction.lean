import Mathlib
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.HSecondDerivative

open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.HSecondDerivative

namespace Workspace.ProofLemmas.CGOneParamReduction

theorem CGOneParamReduction
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (lambda1v : ℝ) (hlam0 : 0 < lambda1v) (hlam1 : lambda1v < 1)
    (delta a : ℝ) (ha1 : a < 1) (n : ℝ) :
    (h_q 2 lambda1v delta 1 = -lambda1v) ∧
    (∀ Na N1 : ℝ, Na + N1 = n → Na * a + N1 = (1 - c) / 2 * n →
      Na = (1 + c) / (2 * (1 - a)) * n ∧ N1 = (1 - 2 * a - c) / (2 * (1 - a)) * n) ∧
    (n ≠ 0 →
      let Na : ℝ := (1 + c) / (2 * (1 - a)) * n
      let N1 : ℝ := (1 - 2 * a - c) / (2 * (1 - a)) * n
      (Na / n) * h_q 2 lambda1v delta a + (N1 / n) * h_q 2 lambda1v delta 1
        = lambda1v / (2 * (1 - a)) * u1delta c delta a) := by
  have h1ma_pos : (0 : ℝ) < 1 - a := by linarith
  have h1ma_ne : (1 : ℝ) - a ≠ 0 := ne_of_gt h1ma_pos
  have h2_1ma_ne : (2 : ℝ) * (1 - a) ≠ 0 := by positivity
  have hinvq_ne : (1 : ℝ) / 2 ≠ 0 := by norm_num
  -- Conjunct 1: h_q at 1 equals -lambda
  have h_q_1 : h_q 2 lambda1v delta 1 = -lambda1v := by
    unfold h_q
    have h1 : (1 - (1 : ℝ)) = 0 := by ring
    rw [h1, Real.zero_rpow hinvq_ne, Real.one_rpow]
    ring
  refine ⟨h_q_1, ?_, ?_⟩
  · -- Conjunct 2: the count system
    intro Na N1 hsum hweighted
    have hNa : Na * (1 - a) = (1 + c) / 2 * n := by
      have : Na * a + N1 = (1 - c) / 2 * n := hweighted
      have hN1 : N1 = n - Na := by linarith
      rw [hN1] at this
      nlinarith [this]
    have hNa_eq : Na = (1 + c) / (2 * (1 - a)) * n := by
      field_simp at hNa ⊢
      linarith [hNa]
    refine ⟨hNa_eq, ?_⟩
    have hN1 : N1 = n - Na := by linarith
    rw [hN1, hNa_eq]
    field_simp
    ring
  · -- Conjunct 3: per-capita identity
    intro hn_ne
    simp only []
    rw [h_q_1]
    unfold h_q u1delta
    field_simp
    ring

end Workspace.ProofLemmas.CGOneParamReduction
