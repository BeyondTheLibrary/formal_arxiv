import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination
import Workspace.ProofLemmas.GaussianDensityDerivBound

open Workspace.Types.GaussianPDF
open Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

/-- The function `fun x => (L.map (fun p => p.1 * p.2.density x)).sum` is differentiable. -/
private lemma signedComb_aux_diff
    (L : List (ℝ × Workspace.Types.GaussianPDF.GaussianPDF)) :
    Differentiable ℝ (fun x : ℝ => (L.map (fun p => p.1 * p.2.density x)).sum) := by
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact differentiable_const 0
  | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h1 : Differentiable ℝ (fun x : ℝ => p.1 * p.2.density x) := by
        have hG := (GaussianDensityDerivBound p.2).1
        exact hG.const_mul p.1
      exact h1.add ih

/-- The derivative of `fun x => (L.map (fun p => p.1 * p.2.density x)).sum` at `x`
    equals the sum of `p.1 * deriv p.2.density x` over `L`. -/
private lemma signedComb_aux_deriv
    (L : List (ℝ × Workspace.Types.GaussianPDF.GaussianPDF)) (x : ℝ) :
    deriv (fun x : ℝ => (L.map (fun p => p.1 * p.2.density x)).sum) x
      = (L.map (fun p => p.1 * deriv p.2.density x)).sum := by
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil]
      simp [deriv_const]
  | cons p L ih =>
      simp only [List.map_cons, List.sum_cons]
      have h_head_diff : DifferentiableAt ℝ (fun x : ℝ => p.1 * p.2.density x) x := by
        have hG := (GaussianDensityDerivBound p.2).1
        exact (hG.const_mul p.1) x
      have h_tail_diff :
          DifferentiableAt ℝ (fun x : ℝ => (L.map (fun p => p.1 * p.2.density x)).sum) x :=
        signedComb_aux_diff L x
      rw [deriv_fun_add h_head_diff h_tail_diff]
      rw [ih]
      have h_head_deriv : deriv (fun x : ℝ => p.1 * p.2.density x) x
          = p.1 * deriv p.2.density x := by
        rw [deriv_const_mul]
        exact (GaussianDensityDerivBound p.2).1 x
      rw [h_head_deriv]

/-- Bound on the absolute value of the sum of `p.1 * deriv p.2.density x` over `L`. -/
private lemma signedComb_aux_abs_bound
    (L : List (ℝ × Workspace.Types.GaussianPDF.GaussianPDF))
    (ε : ℝ) (hε_pos : 0 < ε)
    (hL_bounds : ∀ p ∈ L, |p.fst| ≤ 1 ∧ ε ^ 12 ≤ p.snd.varSq) (x : ℝ) :
    |(L.map (fun p => p.1 * deriv p.2.density x)).sum| ≤ L.length / ε ^ 12 := by
  have hε12_pos : 0 < ε ^ 12 := by positivity
  induction L with
  | nil =>
      simp only [List.map_nil, List.sum_nil, abs_zero, List.length_nil, Nat.cast_zero]
      positivity
  | cons p L ih =>
      have h_head := hL_bounds p (List.mem_cons_self)
      have h_tail : ∀ q ∈ L, |q.fst| ≤ 1 ∧ ε ^ 12 ≤ q.snd.varSq := by
        intro q hq
        exact hL_bounds q (List.mem_cons_of_mem p hq)
      have ih' := ih h_tail
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      -- Triangle inequality
      have hstep : |p.1 * deriv p.2.density x + (L.map (fun p => p.1 * deriv p.2.density x)).sum|
          ≤ |p.1 * deriv p.2.density x|
            + |(L.map (fun p => p.1 * deriv p.2.density x)).sum| := abs_add_le _ _
      -- Bound the head: |p.1 * deriv p.2.density x| ≤ 1 * (1/p.2.varSq) ≤ 1/ε^12
      have h_head_bound : |p.1 * deriv p.2.density x| ≤ 1 / ε ^ 12 := by
        rw [abs_mul]
        have h_deriv_bound : |deriv p.2.density x| ≤ 1 / p.2.varSq :=
          (GaussianDensityDerivBound p.2).2 x
        have h_p2_pos : 0 < p.2.varSq := p.2.varSq_pos
        have h_p2_ge : ε ^ 12 ≤ p.2.varSq := h_head.2
        have h_inv_le : 1 / p.2.varSq ≤ 1 / ε ^ 12 :=
          one_div_le_one_div_of_le hε12_pos h_p2_ge
        have h_abs_p1_nn : 0 ≤ |p.fst| := abs_nonneg _
        have h_chain1 : |p.fst| * |deriv p.2.density x| ≤ |p.fst| * (1 / p.2.varSq) :=
          mul_le_mul_of_nonneg_left h_deriv_bound h_abs_p1_nn
        have h_chain2 : |p.fst| * (1 / p.2.varSq) ≤ 1 * (1 / p.2.varSq) := by
          have h_inv_pos : 0 ≤ 1 / p.2.varSq := by positivity
          exact mul_le_mul_of_nonneg_right h_head.1 h_inv_pos
        have h_chain3 : (1 : ℝ) * (1 / p.2.varSq) ≤ 1 * (1 / ε ^ 12) :=
          mul_le_mul_of_nonneg_left h_inv_le (by norm_num)
        calc |p.fst| * |deriv p.2.density x|
            ≤ |p.fst| * (1 / p.2.varSq) := h_chain1
          _ ≤ 1 * (1 / p.2.varSq) := h_chain2
          _ ≤ 1 * (1 / ε ^ 12) := h_chain3
          _ = 1 / ε ^ 12 := by ring
      -- Combine
      have h_sum_bound : |p.1 * deriv p.2.density x|
            + |(L.map (fun p => p.1 * deriv p.2.density x)).sum|
            ≤ 1 / ε ^ 12 + L.length / ε ^ 12 := add_le_add h_head_bound ih'
      have h_combine : |p.1 * deriv p.2.density x + (L.map (fun p => p.1 * deriv p.2.density x)).sum|
          ≤ 1 / ε ^ 12 + L.length / ε ^ 12 := le_trans hstep h_sum_bound
      -- The goal is: ... ≤ ↑(L.length + 1) / ε ^ 12
      have h_rhs : (1 : ℝ) / ε ^ 12 + L.length / ε ^ 12 = (L.length + 1 : ℕ) / ε ^ 12 := by
        push_cast
        ring
      rw [h_rhs] at h_combine
      exact h_combine

theorem DerivativeBoundOfSignedCombination
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (ε : ℝ)
    (hε_pos : 0 < ε)
    (hε_le : ε ≤ 2 ^ ((1 : ℝ) / 12))
    (hS_len : S.components.length ≤ 4)
    (hS_bounds : ∀ p ∈ S.components, |p.fst| ≤ 1 ∧ ε ^ 12 ≤ p.snd.varSq) :
    Differentiable ℝ S.density
    ∧ ∀ x : ℝ, |deriv S.density x| ≤ 4 / ε ^ 12 := by
  have hε12_pos : 0 < ε ^ 12 := by positivity
  -- Differentiability
  have h_diff : Differentiable ℝ S.density := by
    show Differentiable ℝ (fun x => (S.components.map (fun p => p.1 * p.2.density x)).sum)
    exact signedComb_aux_diff S.components
  refine ⟨h_diff, ?_⟩
  intro x
  -- Derivative equality
  have h_deriv_eq : deriv S.density x
      = (S.components.map (fun p => p.1 * deriv p.2.density x)).sum := by
    show deriv (fun x => (S.components.map (fun p => p.1 * p.2.density x)).sum) x = _
    exact signedComb_aux_deriv S.components x
  rw [h_deriv_eq]
  have h_aux := signedComb_aux_abs_bound S.components ε hε_pos hS_bounds x
  have h_len : (S.components.length : ℝ) ≤ 4 := by exact_mod_cast hS_len
  have h_inv_pos : 0 < 1 / ε ^ 12 := by positivity
  calc |(S.components.map (fun p => p.1 * deriv p.2.density x)).sum|
      ≤ S.components.length / ε ^ 12 := h_aux
    _ = (S.components.length : ℝ) * (1 / ε ^ 12) := by ring
    _ ≤ 4 * (1 / ε ^ 12) := by
        exact mul_le_mul_of_nonneg_right h_len h_inv_pos.le
    _ = 4 / ε ^ 12 := by ring

end Workspace.ProofLemmas
