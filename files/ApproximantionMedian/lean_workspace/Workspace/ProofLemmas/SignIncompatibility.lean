import Mathlib
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.InteriorFOC_Pos
import Workspace.ProofLemmas.InteriorFOC_Neg
import Workspace.ProofLemmas.RightBoundary_ForcesC0

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.ConstrainedMinExists

/-- **Sign Incompatibility lemma.**

Under the same hypotheses as `Claim1_RuleOutInterior`, with
`lqNorm q (p_star - f) > 0` and `lqNorm q p_star > 0`, the following two
conditions cannot both hold simultaneously:

* (P) there exists `j` with `σ j = +1`, `p_star j ≥ f j`, and `f j > 0`;
* (N) there exists `i` with `σ i = -1`, `p_star i < 0`, and `f i > 0`.

Paper reference: `approx.tex` lines 103–106; Block 4, Steps 4.1–4.3
(Gravin & Jia, *Approximation guarantees of Median Mechanism in ℝ^d*,
arXiv:2502.08578v2). -/
theorem SignIncompatibility
    (q : ℝ) (hq : 1 < q) (lambda : ℝ) (hlam0 : 0 < lambda) (hlam1 : lambda < 1)
    {d : ℕ} (hd : 1 ≤ d) (f : Fin d → ℝ)
    (hf_nn : ∀ j, 0 ≤ f j) (hf_sum : (∑ j, (f j) ^ q) = 1)
    (sigma : Fin d → ℝ) (hsigma_pm : ∀ j, sigma j = 1 ∨ sigma j = -1)
    (p_star : Fin d → ℝ)
    (hp_in : ∀ j, (sigma j = 1 → 0 ≤ p_star j) ∧ (sigma j = -1 → p_star j ≤ 0))
    (hp_loc :
      ∃ ε > (0 : ℝ),
        ∀ p : Fin d → ℝ,
          (∀ j, (sigma j = 1 → 0 ≤ p j) ∧ (sigma j = -1 → p j ≤ 0)) →
          (∀ j, |p j - p_star j| < ε) →
          g_lambda q lambda f p_star ≤ g_lambda q lambda f p)
    (hpf_pos : 0 < lqNorm q (fun k => p_star k - f k))
    (hp_pos : 0 < lqNorm q p_star) :
    ¬ ((∃ j : Fin d, sigma j = 1 ∧ f j ≤ p_star j ∧ 0 < f j) ∧
       (∃ i : Fin d, sigma i = -1 ∧ p_star i < 0 ∧ 0 < f i)) := by
  -- Take the assumption and break it down
  intro ⟨⟨j, hsig_j, hfj_le, hfj_pos⟩, ⟨i, hsig_i, hpi_neg, hfi_pos⟩⟩
  -- Notation
  have hq1 : 0 < q - 1 := by linarith
  have hN_pos : 0 < lqNorm q (fun k => p_star k - f k) := hpf_pos
  have hM_pos : 0 < lqNorm q p_star := hp_pos
  have hNqm1_pos : 0 < (lqNorm q (fun k => p_star k - f k)) ^ (q - 1) :=
    Real.rpow_pos_of_pos hN_pos _
  have hMqm1_pos : 0 < (lqNorm q p_star) ^ (q - 1) :=
    Real.rpow_pos_of_pos hM_pos _
  have hNqm1_ne : (lqNorm q (fun k => p_star k - f k)) ^ (q - 1) ≠ 0 := ne_of_gt hNqm1_pos
  have hMqm1_ne : (lqNorm q p_star) ^ (q - 1) ≠ 0 := ne_of_gt hMqm1_pos
  -- p_star j ≥ 0 from orthant
  have hpj_nn : 0 ≤ p_star j := (hp_in j).1 hsig_j
  -- p_star j ≥ f j > 0
  have hpj_pos : 0 < p_star j := lt_of_lt_of_le hfj_pos hfj_le
  -- Case split on whether f j = p_star j or f j < p_star j
  rcases lt_or_eq_of_le hfj_le with hfj_lt | hfj_eq
  · -- Case A: f j < p_star j (interior)
    -- Apply InteriorFOC_Pos
    have h_pos := InteriorFOC_Pos q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
      sigma hsigma_pm p_star hp_in hp_loc hpf_pos hp_pos j hsig_j hfj_lt
    -- Apply InteriorFOC_Neg
    have h_neg := InteriorFOC_Neg q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
      sigma hsigma_pm p_star hp_in hp_loc hpf_pos hp_pos i hsig_i hpi_neg
    -- Positive branch: derive (p_star j - f j)^(q-1) / p_star j^(q-1) = lambda * N^(q-1) / M^(q-1)
    have hpfj_pos : 0 < p_star j - f j := sub_pos.mpr hfj_lt
    have hpj_qm1_pos : 0 < p_star j ^ (q - 1) := Real.rpow_pos_of_pos hpj_pos _
    have hpfj_qm1_pos : 0 < (p_star j - f j) ^ (q - 1) := Real.rpow_pos_of_pos hpfj_pos _
    have hpj_qm1_ne : p_star j ^ (q - 1) ≠ 0 := ne_of_gt hpj_qm1_pos
    have hpfj_qm1_ne : (p_star j - f j) ^ (q - 1) ≠ 0 := ne_of_gt hpfj_qm1_pos
    -- Negative branch positivities
    have hmpi_pos : 0 < -p_star i := neg_pos.mpr hpi_neg
    have h_diff_pos : 0 < f i - p_star i := by linarith
    have h_diff_gt : -p_star i < f i - p_star i := by linarith
    have hmpi_qm1_pos : 0 < (-p_star i) ^ (q - 1) := Real.rpow_pos_of_pos hmpi_pos _
    have h_diff_qm1_pos : 0 < (f i - p_star i) ^ (q - 1) := Real.rpow_pos_of_pos h_diff_pos _
    have hmpi_qm1_ne : (-p_star i) ^ (q - 1) ≠ 0 := ne_of_gt hmpi_qm1_pos
    -- Step 1: rewrite h_pos and h_neg as: ratio of differences = K
    -- where K = lambda * N^(q-1) / M^(q-1)
    -- From h_pos:
    --   (p_star j - f j)^(q-1) / N^(q-1) = lambda * (p_star j^(q-1) / M^(q-1))
    -- Multiply both sides by N^(q-1) / p_star j^(q-1):
    --   (p_star j - f j)^(q-1) / p_star j^(q-1) = lambda * N^(q-1) / M^(q-1)
    set N := lqNorm q (fun k => p_star k - f k)
    set M := lqNorm q p_star
    -- Make K explicit
    set K := lambda * N ^ (q - 1) / M ^ (q - 1) with hK_def
    have hK_pos : 0 < K := by rw [hK_def]; positivity
    -- Convert h_pos to (p_star j - f j)^(q-1) / p_star j^(q-1) = K
    have h_pos_K : (p_star j - f j) ^ (q - 1) / p_star j ^ (q - 1) = K := by
      have hN_ne : N ^ (q - 1) ≠ 0 := hNqm1_ne
      have hM_ne : M ^ (q - 1) ≠ 0 := hMqm1_ne
      rw [hK_def]
      field_simp
      have h := h_pos
      field_simp at h
      linarith
    -- Inequality: (p_star j - f j)^(q-1) / p_star j^(q-1) < 1
    have h_lt_one : (p_star j - f j) ^ (q - 1) / p_star j ^ (q - 1) < 1 := by
      rw [div_lt_one hpj_qm1_pos]
      apply Real.rpow_lt_rpow (le_of_lt hpfj_pos) _ hq1
      linarith
    have hK_lt_one : K < 1 := h_pos_K ▸ h_lt_one
    -- Convert h_neg to (f i - p_star i)^(q-1) / (-p_star i)^(q-1) = K
    have h_neg_K : (f i - p_star i) ^ (q - 1) / (-p_star i) ^ (q - 1) = K := by
      have hN_ne : N ^ (q - 1) ≠ 0 := hNqm1_ne
      have hM_ne : M ^ (q - 1) ≠ 0 := hMqm1_ne
      rw [hK_def]
      field_simp
      have h := h_neg
      field_simp at h
      linarith
    have h_gt_one : 1 < (f i - p_star i) ^ (q - 1) / (-p_star i) ^ (q - 1) := by
      rw [lt_div_iff₀ hmpi_qm1_pos, one_mul]
      apply Real.rpow_lt_rpow (le_of_lt hmpi_pos) h_diff_gt hq1
    have hK_gt_one : 1 < K := h_neg_K ▸ h_gt_one
    linarith
  · -- Case B: f j = p_star j, use RightBoundary_ForcesC0
    have h_eq : p_star j = f j := hfj_eq.symm
    have h_zero := RightBoundary_ForcesC0 q hq lambda hlam0 hlam1 hd f hf_nn hf_sum
      sigma hsigma_pm p_star hp_in hp_loc hpf_pos hp_pos j hsig_j h_eq hfj_pos
    -- h_zero : lqNorm q (fun k => p_star k - f k) = 0
    -- Contradicts hpf_pos
    rw [h_zero] at hpf_pos
    exact lt_irrefl 0 hpf_pos
