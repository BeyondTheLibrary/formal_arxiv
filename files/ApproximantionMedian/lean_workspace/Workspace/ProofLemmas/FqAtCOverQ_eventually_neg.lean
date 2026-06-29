import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqAtCOverQ_tendsto

open Workspace.ProofLemmas.FqSignAt0Pos

theorem FqAtCOverQ_eventually_neg (c : ℝ) (hc : 1/2 < c) :
    ∀ᶠ q in Filter.atTop, F_q q (c/q) < 0 := by
  have hc_pos : (0 : ℝ) < c := by linarith
  have h_tendsto : Filter.Tendsto (fun q : ℝ => F_q q (c/q)) Filter.atTop
      (nhds (1/c - 2)) := FqAtCOverQ_tendsto c hc_pos
  -- Show 1/c - 2 < 0 since c > 1/2
  have h_lim_neg : 1/c - 2 < (0 : ℝ) := by
    have hinv : 1/c < (2 : ℝ) := by
      rw [div_lt_iff₀ hc_pos]
      linarith
    linarith
  exact h_tendsto.eventually_lt_const h_lim_neg
