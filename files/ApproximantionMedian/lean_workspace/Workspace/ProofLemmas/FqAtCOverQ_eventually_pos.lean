import Mathlib
import Workspace.ProofLemmas.FqSignAt0Pos
import Workspace.ProofLemmas.FqAtCOverQ_tendsto

open Workspace.ProofLemmas.FqSignAt0Pos

theorem FqAtCOverQ_eventually_pos (c : ℝ) (hc_pos : 0 < c) (hc_lt : c < 1/2) :
    ∀ᶠ q in Filter.atTop, 0 < F_q q (c/q) := by
  have h_tendsto : Filter.Tendsto (fun q : ℝ => F_q q (c/q)) Filter.atTop
      (nhds (1/c - 2)) := FqAtCOverQ_tendsto c hc_pos
  -- Show 1/c - 2 > 0 since c < 1/2
  have h_lim_pos : (0 : ℝ) < 1/c - 2 := by
    have hinv : (2 : ℝ) < 1/c := by
      rw [lt_div_iff₀ hc_pos]
      linarith
    linarith
  exact h_tendsto.eventually_const_lt h_lim_pos
