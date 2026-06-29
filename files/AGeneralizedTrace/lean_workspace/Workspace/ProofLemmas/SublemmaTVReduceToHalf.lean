import Mathlib
import Workspace.Types.LowerBoundConstants
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.TraceDist
import Workspace.Types.TVDistance
import Workspace.Types.TraceDistAxioms
import Workspace.ProofLemmas.TraceDistExists
import Workspace.ProofLemmas.TVMonotoneInDelta

open Workspace.Types.LowerBoundConstants
open Workspace.Types.ProbVec
open Workspace.Types.DelProb
open Workspace.Types.TraceDist
open Workspace.Types.TVDistance

/--
`SublemmaTVReduceToHalf`:

Suppose that for a fixed constant bundle `C : LowerBoundConstants` and probability
vectors `S, S' : ProbVec n`, the total-variation bound
`TVDistance(td₁.toPMF, td₂.toPMF) ≤ exp(-C.cTv · √n)` holds for every deletion
probability `δ` in the restricted range `C.cDelta/√n ≤ δ.val ≤ 1/2` (and every
pair of trace distributions). Then the same TV bound holds for every `δ` in the
larger range `C.cDelta/√n ≤ δ.val` (with `δ.val < 1` automatic from `DelProb`).

Proof idea (NL): factor a rate-`δ` deletion channel as the composition of a
rate-`1/2` deletion followed by an additional rate-`q = 2δ - 1` deletion
(`(1/2)·(1-q) = 1-δ`), and apply the data-processing inequality for total
variation under Markov-kernel composition.
-/
theorem SublemmaTVReduceToHalf :
    ∀ (C : LowerBoundConstants) (n : ℕ)
      (S S' : ProbVec n),
      (hcd_half : C.cDelta / Real.sqrt n ≤ 1/2) →
      (∀ δ : DelProb,
         δ.val ≤ 1/2 →
         C.cDelta / Real.sqrt n ≤ δ.val →
         ∀ (td₁ : TraceDist n S δ) (td₂ : TraceDist n S' δ),
           TVDistance td₁.toPMF td₂.toPMF
             ≤ Real.exp (-(C.cTv * Real.sqrt n))) →
      ∀ δ : DelProb,
        C.cDelta / Real.sqrt n ≤ δ.val →
        ∀ (td₁ : TraceDist n S δ) (td₂ : TraceDist n S' δ),
          TVDistance td₁.toPMF td₂.toPMF
            ≤ Real.exp (-(C.cTv * Real.sqrt n)) := by
  intro C n S S' hcd_half H δ hδ td₁ td₂
  by_cases hhalf : δ.val ≤ 1 / 2
  · -- Direct application: H δ provides the bound at the same rate.
    exact H δ hhalf hδ td₁ td₂
  · -- δ.val > 1/2: use tv_monotone_in_delta to drop down to a rate-1/2 witness.
    push_neg at hhalf
    -- Introduce the explicit half-rate DelProb.
    set δ_half : DelProb := Workspace.Types.TraceDistAxioms.halfDelProb with hδhalf
    have hδ_half_val : δ_half.val = (1 : ℝ) / 2 :=
      Workspace.Types.TraceDistAxioms.halfDelProb_val
    -- Subcase on whether C.cDelta/√n ≤ 1/2 (whether the H-range covers δ_half).
    by_cases hcd : C.cDelta / Real.sqrt n ≤ (1 : ℝ) / 2
    · -- Standard regime: H is informative at δ_half.
      -- Build the half-rate trace-distribution witnesses via the nonempty axiom.
      let td_halfS : TraceDist n S δ_half :=
        Classical.choice
          (traceDist_exists S δ_half)
      let td_halfS' : TraceDist n S' δ_half :=
        Classical.choice
          (traceDist_exists S' δ_half)
      -- H at δ_half gives the TV bound for the half-rate pair.
      have h_half_bound :
          TVDistance td_halfS.toPMF td_halfS'.toPMF
            ≤ Real.exp (-(C.cTv * Real.sqrt n)) := by
        refine H δ_half ?_ ?_ td_halfS td_halfS'
        · -- δ_half.val ≤ 1/2
          rw [hδ_half_val]
        · -- C.cDelta / √n ≤ δ_half.val
          rw [hδ_half_val]
          exact hcd
      -- tv_monotone_in_delta: TV at rate δ ≤ TV at rate δ_half (since δ_half ≤ δ).
      have hδle : δ_half.val ≤ δ.val := by
        rw [hδ_half_val]
        linarith
      have h_mono :
          TVDistance td₁.toPMF td₂.toPMF
            ≤ TVDistance td_halfS.toPMF td_halfS'.toPMF :=
        tv_monotone_in_delta hδle
          td_halfS td_halfS' td₁ td₂
      exact le_trans h_mono h_half_bound
    · -- Corner regime: C.cDelta/√n > 1/2.  This contradicts the hypothesis
      -- `hcd_half : C.cDelta/√n ≤ 1/2`, so the branch is vacuous.
      push_neg at hcd
      -- hcd : 1/2 < C.cDelta / √n
      exact absurd hcd_half (not_le.mpr hcd)
