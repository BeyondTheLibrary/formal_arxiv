-- Region-split integrand decay helpers (k = 0 / empty-ℓ case of Lemma 8,
-- arXiv:2412.00674v1, §3, lines 369-381). SORRY-FREE.
--
-- These wrap the per-atom decay bounds with the periodicity reduction needed at
-- the "corner" region of the double integral, where the third frequency
-- ζ = π - η - η' (with |η|, |η'| ≤ 1/3) can fall slightly outside [-π, π].
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.DeletionFactorFourierInR
import Workspace.PriorWork.AltRSumEmptyFourierAssembly
import Workspace.PriorWork.AltRSumEmptyRegionSplit
import Workspace.PriorWork.AltRSumEmptyInnerModulusBound
import Workspace.PriorWork.AltRSumEmptyAtomBounds

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyRegionDecay

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.DeletionFactorFourierInR
open Workspace.PriorWork.AltRSumEmptyFourierAssembly
open Workspace.PriorWork.AltRSumEmptyRegionSplit
open Workspace.PriorWork.AltRSumEmptyInnerModulusBound
open Workspace.PriorWork.AltRSumEmptyAtomBounds

/-- `delAtom3FT` decay on `1/3 ≤ |ζ| ≤ π`. (Restatement of
`delAtom3_FT_modulus_decay` in terms of `delAtom3FT`.) -/
theorem delAtom3FT_decay (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zPlus : ℕ) (ζ : ℝ) (hζπ : |ζ| ≤ Real.pi) (hζ : 1 / 3 ≤ |ζ|) :
    ‖delAtom3FT n δ zPlus ζ‖ ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by
  unfold delAtom3FT
  exact delAtom3_FT_modulus_decay n δ hδ0 hδ zPlus ζ hζπ hζ

/-- `delAtom3FT` global bound. -/
theorem delAtom3FT_global (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) (ζ : ℝ) :
    ‖delAtom3FT n δ zPlus ζ‖ ≤ 1 / (1 - δ) := by
  unfold delAtom3FT
  exact delAtom3_FT_modulus_le_global n δ hδ0 hδ1 zPlus ζ

/-- `delAtom2FT` decay on `1/3 ≤ |ζ| ≤ π`. -/
theorem delAtom2FT_decay (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus : ℕ) (ζ : ℝ) (hζπ : |ζ| ≤ Real.pi) (hζ : 1 / 3 ≤ |ζ|) :
    ‖delAtom2FT n δ zMinus ζ‖ ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) := by
  unfold delAtom2FT
  exact delAtom2_FT_modulus_decay n δ hδ0 hδ zMinus ζ hζπ hζ

/-- `delAtom2FT` global bound. -/
theorem delAtom2FT_global (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) (ζ : ℝ) :
    ‖delAtom2FT n δ zMinus ζ‖ ≤ 1 / (1 - δ) := by
  unfold delAtom2FT
  exact delAtom2_FT_modulus_le_global n δ hδ0 hδ1 zMinus ζ

/-- **Corner decay for `delAtom3FT`.** If `ζ ∈ [π - 2/3, π + 2/3]`, then
`‖delAtom3FT(ζ)‖ ≤ e^{-δz₊/20}/(1-δ)`. Handles the corner of the double integral
where `ζ = π - η - η'` with `|η|, |η'| ≤ 1/3` may slightly exceed `π`; uses
`2π`-periodicity to reduce into `[-π, π]`. -/
theorem delAtom3FT_corner_decay (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zPlus : ℕ) (ζ : ℝ) (hlo : Real.pi - 2 / 3 ≤ ζ) (hhi : ζ ≤ Real.pi + 2 / 3) :
    ‖delAtom3FT n δ zPlus ζ‖ ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by
  have hδ1 : δ < 1 := by linarith
  have hpi : (3 : ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
  by_cases hc : ζ ≤ Real.pi
  · -- ζ ∈ [π - 2/3, π]; |ζ| = ζ ∈ [π - 2/3, π] ⊆ [1/3, π]
    have hζnonneg : 0 ≤ ζ := by linarith
    have habs : |ζ| = ζ := abs_of_nonneg hζnonneg
    apply delAtom3FT_decay n δ hδ0 hδ zPlus ζ
    · rw [habs]; exact hc
    · rw [habs]; linarith
  · -- ζ ∈ (π, π + 2/3]; shift by -2π: ζ' := ζ - 2π ∈ (-π, -π + 2/3]
    push_neg at hc
    have hshift : delAtom3FT n δ zPlus ζ = delAtom3FT n δ zPlus (ζ - 2 * Real.pi) := by
      have := delAtom3FT_periodic n δ zPlus (ζ - 2 * Real.pi)
      rw [show ζ - 2 * Real.pi + 2 * Real.pi = ζ by ring] at this
      exact this
    rw [hshift]
    set ζ' := ζ - 2 * Real.pi with hζ'
    -- ζ' ∈ (-π, -π + 2/3]; ζ' < 0, |ζ'| = -ζ' ∈ [π - 2/3, π)
    have hζ'neg : ζ' < 0 := by rw [hζ']; linarith
    have habs : |ζ'| = -ζ' := abs_of_neg hζ'neg
    apply delAtom3FT_decay n δ hδ0 hδ zPlus ζ'
    · rw [habs, hζ']; linarith
    · rw [habs, hζ']; linarith

end Workspace.PriorWork.AltRSumEmptyRegionDecay
