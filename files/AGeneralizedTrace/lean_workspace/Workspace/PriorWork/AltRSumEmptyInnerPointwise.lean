-- Pointwise inner-integrand bound for the double-integral region split
-- (k = 0 / empty-ℓ case of Lemma 8, arXiv:2412.00674v1, §3, lines 369-381).
-- SORRY-FREE.
--
-- For the inner integral ∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT((π-η)-η')‖ dη',
-- with |η| ≤ 1/3, we bound the integrand POINTWISE (no domain split needed) by the
-- constant Cinner := (1/(1-δ)) · max(e^{-δz₋/20}/(1-δ), e^{-δz₊/20}/(1-δ)):
--   * if |η'| ≥ 1/3 : delAtom2FT decays (e^{-δz₋/20}/(1-δ)), delAtom3FT ≤ 1/(1-δ);
--   * if |η'| < 1/3 : delAtom2FT ≤ 1/(1-δ), delAtom3FT corner-decays
--       (η₃=(π-η)-η' ∈ [π-2/3,π+2/3], so e^{-δz₊/20}/(1-δ)).
-- Both products are ≤ Cinner.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumEmptyInnerModulusBound
import Workspace.PriorWork.AltRSumEmptyAtomBounds
import Workspace.PriorWork.AltRSumEmptyRegionDecay

set_option maxHeartbeats 1000000

namespace Workspace.PriorWork.AltRSumEmptyInnerPointwise

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression
open Workspace.PriorWork.AltRSumEmptyInnerModulusBound
open Workspace.PriorWork.AltRSumEmptyAtomBounds
open Workspace.PriorWork.AltRSumEmptyRegionDecay

/-- The inner pointwise bound constant. -/
noncomputable def Cinner (δ : ℝ) (zMinus zPlus : ℕ) : ℝ :=
  (1 / (1 - δ)) *
    max (Real.exp (- δ * zMinus / 20) / (1 - δ)) (Real.exp (- δ * zPlus / 20) / (1 - δ))

theorem Cinner_nonneg (δ : ℝ) (hδ1 : δ < 1) (zMinus zPlus : ℕ) :
    0 ≤ Cinner δ zMinus zPlus := by
  unfold Cinner
  have hD : (0:ℝ) < 1 - δ := by linarith
  apply mul_nonneg
  · positivity
  · apply le_max_of_le_left; positivity

/-- **Pointwise inner-integrand bound.** For `|η| ≤ 1/3` and `|η'| ≤ π`,
`‖delAtom2FT(η')‖ · ‖delAtom3FT((π-η)-η')‖ ≤ Cinner`. -/
theorem inner_integrand_le (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hη : |η| ≤ 1 / 3) (η' : ℝ) (hη'π : |η'| ≤ Real.pi) :
    ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖
      ≤ Cinner δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hM2nn : (0:ℝ) ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) := by positivity
  have hM3nn : (0:ℝ) ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) := by positivity
  have hDnn : (0:ℝ) ≤ 1 / (1 - δ) := by positivity
  have hn2 : 0 ≤ ‖delAtom2FT n δ zMinus η'‖ := norm_nonneg _
  have hn3 : 0 ≤ ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖ := norm_nonneg _
  unfold Cinner
  by_cases hcase : 1 / 3 ≤ |η'|
  · -- |η'| ≥ 1/3 : delAtom2 decays, delAtom3 global
    have hb2 : ‖delAtom2FT n δ zMinus η'‖ ≤ Real.exp (- δ * zMinus / 20) / (1 - δ) :=
      delAtom2FT_decay n δ hδ0 hδ zMinus η' hη'π hcase
    have hb3 : ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖ ≤ 1 / (1 - δ) :=
      delAtom3FT_global n δ hδ0.le hδ1 zPlus _
    calc ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖
        ≤ (Real.exp (- δ * zMinus / 20) / (1 - δ)) * (1 / (1 - δ)) :=
          mul_le_mul hb2 hb3 hn3 hM2nn
      _ = (1 / (1 - δ)) * (Real.exp (- δ * zMinus / 20) / (1 - δ)) := by ring
      _ ≤ (1 / (1 - δ)) *
            max (Real.exp (- δ * zMinus / 20) / (1 - δ))
                (Real.exp (- δ * zPlus / 20) / (1 - δ)) := by
          apply mul_le_mul_of_nonneg_left (le_max_left _ _) hDnn
  · -- |η'| < 1/3 : delAtom2 global, delAtom3 corner decay
    push_neg at hcase
    have hb2 : ‖delAtom2FT n δ zMinus η'‖ ≤ 1 / (1 - δ) :=
      delAtom2FT_global n δ hδ0.le hδ1 zMinus η'
    -- η₃ = (π - η) - η' ∈ [π - 2/3, π + 2/3]
    have hηb : -(1/3) ≤ η ∧ η ≤ 1/3 := abs_le.mp hη
    have hη'b : -(1/3) ≤ η' ∧ η' ≤ 1/3 := abs_le.mp (le_of_lt hcase)
    have hlo : Real.pi - 2 / 3 ≤ (Real.pi - η) - η' := by linarith [hηb.2, hη'b.2]
    have hhi : (Real.pi - η) - η' ≤ Real.pi + 2 / 3 := by linarith [hηb.1, hη'b.1]
    have hb3 : ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖
        ≤ Real.exp (- δ * zPlus / 20) / (1 - δ) :=
      delAtom3FT_corner_decay n δ hδ0 hδ zPlus _ hlo hhi
    calc ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖
        ≤ (1 / (1 - δ)) * (Real.exp (- δ * zPlus / 20) / (1 - δ)) :=
          mul_le_mul hb2 hb3 hn3 hDnn
      _ ≤ (1 / (1 - δ)) *
            max (Real.exp (- δ * zMinus / 20) / (1 - δ))
                (Real.exp (- δ * zPlus / 20) / (1 - δ)) := by
          apply mul_le_mul_of_nonneg_left (le_max_right _ _) hDnn

/-! ### Continuity / integrability of the inner integrand -/

theorem delAtom2FT_continuous (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus : ℕ) : Continuous (fun ξ : ℝ => delAtom2FT n δ zMinus ξ) := by
  have h : (fun ξ : ℝ => delAtom2FT n δ zMinus ξ)
      = (fun ξ : ℝ =>
          Workspace.PriorWork.AltRSumEmptyRegionSplit.delFacFTcf (n / 4 : ℤ) δ zMinus ξ) := by
    funext ξ
    exact Workspace.PriorWork.DelAtomPairFTContinuity.delAtom2_FT_eq_cf n δ hδ0 hδ1 zMinus ξ
  rw [h]
  exact Workspace.PriorWork.AltRSumEmptyRegionSplit.delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zMinus

theorem delAtom3FT_continuous (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zPlus : ℕ) : Continuous (fun ξ : ℝ => delAtom3FT n δ zPlus ξ) := by
  have h : (fun ξ : ℝ => delAtom3FT n δ zPlus ξ)
      = (fun ξ : ℝ =>
          Workspace.PriorWork.AltRSumEmptyRegionSplit.delFacFTcf (n / 4 : ℤ) δ zPlus (-ξ)) := by
    funext ξ
    exact Workspace.PriorWork.DelAtomPairFTContinuity.delAtom3_FT_eq_cf n δ hδ0 hδ1 zPlus ξ
  rw [h]
  exact (Workspace.PriorWork.AltRSumEmptyRegionSplit.delFacFTcf_continuous (n / 4 : ℤ) δ hδ0 hδ1 zPlus).comp
    continuous_neg

/-- The inner integrand `η' ↦ ‖delAtom2FT(η')‖·‖delAtom3FT((π-η)-η')‖` is continuous. -/
theorem inner_integrand_continuous (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (η : ℝ) :
    Continuous (fun η' : ℝ =>
      ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖) := by
  apply Continuous.mul
  · exact (delAtom2FT_continuous n δ hδ0 hδ1 zMinus).norm
  · apply Continuous.norm
    exact (delAtom3FT_continuous n δ hδ0 hδ1 zPlus).comp
      (continuous_const.sub continuous_id)

/-- **Inner integral bound.** For `|η| ≤ 1/3`,
`∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT((π-η)-η')‖ dη' ≤ (2π)·Cinner`. -/
theorem inner_integral_le (n : ℕ) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 2)
    (zMinus zPlus : ℕ) (η : ℝ) (hη : |η| ≤ 1 / 3) :
    (∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖)
      ≤ (2 * Real.pi) * Cinner δ zMinus zPlus := by
  have hδ1 : δ < 1 := by linarith
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hcont := inner_integrand_continuous n δ hδ0.le hδ1 zMinus zPlus η
  have hint : IntervalIntegrable
      (fun η' : ℝ => ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hbound : ∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus ((Real.pi - η) - η')‖
      ≤ ∫ _ in (-Real.pi)..Real.pi, Cinner δ zMinus zPlus := by
    apply intervalIntegral.integral_mono_on hπ hint (intervalIntegrable_const)
    intro η' hη'
    rw [Set.mem_Icc] at hη'
    have hη'π : |η'| ≤ Real.pi := abs_le.mpr ⟨hη'.1, hη'.2⟩
    exact inner_integrand_le n δ hδ0 hδ zMinus zPlus η hη η' hη'π
  refine le_trans hbound ?_
  rw [intervalIntegral.integral_const]
  rw [smul_eq_mul]
  rw [show Real.pi - (-Real.pi) = 2 * Real.pi by ring]

/-! ### Global bound on `delAtomPairFT` -/

/-- **Global inner integral bound.** For ANY `ζ`,
`∫_{-π}^{π} ‖delAtom2FT(η')‖·‖delAtom3FT(ζ-η')‖ dη' ≤ (2π)·(1/(1-δ))²`. -/
theorem inner_integral_global_le (n : ℕ) (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (zMinus zPlus : ℕ) (ζ : ℝ) :
    (∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖)
      ≤ (2 * Real.pi) * (1 / (1 - δ)) ^ 2 := by
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have hD : (0:ℝ) < 1 - δ := by linarith
  have hDnn : (0:ℝ) ≤ 1 / (1 - δ) := by positivity
  have hcont : Continuous (fun η' : ℝ =>
      ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖) := by
    apply Continuous.mul
    · exact (delAtom2FT_continuous n δ hδ0 hδ1 zMinus).norm
    · apply Continuous.norm
      exact (delAtom3FT_continuous n δ hδ0 hδ1 zPlus).comp (continuous_const.sub continuous_id)
  have hint : IntervalIntegrable
      (fun η' : ℝ => ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖)
      MeasureTheory.volume (-Real.pi) Real.pi :=
    hcont.intervalIntegrable _ _
  have hbound : ∫ η' in (-Real.pi)..Real.pi,
        ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
      ≤ ∫ _ in (-Real.pi)..Real.pi, (1 / (1 - δ)) ^ 2 := by
    apply intervalIntegral.integral_mono_on hπ hint (intervalIntegrable_const)
    intro η' _
    have hb2 : ‖delAtom2FT n δ zMinus η'‖ ≤ 1 / (1 - δ) :=
      delAtom2FT_global n δ hδ0 hδ1 zMinus η'
    have hb3 : ‖delAtom3FT n δ zPlus (ζ - η')‖ ≤ 1 / (1 - δ) :=
      delAtom3FT_global n δ hδ0 hδ1 zPlus _
    calc ‖delAtom2FT n δ zMinus η'‖ * ‖delAtom3FT n δ zPlus (ζ - η')‖
        ≤ (1 / (1 - δ)) * (1 / (1 - δ)) := mul_le_mul hb2 hb3 (norm_nonneg _) hDnn
      _ = (1 / (1 - δ)) ^ 2 := by ring
  refine le_trans hbound ?_
  rw [intervalIntegral.integral_const, smul_eq_mul,
      show Real.pi - (-Real.pi) = 2 * Real.pi by ring]

end Workspace.PriorWork.AltRSumEmptyInnerPointwise
