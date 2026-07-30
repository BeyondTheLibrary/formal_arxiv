import Mathlib
import Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem SublemmaWindowVolume {f : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    volume (window (f := f) R) = ENNReal.ofReal (discArea R ^ f) := by
  -- `window R` is the product of `f` closed discs of radius `R` centred at `0`.
  have hwin : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext z
    simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  rw [hwin, volume_pi, Measure.pi_pi]
  simp only [Complex.volume_closedBall]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [discArea, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ Real.pi * R ^ 2)]
  congr 1
  have hpi : (↑NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_mul Real.pi_nonneg, ← ENNReal.ofReal_pow hR, hpi, mul_comm]
