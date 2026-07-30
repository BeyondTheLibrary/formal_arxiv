import Mathlib
import Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem Thm23RadiusChoice (γ : ℝ) (hγ : 0 < γ) :
    ∃ R : ℝ, 1 / 2 < R ∧ 1 ≤ R ∧ Real.log (rho R) > -γ / 2 := by
  -- `c := e^{-γ/4} < 1`.
  set c : ℝ := Real.exp (-γ / 4) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    rw [hcdef]
    have := Real.exp_lt_exp.mpr (show -γ / 4 < 0 by linarith)
    rwa [Real.exp_zero] at this
  have h1c : 0 < 1 - c := by linarith
  -- Choose `R` large.
  set R : ℝ := 1 + 1 / (2 * (1 - c)) with hRdef
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    have hpos : 0 < 1 / (2 * (1 - c)) := by positivity
    linarith
  have hRhalf : 1 / 2 < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  -- volume of a complex closed ball as a real.
  have hcbvol : ∀ (cc : ℂ) (ρ : ℝ), 0 ≤ ρ →
      (volume (Metric.closedBall cc ρ)).toReal = Real.pi * ρ ^ 2 := by
    intro cc ρ hρ
    rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρ, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  -- overlap contains the ball of radius `R - 1/2` centred at `1/2`.
  have hsub : Metric.closedBall (1 / 2 : ℂ) (R - 1 / 2) ⊆
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    have h0 : dist (1 / 2 : ℂ) 0 = 1 / 2 := by simp
    have h1 : dist (1 / 2 : ℂ) 1 = 1 / 2 := by rw [Complex.dist_eq]; norm_num
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall]
      calc dist w 0 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 0 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h0]; exact add_le_add hw le_rfl
        _ = R := by ring
    · rw [Metric.mem_closedBall]
      calc dist w 1 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 1 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h1]; exact add_le_add hw le_rfl
        _ = R := by ring
  have hne : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
    rw [Complex.volume_closedBall]; finiteness
  -- overlapArea lower bound.
  have hoverlap_lb : Real.pi * (R - 1 / 2) ^ 2 ≤ overlapArea R := by
    rw [overlapArea, ← hcbvol (1 / 2) (R - 1 / 2) (by linarith)]
    exact ENNReal.toReal_mono hne (measure_mono hsub)
  -- `rho R ≥ (1 - 1/(2R))²`.
  have hrho_lb : (1 - 1 / (2 * R)) ^ 2 ≤ rho R := by
    rw [rho, discArea, le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi * R ^ 2)]
    calc (1 - 1 / (2 * R)) ^ 2 * (Real.pi * R ^ 2)
          = Real.pi * (R - 1 / 2) ^ 2 := by field_simp
      _ ≤ overlapArea R := hoverlap_lb
  -- `c < 1 - 1/(2R)`.
  have hlin : c < 1 - 1 / (2 * R) := by
    have h2R : 0 < 2 * R := by positivity
    have hkey : (1 - c) * (2 * R) = 2 * (1 - c) + 1 := by rw [hRdef]; field_simp
    rw [lt_sub_comm, div_lt_iff₀ h2R, hkey]
    linarith
  -- `rho R > e^{-γ/2}`.
  have hrho_gt : Real.exp (-γ / 2) < rho R := by
    have hsq : c ^ 2 < (1 - 1 / (2 * R)) ^ 2 :=
      pow_lt_pow_left₀ hlin hc0.le (by norm_num)
    have hcsq : c ^ 2 = Real.exp (-γ / 2) := by
      rw [hcdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc Real.exp (-γ / 2) = c ^ 2 := hcsq.symm
      _ < (1 - 1 / (2 * R)) ^ 2 := hsq
      _ ≤ rho R := hrho_lb
  refine ⟨R, hRhalf, hR1, ?_⟩
  have := Real.log_lt_log (Real.exp_pos _) hrho_gt
  rwa [Real.log_exp] at this
