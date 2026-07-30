import Mathlib
import Workspace.Types.MinkowskiWindow

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem SublemmaArithmeticBound {f : ℕ} (R : ℝ) (hR : 1 / 2 < R) (γ : ℝ) (hγ : 0 < γ)
    (U : Finset (Fin f → ℂ)) (hU_card : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ)))
    (hρ : Real.log (rho R) > -γ / 2) :
    (U.card : ℝ) * rho R ^ f ≥ Real.exp (γ * (f : ℝ) / 2) := by
  -- Geometric positivity of `rho R` (independent of `hρ`).
  have hRpos : (0 : ℝ) < R := by linarith
  have hε : (0 : ℝ) < R - 1 / 2 := by linarith
  have hdisc_pos : 0 < discArea R := by
    rw [discArea]; exact mul_pos Real.pi_pos (pow_pos hRpos 2)
  -- the sub-disc centred at 1/2 sits inside the overlap
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
  have hball_pos : (0 : ENNReal) < volume (Metric.closedBall (1 / 2 : ℂ) (R - 1 / 2)) :=
    Metric.measure_closedBall_pos volume (1 / 2 : ℂ) hε
  have hvol_pos : (0 : ENNReal) <
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) :=
    lt_of_lt_of_le hball_pos (measure_mono hsub)
  have hvol_ne_top : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
    rw [Complex.volume_closedBall]; finiteness
  have hoverlap_pos : 0 < overlapArea R := by
    rw [overlapArea]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_ne_top
  have hrho_pos : 0 < rho R := by
    rw [rho]; exact div_pos hoverlap_pos hdisc_pos
  -- `rho R ^ f = exp (f * log (rho R))`
  have hrf : Real.exp ((f : ℝ) * Real.log (rho R)) = rho R ^ f := by
    rw [Real.exp_nat_mul, Real.exp_log hrho_pos]
  -- lower bound on `rho R ^ f`
  have h2 : Real.exp ((f : ℝ) * (-γ / 2)) ≤ rho R ^ f := by
    rw [← hrf, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hρ.le (Nat.cast_nonneg f)
  -- combine with the cardinality bound
  have hprod : Real.exp (γ * (f : ℝ)) * Real.exp ((f : ℝ) * (-γ / 2)) ≤
      (U.card : ℝ) * rho R ^ f :=
    mul_le_mul hU_card h2 (Real.exp_pos _).le (Nat.cast_nonneg _)
  calc Real.exp (γ * (f : ℝ) / 2)
      = Real.exp (γ * (f : ℝ)) * Real.exp ((f : ℝ) * (-γ / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ (U.card : ℝ) * rho R ^ f := hprod
