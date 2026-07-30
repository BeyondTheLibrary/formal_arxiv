import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.DiscriminantsClassNumber

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

theorem FiberCountToExpBound (d : AdmissibleDatum) (H : ℝ) (hH : 0 < H) (Fcard : ℕ)
    (hh : 0 < classNumber d.K)
    (hfiber : ((2 : ℝ) ^ (d.t * deg d)) / (classNumber d.K : ℝ) ≤ (Fcard : ℝ))
    (hclass : (classNumber d.K : ℝ) ≤ H ^ (deg d)) :
    Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ)) ≤ (Fcard : ℝ) := by
  have hh' : (0 : ℝ) < (classNumber d.K : ℝ) := by exact_mod_cast hh
  have hHf : (0 : ℝ) < H ^ (deg d) := by positivity
  have h2 : (2 : ℝ) ^ (d.t * deg d) = Real.exp (Real.log 2 * (↑(d.t * deg d))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (d.t * deg d), Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  have hHf' : H ^ (deg d) = Real.exp (Real.log H * (↑(deg d))) := by
    rw [← Real.rpow_natCast H (deg d), Real.rpow_def_of_pos hH]
  have hexp : Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ))
      = (2 : ℝ) ^ (d.t * deg d) / H ^ (deg d) := by
    rw [h2, hHf', ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hstep1 : (2 : ℝ) ^ (d.t * deg d) / H ^ (deg d)
      ≤ (2 : ℝ) ^ (d.t * deg d) / (classNumber d.K : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hh' hclass
  exact le_trans hstep1 hfiber
