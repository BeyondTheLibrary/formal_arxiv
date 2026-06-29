import Mathlib
import Workspace.Types.CoordinateMedian

open Workspace.Types.CoordinateMedian

theorem MedianTranslationInvariance {n d : ℕ} (P : Fin n → Fin d → ℝ) (m t : Fin d → ℝ) :
    IsCoordinateMedian m P ↔
    IsCoordinateMedian (fun j => m j - t j) (fun (i : Fin n) (j : Fin d) => P i j - t j) := by
  unfold IsCoordinateMedian
  refine forall_congr' (fun j => ?_)
  have hlt_set : (Finset.univ.filter (fun i : Fin n => P i j < m j)) =
      (Finset.univ.filter (fun i : Fin n => P i j - t j < m j - t j)) := by
    apply Finset.filter_congr
    intros i _
    exact (sub_lt_sub_iff_right (t j)).symm
  have hgt_set : (Finset.univ.filter (fun i : Fin n => P i j > m j)) =
      (Finset.univ.filter (fun i : Fin n => P i j - t j > m j - t j)) := by
    apply Finset.filter_congr
    intros i _
    exact (sub_lt_sub_iff_right (t j)).symm
  rw [hlt_set, hgt_set]
