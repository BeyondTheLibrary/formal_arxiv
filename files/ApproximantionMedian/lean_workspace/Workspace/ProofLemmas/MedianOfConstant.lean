import Mathlib
import Workspace.Types.CoordinateMedian

open Workspace.Types.CoordinateMedian

theorem MedianOfConstant {n d : ℕ} (hn : 1 ≤ n) (c : Fin d → ℝ) (m : Fin d → ℝ)
    (h : IsCoordinateMedian m (fun (_ : Fin n) (j : Fin d) => c j)) :
    m = c := by
  funext j
  obtain ⟨hlt, hgt⟩ := h j
  by_contra hne
  rcases lt_or_gt_of_ne hne with hmlt | hmgt
  · -- m j < c j: for every i, c j > m j, so the `>` filter equals univ.
    have hfilter :
        (Finset.univ.filter (fun _ : Fin n => c j > m j)) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact hmlt
    have hcard : (Finset.univ.filter (fun _ : Fin n => c j > m j)).card = n := by
      rw [hfilter]
      simp
    rw [hcard] at hgt
    omega
  · -- m j > c j: for every i, c j < m j, so the `<` filter equals univ.
    have hfilter :
        (Finset.univ.filter (fun _ : Fin n => c j < m j)) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro i _
      exact hmgt
    have hcard : (Finset.univ.filter (fun _ : Fin n => c j < m j)).card = n := by
      rw [hfilter]
      simp
    rw [hcard] at hlt
    omega
