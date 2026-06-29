import Mathlib
import Workspace.Types.CoordinateMedian

open Workspace.Types.CoordinateMedian

theorem MedianCoordinateReflection {n d : ℕ} (P : Fin n → Fin d → ℝ)
    (eps : Fin d → ℝ) (heps : ∀ j, eps j = 1 ∨ eps j = -1)
    (h : IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ)) P) :
    IsCoordinateMedian (fun (_ : Fin d) => (0 : ℝ))
      (fun (i : Fin n) (j : Fin d) => eps j * P i j) := by
  intro j
  rcases heps j with h1 | h1
  · -- eps j = 1: predicate is unchanged.
    have heq : ∀ i, eps j * P i j = P i j := fun i => by rw [h1]; ring
    have h_lt : (Finset.univ.filter (fun i : Fin n => eps j * P i j < 0)) =
                (Finset.univ.filter (fun i : Fin n => P i j < 0)) := by
      ext i
      simp [heq i]
    have h_gt : (Finset.univ.filter (fun i : Fin n => eps j * P i j > 0)) =
                (Finset.univ.filter (fun i : Fin n => P i j > 0)) := by
      ext i
      simp [heq i]
    rw [h_lt, h_gt]
    exact h j
  · -- eps j = -1: filters swap.
    have heq : ∀ i, eps j * P i j = -(P i j) := fun i => by rw [h1]; ring
    have h_lt : (Finset.univ.filter (fun i : Fin n => eps j * P i j < 0)) =
                (Finset.univ.filter (fun i : Fin n => P i j > 0)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq i]
      constructor <;> intro hh <;> linarith
    have h_gt : (Finset.univ.filter (fun i : Fin n => eps j * P i j > 0)) =
                (Finset.univ.filter (fun i : Fin n => P i j < 0)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, heq i]
      constructor <;> intro hh <;> linarith
    obtain ⟨hlt, hgt⟩ := h j
    rw [h_lt, h_gt]
    exact ⟨hgt, hlt⟩
