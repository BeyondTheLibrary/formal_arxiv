import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.Types.SignedGaussianCombination

namespace Workspace.ProofLemmas

theorem SublemmaExtractSortedZeroList
    (S : Workspace.Types.SignedGaussianCombination.SignedGaussianCombination)
    (ε : ℝ) (hε : 0 < ε)
    (h_finite : Set.Finite ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}))
    (h_atmost : ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}).ncard ≤ 6) :
    ∃ xs : List ℝ,
      xs.Pairwise (· < ·) ∧
      xs.length ≤ 6 ∧
      (∀ x ∈ xs, -(2/ε) ≤ x ∧ x ≤ 2/ε ∧ S.density x = 0) ∧
      (∀ y : ℝ, -(2/ε) ≤ y → y ≤ 2/ε → S.density y = 0 → y ∈ xs) := by
  -- Convert the finite set to a Finset and sort
  set Z : Finset ℝ := h_finite.toFinset with hZ_def
  refine ⟨Z.sort (· ≤ ·), ?_, ?_, ?_, ?_⟩
  · -- Pairwise (· < ·)
    exact (Finset.sort_sorted_lt Z).pairwise
  · -- Length ≤ 6
    rw [Finset.length_sort]
    have hcard : Z.card = ({x ∈ Set.Icc (-(2/ε)) (2/ε) | S.density x = 0}).ncard := by
      rw [hZ_def]
      exact (Set.ncard_eq_toFinset_card _ h_finite).symm
    rw [hcard]
    exact h_atmost
  · -- Every element of xs satisfies the predicate
    intro x hx
    rw [Finset.mem_sort] at hx
    rw [hZ_def, Set.Finite.mem_toFinset] at hx
    obtain ⟨hx_mem, hx_zero⟩ := hx
    rw [Set.mem_Icc] at hx_mem
    exact ⟨hx_mem.1, hx_mem.2, hx_zero⟩
  · -- Every zero y in the interval is in xs
    intro y hy_lo hy_hi hy_zero
    rw [Finset.mem_sort]
    rw [hZ_def, Set.Finite.mem_toFinset]
    refine ⟨?_, hy_zero⟩
    exact ⟨hy_lo, hy_hi⟩

end Workspace.ProofLemmas
