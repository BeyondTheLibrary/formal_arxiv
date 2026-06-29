import Mathlib

namespace Workspace.ProofLemmas

theorem SublemmaGLowerBoundOnA
    (g : ℝ → ℝ) (hg : Continuous g)
    (A : Set ℝ) (hA_compact : IsCompact A) (hA_nonempty : A.Nonempty)
    (h_no_zeros : ∀ x ∈ A, g x ≠ 0) :
    ∃ g_lb : ℝ, 0 < g_lb ∧ ∀ x ∈ A, g_lb ≤ |g x| := by
  -- Continuity of |g|
  have h_abs_cont : Continuous (fun x => |g x|) := continuous_abs.comp hg
  -- The compact set A attains a minimum of |g| at some x₀
  obtain ⟨x₀, hx₀_mem, hx₀_min⟩ :=
    hA_compact.exists_isMinOn hA_nonempty h_abs_cont.continuousOn
  -- |g x₀| is positive since g x₀ ≠ 0
  have h_pos : 0 < |g x₀| := abs_pos.mpr (h_no_zeros x₀ hx₀_mem)
  -- The minimum |g x₀| is our lower bound
  refine ⟨|g x₀|, h_pos, ?_⟩
  intro x hx
  exact hx₀_min hx

end Workspace.ProofLemmas
