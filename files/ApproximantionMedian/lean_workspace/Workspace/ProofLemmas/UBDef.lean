import Mathlib
import Workspace.ProofLemmas.LambdaStarDef

open Workspace.ProofLemmas.LambdaStarDef

namespace Workspace.ProofLemmas.UBDef

noncomputable def UB (q : ℝ) : ℝ :=
  if 1 ≤ q then 1 / lambda_star q else 1

theorem UBDef :
    (∀ q : ℝ, 1 ≤ q → 1 ≤ UB q) ∧ UB 1 = 1 := by
  have hLam := LambdaStarDef
  refine ⟨?_, ?_⟩
  · intro q hq
    simp only [UB, if_pos hq]
    obtain ⟨h_pos, h_le⟩ := hLam.1 q hq
    rw [le_div_iff₀ h_pos]
    linarith
  · simp only [UB, if_pos (le_refl (1 : ℝ))]
    rw [hLam.2]
    norm_num

end Workspace.ProofLemmas.UBDef
