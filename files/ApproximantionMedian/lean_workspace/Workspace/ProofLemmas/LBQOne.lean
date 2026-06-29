import Mathlib
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ProofLemmas.UBDef

open Workspace.Types.SocialCost Workspace.Types.CoordinateMedian Workspace.ProofLemmas.UBDef

namespace Workspace.ProofLemmas.LBQOne

theorem LBQOne :
    UB (1 : ℝ) = 1 ∧
    ∀ (n d : ℕ) (P : Fin n → Fin d → ℝ),
      IsCoordinateMedian (fun _ : Fin d => (0 : ℝ)) P →
      0 < optSocialCost (1 : ℝ) P →
      ∀ (ε : ℝ), 0 < ε →
        (UB (1 : ℝ) - ε) * optSocialCost (1 : ℝ) P ≤
          socialCost (1 : ℝ) P (fun _ : Fin d => (0 : ℝ)) := by
  have hUB : UB (1 : ℝ) = 1 := UBDef.2
  refine ⟨hUB, ?_⟩
  intro n d P _ hOPT ε hε
  rw [hUB]
  have hle : optSocialCost (1 : ℝ) P ≤ socialCost (1 : ℝ) P (fun _ : Fin d => (0 : ℝ)) :=
    optSocialCost_le_socialCost (le_refl 1) P _
  nlinarith [hOPT.le, hε.le, hle]

end Workspace.ProofLemmas.LBQOne
