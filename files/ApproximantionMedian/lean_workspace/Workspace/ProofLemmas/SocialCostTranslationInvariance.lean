import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost

open Workspace.Types.SocialCost
open Workspace.Types.LqNorm

theorem SocialCostTranslationInvariance (q : ℝ) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) (t f : Fin d → ℝ) :
    socialCost q (fun (i : Fin n) (j : Fin d) => P i j - t j) (fun j => f j - t j)
      = socialCost q P f := by
  unfold socialCost
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  funext j
  ring
