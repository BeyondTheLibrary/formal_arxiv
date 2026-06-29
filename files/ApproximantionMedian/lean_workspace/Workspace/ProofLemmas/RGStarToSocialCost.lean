import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.ConsistencyDefs
import Workspace.RobustnessDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.RGDefs
import Workspace.ProofLemmas.ConstrainedMinExists
import Workspace.ProofLemmas.RGWorstCasePredictionSignature

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.ConsistencyTheorem
open Workspace.RobustnessTheorem
open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.RGDefs
open Workspace.ProofLemmas.ConstrainedMinExists

namespace Workspace.ProofLemmas.RGStarToSocialCost

theorem RGStarToSocialCost
    {n d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hlam0 : 0 < lambda2 c) (hRG : 1 / lambda2 c = Workspace.RobustnessTheorem.RG c)
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ)
    (hf_opt : socialCost 2 P f = optSocialCost 2 P)
    (hstar : 0 ≤ ∑ i, g_lambda 2 (lambda2 c) f (P i)) :
    socialCost 2 P (fun _ => 0) ≤ Workspace.RobustnessTheorem.RG c * optSocialCost 2 P := by
  -- Unfold g_lambda and sum: ∑ g = SC(P,f) - λ₂·SC(P,0).
  have h_sum_eq : (∑ i, g_lambda 2 (lambda2 c) f (P i))
      = socialCost 2 P f - lambda2 c * socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) := by
    unfold g_lambda socialCost
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h_ext : (fun j => P i j - (fun (_ : Fin d) => (0 : ℝ)) j) = fun j => P i j := by
      funext j; ring
    rw [h_ext]
  -- From hstar: λ₂·SC(P,0) ≤ SC(P,f) = OPT(P).
  rw [h_sum_eq] at hstar
  have h_le : lambda2 c * socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) ≤ socialCost 2 P f := by
    linarith
  -- Divide by λ₂ > 0 and use 1/λ₂ = RG c, SC(P,f) = OPT(P).
  rw [hf_opt] at h_le
  -- SC(P,0) ≤ (1/λ₂)·OPT(P) = RG c · OPT(P).
  have h_div : socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) ≤ (1 / lambda2 c) * optSocialCost 2 P := by
    rw [show (1 / lambda2 c) * optSocialCost 2 P = optSocialCost 2 P / lambda2 c by ring]
    rw [le_div_iff₀ hlam0]
    linarith
  rw [hRG] at h_div
  exact h_div

end Workspace.ProofLemmas.RGStarToSocialCost
