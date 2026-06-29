import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.ConsistencyDefs
import Workspace.ProofLemmas.CGDefs
import Workspace.ProofLemmas.ConstrainedMinExists

open scoped BigOperators
open Workspace.Types.LqNorm
open Workspace.Types.SocialCost
open Workspace.ConsistencyTheorem
open Workspace.ProofLemmas.CGDefs
open Workspace.ProofLemmas.ConstrainedMinExists

namespace Workspace.ProofLemmas.CGStarToSocialCost

/-- **CGStarToSocialCost** (proof_nlp.md §7, Gap (v); prediction.tex 29–37).

Normalized setting: `m = 0`, `f = f*` the normalized minimizer with
`socialCost 2 P f = optSocialCost 2 P`.  Suppose `(★)` holds:
`∑_{i∈[n]} g(pᵢ) ≥ 0`, where `g(p) := ‖p − f‖₂ − λ₁‖p‖₂ = g_lambda 2 λ₁ f p`,
with `λ₁ = lambda1 c ∈ (0,1)`.  Then
`socialCost 2 P 0 ≤ (1/λ₁)·optSocialCost 2 P = CG c · optSocialCost 2 P`.

(Unfold `g` and sum: `λ₁·SC(P,0) ≤ SC(P,f)`; divide by `λ₁ > 0`; use
`SC(P,f) = OPT(P)` and `1/λ₁ = CG c`.  Undoing the normalization
(translation/reflection/scaling) transfers the bound to the original instance.) -/
theorem CGStarToSocialCost
    {n d : ℕ} (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hlam0 : 0 < lambda1 c) (hCG : 1 / lambda1 c = Workspace.ConsistencyTheorem.CG c)
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ)
    (hf_opt : socialCost 2 P f = optSocialCost 2 P)
    (hstar : 0 ≤ ∑ i, g_lambda 2 (lambda1 c) f (P i)) :
    socialCost 2 P (fun _ => 0) ≤ Workspace.ConsistencyTheorem.CG c * optSocialCost 2 P := by
  -- Unfold g_lambda and sum: ∑ g = SC(P,f) - λ₁·SC(P,0).
  have h_sum_eq : (∑ i, g_lambda 2 (lambda1 c) f (P i))
      = socialCost 2 P f - lambda1 c * socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) := by
    unfold g_lambda socialCost
    rw [Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have h_ext : (fun j => P i j - (fun (_ : Fin d) => (0 : ℝ)) j) = fun j => P i j := by
      funext j; ring
    rw [h_ext]
  -- From hstar: λ₁·SC(P,0) ≤ SC(P,f) = OPT(P).
  rw [h_sum_eq] at hstar
  have h_le : lambda1 c * socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) ≤ socialCost 2 P f := by
    linarith
  -- Divide by λ₁ > 0 and use 1/λ₁ = CG c, SC(P,f) = OPT(P).
  rw [hf_opt] at h_le
  -- SC(P,0) ≤ (1/λ₁)·OPT(P) = CG c · OPT(P).
  have h_div : socialCost 2 P (fun (_ : Fin d) => (0 : ℝ)) ≤ (1 / lambda1 c) * optSocialCost 2 P := by
    rw [show (1 / lambda1 c) * optSocialCost 2 P = optSocialCost 2 P / lambda1 c by ring]
    rw [le_div_iff₀ hlam0]
    linarith
  rw [hCG] at h_div
  exact h_div

end Workspace.ProofLemmas.CGStarToSocialCost
