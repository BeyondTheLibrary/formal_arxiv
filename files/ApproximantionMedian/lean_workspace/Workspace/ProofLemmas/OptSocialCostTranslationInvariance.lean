import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.SocialCostTranslationInvariance

open Workspace.Types.SocialCost

theorem OptSocialCostTranslationInvariance
    (q : ℝ) {n d : ℕ} (P : Fin n → Fin d → ℝ) (t : Fin d → ℝ) :
    optSocialCost q (fun (i : Fin n) (j : Fin d) => P i j - t j) =
      optSocialCost q P := by
  unfold optSocialCost
  -- Apply the bijection f ↦ f - t on the domain.
  -- Function.Surjective.iInf_congr gives ⨅ x, F x = ⨅ y, G y when
  -- there's a surjection h with G (h x) = F x.
  -- We want ⨅ f, socialCost q P f = ⨅ f, socialCost q (P-t) f.
  symm
  refine Function.Surjective.iInf_congr (fun (f : Fin d → ℝ) => fun j => f j - t j) ?_ ?_
  · -- Surjective
    intro g
    refine ⟨fun j => g j + t j, ?_⟩
    funext j
    ring
  · -- pointwise equality
    intro f
    exact SocialCostTranslationInvariance q P t f
