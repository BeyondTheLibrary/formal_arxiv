import Mathlib
import Workspace.Types.LqNorm

open scoped BigOperators
open Workspace.Types.LqNorm

namespace Workspace.Types.SocialCost

/-- The social cost of placing a facility at `f : Fin d → ℝ` for `n`
agents whose preferred locations are the rows of `P : Fin n → Fin d → ℝ`,
measured under the `L_q` norm:
`socialCost q P f = ∑_{i=1}^n lqNorm q (p_i − f)`,
where `(p_i − f) j = P i j − f j`. -/
noncomputable def socialCost (q : ℝ) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ) : ℝ :=
  ∑ i, lqNorm q (fun j => P i j - f j)

/-- The optimal social cost is the infimum over all facility locations. -/
noncomputable def optSocialCost (q : ℝ) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) : ℝ :=
  ⨅ f, socialCost q P f

/-- The social cost is non-negative whenever `1 ≤ q`. -/
lemma socialCost_nonneg {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ) :
    0 ≤ socialCost q P f := by
  unfold socialCost
  exact Finset.sum_nonneg (fun i _ => lqNorm_nonneg hq _)

/-- With zero agents the social cost is `0` for every facility location
and every `q`. -/
lemma socialCost_empty_agents :
    ∀ (q : ℝ), ∀ (d : ℕ) (P : Fin 0 → Fin d → ℝ) (f : Fin d → ℝ),
      socialCost q P f = 0 := by
  intro q d P f
  unfold socialCost
  exact Fin.sum_univ_zero _

/-- The set of social costs (over all facility locations) is bounded below
by `0` whenever `1 ≤ q`. -/
lemma socialCost_bddBelow {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) :
    BddBelow (Set.range (socialCost q P)) := by
  refine ⟨0, ?_⟩
  rintro x ⟨f, rfl⟩
  exact socialCost_nonneg hq P f

/-- The optimal social cost is a lower bound for the social cost at every
facility location (under `1 ≤ q`, which gives `BddBelow`). -/
lemma optSocialCost_le_socialCost {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) (f : Fin d → ℝ) :
    optSocialCost q P ≤ socialCost q P f := by
  unfold optSocialCost
  exact ciInf_le (socialCost_bddBelow hq P) f

/-- The optimal social cost is non-negative under `1 ≤ q`. -/
lemma optSocialCost_nonneg {q : ℝ} (hq : 1 ≤ q) {n d : ℕ}
    (P : Fin n → Fin d → ℝ) :
    0 ≤ optSocialCost q P := by
  unfold optSocialCost
  exact le_ciInf (fun f => socialCost_nonneg hq P f)

end Workspace.Types.SocialCost
