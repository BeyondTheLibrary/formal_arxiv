import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Workspace.Types.FractionalCover
import Workspace.Types.IntegralCover
import Workspace.Types.IsPSmall
import Workspace.Theorems.SharpSelector
import Workspace.Definitions.LambdaH
import Workspace.Definitions.ProbDistributions
import Workspace.Lemmas.Lemma_PositiveS
import Workspace.Lemmas.Lemma_QPos
import Workspace.Lemmas.Lemma_QLeOne
import Workspace.Lemmas.Lemma_HeavyLe
import Workspace.Lemmas.Lemma_QPrimeLePDivSix
import Workspace.Lemmas.Lemma_QPrimeLeOne
import Workspace.Lemmas.Lemma_LambdaH_SumOne
import Workspace.Lemmas.Lemma_LambdaH_Nonneg
import Workspace.Lemmas.Lemma_LambdaH_LeOne
import Workspace.Lemmas.Lemma_LambdaH_Support
import Workspace.Lemmas.Lemma_FinalBound
import Workspace.Lemmas.Lemma_MaxWProb
import Workspace.Lemmas.Lemma_ExpBound

open BigOperators
open Real

namespace Workspace.MainTheorem

open Workspace.Types.FractionalCover
open Workspace.Types.IntegralCover
open Workspace.Types.IsPSmall
open Workspace.Theorems.SharpSelector
open Workspace.Definitions.LambdaH
open Workspace.Definitions.ProbDistributions

/-- Sharp rounding of fractional to integral covers.

This theorem establishes that there exists an absolute constant c > 0 such that:
if a fractional cover w of a hypergraph ℋ satisfies certain cost and support conditions,
then ℋ admits an integral cover with comparably small cost.

Proof strategy (following the paper):
1. Construct weight vectors λ_H for each H ∈ ℋ from the fractional cover w
2. Assume for contradiction that ℋ is not q-small for q = cp/log(t)
3. Apply the Sharp Selector Theorem (Theorem 1.3) to obtain a probabilistic lower bound
4. Derive a lower bound 𝔼[∑_W w(W) · q'^|W|] ≥ 1/6 via λ_H properties
5. Use the cost assumption to show 𝔼[∑_W w(W) · q'^|W|] ≤ 1/12
6. Obtain contradiction: 1/6 ≤ ∑_W w(W) · q'^|W| ≤ 1/12

**Source**: Theorem 1.2 in @../A_sharp_version_of_Talagrands_selector_process_conjecture_and_an_application_to_rounding_fractional_covers.pdf
         (@../arXiv-2412.03540v1.tex, \ref{thm:main})
-/
theorem main_theorem :
    ∃ c : ℝ, 0 < c ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X]
        (t : ℕ) (p : ℝ) (ℋ : Set (Finset X))
        (cov : FractionalCover X ℋ),
        2 ≤ t →
        0 < p → p ≤ 1 →
        (∀ W : Finset X, t < W.card → cov.w W = 0) →
        (∑ W : Finset X, cov.w W * p ^ W.card) ≤ (1 : ℝ) / 2 →
        IsPSmall ℋ (c * p / Real.log t) := by
  -- Obtain the constant from the Sharp Selector Theorem (Theorem 1.2)
  rcases sharp_selector_theorem with ⟨c_sel, hc_sel, hc_sel_le, h_sel⟩

  -- Define our constant c (scaled down version of c_sel)
  let c_val : ℝ := c_sel / 100000
  use c_val
  constructor
  · show 0 < c_val; unfold c_val; linarith

  -- Main proof by contradiction
  intro X instF instD t p ℋ cov ht hp_pos hp_le1 h_supp h_cost
  by_contra h_not_small

  -- Define key parameters:
  -- q = cp/log(t) is the smallness parameter (we assume ℋ is NOT q-small)
  -- s ≈ log(2t)/log(2) determines the heaviness threshold
  -- q' = 16sq is the probability parameter for sampling
  let q := c_val * p / Real.log t
  let s := Nat.ceil (Real.log (2 * t) / Real.log 2)
  let q' := 16 * s * q

  -- Verify basic properties of our parameters
  have hq_pos : 0 < q := Workspace.Lemmas.QPos.q_pos p c_sel t hp_pos hc_sel ht
  have hq_le1 : q ≤ 1 :=
    Workspace.Lemmas.QLeOne.q_le_one p c_sel t hp_le1 hp_pos.le hc_sel hc_sel_le ht
  have hs_pos : 0 < s := Workspace.Lemmas.PositiveS.s_pos t ht

  -- Establish that q' is a valid probability (used as the density-validity
  -- hypothesis `16 * s * p ≤ 1` for sharp_selector_theorem).
  have hq'_pos : 0 ≤ q' := by
    unfold q' q c_val
    have ht_real : 1 < (t : ℝ) := by
      have : (1 : ℝ) < 2 := by norm_num
      have : (2 : ℝ) ≤ t := by exact Nat.cast_le.mpr ht
      linarith
    have : 0 < log (t : ℝ) := log_pos ht_real
    positivity

  have hq'_le_one : q' ≤ 1 :=
    Workspace.Lemmas.QPrimeLeOne.q_prime_le_one p c_sel t s q q' hp_pos hp_le1 hc_sel hc_sel_le ht rfl rfl rfl

  -- Step 1: Apply Sharp Selector Theorem (Theorem 1.3)
  -- This gives us: with probability ≥ 1/3, max_H ∑_{x ∈ X_{q'} ∩ H} λ_H(x) ≥ 1 - 2^(-s)
  -- The density-validity hypothesis `16 * (s : ℝ) * q ≤ 1` is exactly `q' ≤ 1` after unfolding.
  have h_heavy_prob := h_sel q s ℋ (lambdaH cov) hq_pos hq_le1 hs_pos hq'_le_one h_not_small
                         (fun H hH x => ⟨Workspace.Lemmas.LambdaH_Nonneg.lambdaH_nonneg cov H hH x,
                                         Workspace.Lemmas.LambdaH_LeOne.lambdaH_le_one cov H hH x⟩)
                         (fun H hH x hx => Workspace.Lemmas.LambdaH_Support.lambdaH_support cov H hH x hx)
                         (fun H hH => (Workspace.Lemmas.LambdaH_SumOne.lambdaH_sum_one cov H hH).ge)

  -- Step 2: Convert λ_H bound to fractional cover bound
  -- From h_heavy_prob and properties of λ_H, derive that with probability ≥ 1/3:
  -- max_H ∑_{W ⊆ H ∩ X_{q'}} w(W) ≥ 1/2
  have h_max_w_val := Workspace.Lemmas.MaxWProb.max_w_prob t ℋ cov s q' h_heavy_prob
    (Workspace.Lemmas.HeavyLe.heavy_le t s ht rfl) h_supp hq'_pos hq'_le_one rfl

  -- Step 3: Lower bound on expectation
  -- This implies 𝔼[∑_W w(W) · 𝟙[W ⊆ X_{q'}]] ≥ 1/6
  -- By linearity: ∑_W w(W) · q'^|W| ≥ 1/6
  have h_exp_bound_val := Workspace.Lemmas.ExpBound.exp_bound t ℋ cov q' h_max_w_val hq'_pos hq'_le_one

  -- Step 4: Upper bound on expectation
  -- From the cost assumption ∑_W w(W) · p^|W| ≤ 1/2 and q' ≤ p/6,
  -- we get ∑_W w(W) · q'^|W| ≤ 1/12
  have h_final_bound_val := Workspace.Lemmas.FinalBound.final_bound
    c_sel t p ℋ cov s q q' rfl rfl rfl h_cost
    (Workspace.Lemmas.QPrimeLePDivSix.q_prime_le_p_div_6 p c_sel t s q q' hp_pos hp_le1 hc_sel hc_sel_le ht rfl rfl rfl)
    hq'_pos hp_pos.le

  -- Contradiction: We have both ∑_W w(W) · q'^|W| ≥ 1/6 and ∑_W w(W) · q'^|W| ≤ 1/12
  linarith

end Workspace.MainTheorem
