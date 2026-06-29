import Mathlib
import Workspace.Types.SocialCost
import Workspace.Types.CoordinateMedian
import Workspace.Types.LqNorm
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LBConstruction
import Workspace.ProofLemmas.LBQOne
import Workspace.ProofLemmas.LBLambdaStarLtOne
import Workspace.ProofLemmas.LBIntegrality
import Workspace.ProofLemmas.LBMedianAtZero
import Workspace.ProofLemmas.LBSocialCosts
import Workspace.ProofLemmas.LBRatioEqualsUB
import Workspace.ProofLemmas.LBRatioLimit
import Workspace.ProofLemmas.LBOptPositive

open Workspace.Types.SocialCost
open Workspace.Types.CoordinateMedian
open Workspace.Types.LqNorm
open Workspace.ProofLemmas.UBDef
open Workspace.ProofLemmas.LBConstruction
open Workspace.ProofLemmas.FqHasUniqueInteriorZero
open Workspace.ProofLemmas.LambdaStarDef

namespace Workspace.LowerBoundTheorem

/-- **Theorem 2 (tightness / lower bound).**

The upper bound `UB q` of Theorem 1 cannot be improved. For every `q ≥ 1`
and every `ε > 0`, there is a placement instance `P : Fin n → Fin d → ℝ`
(with dimension `d ≥ 1`) whose coordinate-wise median is the zero vector,
whose optimal social cost is strictly positive, and whose median social cost
`socialCost q P 0` is at least `(UB q − ε) · optSocialCost q P`.

Combined with Theorem 1's `socialCost q P m ≤ UB q * optSocialCost q P`,
this pins the worst-case approximation ratio of the coordinate-wise median
mechanism at exactly `UB q`. -/
theorem lower_bound_tight :
    ∀ (q : ℝ), 1 ≤ q → ∀ (ε : ℝ), 0 < ε →
      ∃ (n d : ℕ) (P : Fin n → Fin d → ℝ),
        1 ≤ d ∧
        IsCoordinateMedian (fun _ : Fin d => (0 : ℝ)) P ∧
        0 < optSocialCost q P ∧
        (UB q - ε) * optSocialCost q P ≤ socialCost q P (fun _ : Fin d => (0 : ℝ))
    := by
  intro q hq ε hε
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · -- Case q = 1.  Use an explicit two-point, one-dimensional instance and `LBQOne`.
    subst hq1
    set P : Fin 2 → Fin 1 → ℝ := ![![(-1 : ℝ)], ![(1 : ℝ)]] with hPdef
    -- median 0
    have hmed : IsCoordinateMedian (fun _ : Fin 1 => (0 : ℝ)) P := by
      intro j
      fin_cases j
      refine ⟨?_, ?_⟩
      · refine le_trans (Finset.card_le_card ?_)
          (by simp : ({0} : Finset (Fin 2)).card ≤ (Nat.succ 0).succ / 2)
        intro i hi; fin_cases i <;> simp_all <;> first | rfl | linarith
      · refine le_trans (Finset.card_le_card ?_)
          (by simp : ({1} : Finset (Fin 2)).card ≤ (Nat.succ 0).succ / 2)
        intro i hi; fin_cases i <;> simp_all <;> first | rfl | linarith
    -- OPT > 0
    have hopt : 0 < optSocialCost (1 : ℝ) P := by
      have hP : ∀ (f : Fin 1 → ℝ), (2 : ℝ) ≤ socialCost (1 : ℝ) P f := by
        intro f
        unfold socialCost
        rw [Fin.sum_univ_two]
        rw [lqNorm_dim_one (le_refl 1), lqNorm_dim_one (le_refl 1)]
        simp only [hPdef, Matrix.cons_val_zero, Matrix.cons_val_one]
        cases abs_cases ((-1 : ℝ) - f 0) <;> cases abs_cases ((1 : ℝ) - f 0) <;> linarith
      unfold optSocialCost
      refine lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) ?_
      exact le_ciInf (fun f => hP f)
    -- conclude via LBQOne
    obtain ⟨_, hbound⟩ := Workspace.ProofLemmas.LBQOne.LBQOne
    refine ⟨2, 1, P, le_refl 1, hmed, hopt, ?_⟩
    exact hbound 2 1 P hmed hopt ε hε
  · -- Case 1 < q.  Use the lower-bound construction.
    obtain ⟨ha_pos, ha_half⟩ := AStarLessThanOneHalf q hq1
    obtain ⟨_, ⟨hmu_pos, hmu_lt⟩, hmu1_pos, _⟩ :=
      Workspace.ProofLemmas.LBLambdaStarLtOne.LBLambdaStarLtOne q hq1
    have ha1 : a_star q < 1 := by linarith
    -- denominator base positivity `hD`
    have hK_pos : 0 < Kconst q := by
      unfold Kconst
      apply Real.rpow_pos_of_pos
      have h1 : 0 < (1 - a_star q) / a_star q := by apply div_pos <;> linarith
      have h2 : 0 < mu q / (1 - mu q) := div_pos hmu_pos hmu1_pos
      exact mul_pos h1 h2
    have hc_pos : 0 < c_star q := by unfold c_star; apply div_pos hK_pos; linarith
    have hc_lt : c_star q < 1 := by
      unfold c_star; rw [div_lt_one (by linarith)]; linarith
    have hratio_nonneg : 0 ≤ c_star q / (1 - c_star q) :=
      div_nonneg (le_of_lt hc_pos) (by linarith)
    have hD : 0 < (c_star q / (1 - c_star q)) ^ q * (a_star q) + (1 - a_star q) := by
      have hterm : 0 ≤ (c_star q / (1 - c_star q)) ^ q * (a_star q) :=
        mul_nonneg (Real.rpow_nonneg hratio_nonneg q) (le_of_lt ha_pos)
      linarith
    -- the ratio limit, with η = ε
    obtain ⟨d, hd, hratio⟩ :=
      Workspace.ProofLemmas.LBRatioLimit.LBRatioLimit q hq1 1 (le_refl 1) hD ε hε
    -- R = UB q
    have hReq := Workspace.ProofLemmas.LBRatioEqualsUB.LBRatioEqualsUB q hq1
    rw [hReq] at hratio
    -- positivity facts for the constructed instance
    obtain ⟨hOptPos, hSCfPos⟩ :=
      Workspace.ProofLemmas.LBOptPositive.LBOptPositive q hq1 d hd 1 (le_refl 1)
    have hmedP := LBMedianAtZero q hq1 d hd 1 (le_refl 1)
    -- abbreviations
    set SC0 := socialCost q (P_LB q d 1) (fun _ : Fin d => (0 : ℝ)) with hSC0
    set SCf := socialCost q (P_LB q d 1) (f_opt d) with hSCf
    -- from the ratio bound: (UB q - ε) * SCf ≤ SC0
    have hstep1 : (UB q - ε) * SCf ≤ SC0 := by
      rw [le_div_iff₀ hSCfPos] at hratio
      linarith [hratio]
    -- OPT ≤ SCf
    have hOptLe : optSocialCost q (P_LB q d 1) ≤ SCf :=
      optSocialCost_le_socialCost (le_of_lt hq1) (P_LB q d 1) (f_opt d)
    -- (UB q - ε) * OPT ≤ SC0
    have hSC0_nonneg : 0 ≤ SC0 := socialCost_nonneg (le_of_lt hq1) _ _
    have hfinal : (UB q - ε) * optSocialCost q (P_LB q d 1) ≤ SC0 := by
      rcases le_or_gt 0 (UB q - ε) with hsgn | hsgn
      · have : (UB q - ε) * optSocialCost q (P_LB q d 1) ≤ (UB q - ε) * SCf :=
          mul_le_mul_of_nonneg_left hOptLe hsgn
        linarith
      · have : (UB q - ε) * optSocialCost q (P_LB q d 1) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hsgn) (le_of_lt hOptPos)
        linarith
    exact ⟨nCount q d 1, d, P_LB q d 1, hd, hmedP, hOptPos, hfinal⟩

end Workspace.LowerBoundTheorem
