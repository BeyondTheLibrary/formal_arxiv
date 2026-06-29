import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.OneDMedianMinimizesSumAbsDeviation

open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ProofLemmas.UBDef

theorem MainTheoremApproxBoundQEqOne
    {n d : ℕ} (hd : 1 ≤ d) (P : Fin n → Fin d → ℝ)
    (m : Fin d → ℝ) (hm : IsCoordinateMedian m P) :
    socialCost 1 P m ≤ UB 1 * optSocialCost 1 P := by
  -- Step 1: UB 1 = 1, so RHS becomes optSocialCost 1 P
  have hUB1 : UB 1 = 1 := UBDef.2
  rw [hUB1, one_mul]
  -- Step 2: optSocialCost 1 P = ⨅ f, socialCost 1 P f. Show socialCost 1 P m ≤ socialCost 1 P f for every f.
  unfold optSocialCost
  refine le_ciInf (fun f => ?_)
  -- Step 3: Goal: socialCost 1 P m ≤ socialCost 1 P f
  -- socialCost 1 P g = ∑ i, lqNorm 1 (P i - g) = ∑ i, ∑ j, |P i j - g j|
  unfold socialCost
  -- Rewrite each lqNorm 1 to a sum of abs values
  have hrw_m : ∀ i : Fin n, lqNorm 1 (fun j => P i j - m j) =
      ∑ j, |P i j - m j| := fun i => lqNorm_one_eq_sum_abs _
  have hrw_f : ∀ i : Fin n, lqNorm 1 (fun j => P i j - f j) =
      ∑ j, |P i j - f j| := fun i => lqNorm_one_eq_sum_abs _
  rw [Finset.sum_congr rfl (fun i _ => hrw_m i),
      Finset.sum_congr rfl (fun i _ => hrw_f i)]
  -- Now goal: ∑ i, ∑ j, |P i j - m j| ≤ ∑ i, ∑ j, |P i j - f j|
  -- Swap order of summation on both sides
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i j => |P i j - m j|),
      Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun i j => |P i j - f j|)]
  -- Goal: ∑ j, ∑ i, |P i j - m j| ≤ ∑ j, ∑ i, |P i j - f j|
  -- Apply OneDMedianMinimizesSumAbsDeviation per coordinate j.
  apply Finset.sum_le_sum
  intro j _
  obtain ⟨hlt, hgt⟩ := hm j
  exact OneDMedianMinimizesSumAbsDeviation
    (fun i => P i j) (m j) hlt hgt (f j)
