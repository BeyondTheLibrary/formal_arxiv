import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef
import Workspace.ProofLemmas.LqNormZeroIffEqZero
import Workspace.ProofLemmas.MedianOfConstant
import Workspace.ProofLemmas.SocialCostMinExists

open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ProofLemmas.UBDef

theorem MainTheoremTrivialCases
    (q : ℝ) (hq : 1 ≤ q) {n d : ℕ} (hd : 1 ≤ d)
    (P : Fin n → Fin d → ℝ) (m : Fin d → ℝ)
    (hm : IsCoordinateMedian m P)
    (htrivial : n = 0 ∨ optSocialCost q P = 0) :
    socialCost q P m ≤ UB q * optSocialCost q P := by
  -- Split on n = 0 vs n ≥ 1
  by_cases hn : n = 0
  · -- Case n = 0: socialCost = 0 for all f, optSocialCost = 0
    subst hn
    have hsc : socialCost q P m = 0 := socialCost_empty_agents q d P m
    have hopt : optSocialCost q P = 0 := by
      unfold optSocialCost
      have hconst : ∀ f : Fin d → ℝ, socialCost q P f = 0 :=
        fun f => socialCost_empty_agents q d P f
      simp only [hconst]
      exact ciInf_const
    rw [hsc, hopt, mul_zero]
  · -- Case n ≥ 1: by hypothesis, optSocialCost q P = 0
    have hopt : optSocialCost q P = 0 := by
      rcases htrivial with hn0 | hopt0
      · exact absurd hn0 hn
      · exact hopt0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hn_ge_one : 1 ≤ n := hn_pos
    -- Get a minimizer f*
    obtain ⟨fstar, hfstar⟩ := SocialCostMinExists q hq hd P
    have hsc_fstar : socialCost q P fstar = 0 := by
      rw [hfstar, hopt]
    -- Each summand is 0
    have hterm_zero : ∀ i : Fin n, lqNorm q (fun j => P i j - fstar j) = 0 := by
      have hsum : ∑ i, lqNorm q (fun j => P i j - fstar j) = 0 := by
        unfold socialCost at hsc_fstar
        exact hsc_fstar
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ lqNorm q (fun j => P i j - fstar j) :=
        fun i _ => lqNorm_nonneg hq _
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
      exact this
    -- So P i j = fstar j for all i, j
    have hP_eq : ∀ i : Fin n, (fun j => P i j) = fstar := by
      intro i
      have hzero : (fun j => P i j - fstar j) = 0 := by
        exact (LqNormZeroIffEqZero q hq hd _).mp (hterm_zero i)
      funext j
      have : P i j - fstar j = 0 := by
        have := congr_fun hzero j
        simpa using this
      linarith
    -- Hence P is the constant placement = fstar
    have hP_const : P = (fun (_ : Fin n) (j : Fin d) => fstar j) := by
      funext i j
      have := hP_eq i
      exact congr_fun this j
    -- m = fstar by MedianOfConstant
    have hm_eq : m = fstar := by
      have hm' : IsCoordinateMedian m (fun (_ : Fin n) (j : Fin d) => fstar j) := by
        rw [← hP_const]; exact hm
      exact MedianOfConstant hn_ge_one fstar m hm'
    -- Conclude socialCost q P m = 0
    have hsc_m : socialCost q P m = 0 := by
      rw [hm_eq]; exact hsc_fstar
    rw [hsc_m, hopt, mul_zero]
