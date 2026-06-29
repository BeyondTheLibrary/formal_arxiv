import Mathlib
import Workspace.Types.LqNorm
import Workspace.Types.CoordinateMedian
import Workspace.Types.SocialCost
import Workspace.ProofLemmas.UBDef

open Workspace.Types.LqNorm
open Workspace.Types.CoordinateMedian
open Workspace.Types.SocialCost
open Workspace.ProofLemmas.UBDef

open scoped BigOperators

/-- Auxiliary: when `n = 0`, the social cost is `0` for every `f`. -/
private lemma socialCost_zero_agents {q : ℝ} (d : ℕ)
    (P : Fin 0 → Fin d → ℝ) (f : Fin d → ℝ) :
    socialCost q P f = 0 := by
  unfold socialCost
  exact Fin.sum_univ_zero _

private lemma optSocialCost_zero_agents {q : ℝ} (hq : 1 ≤ q) (d : ℕ)
    (P : Fin 0 → Fin d → ℝ) :
    optSocialCost q P = 0 := by
  apply le_antisymm
  · have := optSocialCost_le_socialCost hq P (fun _ => 0)
    rw [socialCost_zero_agents] at this
    exact this
  · exact optSocialCost_nonneg hq P

theorem ReductionToEvenN
    (h_even : ∀ q : ℝ, 1 ≤ q → ∀ {n d : ℕ}, 0 < n → Even n → 1 ≤ d →
      ∀ (P : Fin n → Fin d → ℝ),
      ∀ (m : Fin d → ℝ), IsCoordinateMedian m P →
        socialCost q P m ≤ UB q * optSocialCost q P) :
    ∀ q : ℝ, 1 ≤ q → ∀ {n d : ℕ}, 1 ≤ d →
      ∀ (P : Fin n → Fin d → ℝ),
      ∀ (m : Fin d → ℝ), IsCoordinateMedian m P →
        socialCost q P m ≤ UB q * optSocialCost q P := by
  intro q hq n d hd P m hm
  -- Case n = 0: both sides are 0
  by_cases hn0 : n = 0
  · subst hn0
    have h1 : socialCost q P m = 0 := socialCost_zero_agents d P m
    have h2 : optSocialCost q P = 0 := optSocialCost_zero_agents hq d P
    rw [h1, h2, mul_zero]
  -- n ≥ 1: reduce to case 2*n via duplication
  have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
  -- Build P' : Fin (n + n) → Fin d → ℝ via duplication using Sum equiv
  let e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  let P' : Fin (n + n) → Fin d → ℝ := fun i => Sum.elim P P (e.symm i)
  -- Show 2n is even and positive
  have hn2_pos : 0 < n + n := by omega
  have hn2_even : Even (n + n) := ⟨n, rfl⟩
  -- Key fact: socialCost q P' f = 2 * socialCost q P f for any f
  have h_sc : ∀ f : Fin d → ℝ, socialCost q P' f = 2 * socialCost q P f := by
    intro f
    unfold socialCost
    -- Define F : Fin n → ℝ as the per-agent norm, so the sum-type sum is Sum.elim F F.
    set F : Fin n → ℝ := fun i => lqNorm q (fun j => P i j - f j) with hF
    -- Use the equiv to rewrite the sum over Fin (n+n) as a sum over Fin n ⊕ Fin n.
    have h1 : (∑ i : Fin (n + n), lqNorm q (fun j => P' i j - f j))
        = ∑ i : Fin n ⊕ Fin n, lqNorm q (fun j => Sum.elim P P i j - f j) := by
      rw [← Equiv.sum_comp e (fun i : Fin (n + n) =>
            lqNorm q (fun j => P' i j - f j))]
      apply Finset.sum_congr rfl
      intro i _
      simp [P', Equiv.symm_apply_apply]
    rw [h1]
    -- Now the summand equals Sum.elim F F i for i : Fin n ⊕ Fin n.
    have h2 : ∀ i : Fin n ⊕ Fin n,
        lqNorm q (fun j => Sum.elim P P i j - f j) = Sum.elim F F i := by
      intro i
      cases i with
      | inl a => simp [F, Sum.elim_inl]
      | inr a => simp [F, Sum.elim_inr]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]
    rw [Fintype.sum_sumElim]
    ring
  -- Show m is a coordinate-wise median of P'
  have hm' : IsCoordinateMedian m P' := by
    intro j
    obtain ⟨hlt, hgt⟩ := hm j
    -- Cardinality lemma: filter on P' equals 2 * filter on P (for any predicate via P).
    -- Use the bijection e.symm to translate to a filter over Fin n ⊕ Fin n.
    have card_eq : ∀ (R : ℝ → ℝ → Prop) [DecidablePred (fun i : Fin (n + n) => R (P' i j) (m j))]
        [DecidablePred (fun i : Fin n => R (P i j) (m j))],
        (Finset.univ.filter (fun i : Fin (n + n) => R (P' i j) (m j))).card =
        2 * (Finset.univ.filter (fun i : Fin n => R (P i j) (m j))).card := by
      intro R _ _
      classical
      -- Express cardinalities as sums of 0/1 indicators, then use Fintype.sum_sumElim.
      have h1 : (Finset.univ.filter (fun i : Fin (n + n) => R (P' i j) (m j))).card =
          ∑ i : Fin (n + n), (if R (P' i j) (m j) then (1 : ℕ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
            mul_one]
      have h2 : (Finset.univ.filter (fun i : Fin n => R (P i j) (m j))).card =
          ∑ i : Fin n, (if R (P i j) (m j) then (1 : ℕ) else 0) := by
        rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
            mul_one]
      rw [h1, h2]
      -- Use Equiv.sum_comp e to push through the sum-type equiv.
      rw [← Equiv.sum_comp e (fun i : Fin (n + n) =>
            (if R (P' i j) (m j) then (1 : ℕ) else 0))]
      -- Now the summand is `if R (P' (e i) j) (m j) then 1 else 0`. Convert via Sum.elim P P i.
      have hF : ∀ i : Fin n ⊕ Fin n,
          (if R (P' (e i) j) (m j) then (1 : ℕ) else 0) =
          Sum.elim
            (fun a : Fin n => if R (P a j) (m j) then (1 : ℕ) else 0)
            (fun a : Fin n => if R (P a j) (m j) then (1 : ℕ) else 0) i := by
        intro i
        cases i with
        | inl a =>
          show (if R (P' (e (Sum.inl a)) j) (m j) then (1 : ℕ) else 0) = _
          have hrw : P' (e (Sum.inl a)) = P a := by
            show Sum.elim P P (e.symm (e (Sum.inl a))) = P a
            rw [e.symm_apply_apply]
            rfl
          simp [hrw]
        | inr a =>
          show (if R (P' (e (Sum.inr a)) j) (m j) then (1 : ℕ) else 0) = _
          have hrw : P' (e (Sum.inr a)) = P a := by
            show Sum.elim P P (e.symm (e (Sum.inr a))) = P a
            rw [e.symm_apply_apply]
            rfl
          simp [hrw]
      rw [Finset.sum_congr rfl (fun i _ => hF i)]
      rw [Fintype.sum_sumElim]
      ring
    classical
    have hlt_card := card_eq (· < ·)
    have hgt_card := card_eq (· > ·)
    have hn2_div : (n + n) / 2 = n := by omega
    refine ⟨?_, ?_⟩
    · rw [hlt_card, hn2_div]
      have hn2 : n / 2 + n / 2 ≤ n := by omega
      omega
    · rw [hgt_card, hn2_div]
      have hn2 : n / 2 + n / 2 ≤ n := by omega
      omega
  -- Apply h_even
  have h_main := h_even q hq hn2_pos hn2_even hd P' m hm'
  -- Now use h_sc to convert
  have h_lhs : socialCost q P' m = 2 * socialCost q P m := h_sc m
  -- Need: optSocialCost q P' ≤ 2 * optSocialCost q P
  have h_opt : optSocialCost q P' ≤ 2 * optSocialCost q P := by
    -- For all f: optSocialCost q P' ≤ socialCost q P' f = 2 * socialCost q P f
    -- So optSocialCost q P' / 2 ≤ socialCost q P f for all f
    -- Hence optSocialCost q P' / 2 ≤ ⨅ f, socialCost q P f = optSocialCost q P
    have hhalf : optSocialCost q P' / 2 ≤ optSocialCost q P := by
      apply le_ciInf
      intro f
      have hle := optSocialCost_le_socialCost hq P' f
      rw [h_sc f] at hle
      linarith
    linarith
  -- UB q ≥ 1 ≥ 0
  have hUB_nn : 0 ≤ UB q := by
    have h1 := UBDef.1 q hq
    linarith
  -- Combine
  rw [h_lhs] at h_main
  have h_chain : 2 * socialCost q P m ≤ UB q * (2 * optSocialCost q P) := by
    calc 2 * socialCost q P m
        ≤ UB q * optSocialCost q P' := h_main
      _ ≤ UB q * (2 * optSocialCost q P) :=
          mul_le_mul_of_nonneg_left h_opt hUB_nn
  -- Cancel 2
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hresult : socialCost q P m ≤ UB q * optSocialCost q P := by
    have h2 : UB q * (2 * optSocialCost q P) = 2 * (UB q * optSocialCost q P) := by ring
    rw [h2] at h_chain
    linarith
  exact hresult
