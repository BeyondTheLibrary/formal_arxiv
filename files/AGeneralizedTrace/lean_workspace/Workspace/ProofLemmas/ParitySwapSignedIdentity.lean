import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.WitnessCoinFlipFormula
import Workspace.ProofLemmas.MiddleWeightExplicit
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.PriorWork.AltRSumKwayFourierBridge

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# ParitySwapSignedIdentity

The **signed** per-`r` parity-swap identity — the genuine faithful core of Lemma 6
of Rivkin–Valiant–Valiant (2024), arXiv:2412.00674v1, §3.1, lines 297-305.

`ParitySwapCore` proves only the *triangle/absolute-value* bound
`|∑_b (Ce(b)−Co(b))·middleIndicator(b,m,r)| ≤ ∏_{j∈ell} ellFactor`.
Lemma 6 needs more than that — it needs the SIGN preserved (the sign lives in
`Ce(b)−Co(b)`, even-vs-odd witnesses).  Lemma 6 is now PROVED (no axiom) via the
`Path4Assembly` route; this file supplies the supporting sign-preserving
identity that route relies on.

This file proves the EXACT signed value of the inner sum, NOT its absolute value:

* **mixed parity** (two `1`-bits of `m` at window positions of opposite parity):
  `∑_b (Ce(b)−Co(b))·middleIndicator(b,m,r) = 0`;
* **empty `ell`** (no `1`-bits in the middle window): the inner sum is `Q_e − Q_o`;
* **same-parity nonempty** with common window parity `p ∈ {0,1}`:
  `∑_b (Ce(b)−Co(b))·middleIndicator(b,m,r)
       = (−1)^p · (witness coin-flip factor Q_p) · ∏_{j∈ell} ellFactor n α r j.val`.

The product `∏_{j∈ell} ellFactor n α r j.val` is EXACTLY the k-way witness factor of
`Fterm` (see `Workspace.Types.AlternatingSumExpression.Fterm`); the sign `(−1)^p`
(with `p = (n/4+r+j)%2`, identical for every `j ∈ ell`) is the genuine parity-swap
sign. This is the sign-preserving identity flagged as the MISSING piece in
`lean_knowledge.md` (line 164) for assembling `∑_r (−1)^|r|·Fterm = altRSum` WITHOUT
dropping to absolute values.
-/

/-- `α * b_i ≤ 1/2` (re-derived from `BinomialPmfMaxBound`). -/
private lemma PSSI_alpha_b_le_half (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (i : ℕ) :
    (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
        ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1 / 2 := by
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  have hn_ge_one : (1 : ℕ) ≤ n := hn_pos
  have hbm := BinomialPmfMaxBound n hn_ge_one i
  set bi : ℝ := (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹ with hbi_def
  set α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hα_def
  have hbi_nonneg : 0 ≤ bi := by rw [hbi_def]; positivity
  have h_e_pos : 0 < Real.exp 2 := Real.exp_pos _
  have hπ_pos : 0 < Real.pi := Real.pi_pos
  have h_2pi_pos : (0 : ℝ) < 2 * Real.pi := by linarith
  have h_sqrt_2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr h_2pi_pos
  have h_alpha_nonneg : 0 ≤ α := by rw [hα_def]; positivity
  have hn_pos_R : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hπn_pos : 0 < Real.pi * n := by positivity
  have hα_bi_le : α * bi ≤ α * Real.sqrt (2 / (Real.pi * n)) :=
    mul_le_mul_of_nonneg_left hbm h_alpha_nonneg
  have hsqrt_n : Real.sqrt n * Real.sqrt (2 / (Real.pi * n)) = Real.sqrt (2 / Real.pi) := by
    rw [← Real.sqrt_mul (by exact_mod_cast hn_pos.le : (0 : ℝ) ≤ n)]
    congr 1
    field_simp
  have hkey : Real.pi * Real.sqrt (2 / Real.pi) = Real.sqrt (2 * Real.pi) := by
    rw [show (2 * Real.pi) = Real.pi^2 * (2 / Real.pi) by field_simp]
    rw [Real.sqrt_mul (by positivity)]
    rw [Real.sqrt_sq hπ_pos.le]
  have h_simplify : α * Real.sqrt (2 / (Real.pi * n)) = 1 / (4 * Real.exp 2 * Real.pi) := by
    rw [hα_def]
    rw [show (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
                * Real.sqrt (2 / (Real.pi * n)) =
              (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi)))
                * (Real.sqrt n * Real.sqrt (2 / (Real.pi * n))) from by ring]
    rw [hsqrt_n]
    rw [div_mul_eq_mul_div, one_mul]
    rw [div_eq_div_iff (by positivity) (by positivity)]
    nlinarith [hkey, h_alpha_nonneg, Real.sqrt_nonneg (2/Real.pi)]
  rw [h_simplify] at hα_bi_le
  have h_e2_ge : 1 ≤ Real.exp 2 := Real.one_le_exp (by norm_num)
  have hπ_ge : 3 ≤ Real.pi := by linarith [Real.pi_gt_d2]
  have hgoal2 : 1 / (4 * Real.exp 2 * Real.pi) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [h_e2_ge, hπ_ge]
  linarith

/-- Marginalization helper (same as `ParitySwapCore`'s). -/
private theorem PSSI_marg_helper {n k : ℕ} (e : Fin k → Fin n)
    (g : Fin n → Bool → ℝ) (m : Fin k → Bool) :
    (∑ x : Fin n → Bool,
        (∏ i : Fin n, g i (x i)) *
        (∏ j : Fin k, (if x (e j) = m j then (1 : ℝ) else 0)))
      = ∏ i : Fin n,
          (∑ c : Bool, g i c *
            (∏ j : Fin k, (if e j = i then (if c = m j then (1:ℝ) else 0) else 1))) := by
  classical
  rw [Fintype.prod_sum (fun i c => g i c *
        (∏ j : Fin k, (if e j = i then (if c = m j then (1:ℝ) else 0) else 1)))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.prod_mul_distrib]
  congr 1
  show (∏ j : Fin k, (if x (e j) = m j then (1:ℝ) else 0))
      = ∏ i : Fin n, ∏ j : Fin k, (if e j = i then (if x i = m j then (1:ℝ) else 0) else 1)
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_eq_single (e j)]
  · simp
  · intro i _ hi
    rw [if_neg (by exact fun h => hi h.symm)]
  · intro h; exact absurd (Finset.mem_univ (e j)) h

/-- The marginalized form simplifies to the window product (same as `ParitySwapCore`'s). -/
private theorem PSSI_marg_helper2 {n k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (g : Fin n → Bool → ℝ) (m : Fin k → Bool)
    (hmarg : ∀ i : Fin n, g i true + g i false = 1) :
    (∑ x : Fin n → Bool,
        (∏ i : Fin n, g i (x i)) *
        (∏ j : Fin k, (if x (e j) = m j then (1 : ℝ) else 0)))
      = ∏ j : Fin k, g (e j) (m j) := by
  classical
  rw [PSSI_marg_helper e g m]
  set F : Fin n → ℝ := fun i =>
      (∑ c : Bool, g i c *
        (∏ j : Fin k, (if e j = i then (if c = m j then (1:ℝ) else 0) else 1))) with hF
  have hF_off : ∀ i : Fin n, (¬ ∃ j, e j = i) → F i = 1 := by
    intro i hex
    show (∑ c : Bool, g i c *
        (∏ j : Fin k, (if e j = i then (if c = m j then (1:ℝ) else 0) else 1))) = 1
    have hinner : ∀ c : Bool,
        (∏ j : Fin k, (if e j = i then (if c = m j then (1:ℝ) else 0) else 1)) = 1 := by
      intro c
      apply Finset.prod_eq_one
      intro j _
      rw [if_neg]; intro hej; exact hex ⟨j, hej⟩
    simp only [hinner, mul_one]
    rw [Fintype.sum_bool]; linarith [hmarg i]
  have hF_on : ∀ j : Fin k, F (e j) = g (e j) (m j) := by
    intro j₀
    show (∑ c : Bool, g (e j₀) c *
        (∏ j : Fin k, (if e j = e j₀ then (if c = m j then (1:ℝ) else 0) else 1)))
        = g (e j₀) (m j₀)
    have hinner : ∀ c : Bool,
        (∏ j : Fin k, (if e j = e j₀ then (if c = m j then (1:ℝ) else 0) else 1))
        = (if c = m j₀ then (1:ℝ) else 0) := by
      intro c
      rw [Finset.prod_eq_single j₀]
      · rw [if_pos rfl]
      · intro j _ hj
        rw [if_neg]; intro hej; exact hj (he hej)
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Fintype.sum_bool, hinner true, hinner false]
    rcases hm : m j₀ with _ | _ <;> simp
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => ∃ j, e j = i)]
  rw [Finset.prod_eq_one (s := Finset.univ.filter (fun i => ¬ ∃ j, e j = i)) ?_]
  · rw [mul_one]
    have himg : (Finset.univ.filter (fun i : Fin n => ∃ j, e j = i))
        = Finset.image e Finset.univ := by
      ext i; simp [Finset.mem_image]
    rw [himg, Finset.prod_image (fun a _ b _ hab => he hab)]
    apply Finset.prod_congr rfl
    intro j _; exact hF_on j
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hF_off i hi

theorem ParitySwapSignedIdentity :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 2 = 1 →
    ∀ (Se So : Workspace.Types.ProbVec.ProbVec n),
      (∀ i : Fin n, Se.p i =
        (if (i.val) % 2 = 0
         then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
              Real.sqrt n *
              ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
         else 0)) →
      (∀ i : Fin n, So.p i =
        (if (i.val) % 2 = 1
         then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
              Real.sqrt n *
              ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
         else 0)) →
    ∀ (m : Workspace.Types.BinVec.BinVec (n / 2))
      (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
      (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So)
      (r : ℤ), r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ) →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let ell : Finset (Fin (n / 2)) :=
        (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
      let LHS : ℝ :=
        ∑ b : Workspace.Types.BinVec.BinVec n,
          ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
            (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal
      let Q_e : ℝ :=
        ∏ j ∈ (Finset.univ.filter
                 (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
      let Q_o : ℝ :=
        ∏ j ∈ (Finset.univ.filter
                 (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
      -- mixed-parity case: the signed inner sum vanishes
      (((∃ j₁ ∈ ell, ∃ j₂ ∈ ell,
            ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 ≠ ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2) →
          LHS = 0)) ∧
      -- empty-window case
      ((ell = ∅) → LHS = Q_e - Q_o) ∧
      -- same-parity nonempty case: SIGNED identity with the k-way `ellFactor` factor
      (∀ p ∈ ({0, 1} : Finset ℤ),
          ell.Nonempty →
          (∀ j ∈ ell, ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = p) →
          LHS = (-1 : ℝ) ^ p.toNat *
                  (if p = 0 then Q_e else Q_o) *
                  (∏ j ∈ ell, ellFactor n α r (j : ℕ))) := by
  intro n hn hmod Se So hSe hSo m Ce Co r hr
  intro α ell LHS Q_e Q_o
  classical
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  -- range condition for r
  rw [Finset.mem_Icc] at hr
  obtain ⟨hr_lo, hr_hi⟩ := hr
  -- window indices lie in [0, n)
  have hwin_lb : ∀ j : Fin (n/2), 0 ≤ ((n/4 : ℕ) : ℤ) + r + (j : ℕ) := by
    intro j
    have : (0:ℤ) ≤ (j : ℕ) := by positivity
    linarith
  have hwin_ub : ∀ j : Fin (n/2), ((n/4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := by
    intro j
    have hjlt : (j : ℕ) < n/2 := j.isLt
    have hjlt' : ((j : ℕ) : ℤ) < (n/2 : ℕ) := by exact_mod_cast hjlt
    have hdiv : ((n/4 : ℕ) : ℤ) + ((n/4 : ℕ) : ℤ) + ((n/2 : ℕ) : ℤ) ≤ (n : ℤ) := by
      have : (n/4) + (n/4) + (n/2) ≤ n := by omega
      exact_mod_cast this
    linarith
  -- the window index map
  set idx : Fin (n/2) → Fin n := fun j =>
    ⟨(((n/4 : ℕ) : ℤ) + r + (j : ℕ)).toNat, by
      have hub := hwin_ub j
      have hlb := hwin_lb j
      have h0 : ((((n/4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
          = ((n/4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hlb
      have : ((((n/4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by rw [h0]; exact hub
      exact_mod_cast this⟩ with hidx_def
  have hidx_val : ∀ j : Fin (n/2),
      (idx j).val = (((n/4 : ℕ) : ℤ) + r + (j : ℕ)).toNat := fun j => rfl
  have hidx_cast : ∀ j : Fin (n/2),
      (((n/4 : ℕ) : ℤ) + r + (j : ℕ)) = ((idx j).val : ℤ) := by
    intro j
    rw [hidx_val j]
    exact (Int.toNat_of_nonneg (hwin_lb j)).symm
  have hidx_inj : Function.Injective idx := by
    intro a b hab
    have := congrArg (fun (z : Fin n) => (z.val : ℤ)) hab
    simp only at this
    rw [← hidx_cast a, ← hidx_cast b] at this
    have : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := by linarith
    have : (a : ℕ) = (b : ℕ) := by exact_mod_cast this
    exact Fin.ext this
  -- toReal of Ce / Co
  have hCe_real : ∀ b : BinVec n,
      (Ce.toPMF b).toReal
        = ∏ i : Fin n, (if b.bit i then Se.p i else 1 - Se.p i) := by
    intro b
    rw [Ce.prod_factorisation b, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [ENNReal.toReal_ofReal]
    by_cases hb : b.bit i
    · rw [if_pos hb]; exact Se.nonneg i
    · rw [if_neg hb]; linarith [Se.le_one i]
  have hCo_real : ∀ b : BinVec n,
      (Co.toPMF b).toReal
        = ∏ i : Fin n, (if b.bit i then So.p i else 1 - So.p i) := by
    intro b
    rw [Co.prod_factorisation b, ENNReal.toReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [ENNReal.toReal_ofReal]
    by_cases hb : b.bit i
    · rw [if_pos hb]; exact So.nonneg i
    · rw [if_neg hb]; linarith [So.le_one i]
  -- toReal of middleIndicator
  have hmid_real : ∀ b : BinVec n,
      (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal
        = ∏ j : Fin (n/2), (if b.bit (idx j) = m.bit j then (1:ℝ) else 0) := by
    intro b
    unfold Workspace.Types.PartialDeletionProcess.middleIndicator
    have hrange : ∀ j : Fin (n / 2),
        0 ≤ ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) ∧
        ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := fun j => ⟨hwin_lb j, hwin_ub j⟩
    rw [dif_pos hrange]
    have hidx_eq_inner : ∀ j : Fin (n/2),
        (⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat, by
          have hj := hrange j
          have : (((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat < n := by
            have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hj.1
            have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by
              rw [h0]; exact hj.2
            exact_mod_cast this
          exact this⟩ : Fin n) = idx j := by
      intro j; apply Fin.ext; rfl
    have hpred : (∀ j : Fin (n / 2),
        b.bit (⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat, by
          have hj := hrange j
          have : (((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat < n := by
            have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hj.1
            have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by
              rw [h0]; exact hj.2
            exact_mod_cast this
          exact this⟩ : Fin n) = m.bit j)
      ↔ (∀ j : Fin (n/2), b.bit (idx j) = m.bit j) := by
      constructor
      · intro h j; rw [← hidx_eq_inner j]; exact h j
      · intro h j; rw [hidx_eq_inner j]; exact h j
    rw [show (if (∀ j : Fin (n / 2),
        b.bit (⟨(((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat, by
          have hj := hrange j
          have : (((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat < n := by
            have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j : ℕ) := Int.toNat_of_nonneg hj.1
            have : ((((n / 4 : ℕ) : ℤ) + r + (j : ℕ)).toNat : ℤ) < (n : ℤ) := by
              rw [h0]; exact hj.2
            exact_mod_cast this
          exact this⟩ : Fin n) = m.bit j) then (1:ENNReal) else 0)
        = (if (∀ j : Fin (n/2), b.bit (idx j) = m.bit j) then (1:ENNReal) else 0)
        from by rw [if_congr hpred rfl rfl]]
    rw [show (∏ j : Fin (n/2), (if b.bit (idx j) = m.bit j then (1:ℝ) else 0))
          = (if (∀ j : Fin (n/2), b.bit (idx j) = m.bit j) then (1:ℝ) else 0)
        from by
          rw [Finset.prod_boole]
          congr 1
          apply propext
          constructor
          · intro h j; exact h j (Finset.mem_univ j)
          · intro h j _; exact h j]
    by_cases hcond : (∀ j : Fin (n/2), b.bit (idx j) = m.bit j)
    · rw [if_pos hcond, if_pos hcond]; simp
    · rw [if_neg hcond, if_neg hcond]; simp
  -- the marginalized cM_e / cM_o
  set cM_e : ℝ := ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) with hcMe
  set cM_o : ℝ := ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) with hcMo
  have hsum_e : (∑ b : BinVec n,
        (Ce.toPMF b).toReal *
          (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)
      = cM_e := by
    rw [← Equiv.sum_comp (Workspace.Types.BinVec.equivFun (n := n)).symm
          (fun b => (Ce.toPMF b).toReal *
            (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)]
    have heq : ∀ x : Fin n → Bool,
        (Ce.toPMF (Workspace.Types.BinVec.equivFun.symm x)).toReal
          * (Workspace.Types.PartialDeletionProcess.middleIndicator n
              (Workspace.Types.BinVec.equivFun.symm x) m r).toReal
        = (∏ i : Fin n, (if x i then Se.p i else 1 - Se.p i))
          * (∏ j : Fin (n/2), (if x (idx j) = m.bit j then (1:ℝ) else 0)) := by
      intro x
      rw [hCe_real, hmid_real]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
    rw [PSSI_marg_helper2 idx hidx_inj
          (fun i c => if c then Se.p i else 1 - Se.p i) (fun j => m.bit j)
          (fun i => by simp)]
  have hsum_o : (∑ b : BinVec n,
        (Co.toPMF b).toReal *
          (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)
      = cM_o := by
    rw [← Equiv.sum_comp (Workspace.Types.BinVec.equivFun (n := n)).symm
          (fun b => (Co.toPMF b).toReal *
            (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)]
    have heq : ∀ x : Fin n → Bool,
        (Co.toPMF (Workspace.Types.BinVec.equivFun.symm x)).toReal
          * (Workspace.Types.PartialDeletionProcess.middleIndicator n
              (Workspace.Types.BinVec.equivFun.symm x) m r).toReal
        = (∏ i : Fin n, (if x i then So.p i else 1 - So.p i))
          * (∏ j : Fin (n/2), (if x (idx j) = m.bit j then (1:ℝ) else 0)) := by
      intro x
      rw [hCo_real, hmid_real]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
    rw [PSSI_marg_helper2 idx hidx_inj
          (fun i c => if c then So.p i else 1 - So.p i) (fun j => m.bit j)
          (fun i => by simp)]
  -- LHS = cM_e - cM_o
  have hLHS_eq : LHS = cM_e - cM_o := by
    show (∑ b : BinVec n,
        ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
          (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)
        = cM_e - cM_o
    rw [← hsum_e, ← hsum_o, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _; ring
  -- range hyps for MiddleWeightExplicit
  have hcast4 : ((n/4 : ℕ) : ℤ) = (n/4 : ℤ) := Int.natCast_div n 4
  have hcast2 : ((n/2 : ℕ) : ℤ) = (n/2 : ℤ) := Int.natCast_div n 2
  have hMW_lo : 0 ≤ r + (n / 4 : ℤ) := by rw [← hcast4]; linarith [hr_lo]
  have hMW_hi : r + (n / 4 : ℤ) + (n / 2 : ℤ) ≤ (n : ℤ) := by
    rw [← hcast4, ← hcast2]
    have hdiv : ((n/4 : ℕ) : ℤ) + ((n/4 : ℕ) : ℤ) + ((n/2 : ℕ) : ℤ) ≤ (n : ℤ) := by
      have : (n/4) + (n/4) + (n/2) ≤ n := by omega
      exact_mod_cast this
    linarith [hr_hi]
  have hidx_spec : ∀ j : Fin (n / 2),
      (idx j).val = ((n / 4 : ℤ) + r + (j : ℕ)).toNat := by
    intro j
    rw [hidx_val j, hcast4]
  have hMW := MiddleWeightExplicit n hn hmod Se So hSe hSo m r hMW_lo hMW_hi idx hidx_spec
  simp only at hMW
  obtain ⟨hQe_bd, hQo_bd, hMixed, hEmpty, hSameP⟩ := hMW
  -- Identify the lemma's `ell`, `Q_e`, `Q_o`, `ellProd` with ours.
  -- MWE's `parity j = ((n/4)+r+j) % 2`; MWE's `ell = filter (m.bit · = true)` = our `ell`.
  -- MWE's Q_e/Q_o use index `((n/4)+r+j).toNat` inside `b`; this matches our Q_e/Q_o.
  -- MWE's `cM_e`/`cM_o` are byte-identical to ours (same idx).
  -- The k-way `ellFactor` product equals MWE's `ellProd`.
  set ellProdF : ℝ := ∏ j ∈ ell, ellFactor n α r (j : ℕ) with hellProdF
  -- bound facts for positivity of factor denominators
  have h_b_nonneg : ∀ j : Fin (n/2),
      0 ≤ α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro j
    have hπ_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by linarith)
    have : (0:ℝ) ≤ α := by
      rw [show α = (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n from rfl]
      have := Real.exp_pos 2
      positivity
    positivity
  have h_b_le_half : ∀ j : Fin (n/2),
      α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1/2 := by
    intro j
    show (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
         ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1/2
    exact PSSI_alpha_b_le_half n hn _
  have h_factor_pos : ∀ j : Fin (n/2),
      (0:ℝ) < 1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro j; linarith [h_b_le_half j]
  -- The k-way `ellFactor` product equals MWE's `ellProd` shape.
  have hellProdF_eq : ellProdF
      = ∏ j ∈ ell,
          (α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) /
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
    rw [hellProdF]
    apply Finset.prod_congr rfl
    intro j _
    -- ellFactor n α r j = α·X/(1-α·X), X = binPMFInt n (1/2) (r + n/4 + j)
    unfold ellFactor
    simp only
    -- X = binPMFInt n (1/2) (r + (n/4:ℤ) + j) = C(n, (r+n/4+j).toNat)·2^{-n}
    have hxlo : (0 : ℤ) ≤ r + (n / 4 : ℤ) + (j : ℤ) := by
      have := hwin_lb j; rw [hcast4] at this; linarith
    have hxhi : r + (n / 4 : ℤ) + (j : ℤ) ≤ (n : ℤ) := by
      have := hwin_ub j; rw [hcast4] at this; linarith
    have hX := Workspace.PriorWork.AltRSumKwayFourierBridge.binPMFInt_half n
      (r + (n / 4 : ℤ) + (j : ℤ)) hxlo hxhi
    -- the toNat index used in MWE is ((n/4:ℤ)+r+j).toNat; reconcile order with binPMFInt's
    have htoNat : (r + (n / 4 : ℤ) + (j : ℤ)).toNat = ((n / 4 : ℤ) + r + (j : ℕ)).toNat := by
      congr 1; ring
    rw [hX, htoNat]
  -- Now case split exactly as MWE.
  refine ⟨?_, ?_, ?_⟩
  · -- mixed parity → LHS = 0
    intro hmix
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := hmix
    -- translate to MWE's `mixedParity`
    have hMWmix : ∃ j₁ ∈ ell, ∃ j₂ ∈ ell,
        ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 ≠ ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2 :=
      ⟨j₁, hj₁, j₂, hj₂, hne⟩
    obtain ⟨hce0, hco0⟩ := hMixed hMWmix
    rw [hLHS_eq, hcMe, hcMo, hce0, hco0, sub_zero]
  · -- empty → LHS = Q_e - Q_o
    intro hell_e
    obtain ⟨hcMe_eq, hcMo_eq⟩ := hEmpty hell_e
    show LHS = Q_e - Q_o
    rw [hLHS_eq, hcMe, hcMo, hcMe_eq, hcMo_eq]
  · -- same-parity nonempty → signed identity
    intro p hp_mem hell_ne hpar_all
    have hSP := hSameP p hp_mem hell_ne hpar_all
    obtain ⟨⟨hp1e, hp0e⟩, ⟨hp0o, hp1o⟩⟩ := hSP
    have hp_cases : p = 0 ∨ p = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      exact hp_mem
    rcases hp_cases with hp0 | hp1
    · -- p = 0: cM_e = Q_e * ellProd, cM_o = 0
      have hce := hp0e hp0
      have hco := hp0o hp0
      show LHS = (-1 : ℝ) ^ p.toNat * (if p = 0 then Q_e else Q_o) * ellProdF
      rw [hLHS_eq, hcMe, hcMo, hce, hco, sub_zero]
      rw [hp0]
      simp only [Int.toNat_zero, pow_zero, one_mul, if_true]
      -- goal: Q_e_prod(MWE) * ellProd(MWE) = Q_e * ellProdF
      show _ = Q_e * ellProdF
      rw [hellProdF_eq]
    · -- p = 1: cM_e = 0, cM_o = Q_o * ellProd
      have hce := hp1e hp1
      have hco := hp1o hp1
      show LHS = (-1 : ℝ) ^ p.toNat * (if p = 0 then Q_e else Q_o) * ellProdF
      rw [hLHS_eq, hcMe, hcMo, hce, hco, zero_sub]
      rw [hp1]
      have hif : (if (1 : ℤ) = 0 then Q_e else Q_o) = Q_o := by norm_num
      rw [hif, show ((1 : ℤ).toNat) = 1 from rfl, pow_one]
      -- goal: - (Q_o_prod(MWE) * ellProd(MWE)) = -1 * Q_o * ellProdF
      show _ = -1 * Q_o * ellProdF
      rw [hellProdF_eq]
      ring
