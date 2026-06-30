import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.LengthsOnlyProcess
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.WitnessCoinFlipFormula
import Workspace.ProofLemmas.BinomialPmfMaxBound
import Workspace.ProofLemmas.CoinFlipDistExists
import Workspace.ProofLemmas.OddNConstructionArith
import Workspace.PriorWork.AltRSumKwayFourierBridge

/-!
# `n ≡ 3 (mod 4)` parity-swap foundation

The witness construction's middle-window analysis (Lemma 6 of Rivkin–Valiant–Valiant
(2024), arXiv:2412.00674v1, §3.1, lines 297-305) is encoded by the four lemmas
`MiddleWeightExplicit`, `MixedParityVanishes`, `ParitySwapCore`,
`ParitySwapSignedIdentity`, all carrying a hypothesis `n % 8 = 1`.

**Key structural fact** (this file): every one of those four proofs operates ONLY on
`middleIndicator n b m r`, the `n/2`-bit middle window over positions
`[n/4+r, n/4+r+n/2)` indexed by `idx j = ⟨(n/4+r+j).toNat, …⟩`. The window's
in-range bound needs only `n/4 + n/4 + n/2 ≤ n`, which holds for ALL `n` (it is
`omega`-true: `4·(n/4) ≤ n` and `2·(n/2) ≤ n`). In particular it holds for
`n ≡ 3 (mod 4)` where `n/2 = 2·(n/4)+1`
(`OddNConstructionArith.gate_off_by_one_of_mod4_eq_three`), because
`n/4+n/4+n/2 = (n/2−1)+n/2 = n−1 ≤ n`.

The off-by-one for `n ≡ 3 (mod 4)` pinned in `lean_knowledge.md` (F83/F88) is a
property of the SUFFIX boundary (`3*(n/4)+r` vs `3*(n/4)+r+1`), which the
parity-swap layer never touches: it sums over the full bit-vector `b` against the
middle indicator only. The paper's parity argument — the `S_e` vs `S_o` probability
difference is the alternating sum over `r` driven by the parity of `r+ℓ_j`, with the
`∏(1−α·bin)` term equal by symmetry and `O(1)` — is RESIDUE-INDEPENDENT.

The existing public theorems above destructure but NEVER use the `n%8=1`
hypothesis:
* `WitnessCoinFlipFormula` does `intro n _ _ …` (discards `hn` and `hmod`);
* `MiddleWeightExplicit` does `intro n hn hmod …` then never references `hmod`;
* `MixedParityVanishes` forwards `hmod` only into `WitnessCoinFlipFormula` (drops it);
* `ParitySwapCore` / `ParitySwapSignedIdentity` forward `hmod` only into
  `MiddleWeightExplicit`.

We therefore re-derive each lemma with the hypothesis `n % 4 = 3` in place of
`n % 8 = 1`, reusing each proof body verbatim (the bodies are residue-free; the only
arithmetic input is the `omega`-true range bound). This file imports only built
modules and edits no existing file; the build stays green.
-/

namespace ParitySwapOddThree

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.LengthsOnlyProcess
open Workspace.Types.AlternatingSumExpression
open scoped BigOperators

/-! ## `α * b_i ≤ 1/2` helper (re-derived from `BinomialPmfMaxBound`). -/
private lemma PSOT_alpha_b_le_half (n : ℕ) (hn : (10 ^ 12 : ℕ) ≤ n) (i : ℕ) :
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

/-! ## Middle-weight / window factorization for `n ≡ 3 (mod 4)`.

This is the `n ≡ 3 (mod 4)` analogue of `MiddleWeightExplicit`.  The proof body is
identical to the `n % 8 = 1` original because that body never uses its `hmod`
hypothesis: the only arithmetic about `n` it relies on is the `omega`-true range
bound `n/4 + n/4 + n/2 ≤ n`, which holds at `n ≡ 3 (mod 4)` (where
`n/2 = 2*(n/4)+1`, so the sum is `n−1 ≤ n`). The corrected suffix boundary
`3*(n/4)+r+1` of `PartialDominatesHCoreOddThreeCorrected` does NOT enter here:
the middle window is the genuine `n/2`-bit window `[n/4+r, n/4+r+n/2)`, untouched
by the suffix shift. -/
theorem MiddleWeightExplicit_oddThree :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 4 = 3 →
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
        ∀ (m : BinVec (n / 2)) (r : ℤ),
          0 ≤ r + (n / 4 : ℤ) → r + (n / 4 : ℤ) + (n / 2 : ℤ) ≤ (n : ℤ) →
          ∀ (idx : Fin (n / 2) → Fin n),
            (∀ j : Fin (n / 2),
                (idx j).val = ((n / 4 : ℤ) + r + (j : ℕ)).toNat) →
          let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                       Real.sqrt n
          let b : ℕ → ℝ := fun i => (Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹
          let cM_e : ℝ :=
            ∏ j : Fin (n / 2),
              (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
          let cM_o : ℝ :=
            ∏ j : Fin (n / 2),
              (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
          let ell : Finset (Fin (n / 2)) :=
            (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
          let parity : Fin (n / 2) → ℤ :=
            fun j => ((n / 4 : ℤ) + r + (j : ℕ)) % 2
          let Q_e : ℝ :=
            ∏ j ∈ (Finset.univ : Finset (Fin (n / 2))).filter
                     (fun j => parity j = 0),
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let Q_o : ℝ :=
            ∏ j ∈ (Finset.univ : Finset (Fin (n / 2))).filter
                     (fun j => parity j = 1),
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let ellProd : ℝ :=
            ∏ j ∈ ell,
              (α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat) /
              (1 - α * b ((n / 4 : ℤ) + r + (j : ℕ)).toNat)
          let mixedParity : Prop :=
            ∃ j₁ ∈ ell, ∃ j₂ ∈ ell, parity j₁ ≠ parity j₂
          (((1 : ℝ) / 2) ^ (n / 2) ≤ Q_e ∧ Q_e ≤ 1) ∧
          (((1 : ℝ) / 2) ^ (n / 2) ≤ Q_o ∧ Q_o ≤ 1) ∧
          (mixedParity → cM_e = 0 ∧ cM_o = 0) ∧
          (ell = ∅ → cM_e = Q_e ∧ cM_o = Q_o) ∧
          (∀ p ∈ ({0, 1} : Finset ℤ),
              ell.Nonempty →
              (∀ j ∈ ell, parity j = p) →
              ((p = 1 → cM_e = 0) ∧
               (p = 0 → cM_e = Q_e * ellProd)) ∧
              ((p = 0 → cM_o = 0) ∧
               (p = 1 → cM_o = Q_o * ellProd))) := by
  intro n hn hmod Se So hSe hSo m r hr1 hr2 idx hidx
  intro α b cM_e cM_o ell parity Q_e Q_o ellProd mixedParity
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  have hidx_nonneg : ∀ j : Fin (n/2), 0 ≤ (n/4 : ℤ) + r + (j : ℕ) := by
    intro j
    have h1 : (0 : ℤ) ≤ (j : ℕ) := by positivity
    linarith
  have hidx_eq : ∀ j : Fin (n/2),
      ((n/4 : ℤ) + r + (j : ℕ)) = ((idx j).val : ℤ) := by
    intro j
    rw [hidx j]
    exact (Int.toNat_of_nonneg (hidx_nonneg j)).symm
  have hidx_toNat : ∀ j : Fin (n/2),
      ((n/4 : ℤ) + r + (j : ℕ)).toNat = (idx j).val := by
    intro j; exact (hidx j).symm
  have hSe_idx : ∀ j : Fin (n/2),
      Se.p (idx j) = if ((idx j).val) % 2 = 0
                     then α * b (idx j).val
                     else 0 := by
    intro j; rw [hSe (idx j)]
  have hSo_idx : ∀ j : Fin (n/2),
      So.p (idx j) = if ((idx j).val) % 2 = 1
                     then α * b (idx j).val
                     else 0 := by
    intro j; rw [hSo (idx j)]
  have hαb_le_half : ∀ j : Fin (n/2), α * b (idx j).val ≤ 1/2 := by
    intro j
    show (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
         ((Nat.choose n (idx j).val : ℝ) * (2 ^ n : ℝ)⁻¹) ≤ 1/2
    exact PSOT_alpha_b_le_half n hn (idx j).val
  have hαb_nonneg : ∀ j : Fin (n/2), 0 ≤ α * b (idx j).val := by
    intro j
    show 0 ≤ (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
            ((Nat.choose n (idx j).val : ℝ) * (2 ^ n : ℝ)⁻¹)
    have h1 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have h2 : 0 ≤ (Nat.choose n (idx j).val : ℝ) := Nat.cast_nonneg _
    have h3 : 0 ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
    have hπ_pos : 0 < Real.pi := Real.pi_pos
    have hsqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have h_factor_form : ∀ j : Fin (n/2),
      (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) = 1 - α * b (idx j).val := by
    intro j; rw [hidx_toNat j]
  have h_factor_lb : ∀ j : Fin (n/2),
      (1 : ℝ)/2 ≤ 1 - α * b (idx j).val := by
    intro j; linarith [hαb_le_half j]
  have h_factor_ub : ∀ j : Fin (n/2),
      1 - α * b (idx j).val ≤ 1 := by
    intro j; linarith [hαb_nonneg j]
  have h_factor_nonneg : ∀ j : Fin (n/2),
      (0 : ℝ) ≤ 1 - α * b (idx j).val := by
    intro j; linarith [h_factor_lb j]
  have h_factor_pos : ∀ j : Fin (n/2),
      (0 : ℝ) < 1 - α * b (idx j).val := by
    intro j; linarith [h_factor_lb j]
  have h_factor_ne_zero : ∀ j : Fin (n/2),
      (1 - α * b (idx j).val) ≠ 0 := by
    intro j; linarith [h_factor_pos j]
  have hQ_bound : ∀ (S : Finset (Fin (n/2))),
      ((1 : ℝ)/2) ^ S.card ≤
      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1 := by
    intro S
    refine ⟨?_, ?_⟩
    · have hprod_ge : ∏ j ∈ S, ((1:ℝ)/2) ≤
                      ∏ j ∈ S, (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) := by
        apply Finset.prod_le_prod
        · intros; norm_num
        · intro j _; rw [h_factor_form j]; exact h_factor_lb j
      simpa [Finset.prod_const] using hprod_ge
    · apply Finset.prod_le_one
      · intro j _; rw [h_factor_form j]; exact h_factor_nonneg j
      · intro j _; rw [h_factor_form j]; exact h_factor_ub j
  have hcard_filter_e : (Finset.univ.filter
        (fun j : Fin (n/2) => parity j = 0)).card ≤ n / 2 := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  have hcard_filter_o : (Finset.univ.filter
        (fun j : Fin (n/2) => parity j = 1)).card ≤ n / 2 := by
    apply le_trans (Finset.card_filter_le _ _)
    simp
  have hpow_le_half : ∀ k : ℕ, k ≤ n / 2 → ((1:ℝ)/2)^(n/2) ≤ ((1:ℝ)/2)^k := by
    intro k hk
    apply pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
                                (by norm_num : (1:ℝ)/2 ≤ 1) hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show ((1:ℝ)/2)^(n/2) ≤ Q_e ∧ Q_e ≤ 1
    show ((1:ℝ)/2)^(n/2) ≤ ∏ j ∈ Finset.univ.filter (fun j => parity j = 0),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
         ∏ j ∈ Finset.univ.filter (fun j => parity j = 0),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1
    obtain ⟨hlow, hup⟩ := hQ_bound (Finset.univ.filter (fun j => parity j = 0))
    refine ⟨le_trans (hpow_le_half _ hcard_filter_e) hlow, hup⟩
  · show ((1:ℝ)/2)^(n/2) ≤ Q_o ∧ Q_o ≤ 1
    show ((1:ℝ)/2)^(n/2) ≤ ∏ j ∈ Finset.univ.filter (fun j => parity j = 1),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ∧
         ∏ j ∈ Finset.univ.filter (fun j => parity j = 1),
                            (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) ≤ 1
    obtain ⟨hlow, hup⟩ := hQ_bound (Finset.univ.filter (fun j => parity j = 1))
    refine ⟨le_trans (hpow_le_half _ hcard_filter_o) hlow, hup⟩
  · show mixedParity → cM_e = 0 ∧ cM_o = 0
    intro hmixed
    obtain ⟨j₁, hj₁_ell, j₂, hj₂_ell, hpar_diff⟩ := hmixed
    have hbit_j1 : m.bit j₁ = true := by
      have : j₁ ∈ ell := hj₁_ell
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hbit_j2 : m.bit j₂ = true := by
      have : j₂ ∈ ell := hj₂_ell
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    have hpar_j1 : ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 = 0 ∨
                   ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 = 1 := by omega
    have hpar_j2 : ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 = 0 ∨
                   ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 = 1 := by omega
    have hparity_j1 : parity j₁ = ((n/4 : ℤ) + r + (j₁ : ℕ)) % 2 := rfl
    have hparity_j2 : parity j₂ = ((n/4 : ℤ) + r + (j₂ : ℕ)) % 2 := rfl
    rw [hparity_j1, hparity_j2] at hpar_diff
    rcases hpar_j1 with hp1 | hp1 <;> rcases hpar_j2 with hp2 | hp2
    · exact absurd (hp1.trans hp2.symm) hpar_diff
    · have hidx_j1_par : (idx j₁).val % 2 = 0 := by have := hidx_eq j₁; omega
      have hidx_j2_par : (idx j₂).val % 2 = 1 := by have := hidx_eq j₂; omega
      refine ⟨?_, ?_⟩
      · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₂)
        rw [if_pos hbit_j2, hSe_idx j₂]
        rw [if_neg (by omega : ¬ ((idx j₂).val % 2 = 0))]
      · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₁)
        rw [if_pos hbit_j1, hSo_idx j₁]
        rw [if_neg (by omega : ¬ ((idx j₁).val % 2 = 1))]
    · have hidx_j1_par : (idx j₁).val % 2 = 1 := by have := hidx_eq j₁; omega
      have hidx_j2_par : (idx j₂).val % 2 = 0 := by have := hidx_eq j₂; omega
      refine ⟨?_, ?_⟩
      · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₁)
        rw [if_pos hbit_j1, hSe_idx j₁]
        rw [if_neg (by omega : ¬ ((idx j₁).val % 2 = 0))]
      · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ j₂)
        rw [if_pos hbit_j2, hSo_idx j₂]
        rw [if_neg (by omega : ¬ ((idx j₂).val % 2 = 1))]
    · exact absurd (hp1.trans hp2.symm) hpar_diff
  · show ell = ∅ → cM_e = Q_e ∧ cM_o = Q_o
    intro hell_empty
    have hbits_false : ∀ j : Fin (n/2), m.bit j = false := by
      intro j
      by_contra h
      have hj_in : j ∈ ell := by
        simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
        cases hb : m.bit j
        · simp [hb] at h
        · rfl
      rw [hell_empty] at hj_in
      exact (Finset.notMem_empty j) hj_in
    refine ⟨?_, ?_⟩
    · show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
         = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 0),
              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)))
                = ∏ j : Fin (n/2), (1 - Se.p (idx j))
            from Finset.prod_congr rfl (fun j _ => by rw [if_neg (by rw [hbits_false j]; simp)])]
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (1 - Se.p (idx j)))
                = ∏ j : Fin (n/2),
                    if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1
            from Finset.prod_congr rfl (fun j _ => by
              rw [hSe_idx j]
              by_cases hpar : (idx j).val % 2 = 0
              · rw [if_pos hpar, if_pos hpar]
              · rw [if_neg hpar, if_neg hpar]; ring)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => (idx j).val % 2 = 0)]
      have heven : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                      if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                      (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_pos hj]
      have hodd : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ (idx j).val % 2 = 0),
                      if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [heven, hodd, mul_one]
      apply Finset.prod_congr ?_ ?_
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; show parity j = 0
          have := hidx_eq j
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0
          omega
        · intro h
          show (idx j).val % 2 = 0
          have hpj : ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0 := h
          have := hidx_eq j
          omega
      · intro j hj
        rw [h_factor_form j]
    · show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
         = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 1),
              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)))
                = ∏ j : Fin (n/2), (1 - So.p (idx j))
            from Finset.prod_congr rfl (fun j _ => by rw [if_neg (by rw [hbits_false j]; simp)])]
      conv_lhs =>
        rw [show (∏ j : Fin (n/2), (1 - So.p (idx j)))
                = ∏ j : Fin (n/2),
                    if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1
            from Finset.prod_congr rfl (fun j _ => by
              rw [hSo_idx j]
              by_cases hpar : (idx j).val % 2 = 1
              · rw [if_pos hpar, if_pos hpar]
              · rw [if_neg hpar, if_neg hpar]; ring)]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => (idx j).val % 2 = 1)]
      have hodd_part : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_pos hj]
      have heven_part : (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ (idx j).val % 2 = 1),
                          if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                    = 1 := by
        apply Finset.prod_eq_one
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hodd_part, heven_part, mul_one]
      apply Finset.prod_congr ?_ ?_
      · ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro h; show parity j = 1
          have := hidx_eq j
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1
          omega
        · intro h
          show (idx j).val % 2 = 1
          have hpj : ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1 := h
          have := hidx_eq j
          omega
      · intro j hj
        rw [h_factor_form j]
  · intro p hp_mem hell_ne hpar_all
    have hp_cases : p = 0 ∨ p = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      exact hp_mem
    have hidx_par_of_ell : ∀ j ∈ ell, ((idx j).val : ℤ) % 2 = p := by
      intro j hj
      have hpj : parity j = p := hpar_all j hj
      have hp1 : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
      rw [hp1] at hpj
      have := hidx_eq j
      omega
    have hbit_of_ell : ∀ j ∈ ell, m.bit j = true := by
      intro j hj
      simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · intro hp1
      obtain ⟨j₀, hj₀⟩ := hell_ne
      have hbit_j0 : m.bit j₀ = true := hbit_of_ell j₀ hj₀
      have hidxj0 := hidx_par_of_ell j₀ hj₀
      rw [hp1] at hidxj0
      have hidx_par1 : (idx j₀).val % 2 = 1 := by
        have h1 : ((idx j₀).val : ℤ) % 2 = 1 := hidxj0
        omega
      show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j₀)
      rw [if_pos hbit_j0, hSe_idx j₀]
      rw [if_neg (by omega : ¬ ((idx j₀).val % 2 = 0))]
    · intro hp0
      have hidx_par_ell : ∀ j ∈ ell, (idx j).val % 2 = 0 := by
        intro j hj
        have h1 := hidx_par_of_ell j hj
        rw [hp0] at h1
        omega
      have h_parity_eq_idx : ∀ j : Fin (n/2),
          parity j = 0 ↔ (idx j).val % 2 = 0 := by
        intro j
        have := hidx_eq j
        constructor
        · intro h
          show (idx j).val % 2 = 0
          have hp1 : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
          rw [hp1] at h
          omega
        · intro h
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 0
          omega
      have hQe_filter_eq :
          (Finset.univ.filter (fun j : Fin (n/2) => parity j = 0)) =
          (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_parity_eq_idx j
      show ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
         = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 0),
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)) *
           (∏ j ∈ ell,
                (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat))
      rw [hQe_filter_eq]
      have hQe_simp : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                        (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                        (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _; rw [h_factor_form j]
      rw [hQe_simp]
      have hellProd_simp : ∏ j ∈ ell,
                              (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                        = ∏ j ∈ ell,
                              (α * b (idx j).val) / (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _
        rw [hidx_toNat j]
      rw [hellProd_simp]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => m.bit j = true)]
      have hell_filter : (Finset.univ.filter (fun j : Fin (n/2) => m.bit j = true)) = ell := rfl
      rw [hell_filter]
      have hLHS_ell : ∏ j ∈ ell,
                        (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
                    = ∏ j ∈ ell, Se.p (idx j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_pos (hbit_of_ell j hj)]
      rw [hLHS_ell]
      have hLHS_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j))
                        = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (1 - Se.p (idx j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hLHS_notell]
      have hSe_ell : ∏ j ∈ ell, Se.p (idx j)
                    = ∏ j ∈ ell, α * b (idx j).val := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hSe_idx j, if_pos (hidx_par_ell j hj)]
      rw [hSe_ell]
      have hSe_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (1 - Se.p (idx j))
                      = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [hSe_idx j]
        by_cases hpar : (idx j).val % 2 = 0
        · rw [if_pos hpar, if_pos hpar]
        · rw [if_neg hpar, if_neg hpar]; ring
      rw [hSe_notell]
      have hQe_split : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0),
                          (1 - α * b (idx j).val)
                      = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                        (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                            ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
                          (1 - α * b (idx j).val)) := by
        rw [show ell = Finset.univ.filter (fun j : Fin (n/2) =>
                m.bit j = true ∧ (idx j).val % 2 = 0) from by
              ext j
              simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; refine ⟨h, ?_⟩
                exact hidx_par_ell j (by simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
              · intro ⟨h1, _⟩; exact h1]
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 0))
              (fun j => m.bit j = true)]
        congr 1
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
      rw [hQe_split]
      have hLHS_notell_split :
          ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
            (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
          = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
              ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
            (1 - α * b (idx j).val)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true))
              (fun j => (idx j).val % 2 = 0)]
        have h1 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => (idx j).val % 2 = 0),
                    (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                        ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
                    (1 - α * b (idx j).val) := by
          rw [show (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                    (fun j : Fin (n/2) => (idx j).val % 2 = 0)
              = Finset.univ.filter (fun j : Fin (n/2) =>
                    ¬ m.bit j = true ∧ (idx j).val % 2 = 0) from by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
          apply Finset.prod_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_pos hj.2]
        have h2 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => ¬ (idx j).val % 2 = 0),
                    (if (idx j).val % 2 = 0 then 1 - α * b (idx j).val else 1)
                = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_neg hj.2]
        rw [h1, h2, mul_one]
      rw [hLHS_notell_split]
      have hProd_combine : (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                           (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val))
                         = ∏ j ∈ ell, α * b (idx j).val := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        field_simp [h_factor_ne_zero j]
      calc (∏ j ∈ ell, α * b (idx j).val) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val)
          = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
            (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val) := by
            rw [hProd_combine]
        _ = ((∏ j ∈ ell, (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 0),
              (1 - α * b (idx j).val)) *
            ∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val) := by ring
    · intro hp0
      obtain ⟨j₀, hj₀⟩ := hell_ne
      have hbit_j0 : m.bit j₀ = true := hbit_of_ell j₀ hj₀
      have hidxj0 := hidx_par_of_ell j₀ hj₀
      rw [hp0] at hidxj0
      have hidx_par0 : (idx j₀).val % 2 = 0 := by
        have h1 : ((idx j₀).val : ℤ) % 2 = 0 := hidxj0
        omega
      show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ j₀)
      rw [if_pos hbit_j0, hSo_idx j₀]
      rw [if_neg (by omega : ¬ ((idx j₀).val % 2 = 1))]
    · intro hp1
      have hidx_par_ell : ∀ j ∈ ell, (idx j).val % 2 = 1 := by
        intro j hj
        have h1 := hidx_par_of_ell j hj
        rw [hp1] at h1
        omega
      have h_parity_eq_idx : ∀ j : Fin (n/2),
          parity j = 1 ↔ (idx j).val % 2 = 1 := by
        intro j
        have := hidx_eq j
        constructor
        · intro h
          show (idx j).val % 2 = 1
          have hp_def : parity j = ((n/4 : ℤ) + r + (j : ℕ)) % 2 := rfl
          rw [hp_def] at h
          omega
        · intro h
          show ((n/4 : ℤ) + r + (j : ℕ)) % 2 = 1
          omega
      have hQo_filter_eq :
          (Finset.univ.filter (fun j : Fin (n/2) => parity j = 1)) =
          (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_parity_eq_idx j
      show ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
         = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => parity j = 1),
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)) *
           (∏ j ∈ ell,
                (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat))
      rw [hQo_filter_eq]
      have hQo_simp : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                        (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                    = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                        (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _; rw [h_factor_form j]
      rw [hQo_simp]
      have hellProd_simp : ∏ j ∈ ell,
                              (α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat) /
                              (1 - α * b ((n/4 : ℤ) + r + (j : ℕ)).toNat)
                        = ∏ j ∈ ell,
                              (α * b (idx j).val) / (1 - α * b (idx j).val) := by
        apply Finset.prod_congr rfl
        intros j _
        rw [hidx_toNat j]
      rw [hellProd_simp]
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => m.bit j = true)]
      have hell_filter : (Finset.univ.filter (fun j : Fin (n/2) => m.bit j = true)) = ell := rfl
      rw [hell_filter]
      have hLHS_ell : ∏ j ∈ ell,
                        (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
                    = ∏ j ∈ ell, So.p (idx j) := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [if_pos (hbit_of_ell j hj)]
      rw [hLHS_ell]
      have hLHS_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (if m.bit j then So.p (idx j) else 1 - So.p (idx j))
                        = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                            (1 - So.p (idx j)) := by
        apply Finset.prod_congr rfl
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        rw [if_neg hj]
      rw [hLHS_notell]
      have hSo_ell : ∏ j ∈ ell, So.p (idx j)
                    = ∏ j ∈ ell, α * b (idx j).val := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [hSo_idx j, if_pos (hidx_par_ell j hj)]
      rw [hSo_ell]
      have hSo_notell : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (1 - So.p (idx j))
                      = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
                          (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1) := by
        apply Finset.prod_congr rfl
        intro j _
        rw [hSo_idx j]
        by_cases hpar : (idx j).val % 2 = 1
        · rw [if_pos hpar, if_pos hpar]
        · rw [if_neg hpar, if_neg hpar]; ring
      rw [hSo_notell]
      have hQo_split : ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val)
                      = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                        (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                            ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
                          (1 - α * b (idx j).val)) := by
        rw [show ell = Finset.univ.filter (fun j : Fin (n/2) =>
                m.bit j = true ∧ (idx j).val % 2 = 1) from by
              ext j
              simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · intro h; refine ⟨h, ?_⟩
                exact hidx_par_ell j (by simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and]; exact h)
              · intro ⟨h1, _⟩; exact h1]
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => (idx j).val % 2 = 1))
              (fun j => m.bit j = true)]
        congr 1
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
        · apply Finset.prod_congr ?_ (fun _ _ => rfl)
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          tauto
      rw [hQo_split]
      have hLHS_notell_split :
          ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true),
            (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
          = (∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
              ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
            (1 - α * b (idx j).val)) := by
        rw [← Finset.prod_filter_mul_prod_filter_not
              (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true))
              (fun j => (idx j).val % 2 = 1)]
        have h1 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => (idx j).val % 2 = 1),
                    (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                = ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                        ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
                    (1 - α * b (idx j).val) := by
          rw [show (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                    (fun j : Fin (n/2) => (idx j).val % 2 = 1)
              = Finset.univ.filter (fun j : Fin (n/2) =>
                    ¬ m.bit j = true ∧ (idx j).val % 2 = 1) from by
                ext j
                simp only [Finset.mem_filter, Finset.mem_univ, true_and]]
          apply Finset.prod_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_pos hj.2]
        have h2 : ∏ j ∈ (Finset.univ.filter (fun j : Fin (n/2) => ¬ m.bit j = true)).filter
                        (fun j => ¬ (idx j).val % 2 = 1),
                    (if (idx j).val % 2 = 1 then 1 - α * b (idx j).val else 1)
                = 1 := by
          apply Finset.prod_eq_one
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [if_neg hj.2]
        rw [h1, h2, mul_one]
      rw [hLHS_notell_split]
      have hProd_combine : (∏ j ∈ ell, (1 - α * b (idx j).val)) *
                           (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val))
                         = ∏ j ∈ ell, α * b (idx j).val := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro j _
        field_simp [h_factor_ne_zero j]
      calc (∏ j ∈ ell, α * b (idx j).val) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val)
          = (∏ j ∈ ell, (1 - α * b (idx j).val)) *
            (∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val) := by
            rw [hProd_combine]
        _ = ((∏ j ∈ ell, (1 - α * b (idx j).val)) *
            ∏ j ∈ Finset.univ.filter (fun j : Fin (n/2) =>
                ¬ m.bit j = true ∧ (idx j).val % 2 = 1),
              (1 - α * b (idx j).val)) *
            ∏ j ∈ ell, (α * b (idx j).val) / (1 - α * b (idx j).val) := by ring

/-! ## Marginalization helpers (same as `ParitySwapCore` / `ParitySwapSignedIdentity`). -/

private theorem PSOT_marg_helper {n k : ℕ} (e : Fin k → Fin n)
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

private theorem PSOT_marg_helper2 {n k : ℕ} (e : Fin k → Fin n) (he : Function.Injective e)
    (g : Fin n → Bool → ℝ) (m : Fin k → Bool)
    (hmarg : ∀ i : Fin n, g i true + g i false = 1) :
    (∑ x : Fin n → Bool,
        (∏ i : Fin n, g i (x i)) *
        (∏ j : Fin k, (if x (e j) = m j then (1 : ℝ) else 0)))
      = ∏ j : Fin k, g (e j) (m j) := by
  classical
  rw [PSOT_marg_helper e g m]
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

/-! ## `ParitySwapCore` for `n ≡ 3 (mod 4)` — the triangle/absolute-value bound. -/
theorem ParitySwapCore_oddThree :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 4 = 3 →
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
    ∀ (m : Workspace.Types.BinVec.BinVec (n / 2)),
      (∀ j₁ ∈ (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true),
       ∀ j₂ ∈ (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true),
        (j₁.val) % 2 = (j₂.val) % 2) →
    ∀ (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
      (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So)
      (r : ℤ), r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ) →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let ell : Finset (Fin (n / 2)) :=
        (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
      |∑ b : Workspace.Types.BinVec.BinVec n,
          ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
            (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal|
        ≤ ∏ j ∈ ell,
            α * ((Nat.choose n (((n / 4 : ℕ) : ℤ) + r + (j.val : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) /
            (1 - α * ((Nat.choose n (((n / 4 : ℕ) : ℤ) + r + (j.val : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
  intro n hn hmod Se So hSe hSo m hparity Ce Co r hr
  intro α ell
  classical
  have hn_pos : 0 < n := by
    have : (10^12 : ℕ) > 0 := by norm_num
    omega
  rw [Finset.mem_Icc] at hr
  obtain ⟨hr_lo, hr_hi⟩ := hr
  have hwin_lb : ∀ j : Fin (n/2), 0 ≤ ((n/4 : ℕ) : ℤ) + r + (j : ℕ) := by
    intro j
    have : (0:ℤ) ≤ (j : ℕ) := by positivity
    linarith
  have hwin_ub : ∀ j : Fin (n/2), ((n/4 : ℕ) : ℤ) + r + (j : ℕ) < (n : ℤ) := by
    intro j
    have hjlt : (j : ℕ) < n/2 := j.isLt
    have hjlt' : ((j : ℕ) : ℤ) < (n/2 : ℕ) := by exact_mod_cast hjlt
    have hdiv : ((n/4 : ℕ) : ℤ) + ((n/4 : ℕ) : ℤ) + ((n/2 : ℕ) : ℤ) ≤ (n : ℤ) := by
      have e1 : 4 * (n/4) ≤ n := Nat.mul_div_le n 4 |>.trans_eq rfl
      have e2 : 2 * (n/2) ≤ n := Nat.mul_div_le n 2
      have : (n/4) + (n/4) + (n/2) ≤ n := by omega
      exact_mod_cast this
    linarith
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
  have hmid_real : ∀ b : BinVec n,
      (middleIndicator n b m r).toReal
        = ∏ j : Fin (n/2), (if b.bit (idx j) = m.bit j then (1:ℝ) else 0) := by
    intro b
    unfold middleIndicator
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
  set cM_e : ℝ := ∏ j : Fin (n/2), (if m.bit j then Se.p (idx j) else 1 - Se.p (idx j)) with hcMe
  set cM_o : ℝ := ∏ j : Fin (n/2), (if m.bit j then So.p (idx j) else 1 - So.p (idx j)) with hcMo
  have hsum_e : (∑ b : BinVec n, (Ce.toPMF b).toReal * (middleIndicator n b m r).toReal)
      = cM_e := by
    rw [← Equiv.sum_comp (Workspace.Types.BinVec.equivFun (n := n)).symm
          (fun b => (Ce.toPMF b).toReal * (middleIndicator n b m r).toReal)]
    have heq : ∀ x : Fin n → Bool,
        (Ce.toPMF (Workspace.Types.BinVec.equivFun.symm x)).toReal
          * (middleIndicator n (Workspace.Types.BinVec.equivFun.symm x) m r).toReal
        = (∏ i : Fin n, (if x i then Se.p i else 1 - Se.p i))
          * (∏ j : Fin (n/2), (if x (idx j) = m.bit j then (1:ℝ) else 0)) := by
      intro x
      rw [hCe_real, hmid_real]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
    rw [PSOT_marg_helper2 idx hidx_inj
          (fun i c => if c then Se.p i else 1 - Se.p i) (fun j => m.bit j)
          (fun i => by simp)]
  have hsum_o : (∑ b : BinVec n, (Co.toPMF b).toReal * (middleIndicator n b m r).toReal)
      = cM_o := by
    rw [← Equiv.sum_comp (Workspace.Types.BinVec.equivFun (n := n)).symm
          (fun b => (Co.toPMF b).toReal * (middleIndicator n b m r).toReal)]
    have heq : ∀ x : Fin n → Bool,
        (Co.toPMF (Workspace.Types.BinVec.equivFun.symm x)).toReal
          * (middleIndicator n (Workspace.Types.BinVec.equivFun.symm x) m r).toReal
        = (∏ i : Fin n, (if x i then So.p i else 1 - So.p i))
          * (∏ j : Fin (n/2), (if x (idx j) = m.bit j then (1:ℝ) else 0)) := by
      intro x
      rw [hCo_real, hmid_real]
      rfl
    rw [Finset.sum_congr rfl (fun x _ => heq x)]
    rw [PSOT_marg_helper2 idx hidx_inj
          (fun i c => if c then So.p i else 1 - So.p i) (fun j => m.bit j)
          (fun i => by simp)]
  have hinner : (∑ b : BinVec n,
      ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) * (middleIndicator n b m r).toReal)
      = cM_e - cM_o := by
    rw [← hsum_e, ← hsum_o, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _; ring
  rw [hinner]
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
  have hMW := MiddleWeightExplicit_oddThree n hn hmod Se So hSe hSo m r hMW_lo hMW_hi idx hidx_spec
  simp only at hMW
  obtain ⟨hQe_bd, hQo_bd, hMixed, hEmpty, hSameP⟩ := hMW
  set ellProd : ℝ := ∏ j ∈ ell,
      (α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) /
      (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
      with hellProd
  have hRHS_eq : (∏ j ∈ ell,
      α * ((Nat.choose n (((n / 4 : ℕ) : ℤ) + r + (j.val : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) /
      (1 - α * ((Nat.choose n (((n / 4 : ℕ) : ℤ) + r + (j.val : ℤ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)))
      = ellProd := by
    rw [hellProd]
    apply Finset.prod_congr rfl
    intro j _
    rw [show (((n / 4 : ℕ) : ℤ) + r + (j.val : ℤ)) = ((n / 4 : ℤ) + r + (j : ℕ)) from by
      rw [hcast4]]
  rw [hRHS_eq]
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
    exact PSOT_alpha_b_le_half n hn _
  have h_factor_pos : ∀ j : Fin (n/2),
      (0:ℝ) < 1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro j; linarith [h_b_le_half j]
  have hellProd_nonneg : 0 ≤ ellProd := by
    rw [hellProd]
    apply Finset.prod_nonneg
    intro j _
    apply div_nonneg (h_b_nonneg j) (le_of_lt (h_factor_pos j))
  rcases Finset.eq_empty_or_nonempty ell with hell_e | hell_ne
  · obtain ⟨hcMe_eq, hcMo_eq⟩ := hEmpty hell_e
    have hellProd_one : ellProd = 1 := by rw [hellProd, hell_e]; simp
    rw [hellProd_one]
    have hQe_lo := hQe_bd.1
    have hQe_hi := hQe_bd.2
    have hQo_lo := hQo_bd.1
    have hQo_hi := hQo_bd.2
    have hQe0 : (0:ℝ) ≤ _ := le_trans (by positivity) hQe_lo
    have hQo0 : (0:ℝ) ≤ _ := le_trans (by positivity) hQo_lo
    rw [hcMe, hcMo, hcMe_eq, hcMo_eq]
    rw [abs_le]
    constructor <;> linarith
  · have hnot_mixed : ¬ (∃ j₁ ∈ ell, ∃ j₂ ∈ ell,
        ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 ≠ ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2) := by
      rintro ⟨j₁, hj₁, j₂, hj₂, hne⟩
      apply hne
      have hp := hparity j₁ (by simpa [ell] using hj₁) j₂ (by simpa [ell] using hj₂)
      omega
    obtain ⟨j₀, hj₀⟩ := hell_ne.exists_mem
    set p : ℤ := ((n / 4 : ℤ) + r + (j₀ : ℕ)) % 2 with hp_def
    have hp_mem : p ∈ ({0, 1} : Finset ℤ) := by
      have : p = 0 ∨ p = 1 := by rw [hp_def]; omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have hpar_all : ∀ j ∈ ell, ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = p := by
      intro j hj
      rw [hp_def]
      by_contra hne
      exact hnot_mixed ⟨j, hj, j₀, hj₀, hne⟩
    have hSP := hSameP p hp_mem hell_ne hpar_all
    obtain ⟨⟨hp1e, hp0e⟩, ⟨hp0o, hp1o⟩⟩ := hSP
    have hQe_hi := hQe_bd.2
    have hQo_hi := hQo_bd.2
    have hQe_lo0 : (0:ℝ) ≤ _ := le_trans (by positivity) hQe_bd.1
    have hQo_lo0 : (0:ℝ) ≤ _ := le_trans (by positivity) hQo_bd.1
    have hp_cases : p = 0 ∨ p = 1 := by rw [hp_def]; omega
    rcases hp_cases with hp0 | hp1
    · have hce := hp0e hp0
      have hco := hp0o hp0
      rw [hcMe, hcMo, hce, hco]
      rw [sub_zero, abs_of_nonneg (mul_nonneg hQe_lo0 hellProd_nonneg)]
      calc _ ≤ 1 * ellProd := mul_le_mul_of_nonneg_right hQe_hi hellProd_nonneg
        _ = ellProd := one_mul _
    · have hce := hp1e hp1
      have hco := hp1o hp1
      rw [hcMe, hcMo, hce, hco]
      rw [zero_sub, abs_neg, abs_of_nonneg (mul_nonneg hQo_lo0 hellProd_nonneg)]
      calc _ ≤ 1 * ellProd := mul_le_mul_of_nonneg_right hQo_hi hellProd_nonneg
        _ = ellProd := one_mul _

/-! ## `ParitySwapSignedIdentity` for `n ≡ 3 (mod 4)` — the SIGNED core.

The exact signed value of the inner middle-window sum (NOT its absolute value),
which is what de-axiomatizing the paper's Lemma-6 algebraic identity needs. The
sign `(−1)^p` (with `p = (n/4+r+j)%2`, common over `j ∈ ell`) is the genuine
parity-swap sign. Residue-independent; routes through
`MiddleWeightExplicit_oddThree`. -/
theorem ParitySwapSignedIdentity_oddThree :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 4 = 3 →
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
      (((∃ j₁ ∈ ell, ∃ j₂ ∈ ell,
            ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 ≠ ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2) →
          LHS = 0)) ∧
      ((ell = ∅) → LHS = Q_e - Q_o) ∧
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
  rw [Finset.mem_Icc] at hr
  obtain ⟨hr_lo, hr_hi⟩ := hr
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
    rw [PSOT_marg_helper2 idx hidx_inj
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
    rw [PSOT_marg_helper2 idx hidx_inj
          (fun i c => if c then So.p i else 1 - So.p i) (fun j => m.bit j)
          (fun i => by simp)]
  have hLHS_eq : LHS = cM_e - cM_o := by
    show (∑ b : BinVec n,
        ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
          (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)
        = cM_e - cM_o
    rw [← hsum_e, ← hsum_o, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b _; ring
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
  have hMW := MiddleWeightExplicit_oddThree n hn hmod Se So hSe hSo m r hMW_lo hMW_hi idx hidx_spec
  simp only at hMW
  obtain ⟨hQe_bd, hQo_bd, hMixed, hEmpty, hSameP⟩ := hMW
  set ellProdF : ℝ := ∏ j ∈ ell, ellFactor n α r (j : ℕ) with hellProdF
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
    exact PSOT_alpha_b_le_half n hn _
  have h_factor_pos : ∀ j : Fin (n/2),
      (0:ℝ) < 1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹) := by
    intro j; linarith [h_b_le_half j]
  have hellProdF_eq : ellProdF
      = ∏ j ∈ ell,
          (α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) /
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹)) := by
    rw [hellProdF]
    apply Finset.prod_congr rfl
    intro j _
    unfold ellFactor
    simp only
    have hxlo : (0 : ℤ) ≤ r + (n / 4 : ℤ) + (j : ℤ) := by
      have := hwin_lb j; rw [hcast4] at this; linarith
    have hxhi : r + (n / 4 : ℤ) + (j : ℤ) ≤ (n : ℤ) := by
      have := hwin_ub j; rw [hcast4] at this; linarith
    have hX := Workspace.PriorWork.AltRSumKwayFourierBridge.binPMFInt_half n
      (r + (n / 4 : ℤ) + (j : ℤ)) hxlo hxhi
    have htoNat : (r + (n / 4 : ℤ) + (j : ℤ)).toNat = ((n / 4 : ℤ) + r + (j : ℕ)).toNat := by
      congr 1; ring
    rw [hX, htoNat]
  refine ⟨?_, ?_, ?_⟩
  · intro hmix
    obtain ⟨j₁, hj₁, j₂, hj₂, hne⟩ := hmix
    have hMWmix : ∃ j₁ ∈ ell, ∃ j₂ ∈ ell,
        ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 ≠ ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2 :=
      ⟨j₁, hj₁, j₂, hj₂, hne⟩
    obtain ⟨hce0, hco0⟩ := hMixed hMWmix
    rw [hLHS_eq, hcMe, hcMo, hce0, hco0, sub_zero]
  · intro hell_e
    obtain ⟨hcMe_eq, hcMo_eq⟩ := hEmpty hell_e
    show LHS = Q_e - Q_o
    rw [hLHS_eq, hcMe, hcMo, hcMe_eq, hcMo_eq]
  · intro p hp_mem hell_ne hpar_all
    have hSP := hSameP p hp_mem hell_ne hpar_all
    obtain ⟨⟨hp1e, hp0e⟩, ⟨hp0o, hp1o⟩⟩ := hSP
    have hp_cases : p = 0 ∨ p = 1 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
      exact hp_mem
    rcases hp_cases with hp0 | hp1
    · have hce := hp0e hp0
      have hco := hp0o hp0
      show LHS = (-1 : ℝ) ^ p.toNat * (if p = 0 then Q_e else Q_o) * ellProdF
      rw [hLHS_eq, hcMe, hcMo, hce, hco, sub_zero]
      rw [hp0]
      simp only [Int.toNat_zero, pow_zero, one_mul, if_true]
      show _ = Q_e * ellProdF
      rw [hellProdF_eq]
    · have hce := hp1e hp1
      have hco := hp1o hp1
      show LHS = (-1 : ℝ) ^ p.toNat * (if p = 0 then Q_e else Q_o) * ellProdF
      rw [hLHS_eq, hcMe, hcMo, hce, hco, zero_sub]
      rw [hp1]
      have hif : (if (1 : ℤ) = 0 then Q_e else Q_o) = Q_o := by norm_num
      rw [hif, show ((1 : ℤ).toNat) = 1 from rfl, pow_one]
      show _ = -1 * Q_o * ellProdF
      rw [hellProdF_eq]
      ring

/-! ## Residue-free witness coin-flip product formula.

`WitnessCoinFlipFormula` carries a `n % 8 = 1` hypothesis it never uses (its body
opens with `intro n _ _`). We cannot instantiate it at `n ≡ 3 (mod 4)` because we
cannot supply a (false) proof of `n % 8 = 1`. So we restate it WITHOUT the residue
hypothesis (proof body copied verbatim from `WitnessCoinFlipFormula`, which only
uses `hSe`/`hSo`/`Se.nonneg`/`Se.le_one` etc.), and route `MixedParityVanishes_oddThree`
through this residue-free wrapper. -/
private theorem PSOT_witness :
    ∀ (n : ℕ),
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
        ∀ (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
          (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So) (b : BinVec n),
          (Ce.toPMF b =
              ENNReal.ofReal
                ((∏ i : Fin n, (if (i.val) % 2 = 1
                    then (if b.bit i = false then (1 : ℝ) else 0)
                    else 1)) *
                 (∏ i : Fin n, (if (i.val) % 2 = 0
                    then (if b.bit i
                          then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                          else 1 -
                                (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                    else 1)))) ∧
          (Co.toPMF b =
              ENNReal.ofReal
                ((∏ i : Fin n, (if (i.val) % 2 = 0
                    then (if b.bit i = false then (1 : ℝ) else 0)
                    else 1)) *
                 (∏ i : Fin n, (if (i.val) % 2 = 1
                    then (if b.bit i
                          then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                          else 1 -
                                (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                                 Real.sqrt n *
                                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                    else 1)))) := by
  intro n Se So hSe hSo Ce Co b
  set C : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n with hC
  have key_e : ∀ i : Fin n,
      (if b.bit i then Se.p i else 1 - Se.p i) =
      (if (i.val) % 2 = 1
          then (if b.bit i = false then (1 : ℝ) else 0)
          else 1) *
      (if (i.val) % 2 = 0
          then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
          else 1) := by
    intro i
    have hSei := hSe i
    rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
    · have hpar1ne : ¬ (i.val % 2 = 1) := by omega
      rw [if_neg hpar1ne, if_pos hpar, one_mul]
      rw [hSei, if_pos hpar]
    · have hpar0ne : ¬ (i.val % 2 = 0) := by omega
      rw [if_pos hpar, if_neg hpar0ne, mul_one]
      rw [hSei, if_neg hpar0ne]
      by_cases hb : b.bit i
      · simp [hb]
      · simp [hb]
  have key_o : ∀ i : Fin n,
      (if b.bit i then So.p i else 1 - So.p i) =
      (if (i.val) % 2 = 0
          then (if b.bit i = false then (1 : ℝ) else 0)
          else 1) *
      (if (i.val) % 2 = 1
          then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
          else 1) := by
    intro i
    have hSoi := hSo i
    rcases Nat.mod_two_eq_zero_or_one i.val with hpar | hpar
    · have hpar1ne : ¬ (i.val % 2 = 1) := by omega
      rw [if_pos hpar, if_neg hpar1ne, mul_one]
      rw [hSoi, if_neg hpar1ne]
      by_cases hb : b.bit i
      · simp [hb]
      · simp [hb]
    · have hpar0ne : ¬ (i.val % 2 = 0) := by omega
      rw [if_neg hpar0ne, if_pos hpar, one_mul]
      rw [hSoi, if_pos hpar]
  refine ⟨?_, ?_⟩
  · have hnonneg_e : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 1
              then (if b.bit i = false then (1 : ℝ) else 0)
              else 1) := by
      intro i; split_ifs <;> norm_num
    have hnonneg_o : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 0
              then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) := by
      intro i
      by_cases hpar : (i.val) % 2 = 0
      · rw [if_pos hpar]
        have h0 : 0 ≤ Se.p i := Se.nonneg i
        have h1 : Se.p i ≤ 1 := Se.le_one i
        have hSei := hSe i
        rw [hSei, if_pos hpar] at h0 h1
        split_ifs
        · exact h0
        · linarith
      · rw [if_neg hpar]; norm_num
    rw [Ce.prod_factorisation b]
    have step1 : (∏ i : Fin n, ENNReal.ofReal (if b.bit i then Se.p i else 1 - Se.p i)) =
                 (∏ i : Fin n, ENNReal.ofReal
                    ((if (i.val) % 2 = 1
                        then (if b.bit i = false then (1 : ℝ) else 0)
                        else 1) *
                     (if (i.val) % 2 = 0
                        then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                              else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                        else 1))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [key_e i]
    rw [step1]
    rw [← ENNReal.ofReal_prod_of_nonneg
          (fun i _ => mul_nonneg (hnonneg_e i) (hnonneg_o i))]
    rw [Finset.prod_mul_distrib]
  · have hnonneg_e : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 0
              then (if b.bit i = false then (1 : ℝ) else 0)
              else 1) := by
      intro i; split_ifs <;> norm_num
    have hnonneg_o : ∀ i : Fin n,
        0 ≤ (if (i.val) % 2 = 1
              then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) := by
      intro i
      by_cases hpar : (i.val) % 2 = 1
      · rw [if_pos hpar]
        have h0 : 0 ≤ So.p i := So.nonneg i
        have h1 : So.p i ≤ 1 := So.le_one i
        have hSoi := hSo i
        rw [hSoi, if_pos hpar] at h0 h1
        split_ifs
        · exact h0
        · linarith
      · rw [if_neg hpar]; norm_num
    rw [Co.prod_factorisation b]
    have step1 : (∏ i : Fin n, ENNReal.ofReal (if b.bit i then So.p i else 1 - So.p i)) =
                 (∏ i : Fin n, ENNReal.ofReal
                    ((if (i.val) % 2 = 0
                        then (if b.bit i = false then (1 : ℝ) else 0)
                        else 1) *
                     (if (i.val) % 2 = 1
                        then (if b.bit i then C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                              else 1 - C * ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
                        else 1))) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [key_o i]
    rw [step1]
    rw [← ENNReal.ofReal_prod_of_nonneg
          (fun i _ => mul_nonneg (hnonneg_e i) (hnonneg_o i))]
    rw [Finset.prod_mul_distrib]

/-! ## `MixedParityVanishes` for `n ≡ 3 (mod 4)`.

A mixed-parity middle mask `m` (two `1`-bits at window positions of opposite
parity) makes both the even-witness and odd-witness length PMFs vanish at
`(m, zMinus, zPlus)`, hence they are equal. The body forwards `hmod` only into
`WitnessCoinFlipFormula` (which discards it); the geometry is again the genuine
`n/2`-bit middle window. -/
theorem MixedParityVanishes_oddThree :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 4 = 3 →
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
      ∀ (δ : Workspace.Types.DelProb.DelProb),
        (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
        ∀ (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
          (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
        ∀ (m : Workspace.Types.BinVec.BinVec (n / 2)),
          (∃ j₁ j₂ : Fin (n / 2),
            m.bit j₁ = true ∧ m.bit j₂ = true ∧ (j₁.val) % 2 ≠ (j₂.val) % 2) →
          ∀ (zMinus zPlus : ℕ),
            ((lenE.toPMF (m, zMinus, zPlus)).toReal)
              = ((lenO.toPMF (m, zMinus, zPlus)).toReal) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO m hmix zMinus zPlus
  obtain ⟨Ce⟩ := CoinFlipDistExists Se
  obtain ⟨Co⟩ := CoinFlipDistExists So
  have hwitness := fun b => PSOT_witness n Se So hSe hSo Ce Co b
  have hE_zero : lenE.toPMF (m, zMinus, zPlus) = 0 := by
    have hcomp := lenE.composition_law Ce m zMinus zPlus
    rw [hcomp]
    rw [ENNReal.tsum_eq_zero]
    intro b
    rw [ENNReal.tsum_eq_zero]
    intro r
    by_cases hmid : middleIndicator n b m r = 0
    · rw [hmid]; ring
    · have hCe_zero : Ce.toPMF b = 0 := by
        rw [middleIndicator] at hmid
        split_ifs at hmid with h₁ h₂
        · obtain ⟨j₁, j₂, hbj₁, hbj₂, hpar⟩ := hmix
          have hb1 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat,
              by
                have hj := h₁ j₁
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₁
            rw [this]; exact hbj₁
          have hb2 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat,
              by
                have hj := h₁ j₂
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₂
            rw [this]; exact hbj₂
          set i₁ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat, _⟩ with hi₁_def
          set i₂ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat, _⟩ with hi₂_def
          have hpar_i : i₁.val % 2 ≠ i₂.val % 2 := by
            have hj₁' := h₁ j₁
            have hj₂' := h₁ j₂
            have h0₁ : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hj₁'.1
            have h0₂ : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hj₂'.1
            intro heq
            apply hpar
            have ki₁ : (i₁.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := h0₁
            have ki₂ : (i₂.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := h0₂
            have hmod_eq : (i₁.val : ℤ) % 2 = (i₂.val : ℤ) % 2 := by
              have : ((i₁.val % 2 : ℕ) : ℤ) = ((i₂.val % 2 : ℕ) : ℤ) := by exact_mod_cast heq
              calc (i₁.val : ℤ) % 2
                  = ((i₁.val % 2 : ℕ) : ℤ) := by push_cast; rfl
                _ = ((i₂.val % 2 : ℕ) : ℤ) := this
                _ = (i₂.val : ℤ) % 2 := by push_cast; rfl
            rw [ki₁, ki₂] at hmod_eq
            have : ((j₁.val : ℤ)) % 2 = ((j₂.val : ℤ)) % 2 := by omega
            zify
            exact this
          have ⟨hCe_eq, _⟩ := hwitness b
          rw [hCe_eq]
          rw [ENNReal.ofReal_eq_zero]
          set P_e_odd := ∏ i : Fin n, (if (i.val) % 2 = 1
              then (if b.bit i = false then (1 : ℝ) else 0) else 1) with hP_def
          set P_e_even := ∏ i : Fin n, (if (i.val) % 2 = 0
              then (if b.bit i
                    then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 -
                          (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) with hPe_def
          show P_e_odd * P_e_even ≤ 0
          have hP_e_odd : P_e_odd = 0 := by
            by_cases hi1 : i₁.val % 2 = 1
            · apply Finset.prod_eq_zero (Finset.mem_univ i₁)
              simp [hi1, hb1]
            · have hi2 : i₂.val % 2 = 1 := by
                have h_or : i₁.val % 2 = 0 ∨ i₁.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                cases h_or with
                | inl h =>
                  have h_or2 : i₂.val % 2 = 0 ∨ i₂.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                  cases h_or2 with
                  | inl h2 => exact absurd (h.trans h2.symm) hpar_i
                  | inr h2 => exact h2
                | inr h => exact absurd h hi1
              apply Finset.prod_eq_zero (Finset.mem_univ i₂)
              simp [hi2, hb2]
          rw [hP_e_odd, zero_mul]
        · exfalso; exact hmid rfl
        · exfalso; exact hmid rfl
      rw [hCe_zero]
      ring
  have hO_zero : lenO.toPMF (m, zMinus, zPlus) = 0 := by
    have hcomp := lenO.composition_law Co m zMinus zPlus
    rw [hcomp]
    rw [ENNReal.tsum_eq_zero]
    intro b
    rw [ENNReal.tsum_eq_zero]
    intro r
    by_cases hmid : middleIndicator n b m r = 0
    · rw [hmid]; ring
    · have hCo_zero : Co.toPMF b = 0 := by
        rw [middleIndicator] at hmid
        split_ifs at hmid with h₁ h₂
        · obtain ⟨j₁, j₂, hbj₁, hbj₂, hpar⟩ := hmix
          have hb1 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat,
              by
                have hj := h₁ j₁
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₁
            rw [this]; exact hbj₁
          have hb2 : b.bit ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat,
              by
                have hj := h₁ j₂
                have hlt := hj.2
                have hnonneg := hj.1
                have h0 : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                    = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hnonneg
                have : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ) < (n : ℤ) := by
                  rw [h0]; exact hlt
                exact_mod_cast this⟩ = true := by
            have := h₂ j₂
            rw [this]; exact hbj₂
          set i₁ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) |>.toNat, _⟩ with hi₁_def
          set i₂ : Fin n := ⟨((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) |>.toNat, _⟩ with hi₂_def
          have hpar_i : i₁.val % 2 ≠ i₂.val % 2 := by
            have hj₁' := h₁ j₁
            have hj₂' := h₁ j₂
            have h0₁ : ((((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := Int.toNat_of_nonneg hj₁'.1
            have h0₂ : ((((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ)).toNat : ℤ)
                = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := Int.toNat_of_nonneg hj₂'.1
            intro heq
            apply hpar
            have ki₁ : (i₁.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₁ : ℕ) := h0₁
            have ki₂ : (i₂.val : ℤ) = ((n / 4 : ℕ) : ℤ) + r + (j₂ : ℕ) := h0₂
            have hmod_eq : (i₁.val : ℤ) % 2 = (i₂.val : ℤ) % 2 := by
              have : ((i₁.val % 2 : ℕ) : ℤ) = ((i₂.val % 2 : ℕ) : ℤ) := by exact_mod_cast heq
              calc (i₁.val : ℤ) % 2
                  = ((i₁.val % 2 : ℕ) : ℤ) := by push_cast; rfl
                _ = ((i₂.val % 2 : ℕ) : ℤ) := this
                _ = (i₂.val : ℤ) % 2 := by push_cast; rfl
            rw [ki₁, ki₂] at hmod_eq
            have : ((j₁.val : ℤ)) % 2 = ((j₂.val : ℤ)) % 2 := by omega
            zify
            exact this
          have ⟨_, hCo_eq⟩ := hwitness b
          rw [hCo_eq]
          rw [ENNReal.ofReal_eq_zero]
          set P_o_even := ∏ i : Fin n, (if (i.val) % 2 = 0
              then (if b.bit i = false then (1 : ℝ) else 0) else 1) with hP_def
          set P_o_odd := ∏ i : Fin n, (if (i.val) % 2 = 1
              then (if b.bit i
                    then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
                    else 1 -
                          (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) *
                           Real.sqrt n *
                           ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹))
              else 1) with hPo_def
          show P_o_even * P_o_odd ≤ 0
          have hP_o_even : P_o_even = 0 := by
            by_cases hi1 : i₁.val % 2 = 0
            · apply Finset.prod_eq_zero (Finset.mem_univ i₁)
              simp [hi1, hb1]
            · have hi2 : i₂.val % 2 = 0 := by
                have h_or : i₁.val % 2 = 0 ∨ i₁.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                cases h_or with
                | inl h => exact absurd h hi1
                | inr h =>
                  have h_or2 : i₂.val % 2 = 0 ∨ i₂.val % 2 = 1 := Nat.mod_two_eq_zero_or_one _
                  cases h_or2 with
                  | inl h2 => exact h2
                  | inr h2 => exact absurd (h.trans h2.symm) hpar_i
              apply Finset.prod_eq_zero (Finset.mem_univ i₂)
              simp [hi2, hb2]
          rw [hP_o_even, zero_mul]
        · exfalso; exact hmid rfl
        · exfalso; exact hmid rfl
      rw [hCo_zero]
      ring
  rw [hE_zero, hO_zero]

end ParitySwapOddThree

