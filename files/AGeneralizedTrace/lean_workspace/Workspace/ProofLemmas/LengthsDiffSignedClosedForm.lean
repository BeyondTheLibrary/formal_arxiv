import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist
import Workspace.Types.PartialDeletionProcess
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.ParitySwapSignedIdentity

open Workspace.Types.BinVec
open Workspace.Types.PartialDeletionProcess
open Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-!
# LengthsDiffSignedClosedForm — `InnerSumSignedClosedForm`

The genuine sorry-free *assembly* step that eliminates the inner marginal sum
`∑_b (Ce(b) − Co(b)) · middleIndicator(b, m, r)` in favour of its closed
signed product form, for a middle vector `m` whose `1`-bit positions all share
the same parity (index-level same-parity, `hpar`).

For such `m`, the mixed-parity case of `ParitySwapSignedIdentity` cannot occur,
so the inner sum is exactly:

* `Q_e − Q_o` when the `1`-bit window `ell` is empty;
* `(−1)^p · (Q_e or Q_o according to p) · ∏_{j ∈ ell} ellFactor n α r j` when
  `ell` is nonempty, where `p ∈ {0,1}` is the common window parity of every
  `j ∈ ell` (computed from any representative — we use `ell.min'`).
-/

namespace Workspace.ProofLemmas.LengthsDiffSignedClosedForm

theorem InnerSumSignedClosedForm :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
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
      (∀ j₁ j₂ : Fin (n / 2), m.bit j₁ = true → m.bit j₂ = true →
          (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2) →
    ∀ (Ce : Workspace.Types.CoinFlipDist.CoinFlipDist n Se)
      (Co : Workspace.Types.CoinFlipDist.CoinFlipDist n So)
      (r : ℤ), r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)) →
      let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n
      let ell : Finset (Fin (n / 2)) :=
        (Finset.univ : Finset (Fin (n / 2))).filter (fun j => m.bit j = true)
      let Q_e : ℝ :=
        ∏ j ∈ (Finset.univ.filter
                 (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 0)),
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
      let Q_o : ℝ :=
        ∏ j ∈ (Finset.univ.filter
                 (fun j : Fin (n / 2) => ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = 1)),
          (1 - α * ((Nat.choose n ((n / 4 : ℤ) + r + (j : ℕ)).toNat : ℝ) * (2 ^ n : ℝ)⁻¹))
      (∑ b : Workspace.Types.BinVec.BinVec n,
          ((Ce.toPMF b).toReal - (Co.toPMF b).toReal) *
            (Workspace.Types.PartialDeletionProcess.middleIndicator n b m r).toReal)
        = (if h : ell.Nonempty then
              (-1 : ℝ) ^ (((n / 4 : ℤ) + r + ((ell.min' h : Fin (n / 2)) : ℕ)) % 2).toNat *
                (if ((n / 4 : ℤ) + r + ((ell.min' h : Fin (n / 2)) : ℕ)) % 2 = 0
                 then Q_e else Q_o) *
                (∏ j ∈ ell, ellFactor n α r (j : ℕ))
            else Q_e - Q_o) := by
  intro n hn hmod Se So hSe hSo m hpar Ce Co r hr
  intro α ell Q_e Q_o
  classical
  -- range membership in the ℕ-cast Icc that ParitySwapSignedIdentity expects
  have hcast4 : ((n / 4 : ℕ) : ℤ) = (n / 4 : ℤ) := Int.natCast_div n 4
  have hr' : r ∈ Finset.Icc (-((n / 4 : ℕ) : ℤ)) ((n / 4 : ℕ) : ℤ) := by
    rw [Finset.mem_Icc] at hr ⊢
    rw [hcast4]; exact hr
  have hPSSI := ParitySwapSignedIdentity n hn (by omega : n % 2 = 1) Se So hSe hSo m Ce Co r hr'
  simp only at hPSSI
  obtain ⟨hMixed, hEmpty, hSame⟩ := hPSSI
  -- the window parity is constant on `ell` (consequence of `hpar`)
  have hwin_const : ∀ j₁ ∈ ell, ∀ j₂ ∈ ell,
      ((n / 4 : ℤ) + r + (j₁ : ℕ)) % 2 = ((n / 4 : ℤ) + r + (j₂ : ℕ)) % 2 := by
    intro j₁ hj₁ j₂ hj₂
    simp only [ell, Finset.mem_filter, Finset.mem_univ, true_and] at hj₁ hj₂
    have hpe := hpar j₁ j₂ hj₁ hj₂
    omega
  by_cases hne : ell.Nonempty
  · -- nonempty: the same-parity case applies; mixed case is excluded
    rw [dif_pos hne]
    -- representative
    set j₀ : Fin (n / 2) := ell.min' hne with hj₀_def
    have hj₀_mem : j₀ ∈ ell := Finset.min'_mem ell hne
    set p : ℤ := ((n / 4 : ℤ) + r + (j₀ : ℕ)) % 2 with hp_def
    have hp_all : ∀ j ∈ ell, ((n / 4 : ℤ) + r + (j : ℕ)) % 2 = p := by
      intro j hj
      rw [hp_def]
      exact hwin_const j hj j₀ hj₀_mem
    have hp_mem : p ∈ ({0, 1} : Finset ℤ) := by
      have : p = 0 ∨ p = 1 := by rw [hp_def]; omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      exact this
    have := hSame p hp_mem hne hp_all
    rw [this]
  · -- empty
    rw [dif_neg hne]
    have hell_e : ell = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    exact hEmpty hell_e

end Workspace.ProofLemmas.LengthsDiffSignedClosedForm
