import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.DelProb
import Workspace.Types.BinVec
import Workspace.Types.LengthsOnlyProcess
import Workspace.ProofLemmas.MixedParityVanishes

open Workspace.Types.BinVec

open scoped BigOperators

/-!
# LengthsDiffTsumSameParity

Sorry-free *assembly* step toward de-axiomatising paper Lemma 6.  It rewrites the
total-variation tsum
`∑'_{(m,z₋,z₊)} |lenE(m,z₋,z₊) − lenO(m,z₋,z₊)|`
as a finite sum over `m : BinVec (n/2)` of inner `(z₋,z₊)`-tsums, in which the
mixed-parity middle masks contribute `0` (by `MixedParityVanishes`).  Concretely
the summand for `m` is replaced by `if (m has same-parity support) then … else 0`,
so only the same-parity masks survive — exactly the masks for which the signed
closed form of `LengthsDiffPerSummandSigned` is available.

This isolates the analytic core (relating the surviving same-parity inner sums to
`altSum`) from the trivial mixed-parity vanishing, and turns the outer tsum over
the Fintype `BinVec (n/2)` into an honest `Finset` sum.

The two summability facts used (`ENNReal.summable_toReal` applied to the PMFs,
plus `summable_abs_iff`) are completely standard; the mixed-parity vanishing is
`MixedParityVanishes`.
-/

namespace Workspace.ProofLemmas.LengthsDiffTsumSameParity

theorem LengthsDiffTsumSameParity :
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
        ∀ (δ : Workspace.Types.DelProb.DelProb),
          (320 : ℝ) / Real.sqrt n ≤ δ.val → δ.val ≤ 1 / 2 →
          ∀ (lenE : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n Se δ)
            (lenO : Workspace.Types.LengthsOnlyProcess.LengthsOnlyProcess n So δ),
            (∑' s : (BinVec (n / 2) × ℕ × ℕ),
                |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)|)
              =
            ∑ m : BinVec (n / 2),
              (if (∀ j₁ j₂ : Fin (n / 2),
                      m.bit j₁ = true → m.bit j₂ = true →
                      (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
               then ∑' p : ℕ × ℕ,
                      |((lenE.toPMF (m, p.1, p.2)).toReal)
                        - ((lenO.toPMF (m, p.1, p.2)).toReal)|
               else 0) := by
  intro n hn hmod Se So hSe hSo δ hδ_lb hδ_ub lenE lenO
  classical
  -- Abbreviate the integrand.
  set g : (BinVec (n / 2) × ℕ × ℕ) → ℝ :=
    fun s => |((lenE.toPMF s).toReal) - ((lenO.toPMF s).toReal)| with hg
  -- Summability of the toReal of each PMF (their tsums are 1 ≠ ⊤).
  have hsumE : Summable (fun s : (BinVec (n / 2) × ℕ × ℕ) => (lenE.toPMF s).toReal) := by
    apply ENNReal.summable_toReal
    rw [PMF.tsum_coe]; exact ENNReal.one_ne_top
  have hsumO : Summable (fun s : (BinVec (n / 2) × ℕ × ℕ) => (lenO.toPMF s).toReal) := by
    apply ENNReal.summable_toReal
    rw [PMF.tsum_coe]; exact ENNReal.one_ne_top
  have hsum_diff : Summable
      (fun s : (BinVec (n / 2) × ℕ × ℕ) =>
        (lenE.toPMF s).toReal - (lenO.toPMF s).toReal) := hsumE.sub hsumO
  have hsum_g : Summable g := by
    rw [hg]; exact (summable_abs_iff).mpr hsum_diff
  -- Inner summability for each fixed middle mask `m`.
  have hinner : ∀ m : BinVec (n / 2), Summable (fun p : ℕ × ℕ => g (m, p)) := by
    intro m
    exact hsum_g.comp_injective (fun p q h => by simpa using h)
  -- Split the product tsum (outer Fintype factor, inner ℕ × ℕ).
  rw [hsum_g.tsum_prod' hinner]
  -- The outer index is a Fintype, so the outer tsum is a Finset sum.
  rw [tsum_fintype]
  -- Decide each middle mask by whether its support is same-parity.
  refine Finset.sum_congr rfl (fun m _ => ?_)
  by_cases hpar : (∀ j₁ j₂ : Fin (n / 2),
      m.bit j₁ = true → m.bit j₂ = true → (j₁ : ℕ) % 2 = (j₂ : ℕ) % 2)
  · rw [if_pos hpar]
  · rw [if_neg hpar]
    -- Mixed parity: every term of the inner tsum is `|x − x| = 0`.
    push_neg at hpar
    obtain ⟨j₁, j₂, hb₁, hb₂, hne⟩ := hpar
    have hmix : ∃ a b : Fin (n / 2),
        m.bit a = true ∧ m.bit b = true ∧ (a.val) % 2 ≠ (b.val) % 2 :=
      ⟨j₁, j₂, hb₁, hb₂, hne⟩
    rw [show (∑' p : ℕ × ℕ, g (m, p)) = ∑' _p : ℕ × ℕ, (0 : ℝ) from ?_]
    · simp
    · refine tsum_congr (fun p => ?_)
      simp only [hg]
      have heq := MixedParityVanishes n hn (by omega : n % 2 = 1) Se So hSe hSo δ hδ_lb hδ_ub
                    lenE lenO m hmix p.1 p.2
      rw [heq, sub_self, abs_zero]

end Workspace.ProofLemmas.LengthsDiffTsumSameParity
