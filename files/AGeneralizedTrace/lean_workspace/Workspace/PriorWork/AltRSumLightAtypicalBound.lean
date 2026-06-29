-- Cited from: §3.1 assembly of arXiv:2412.00674v1 (proof of thm:lower-detail, line 418),
-- the ATYPICAL-deletion absorption for the LIGHT family of ℓ-supports. The paper observes
-- that z₋ ← Bin(n/4+r, 1-δ) and z₊ ← Bin(n/4-r, 1-δ) are each ≥ n/16 except with
-- probability e^{-Ω(n)} (since δ ≤ 1/2 and |r| ≤ n/8 whp), and "henceforth assumes this
-- does not happen", folding the atypical z-range into the additive e^{-Ω(n)} error of the
-- whole statistical-distance bound. Aggregated over the light family P_L of same-parity
-- supports whose rare-support envelope mass is small (the < e^{-√n/2} branch of Lemma 11),
-- the total atypical contribution is exponentially small.
-- Paper label: §3.1 atypical-z absorption (e^{-Ω(n)} additive error, line 418), light family
-- NL statement: Let n ∈ ℕ with n ≥ 10^12 and n % 8 = 1. Let δ ∈ ℝ with 320/√n ≤ δ ≤ 1/2,
-- α := c'·√n where c' := 1/(4 e² √(2π)), n_h := n/2. Let
--   S_er(r,j) := α · bin(n,1/2,r+n/4+j),
--   widetildeMu_er(r,ℓ) := ∏_{j∈Icc 1 (n/2)} (if j∈ℓ then S_er(r,j) else 1 - S_er(r,j)),
--   P_L := { ℓ ⊆ Icc 1 n_h : sameParity ℓ ∧ ∀ r ∈ Icc(-(n/4))(n/4), widetildeMu_er(r,ℓ) < e^{-√n/2} }.
-- Then the L¹-summed inner alternating r-sum, restricted to the ATYPICAL deletion range
-- (z₋ < n/16, or z₊ < n/16 with z₋ ≥ n/16), aggregated over all light supports ℓ ∈ P_L,
-- is exponentially small:
--   ∑_{ℓ ∈ P_L} [ (∑_{z₋ < n/16} ∑_{z₊ ≤ n/2} |altRSum n δ α z₋ z₊ ℓ|)
--               + (∑_{z₋ ∈ Ico (n/16) (n/2+1)} ∑_{z₊ < n/16} |altRSum n δ α z₋ z₊ ℓ|) ]
--     ≤ (1/16) · exp(-√n/4).
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.AltRSumLightAtypicalBoundFinal

open Classical

/--
**Atypical-z absorption for the light family (§3.1, line 418).**
The deletion proxies `z₋ ← Bin(n/4+r, 1-δ)` and `z₊ ← Bin(n/4-r, 1-δ)` are each `≥ n/16`
except with probability `e^{-Ω(n)}`; the paper folds the atypical range into the additive
`e^{-Ω(n)}` error of the whole TV bound. Aggregated over the light family `P_L` (supports
whose rare-support envelope mass is below `e^{-√n/2}`), the total atypical contribution is
exponentially small, comfortably below the `(1/8)·e^{-√n/4}` budget that
`LightContributionBound` allots to the light supports (here we use the `(1/16)·e^{-√n/4}`
half-budget so the typical part can take the other half).

For `n ≥ 10^{12}` with `n ≡ 1 (mod 8)` and `δ ∈ [320/√n, 1/2]`, with the light family `P_L`
defined by the small-envelope (`< e^{-√n/2}`) condition, the atypical-z contribution
summed over `ℓ ∈ P_L` is at most `(1/16) · exp(-√n/4)`.
-/
theorem AltRSumLightAtypicalBound :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), (320 : ℝ) / Real.sqrt n ≤ δ → δ ≤ 1 / 2 →
    let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    let α : ℝ := c' * Real.sqrt n
    let n_h : ℕ := n / 2
    let S_er : ℤ → ℕ → ℝ := fun r j =>
      α * Workspace.Types.AlternatingSumExpression.binPMFInt n (1/2)
        (r + ((n : ℤ) / 4) + (j : ℤ))
    let widetildeMu_er : ℤ → Finset ℕ → ℝ := fun r x =>
      ∏ j ∈ Finset.Icc 1 (n / 2),
        (if j ∈ x then S_er r j else (1 - S_er r j))
    let P_L : Finset (Finset ℕ) :=
      ((Finset.Icc 1 n_h).powerset).filter (fun ℓ =>
        Workspace.Types.AlternatingSumExpression.sameParity ℓ ∧
        ∀ r ∈ Finset.Icc (-((n : ℤ) / 4)) ((n : ℤ) / 4),
          widetildeMu_er r ℓ < Real.exp (-(Real.sqrt n / 2)))
    (∑ ℓ ∈ P_L,
        ((∑ zMinus ∈ Finset.range (n / 16),
            ∑ zPlus ∈ Finset.range (n / 2 + 1),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)
          +
         (∑ zMinus ∈ Finset.Ico (n / 16) (n / 2 + 1),
            ∑ zPlus ∈ Finset.range (n / 16),
              |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ℓ|)))
      ≤ (1 : ℝ) / 16 * Real.exp (-(Real.sqrt n / 4)) :=
  AltRSumLightAtypicalBoundFinal
