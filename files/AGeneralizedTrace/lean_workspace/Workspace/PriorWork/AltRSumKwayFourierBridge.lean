-- Intermediate (SORRY-FREE) lemmas wiring Lemma 7 (`SublemmaFourierKway`) into the
-- proof of Lemma 8 (`AltRSumFourierBound`), Rivkin–Valiant–Valiant 2024,
-- arXiv:2412.00674v1, §3, lines 362-382.
--
-- The paper's Lemma 8 proof expresses `altRSum` at ξ = π as the Fourier transform
-- of a pointwise product [3 binomial factors] × [k-way product of α·bin/(1-α·bin)].
-- The k-way factor's Fourier transform is bounded by `2·e^{-√n}` for |ξ| ≥ 2; THIS
-- bound is exactly Lemma 7 (`SublemmaFourierKway`).
--
-- The lemmas below land the *index-alignment bridge*: they show that the k-way
-- product factor appearing inside `Fterm` (built from `ellFactor`, i.e.
-- `α·binPMFInt n (1/2) (r + n/4 + j) / (1 - α·binPMFInt …)`) is, pointwise in `r`,
-- EXACTLY the `T4` function of `SublemmaFourierKway` (built from
-- `α·(C(n,i)·2^{-n}) / (1 - …)` with index `r + (n-1)/4 + ℓ_j`). For `n ≡ 1 (mod 8)`
-- the two index conventions `n/4` and `(n-1)/4` coincide, and on the support
-- `0 ≤ m ≤ n` we have `binPMFInt n (1/2) m = C(n, m.toNat)·2^{-n}`. Hence the
-- k-way Fourier-tail bound of Lemma 7 transports verbatim to the k-way factor of
-- `Fterm` (lemma `kwayFactor_fourier_tail_bound`, which directly invokes
-- `SublemmaFourierKway`).
--
-- These are real, sorry-free reductions. They do NOT yet assemble the full
-- 4-fold-convolution magnitude bound of Lemma 8 (that requires the circular
-- convolution of the 3-binomial Fourier transform with this k-way factor, plus
-- the [-π,π] region split). See the report for the precise remaining steps.
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.ProofLemmas.SublemmaFourierKway

open scoped BigOperators
open Workspace.Types.AlternatingSumExpression

namespace Workspace.PriorWork.AltRSumKwayFourierBridge

/-- **Closed form of the symmetric binomial pmf.** For `k ≤ n`,
`binPMF n (1/2) k = C(n, k) · 2^{-n}`. -/
theorem binPMF_half (n k : ℕ) (h : k ≤ n) :
    binPMF n (1 / 2) k = (n.choose k : ℝ) * (2 ^ n : ℝ)⁻¹ := by
  unfold binPMF
  rw [if_pos h]
  rw [one_div]
  rw [show (1 - (2 : ℝ)⁻¹) = (2 : ℝ)⁻¹ by norm_num]
  rw [mul_assoc, ← pow_add, inv_pow]
  rw [Nat.add_sub_cancel' h]

/-- **Closed form of the integer-indexed symmetric binomial pmf on its support.**
For `0 ≤ m ≤ n`, `binPMFInt n (1/2) m = C(n, m.toNat) · 2^{-n}`. -/
theorem binPMFInt_half (n : ℕ) (m : ℤ) (h0 : 0 ≤ m) (hn : m ≤ (n : ℤ)) :
    binPMFInt n (1 / 2) m = (n.choose m.toNat : ℝ) * (2 ^ n : ℝ)⁻¹ := by
  unfold binPMFInt
  rw [if_pos ⟨h0, hn⟩]
  apply binPMF_half
  omega

/-- **The `ellFactor` of `Fterm` equals the `T4`-atom of Lemma 7, pointwise.**
For `n ≡ 1 (mod 8)` (so `n / 4 = (n - 1) / 4` in `ℕ`-division), `α := c'·√n`, and
each index `j`, the rational factor `ellFactor n α r j` from `Fterm` equals the
`r`-indexed atom in `SublemmaFourierKway`'s `T4`:
`(if 0 ≤ m ∧ m ≤ n then p/(1-p) else 0)` with `m := r + (n-1)/4 + j`,
`p := α·(C(n, m.toNat)·2^{-n})`.

Note: when the index `m := r + n/4 + j` is OUT of `{0,…,n}`, `binPMFInt` is `0`, so
`ellFactor = α·0/(1-α·0) = 0`, matching the `else 0` branch of `T4`. -/
theorem ellFactor_eq_T4atom (n : ℕ) (hn8 : n % 8 = 1) (r : ℤ) (j : ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    ellFactor n α r j
      = (let m : ℤ := r + ((n - 1) / 4 : ℤ) + (j : ℤ)
         if 0 ≤ m ∧ m ≤ (n : ℤ) then
           let i : ℕ := m.toNat
           let p : ℝ :=
             ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) *
               ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
           p / (1 - p)
         else 0) := by
  intro α
  -- For n ≡ 1 mod 8, ⌊n/4⌋ = ⌊(n-1)/4⌋ as integers.
  have hdiv : ((n / 4 : ℤ)) = ((n - 1) / 4 : ℤ) := by
    have : n % 4 = 1 := by omega
    omega
  unfold ellFactor
  simp only
  -- The first-factor index of ellFactor is `r + n/4 + j`; rewrite n/4 → (n-1)/4.
  rw [hdiv]
  set m : ℤ := r + ((n - 1) / 4 : ℤ) + (j : ℤ) with hm
  by_cases hsupp : 0 ≤ m ∧ m ≤ (n : ℤ)
  · -- On support: binPMFInt = C(n, m.toNat)·2^{-n}, so the whole atom matches.
    rw [if_pos hsupp]
    rw [binPMFInt_half n m hsupp.1 hsupp.2]
  · -- Off support: binPMFInt = 0, so ellFactor = α·0/(1-α·0) = 0.
    rw [if_neg hsupp]
    have hz : binPMFInt n (1 / 2) m = 0 := by
      unfold binPMFInt
      rw [if_neg hsupp]
    rw [hz]
    simp

/-- **The k-way product factor of `Fterm` equals the `T4` product of Lemma 7.**
With `ℓ : Finset ℕ` enumerated by a strictly increasing tuple, the product
`∏ j ∈ ℓ, ellFactor n α r j` equals the `T4 r` value of `SublemmaFourierKway` for
the corresponding `Fin k → ℕ` index map. (Stated abstractly: for any index map
`g : Fin k → ℕ`, the product of `ellFactor` atoms equals the product of `T4`
atoms.) -/
theorem kwayProd_eq_T4 (n : ℕ) (hn8 : n % 8 = 1) (r : ℤ) (k : ℕ) (g : Fin k → ℕ) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    (∏ i : Fin k, ellFactor n α r (g i))
      = ∏ i : Fin k,
          (let m : ℤ := r + ((n - 1) / 4 : ℤ) + (g i : ℤ)
           if 0 ≤ m ∧ m ≤ (n : ℤ) then
             let idx : ℕ := m.toNat
             let p : ℝ :=
               ((1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)) *
                 ((Nat.choose n idx : ℝ) * (2 ^ n : ℝ)⁻¹)
             p / (1 - p)
           else 0) := by
  intro α
  apply Finset.prod_congr rfl
  intro i _
  exact ellFactor_eq_T4atom n hn8 r (g i)

/-- **k-way Fourier-tail bound on the `Fterm` product factor (INVOKES Lemma 7).**
For `n ≥ 1`, `n ≡ 1 (mod 8)`, every strictly-increasing same-parity tuple
`ℓ : Fin k → ℕ` of indices in `{1,…,(n-1)/2}`, and every `ξ` with `2 ≤ |ξ| ≤ π`,
the discrete Fourier sum of the k-way product factor of `Fterm`,
`r ↦ ∏ i, ellFactor n α r (ℓ i)`, has modulus `≤ 2·e^{-√n}`.

This is the LOW-region ingredient of Lemma 8's proof: it is obtained by rewriting
the k-way product factor as `SublemmaFourierKway`'s `T4` (via `kwayProd_eq_T4`) and
then applying **Lemma 7 (`SublemmaFourierKway`)** verbatim. -/
theorem kwayFactor_fourier_tail_bound
    (n : ℕ) (hn : 1 ≤ n) (hn8 : n % 8 = 1)
    (k : ℕ) (ℓ : Fin k → ℕ)
    (hℓ_strict : ∀ i j : Fin k, i.val < j.val → ℓ i < ℓ j)
    (hℓ_parity : ∀ i j : Fin k, ℓ i % 2 = ℓ j % 2)
    (hℓ_range : ∀ i : Fin k, 1 ≤ ℓ i ∧ ℓ i ≤ (n - 1) / 2)
    (ξ : ℝ) (hξπ : |ξ| ≤ Real.pi) (hξ2 : (2 : ℝ) ≤ |ξ|) :
    let α : ℝ := (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
    ‖∑' r : ℤ,
        ((∏ i : Fin k, ellFactor n α r (ℓ i) : ℝ) : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ)))‖
      ≤ 2 * Real.exp (- Real.sqrt (n : ℝ)) := by
  intro α
  -- Define T4 exactly as SublemmaFourierKway expects.
  set T4 : ℤ → ℝ := fun r =>
    ∏ j : Fin k,
      (let m : ℤ := r + ((n - 1) / 4 : ℤ) + (ℓ j : ℤ)
       if 0 ≤ m ∧ m ≤ (n : ℤ) then
         let i : ℕ := m.toNat
         let a : ℝ :=
           (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt (n : ℝ)
         let p : ℝ := a * ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹)
         p / (1 - p)
       else 0) with hT4_def
  -- The k-way product factor of Fterm equals T4 pointwise.
  have hpoint : ∀ r : ℤ, (∏ i : Fin k, ellFactor n α r (ℓ i)) = T4 r := by
    intro r
    rw [hT4_def]
    simp only
    exact kwayProd_eq_T4 n hn8 r k ℓ
  -- Rewrite the Fourier sum using the pointwise identity.
  have hsum_eq : (∑' r : ℤ,
      ((∏ i : Fin k, ellFactor n α r (ℓ i) : ℝ) : ℂ) *
        Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))))
      = ∑' r : ℤ, (T4 r : ℂ) *
          Complex.exp (-(Complex.I * (ξ : ℂ) * (r : ℂ))) := by
    apply tsum_congr
    intro r
    rw [hpoint r]
  rw [hsum_eq]
  -- Apply Lemma 7 (SublemmaFourierKway).
  exact SublemmaFourierKway n hn hn8 k ℓ hℓ_strict hℓ_parity hℓ_range T4
    (by intro r; rfl) ξ hξπ hξ2

end Workspace.PriorWork.AltRSumKwayFourierBridge
