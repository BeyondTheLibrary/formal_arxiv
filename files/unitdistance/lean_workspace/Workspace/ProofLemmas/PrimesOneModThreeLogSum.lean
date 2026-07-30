-- Cited from: H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer, 2000 (revised by H. L. Montgomery) — prime number theorem in arithmetic progressions.
-- Paper label: Fact 3.10 (the O(l log l) bound used in equation (6) of Proposition 3.8, Step 1)
-- NL statement: There is a constant C > 0 such that for every l >= 2, the sum of the logarithms of the first l rational primes congruent to 1 modulo 3 is at most C * l * log l. (Consequence of the prime number theorem in arithmetic progressions.)
--
-- The passage from the polynomial bound `Workspace.ProofLemmas.PrimesOneModThreePolyBound` (the `i`-th
-- prime `≡ 1 (mod 3)` is at most `(i+2)^A`, equivalently `π(y;3,1) ≫ y^{1/A}`) to the `O(ℓ log ℓ)`
-- log-sum is proved from Mathlib in `Workspace.ProofLemmas.PrimesOneModThreeReduction`.
import Mathlib
import Workspace.ProofLemmas.PrimesOneModThreeReduction
import Workspace.ProofLemmas.PrimesOneModThreePolyBound

/-- **Fact 3.10.** There is `C > 0` such that the sum of `log` of the first `ℓ` primes
`≡ 1 (mod 3)` is `≤ C·ℓ·log ℓ`.  The first `ℓ` such primes are enumerated by `Nat.nth`. -/
theorem PrimesOneModThreeLogSum :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 2 ≤ ℓ →
      (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i : ℝ)))
        ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  obtain ⟨A, hA, hbd⟩ := PrimesOneModThreePolyBound
  refine ⟨2 * A, by positivity, ?_⟩
  exact Workspace.ProofLemmas.PrimesOneModThreeReduction.logSum_le_of_poly_bound A hA hbd
