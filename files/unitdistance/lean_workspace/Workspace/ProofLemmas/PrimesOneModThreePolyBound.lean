-- Cited from: H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer, 2000 — prime
-- number theorem in arithmetic progressions (or already Linnik/Chebyshev-type lower bounds for
-- π(x; 3, 1), which suffice).
-- Paper label: Fact 3.10 (quantitative core)
--
-- Proved from Mathlib alone in `Workspace.ProofLemmas.MertensThreeMod` by an elementary
-- (Chebyshev/Mertens-style) argument in the field `ℚ(√-3)`:
--   * `r = 1 ∗ χ` for the quadratic character `χ` mod 3 has `A(N) = ∑_{n≤N} r n ∈ [N/2, N]`
--     (a hyperbola/partial-summation count, no L-functions);
--   * `∑_{n≤N} r n log n = ∑_k Λ(k)(1+χ(k)) A(N/k)` (Dirichlet convolution `log = Λ ∗ 1`),
--     and this double-counted sum is squeezed between `(N/2)log N − N` and `N log N`,
--     giving the Mertens-type lower bound `∑_{k≤N} Λ(k)(1+χ(k))/k ≥ (1/2)log N − 1`;
--   * Chebyshev's `ψ(x) ≤ (log 4 + 4)x` (Mathlib) gives the matching upper bound
--     `∑_{k≤N} Λ(k)/k ≤ log N + (log 4 + 4)`, and the prime-power tail
--     `∑_{k≤N, k not prime} Λ(k)/k` is bounded by an absolute constant via
--     `Chebyshev.sum_PrimePow_eq_sum_sum` + `θ(x) ≤ log 4 · x`;
--   * hence `S₁(N) = ∑_{p≤N, p≡1(3)} log p/p ≥ (1/4)log N − C`; comparing `S₁(m^8)` with
--     `S₁(m)` and using `log p ≤ 8 log m`, `1/p ≤ 1/m` on the range `m < p ≤ m^8` gives
--     `π(m^8; 3, 1) ≥ m/16` for `m ≥ m₀`, i.e. the polynomial bound below with `A = 40`
--     (enlarged to `max 40 m₀^8` to absorb the finitely many small indices).
--
-- This quantitative prime-counting bound (equivalently `π(y; 3, 1) ≫ y^{1/A}`) is the input to
-- `PrimesOneModThreeLogSum`: from a polynomial bound `pᵢ ≤ (i+2)^A` one gets
-- `∑_{i<ℓ} log pᵢ ≤ ℓ·A·log(ℓ+1) ≤ 2A·ℓ log ℓ` for `ℓ ≥ 2`
-- (`Workspace.ProofLemmas.PrimesOneModThreeReduction.logSum_le_of_poly_bound`).  Mathlib has
-- Dirichlet's theorem (qualitative infinitude) but no quantitative counting in arithmetic
-- progressions; the quantitative input is developed in `Workspace/ProofLemmas/MertensThreeMod.lean`.
--
-- NL statement: There is a positive integer A such that for every i, the i-th prime congruent to
-- 1 modulo 3 (in increasing order, 0-indexed by Nat.nth) is at most (i + 2)^A.
import Mathlib
import Workspace.ProofLemmas.MertensThreeMod

/-- **Quantitative prime counting.**  The `i`-th prime `≡ 1 (mod 3)` is polynomially bounded. -/
theorem PrimesOneModThreePolyBound :
    ∃ A : ℕ, 0 < A ∧ ∀ i : ℕ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i ≤ (i + 2) ^ A :=
  Workspace.ProofLemmas.MertensThreeMod.primes_one_mod_three_poly_bound
