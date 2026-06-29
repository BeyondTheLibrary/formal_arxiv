import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.StirlingAxioms

open Workspace.Types.ProbVec
open Workspace.Types.BinVec

/--
Fact 9 + Lemma 10 of the paper: two square-root summability bounds.

(a) `centralBinomialL1HalfNorm`: the `L^{1/2}` norm of the centred-binomial
    distribution `Bin(n, 1/2)` over `{0, …, n}` is bounded by `(2π n)^{1/4}`,
    i.e. `∑ i, sqrt(C(n,i) / 2^n) ≤ (2π n)^{1/4}` for every `n ≥ 1`.

(b) `productSqrtBound`: with the parameter choice `α := c' · √n`,
    `c' := 1 / (4 e² √(2π))`, and the witness `S_e` from
    `SublemmaWitnessConstruction` (which assigns
    `S_e.p i = α · C(n, i) / 2^n` on even coordinates and `0` on odd ones),
    the product-Bernoulli measure `μ_e(x) = ∏_i (S_e.p i)^{x_i}(1 - S_e.p i)^{1-x_i}`
    on `{0,1}^n` satisfies
    `∑_x sqrt(μ_e(x)) ≤ exp(√α · (2π n)^{1/4}) = exp(√n / (2 e))`.

The Bernoulli product is encoded as
`∏ i, if x i then S_e.p i else 1 - S_e.p i`, summed over `x : Fin n → Bool`.
-/
theorem SublemmaSqrtSum :
    -- (a) Central-binomial L^{1/2} norm bound.
    (∀ (n : ℕ), 1 ≤ n →
      (∑ i ∈ Finset.range (n + 1),
        Real.sqrt ((Nat.choose n i : ℝ) * (2 ^ n : ℝ)⁻¹))
        ≤ (2 * Real.pi * (n : ℝ)) ^ ((1 : ℝ) / 4)) ∧
    -- (b) Product-Bernoulli L^{1/2} norm bound for the witness `S_e`.
    (∀ (n : ℕ), 1 ≤ n → n % 8 = 1 →
      ∀ (Se : ProbVec n),
        (∀ i : Fin n, Se.p i =
          (if (i.val) % 2 = 0
            then (1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))) * Real.sqrt n *
                 ((Nat.choose n i.val : ℝ) * (2 ^ n : ℝ)⁻¹)
            else 0)) →
        (∑ x : Fin n → Bool,
          Real.sqrt (∏ i : Fin n, if x i then Se.p i else 1 - Se.p i))
          ≤ Real.exp (Real.sqrt n / (2 * Real.exp 1))) := by
  refine ⟨?_, ?_⟩
  · intro n hn
    exact Workspace.Types.StirlingAxioms.binomial_pmf_l_half_sum_bound hn
  · intro n hn hmod Se hSe
    exact Workspace.Types.StirlingAxioms.product_bernoulli_l_half_sum_bound_witness_even hn hmod Se hSe
