import Mathlib
import Workspace.Types.DelProb

/-!
# AlternatingSumExpression

Closed-form arithmetic expression appearing in Lemma 6 of
Rivkin–Valiant–Valiant (2024), §3.1. Given parameters `n : ℕ`,
`δ : ℝ` (deletion probability) and `α : ℝ` (witness scaling parameter),
the expression `altSum n δ α` is a real number defined by

```
altSum n δ α =
  ∑_{k = 0}^{n/2}
    ∑_{ℓ ⊂ {1, ..., n/2}, |ℓ| = k, all elements of ℓ have same parity}
      ∑_{z₋ = 0}^{n/2}
        ∑_{z₊ = 0}^{n/2}
          | ∑_{r = -(n/4)}^{n/4} (-1)^r · F_{n,δ,α}(r, z₋, z₊, ℓ) |
```

where the inner function `F_{n,δ,α}(r, z₋, z₊, ℓ)` is a product of three
binomial PMF factors and a product of one rational factor per element of `ℓ`.
See `Fterm` and `binPMF` below for the precise definitions.
-/

namespace Workspace.Types.AlternatingSumExpression

open scoped BigOperators

/-- The standard binomial probability mass function evaluated at `k`,
with `n` trials and success probability `p`:
`binPMF n p k = C(n, k) · p^k · (1 - p)^(n - k)` if `k ≤ n`, and `0` otherwise. -/
noncomputable def binPMF (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  if k ≤ n then
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k)
  else
    0

/-- Binomial PMF evaluated at an integer index `k : ℤ`. If `k` is outside
`{0, 1, ..., n}` the value is `0`. -/
noncomputable def binPMFInt (n : ℕ) (p : ℝ) (k : ℤ) : ℝ :=
  if 0 ≤ k ∧ k ≤ (n : ℤ) then
    binPMF n p k.toNat
  else
    0

/-- The "rational factor" `α · X / (1 - α · X)` where `X = binPMF n (1/2) (r + n/4 + j)`.
The argument `j` is an element of `ℓ ⊆ {1, ..., n/2}` and `r` is an integer in
`{-(n/4), ..., n/4}`. -/
noncomputable def ellFactor (n : ℕ) (α : ℝ) (r : ℤ) (j : ℕ) : ℝ :=
  let X : ℝ := binPMFInt n (1 / 2) (r + (n / 4 : ℤ) + (j : ℤ))
  α * X / (1 - α * X)

/-- The inner function `F_{n,δ,α}(r, z₋, z₊, ℓ)` from Lemma 6. It is a product
of three binomial PMF factors and a product of `ellFactor` values, one for
each element of `ℓ`.

* The first factor is a `Bin(n/2, 1/2, ·)` factor at index `r + n/4` (the partial-deletion process's offset weight; corrected from the paper's Lemma-6 statement typo `Bin(n)` to the `Bin(n/2)` actually used in the paper's Lemma-8 Fourier proof, `cos(ξ/2)^{n/2}`).
* The second factor is a `Bin(n/4 + r, 1 - δ, z₋)` factor.
* The third factor is a `Bin(n/4 - r, 1 - δ, z₊)` factor.
* The product is over `j ∈ ℓ`, with each factor `ellFactor n α r (j-1)` (witness index `r + n/4 + (j-1)`; the `-1` aligns the closed form's 1-based location set `ℓ ⊆ {1,…,n/2}` with the partial-deletion process's 0-based middle-window indexing, so `altRSum`'s witness positions match `signedInner`'s exactly). -/
noncomputable def Fterm
    (n : ℕ) (δ α : ℝ) (r : ℤ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) : ℝ :=
  binPMFInt (n / 2) (1 / 2) (r + (n / 4 : ℤ)) *
    binPMFInt ((n / 4 : ℤ) + r).toNat (1 - δ) zMinus *
    binPMFInt ((n / 4 : ℤ) - r).toNat (1 - δ) zPlus *
    ∏ j ∈ ℓ, ellFactor n α r (j - 1)

/-- The alternating sum over `r ∈ {-(n/4), ..., n/4}`:
`∑_{r = -(n/4)}^{n/4} (-1)^r · F_{n,δ,α}(r, z₋, z₊, ℓ)`. -/
noncomputable def altRSum
    (n : ℕ) (δ α : ℝ) (zMinus zPlus : ℕ) (ℓ : Finset ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc (-(n / 4 : ℤ)) ((n / 4 : ℤ)),
    (-1 : ℝ) ^ r.natAbs * Fterm n δ α r zMinus zPlus ℓ

/-- Predicate "all elements of the finite set `ℓ` have the same parity". -/
def sameParity (ℓ : Finset ℕ) : Prop :=
  ∀ i ∈ ℓ, ∀ j ∈ ℓ, i % 2 = j % 2

instance (ℓ : Finset ℕ) : Decidable (sameParity ℓ) := by
  unfold sameParity
  exact inferInstance

/-- Sum over k-element subsets of `{1, ..., n/2}` with the same-parity
constraint, of the absolute value of the alternating r-sum, summed over
`z₋, z₊ ∈ {0, ..., n/2}`. -/
noncomputable def innerSumOverEll (n : ℕ) (δ α : ℝ) (k : ℕ) : ℝ :=
  ∑ ℓ ∈ ((Finset.Icc 1 (n / 2)).powersetCard k).filter sameParity,
    ∑ zMinus ∈ Finset.range (n / 2 + 1),
      ∑ zPlus ∈ Finset.range (n / 2 + 1),
        |altRSum n δ α zMinus zPlus ℓ|

/-- The alternating-sum expression `altSum n δ α` from Lemma 6 of
Rivkin–Valiant–Valiant (2024). Sums `innerSumOverEll` over `k ∈ {0, ..., n/2}`. -/
noncomputable def altSum (n : ℕ) (δ α : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1), innerSumOverEll n δ α k

/-- Convenience wrapper that takes a `DelProb` for `δ`. -/
noncomputable def altSum' (n : ℕ) (δ : Workspace.Types.DelProb.DelProb) (α : ℝ) : ℝ :=
  altSum n δ.val α

end Workspace.Types.AlternatingSumExpression
