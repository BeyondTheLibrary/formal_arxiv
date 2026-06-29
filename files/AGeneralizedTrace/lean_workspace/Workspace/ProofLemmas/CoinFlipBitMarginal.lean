import Mathlib
import Workspace.Types.ProbVec
import Workspace.Types.BinVec
import Workspace.Types.CoinFlipDist

/-!
**`CoinFlipBitMarginal`** — marginal of a single coordinate of a product
coin-flip distribution.

For `cfd : CoinFlipDist n S` whose PMF factorises as a product of
per-coordinate Bernoulli factors (the `prod_factorisation` axiom of the
type), the total mass assigned to the set `{b : b.bit i₀ = true}` equals
`ENNReal.ofReal (S.p i₀)`.

This is the building block for the union bound in
`WitnessPrefixSuffixTail`: the probability that *some* prefix/suffix bit is
`true` is at most the sum over those coordinates of `S.p i`.
-/

open Workspace.Types.ProbVec Workspace.Types.BinVec Workspace.Types.CoinFlipDist
open scoped BigOperators

namespace CoinFlipBitMarginal

variable {n : ℕ}

/-- The sum over all binary vectors with bit `i₀` set to `true`, of the
product-factorised PMF mass, equals the Bernoulli factor `S.p i₀`. -/
theorem bit_marginal (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hp : ∀ i : Fin n, 0 ≤ S.p i) (hi₀ : ∀ i : Fin n, S.p i ≤ 1)
    (i₀ : Fin n) :
    (∑ b : BinVec n, if b.bit i₀ = true then (cfd.toPMF b) else 0)
      = ENNReal.ofReal (S.p i₀) := by
  -- abbreviate the per-coordinate factor as a function of (i, c : Bool)
  set g : Fin n → Bool → ENNReal := fun i c =>
    (if i = i₀
     then (if c = true then ENNReal.ofReal (S.p i₀) else 0)
     else ENNReal.ofReal (if c then S.p i else 1 - S.p i)) with hg
  -- rewrite each pmf value by the product factorisation
  have hfac : ∀ b : BinVec n,
      (if b.bit i₀ = true then (cfd.toPMF b) else 0)
        = ∏ i : Fin n, g i (b.bit i) := by
    intro b
    rw [cfd.prod_factorisation b]
    by_cases hbit : b.bit i₀ = true
    · rw [if_pos hbit]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i = i₀
      · subst hi; simp only [hg, if_pos rfl, if_pos hbit]
      · simp only [hg, if_neg hi]
    · rw [if_neg hbit]
      -- the factor at i₀ becomes 0, so the whole product is 0
      rw [Finset.prod_eq_zero (Finset.mem_univ i₀)]
      simp only [hg, if_pos rfl, if_neg hbit]
  simp_rw [hfac]
  -- reindex the sum over BinVec n to a sum over (Fin n → Bool)
  have hreindex :
      (∑ b : BinVec n, ∏ i : Fin n, g i (b.bit i))
        = ∑ f : Fin n → Bool, ∏ i : Fin n, g i (f i) := by
    exact Fintype.sum_equiv equivFun _ _ (fun b => rfl)
  rw [hreindex]
  -- product-of-sums form
  rw [← Fintype.prod_sum]
  -- evaluate each coordinate's Bool-sum
  rw [Finset.prod_eq_single i₀]
  · -- the i₀ factor
    simp only [hg, if_pos rfl]
    rw [Fintype.sum_bool]
    simp
  · -- factors at i ≠ i₀ equal 1
    intro i _ hi
    simp only [hg, if_neg hi]
    rw [Fintype.sum_bool]
    have e1 : (if (true = true) then S.p i else 1 - S.p i) = S.p i := if_pos rfl
    have e2 : (if (false = true) then S.p i else 1 - S.p i) = 1 - S.p i :=
      if_neg (by decide)
    rw [e1, e2]
    rw [← ENNReal.ofReal_add (hp i) (by linarith [hi₀ i])]
    simp [add_sub_cancel]
  · intro h; exact absurd (Finset.mem_univ i₀) h

/-- Union bound: the mass of the event "some coordinate in `T` is `true`"
is at most the sum of the per-coordinate true-probabilities `S.p i`. -/
theorem bit_union_bound (S : ProbVec n) (cfd : CoinFlipDist n S)
    (hp : ∀ i : Fin n, 0 ≤ S.p i) (hi₁ : ∀ i : Fin n, S.p i ≤ 1)
    (T : Finset (Fin n)) [DecidablePred (fun b : BinVec n => ∃ i ∈ T, b.bit i = true)] :
    (∑ b : BinVec n, if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b) else 0)
      ≤ ∑ i ∈ T, ENNReal.ofReal (S.p i) := by
  -- pointwise: the union indicator is ≤ the sum of per-coordinate indicators
  have hpt : ∀ b : BinVec n,
      (if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b) else 0)
        ≤ ∑ i ∈ T, (if b.bit i = true then (cfd.toPMF b) else 0) := by
    intro b
    by_cases hex : ∃ i ∈ T, b.bit i = true
    · rw [if_pos hex]
      obtain ⟨i, hiT, hbit⟩ := hex
      calc cfd.toPMF b
          = (if b.bit i = true then (cfd.toPMF b) else 0) := by rw [if_pos hbit]
        _ ≤ ∑ j ∈ T, (if b.bit j = true then (cfd.toPMF b) else 0) :=
            Finset.single_le_sum
              (f := fun j => (if b.bit j = true then (cfd.toPMF b) else 0))
              (fun j _ => by positivity) hiT
    · rw [if_neg hex]
      positivity
  calc (∑ b : BinVec n, if (∃ i ∈ T, b.bit i = true) then (cfd.toPMF b) else 0)
      ≤ ∑ b : BinVec n, ∑ i ∈ T, (if b.bit i = true then (cfd.toPMF b) else 0) :=
        Finset.sum_le_sum (fun b _ => hpt b)
    _ = ∑ i ∈ T, ∑ b : BinVec n, (if b.bit i = true then (cfd.toPMF b) else 0) := by
        rw [Finset.sum_comm]
    _ = ∑ i ∈ T, ENNReal.ofReal (S.p i) := by
        apply Finset.sum_congr rfl
        intro i _
        exact bit_marginal S cfd hp hi₁ i

end CoinFlipBitMarginal
