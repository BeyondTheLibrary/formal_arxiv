import Mathlib

/-!
# ZeroCount — utility for counting distinct zeros of a function `ℝ → ℝ`

This module provides three small utilities used downstream in Proposition 7
(linear combination of `k` Gaussians has at most `2(k-1)` zeros) and
Theorem 8 (Gaussian convolution does not increase the number of zeros):

* `zeroSet f` — the set of points where `f x = 0`;
* `zeroCount f` — the (extended) cardinality of `zeroSet f` in `ℕ∞`;
* `hasAtMostNZeros f n` — the predicate `zeroCount f ≤ n`.

The count is `Set.encard`, which returns an `ℕ∞` (`= WithTop ℕ`), so it
gracefully handles the case where `f` has infinitely many zeros (the value
is `⊤`). Distinct zeros only — no notion of multiplicity is introduced.
-/

namespace Workspace.Types.ZeroCount

open Set

/-- The set of zeros of `f : ℝ → ℝ`. -/
def zeroSet : (ℝ → ℝ) → Set ℝ := fun f => {x | f x = 0}

/-- The number of distinct zeros of `f`, as an extended natural number. -/
noncomputable def zeroCount : (ℝ → ℝ) → ℕ∞ := fun f => (zeroSet f).encard

/-- `f` has at most `n` zeros. -/
def hasAtMostNZeros : (ℝ → ℝ) → ℕ → Prop := fun f n => zeroCount f ≤ (n : ℕ∞)

/-- Unfolding lemma for `zeroSet`. -/
@[simp] lemma zeroSet_def (f : ℝ → ℝ) : zeroSet f = {x | f x = 0} := rfl

/-- Unfolding lemma for `zeroCount`. -/
lemma zeroCount_def (f : ℝ → ℝ) : zeroCount f = (zeroSet f).encard := rfl

/-- Unfolding lemma for `hasAtMostNZeros`. -/
lemma hasAtMostNZeros_def (f : ℝ → ℝ) (n : ℕ) :
    hasAtMostNZeros f n ↔ zeroCount f ≤ (n : ℕ∞) := Iff.rfl

end Workspace.Types.ZeroCount
