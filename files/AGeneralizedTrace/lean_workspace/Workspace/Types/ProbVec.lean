import Mathlib

namespace Workspace.Types.ProbVec

/--
A length-`n` probability vector: a finite sequence `(p 0, …, p (n-1))` of
real numbers, each in the closed interval `[0, 1]`.

This is the fundamental input to the trace-reconstruction problem: each
coordinate `p i` is the parameter of an independent Bernoulli random
variable from which the `i`-th bit of a "trace" is drawn.

This type carries only the underlying data and the per-coordinate bounds;
it does NOT carry a metric / distance. Distances belong to separate types
(e.g. `LInfDistance`, `L1Distance`).
-/
structure ProbVec (n : ℕ) where
  /-- The underlying coordinate function. -/
  p : Fin n → ℝ
  /-- Every coordinate is non-negative. -/
  nonneg : ∀ i : Fin n, 0 ≤ p i
  /-- Every coordinate is at most one. -/
  le_one : ∀ i : Fin n, p i ≤ 1

namespace ProbVec

variable {n : ℕ}

/-- The all-zero probability vector of length `n`. -/
def zero (n : ℕ) : ProbVec n where
  p := fun _ => 0
  nonneg := fun _ => le_refl 0
  le_one := fun _ => by norm_num

/-- The all-one probability vector of length `n`. -/
def one (n : ℕ) : ProbVec n where
  p := fun _ => 1
  nonneg := fun _ => by norm_num
  le_one := fun _ => le_refl 1

/-- The constant probability vector of length `n` whose every coordinate
equals `c`, given that `c ∈ [0, 1]`. -/
def const (n : ℕ) (c : ℝ) (h0 : 0 ≤ c) (h1 : c ≤ 1) : ProbVec n where
  p := fun _ => c
  nonneg := fun _ => h0
  le_one := fun _ => h1

end ProbVec

end Workspace.Types.ProbVec
