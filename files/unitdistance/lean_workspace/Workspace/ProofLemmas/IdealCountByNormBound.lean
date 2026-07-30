-- Cited from: the elementary divisor-function bound for the number of integral ideals of given norm — the number of ideals of norm m is at most the n-fold divisor function d_n(m), and the summatory bound Σ_{m ≤ X} d_n(m) ≤ C^n · X · (1 + log X)^{n-1} / (n-1)! (Dirichlet hyperbola / Stirling); see J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter I, Section 5, and S. Lang, Algebraic Number Theory, 2nd ed., Springer, 1994, Chapter V.
-- Paper label: Proposition 3.7 / Proposition A.13 (ideal-counting core)
-- NL statement: There is an absolute constant C_class > 0 — independent of the field, its degree and its signature — such that for every number field K, the number of nonzero integral ideals of 𝓞 K whose absolute norm does not exceed the Minkowski bound MB(K) = (4/π)^{r₂} · (n!/nⁿ) · √|D_K| (n = [K:Q], r₂ = number of complex places) is at most max{2, rd(K)}^{C_class · [K:Q]}, where rd(K) = |D_K|^{1/[K:Q]} is the root discriminant.
--
-- Everything analytic and arithmetic is proved from Mathlib in
-- `Workspace.ProofLemmas.IdealNormCount`:
--   * `#(D n m) ≤ 2ⁿ m²` where `D n m` is the set of `n`-tuples of positive integers with product
--     `≤ m` (induction on `n`, splitting off the first coordinate, with `∑_{c ≤ m} c⁻² ≤ 2`);
--   * `MB K ≤ max{2, rd K}^(3n/2)` from `(4/π)^{r₂} ≤ 2ⁿ`, `n!/nⁿ ≤ 1`, `√|D_K| = rd(K)^{n/2}`;
--   * combining, the constant `C = 4` works.
-- The only admitted input is the combinatorial comparison `#{I : N(I) ≤ m} ≤ #(D n m)`
-- (equivalently `#{I : N(I) = k} ≤ d_n(k)`), cited as `Workspace.ProofLemmas.IdealCountDivisorTuple`.
import Mathlib
import Workspace.Types.DiscriminantsClassNumber
import Workspace.ProofLemmas.IdealNormCount
import Workspace.ProofLemmas.IdealCountDivisorTuple

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

theorem IdealCountByNormBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K],
      (Nat.card {I : Ideal (𝓞 K) //
        I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤
          (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
            ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(NumberField.discr K : ℝ)|)} : ℝ)
        ≤ (max 2 (rootDiscriminant K)) ^ (C * (Module.finrank ℚ K : ℝ)) :=
  ⟨4, by norm_num, fun K _ _ =>
    Workspace.ProofLemmas.IdealNormCount.idealCount_bound_of_inj IdealCountDivisorTuple K⟩
