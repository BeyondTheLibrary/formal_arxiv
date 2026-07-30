-- Cited from: the elementary bound `#{I ⊆ 𝓞_K : N(I) = k} ≤ d_n(k)` (the `n`-fold divisor
-- function), see J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter I, Section 5, and
-- S. Lang, Algebraic Number Theory, 2nd ed., Springer, 1994, Chapter V.
-- Paper label: Proposition 3.7 / Proposition A.13 (ideal-counting core, combinatorial half)
--
-- This is the combinatorial half of `IdealCountByNormBound`: the number of nonzero integral ideals
-- of norm at most `m` is at most the number of `n`-tuples of positive integers with product at most
-- `m` (equivalently `#{I : N(I) = k} ≤ d_n(k)`).  It rests on unique factorisation of ideals
-- together with `∑_{P | q} e_P f_P = [K:ℚ]`.  The analytic and arithmetic half of the Minkowski-bound
-- estimate is proved separately in `Workspace.ProofLemmas.IdealNormCount`.
--
-- NL statement: For every number field `K` with `n = [K : ℚ]` and every natural number `m`, the
-- number of nonzero integral ideals of `𝓞 K` of absolute norm at most `m` is at most the number of
-- `n`-tuples of positive integers whose product is at most `m`.
--
-- Proof: the injection is built in `Workspace.ProofLemmas.IdealCountInjection`: for each rational
-- prime q there are at most n = [K:ℚ] primes of 𝓞 K above q (from ∑_{P|q} e_P f_P = n), so they can
-- be indexed injectively by `Fin n`; sending a nonzero ideal I to the tuple
--   Φ I i = ∏_{idx P = i} N(P)^{v_P(I)}
-- gives ∏ i, Φ I i = N(I), and Φ is injective because N(P) = q(P)^{f(P)}, so the q(P)-adic
-- valuation of Φ I (idx P) recovers v_P(I)·f(P) with f(P) > 0.
import Mathlib
import Workspace.ProofLemmas.IdealNormCount
import Workspace.ProofLemmas.IdealCountInjection

open scoped NumberField

/-- **Ideal count ≤ divisor-tuple count.**  The number of nonzero integral ideals of `𝓞 K` of norm
at most `m` is at most the number of `[K:ℚ]`-tuples of positive integers with product at most `m`. -/
theorem IdealCountDivisorTuple :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ),
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
        ≤ (Workspace.ProofLemmas.IdealNormCount.DivisorCount.D (Module.finrank ℚ K) m).card :=
  fun K _ _ m => Workspace.ProofLemmas.IdealCountInjection.idealCount_le_D (K := K) m
