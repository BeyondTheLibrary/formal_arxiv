-- Cited from: N. Tschebotareff, Die Bestimmung der Dichtigkeit einer Menge von Primzahlen, welche zu einer gegebenen Substitutionsklasse gehören, Math. Ann. 95(1):191-228, 1926; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VII, Section 13.
-- Paper label: Proposition A.12 (Chebotarev density theorem)
-- NL statement: For every finite Galois extension N/Q, every finite excluded set T of rational primes, and every natural number t, there exist t distinct rational primes outside T, each splitting completely in N.
--
-- The paper cites Chebotarev density, which is not in Mathlib; but the statement it actually uses is
-- the far weaker "infinitely many primes split completely in a finite Galois N/ℚ", which has a
-- classical elementary proof.  That proof is formalised in
-- `Workspace.ProofLemmas.ChebotarevSplitPrimes`:
--   * Schur: a nonconstant f ∈ ℤ[X] has values divisible by arbitrarily large primes (with
--     c = f(0), every f(c·n₀!·y) is c·(1 + n₀!·k), whose second factor is coprime to n₀!);
--   * for a primitive integral generator θ of N, the Kummer–Dedekind exponent of θ is nonzero
--     (denominators cleared by `Algebra.discr_mul_isIntegral_mem_adjoin`);
--   * a prime not dividing |D_N| is unramified (`NumberField.absNorm_differentIdeal` and
--     `not_dvd_differentIdeal_iff`);
--   * for such a prime with a root of minpoly ℤ θ mod p, Kummer–Dedekind
--     (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) produces a prime of residue degree 1;
--     Galois-ness makes ALL residue degrees 1 (`Ideal.inertiaDeg_eq_of_isGaloisGroup`), and the
--     fundamental identity then gives exactly [N:ℚ] primes above p — i.e. p splits completely.
import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.ChebotarevSplitPrimes

open scoped NumberField
open Workspace.Types.SplittingRamification

/-- For a finite Galois extension `N/ℚ`, a finite excluded set `T` of rational primes and any `t`,
there exist `t` distinct rational primes outside `T`, each splitting completely in `N`.

Proved from Mathlib; see `Workspace.ProofLemmas.ChebotarevSplitPrimes`. -/
theorem ChebotarevManySplitPrimes (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (T : Finset ℕ) (t : ℕ) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧
      ∀ b, (q b).Prime ∧ q b ∉ T ∧ SplitsCompletelyRat (q b) N :=
  Workspace.ProofLemmas.ChebotarevSplitPrimes.chebotarevManySplitPrimes N T t
