import Mathlib
import Workspace.Types.CMAdjoinI
import Workspace.Types.SplittingRamification

/-!
# Admissible datum (Definition 2.1)

This file bundles the *admissible datum* of Definition 2.1 of the paper: a totally real
number field `L` of degree `f = [L : ℚ]`, its CM extension `K = L(i)` (encoded by the
`IsAdjoinI` predicate from `CMAdjoinI`), a positive integer `t`, and `t` distinct rational
primes `q₁, …, q_t`, each `≡ 1 (mod 4)` and each splitting completely in `L` (encoded by
`SplitsCompletelyRat` from `SplittingRamification`).

The structure carries *only* foundational data and hypotheses — no conclusions (no
class-number hypotheses; those appear in theorem statements elsewhere). Derived quantities
`deg`, `Qprod`, `Dq` are provided as plain defs.
-/

open scoped NumberField

namespace Workspace.Types.AdmissibleDatum

open Workspace.Types.CMAdjoinI Workspace.Types.SplittingRamification

/-- An **admissible datum** (Definition 2.1).

It bundles:
* a totally real number field `L` (fields `L`, `fieldL`, `nfL`, `trL`);
* the CM field `K = L(i)` as an `L`-algebra (fields `K`, `fieldK`, `nfK`, `algLK`) together
  with the defining property `h_adjoin : IsAdjoinI L K` (there is `iota ∈ K` with
  `iota ^ 2 = -1` generating `K` over `L`);
* a positive integer `t` (fields `t`, `ht`);
* `t` distinct rational primes `q : Fin t → ℕ`, each prime (`hq_prime`), pairwise distinct
  (`hq_distinct`), congruent to `1 (mod 4)` (`hq_mod4`), and splitting completely in `L`
  (`hq_split`).

The type-class fields are declared as instance-implicit so that they are available for the
subsequent fields; the `attribute [instance]` block below re-registers the projections as
instances so the derived defs and downstream theorems can use them. -/
structure AdmissibleDatum where
  /-- The totally real base field `L`. -/
  L : Type
  /-- The CM field `K = L(i)`. -/
  K : Type
  [fieldL : Field L]
  [fieldK : Field K]
  [nfL : NumberField L]
  [nfK : NumberField K]
  [trL : NumberField.IsTotallyReal L]
  [algLK : Algebra L K]
  /-- `K` is obtained from `L` by adjoining a square root of `-1`. -/
  h_adjoin : IsAdjoinI L K
  /-- The number of primes. -/
  t : ℕ
  /-- Positivity of `t`. -/
  ht : 0 < t
  /-- The `t` rational primes. -/
  q : Fin t → ℕ
  /-- Each `q b` is prime. -/
  hq_prime : ∀ b, (q b).Prime
  /-- The primes are pairwise distinct. -/
  hq_distinct : Function.Injective q
  /-- Each `q b` is congruent to `1` modulo `4`. -/
  hq_mod4 : ∀ b, q b % 4 = 1
  /-- Each `q b` splits completely in `L`. -/
  hq_split : ∀ b, SplitsCompletelyRat (q b) L

attribute [instance] AdmissibleDatum.fieldL AdmissibleDatum.fieldK AdmissibleDatum.nfL
  AdmissibleDatum.nfK AdmissibleDatum.trL AdmissibleDatum.algLK

/-- The degree `f = [L : ℚ]` of the base field. -/
noncomputable def deg (d : AdmissibleDatum) : ℕ := Module.finrank ℚ d.L

/-- The product `Q = ∏_b q_b` of the chosen primes. -/
def Qprod (d : AdmissibleDatum) : ℕ := ∏ b, d.q b

/-- The quantity `D = Q ^ 2`. -/
def Dq (d : AdmissibleDatum) : ℕ := (Qprod d) ^ 2

end Workspace.Types.AdmissibleDatum
