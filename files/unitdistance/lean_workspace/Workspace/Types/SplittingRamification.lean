import Mathlib

/-!
# Splitting and ramification predicates for number fields (Definition A.2)

This file formalizes the splitting/ramification predicates used throughout the paper:

* `SplitsCompletelyRat q L` : a rational prime `q` splits completely in a number field `L`.
* `SplitsCompletely p M`    : a finite prime `p` of `F` splits completely in a finite
  extension `M/F` of number fields.
* `UnramifiedAtFinitePrimes F M` : the extension `M/F` is unramified at every finite prime.
* `EverywhereUnramified F M` : `M/F` is unramified at all finite primes and all infinite places.

Ramification indices and residue (inertia) degrees are Mathlib's `Ideal.ramificationIdx`
and `Ideal.inertiaDeg`; the set of primes lying over a prime is `Ideal.primesOver`.
-/

set_option maxHeartbeats 400000

open scoped NumberField

namespace Workspace.Types.SplittingRamification

/-- A rational prime `q` **splits completely** in a number field `L` if:
* `q` is prime, and
* the number of prime ideals of `𝓞 L` lying over the ideal `(q) ⊆ ℤ` equals `[L : ℚ]`, and
* each such prime has ramification index `1` and residue (inertia) degree `1` over `(q)`.

The last two conditions force `q · 𝓞 L = 𝔭₁ ⋯ 𝔭_{[L:ℚ]}` with the `𝔭ᵢ` distinct, each
unramified with residue field `𝔽_q`. -/
def SplitsCompletelyRat (q : ℕ) (L : Type*) [Field L] [NumberField L] : Prop :=
  q.Prime ∧
  (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 L)).ncard = Module.finrank ℚ L ∧
  ∀ P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 L),
    Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
    Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1

/-- A finite prime `p` of a number field `F` **splits completely** in a finite extension
`M/F` of number fields if:
* there are exactly `[M : F]` primes of `𝓞 M` lying over `p`, and
* each has ramification index `1` and residue (inertia) degree `1` over `p`. -/
def SplitsCompletely {F : Type*} [Field F] [NumberField F] {M : Type*} [Field M] [NumberField M]
    [Algebra F M] (p : Ideal (𝓞 F)) : Prop :=
  (Ideal.primesOver p (𝓞 M)).ncard = Module.finrank F M ∧
  ∀ P ∈ Ideal.primesOver p (𝓞 M),
    Ideal.ramificationIdx p P = 1 ∧
    Ideal.inertiaDeg p P = 1

/-- The extension `M/F` of number fields is **unramified at all finite primes** if every
nonzero prime `p` of `𝓞 F` is unramified in `𝓞 M`, i.e. every prime `P` of `𝓞 M` lying over
`p` has ramification index `e(P/p) = 1`. -/
def UnramifiedAtFinitePrimes (F : Type*) [Field F] [NumberField F] (M : Type*) [Field M]
    [NumberField M] [Algebra F M] : Prop :=
  ∀ p : Ideal (𝓞 F), p ≠ ⊥ → p.IsPrime →
    ∀ P ∈ Ideal.primesOver p (𝓞 M),
      Ideal.ramificationIdx p P = 1

/-- The extension `M/F` of number fields is **everywhere unramified** if it is unramified at
all finite primes and at all infinite places (no real place of `F` becomes complex in `M`,
captured by Mathlib's `NumberField.IsUnramifiedAtInfinitePlaces`). -/
def EverywhereUnramified (F : Type*) [Field F] [NumberField F] (M : Type*) [Field M]
    [NumberField M] [Algebra F M] : Prop :=
  UnramifiedAtFinitePrimes F M ∧ IsUnramifiedAtInfinitePlaces F M

end Workspace.Types.SplittingRamification
