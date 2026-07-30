-- Cited from: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed.,
-- Springer, 2008 (NSW08), and J. Neukirch, Algebraic Number Theory, Springer, 1999 (Neu99):
-- a compositum of finitely many finite Galois everywhere-unramified extensions is unramified at
-- every FINITE prime.
-- Paper label: Definitions A.2/A.3 (finite-primes half).
-- NL statement: For a finite set `s` of members of the defining family
-- (finite Galois everywhere-unramified pro-3 subextensions of `AlgebraicClosure F`), their
-- compositum `⨆ i ∈ s, i` is unramified at every finite prime of `F`.
--
-- This is the Neukirch arithmetic input. The closure of the ramification index at finite primes
-- under compositum/⊔/iSup of rings of integers is not currently a Mathlib lemma (there is no lemma
-- that `ramificationIdx p P = 1` is preserved when passing from `𝓞 Eᵢ` to `𝓞 (⨆ Eᵢ)`). The
-- infinite-places half of everywhere-unramifiedness is not part of this axiom: it is derived
-- from Mathlib (`IsUnramifiedAtInfinitePlaces_of_odd_finrank`, using that the compositum is
-- finite Galois of odd — in fact 3-power — degree over `F`) in the consuming file.
--
-- Proof (Hilbert's inertia argument), in `Workspace.ProofLemmas.CompositumUnramified`:
--   * for `M/F` finite Galois and `P | p`, Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn`
--     gives `|I_{M/F}(P)| = e(P/p)`;
--   * for an intermediate field `E` with `E/F` unramified, tower multiplicativity of the
--     ramification index gives `e(P/p) = e(P/P∩E)`, so `|I_{M/E}(P)| = |I_{M/F}(P)|`; since
--     `I_{M/E}(P)` embeds in `I_{M/F}(P)` by `AlgEquiv.restrictScalars` (the two inertia groups are
--     cut out by the *same* condition on `𝓞 M`), the embedding is onto, i.e.
--     `I_{M/F}(P) ≤ Gal(M/E)`;
--   * with `A ⊔ B = ⊤` this yields `I_{M/F}(P) ≤ Gal(M/A) ⊓ Gal(M/B) = Gal(M/⊤) = 1`, so
--     `e(P/p) = 1`;
--   * a `Finset` induction lifts the two-field statement to the whole family (compositum of
--     finitely many Galois extensions is Galois, `IntermediateField.normal_iSup`/`isSeparable_iSup`).
-- Transport of unramifiedness along field isomorphisms is free because it is equivalent to the
-- discriminant identity `|D_L| = |D_K|^[L:K]` (`unramified_iff_natAbs_discr`), and `NumberField.discr`
-- is a ring-isomorphism invariant.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.SplittingRamification
import Workspace.ProofLemmas.CompositumUnramified

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

/-- **Compositum of family members is unramified at finite primes.**
For a finite set `s` of members of the defining family of finite Galois everywhere-unramified
pro-3 subextensions of `AlgebraicClosure F`, the compositum `⨆ i ∈ s, i` is unramified at every
finite prime of `F`.

Proved from Mathlib by Hilbert's inertia argument — see
`Workspace.ProofLemmas.CompositumUnramified`. -/
theorem CompositumFamilyUnramifiedAtFinitePrimes :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
        NumberField.of_module_finite (K := F)
          (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
      UnramifiedAtFinitePrimes F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
  Workspace.ProofLemmas.CompositumUnramified.compositumFamilyUnramifiedAtFinitePrimes
