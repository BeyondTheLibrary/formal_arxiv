import Mathlib
import Workspace.Types.SplittingRamification

/-!
# Frobenius elements at unramified primes (Definition A.7)

This file formalizes Frobenius elements for finite Galois extensions of number fields and the
Frobenius-representative notion for (possibly infinite) profinite Galois extensions, used in the
Chebotarev step and the tower cutting of the paper.

## Design (predicate-first)

Rather than *constructing* the Frobenius element (which for the profinite case would require
carrying a compatible system through a limit), we characterize it by its defining property.

For a finite Galois extension `N/K` of number fields, an element `σ : Gal(N/K) = N ≃ₐ[K] N`
restricts to an `𝓞 K`-algebra automorphism `galRestrict (𝓞 K) K N (𝓞 N) σ` of `𝓞 N`.
Mathlib's `AlgHom.IsArithFrobAt` says a map `φ : 𝓞 N →ₐ[𝓞 K] 𝓞 N` is an *arithmetic Frobenius*
at a prime `P` of `𝓞 N` when
`φ x ≡ x ^ #(𝓞 K / (P ∩ 𝓞 K)) (mod P)` for all `x : 𝓞 N`.
This single condition simultaneously encodes that `σ` fixes `P` (see
`AlgHom.IsArithFrobAt.comap_eq`) and that it induces `x ↦ x ^ |𝓞K/p|` on the residue ring
`𝓞 N / P`, which is exactly the paper's characterization of `Frob_{P/p}`.

* `IsFrobeniusAtPrime σ P` — `σ` is a Frobenius at the prime `P` of `𝓞 N`.
* `IsFrobeniusAt σ p`      — `σ` is a Frobenius at some prime `P` of `𝓞 N` above `p` (finite case).
* `frobeniusClass p`       — the set of all Frobenius elements at `p` (a conjugacy class).
* `IsFrobeniusRepAt σ p`   — for a possibly infinite Galois extension `Ω/F`, `σ` restricts to a
  Frobenius at `p` on every finite Galois subextension (a compatible system of Frobenii).
-/

set_option maxHeartbeats 400000

open scoped NumberField

namespace Workspace.Types.FrobeniusSplitting

/-! ## Finite Galois case -/

section FiniteGalois

variable {K N : Type*} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]

/-- `σ ∈ Gal(N/K)` is an **(arithmetic) Frobenius at the prime `P`** of `𝓞 N`: the induced
automorphism of `𝓞 N` over `𝓞 K` satisfies `σ x ≡ x ^ #(𝓞 K / (P ∩ 𝓞 K)) (mod P)` for all
`x : 𝓞 N`. Equivalently `σ` fixes `P` and acts on the residue ring `𝓞 N / P` as `x ↦ x ^ |𝓞K/p|`,
where `p = P ∩ 𝓞 K`. -/
def IsFrobeniusAtPrime (σ : N ≃ₐ[K] N) (P : Ideal (𝓞 N)) : Prop :=
  (galRestrict (𝓞 K) K N (𝓞 N) σ).toAlgHom.IsArithFrobAt P

/-- `σ ∈ Gal(N/K)` is a **Frobenius element at the finite prime `p`** of `𝓞 K` if it is a Frobenius
at some prime `P` of `𝓞 N` lying over `p`. (When `p` is unramified in `N`, this `σ` is unique for a
fixed `P`, and the collection over all `P | p` forms a single conjugacy class.) -/
def IsFrobeniusAt (σ : N ≃ₐ[K] N) (p : Ideal (𝓞 K)) : Prop :=
  ∃ P : Ideal (𝓞 N), P.IsPrime ∧ P.LiesOver p ∧ IsFrobeniusAtPrime σ P

end FiniteGalois

/-! ## Profinite (possibly infinite) case -/

section Profinite

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

/-- `σ ∈ Gal(Ω/F)` is a **Frobenius representative at the finite prime `p`** of `𝓞 F`, for a
(possibly infinite) Galois extension `Ω/F`: for every finite-dimensional Galois subextension
`F ≤ E ≤ Ω`, the restriction `σ|_E ∈ Gal(E/F)` is a Frobenius element at `p` (viewing `p` as a
prime of the common base `F`).

This is the correct receptacle for the paper's "choose one Frobenius representative `σ_v` in `G`":
a compatible system of Frobenii, one on each finite layer. -/
def IsFrobeniusRepAt (σ : Ω ≃ₐ[F] Ω) (p : Ideal (𝓞 F)) : Prop :=
  ∀ (E : IntermediateField F Ω) [FiniteDimensional F E] [IsGalois F E],
    letI : NumberField E := NumberField.of_module_finite (K := F) (L := (E : Type _))
    IsFrobeniusAt (AlgEquiv.restrictNormalHom (E : Type _) σ) p

end Profinite

end Workspace.Types.FrobeniusSplitting
