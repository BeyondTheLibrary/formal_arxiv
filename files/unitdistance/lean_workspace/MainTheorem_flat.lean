import Mathlib

/-!
# PlanarCounting

Unit-distance counting functions of the paper "Planar Point Sets with Many Unit
Distances".

* `nu P` counts, for a finite set `P` of points in a (pseudo-)metric space, the
  number of **unordered** pairs `{x, y}` of **distinct** points of `P` at distance
  exactly `1`.
* `nuMax n` is the maximum of `nu P` over all `n`-point subsets `P` of the Euclidean
  plane `EuclideanSpace ℝ (Fin 2)`.
* `toPlane` / `embedFinset` provide the standard isometric identification of the
  complex plane `ℂ` with `EuclideanSpace ℝ (Fin 2)`, so that `nu` computed on a
  `Finset ℂ` agrees with `nu` on its image in the Euclidean plane.
-/

open scoped Classical

namespace Workspace.Types.PlanarCounting

variable {X : Type*} [PseudoMetricSpace X]

/-- The symmetric distance function packaged as a map out of `Sym2`, so that it can
be evaluated on an *unordered* pair. -/
noncomputable def distSym2 : Sym2 X → ℝ :=
  Sym2.lift ⟨dist, fun x y => dist_comm x y⟩

@[simp] lemma distSym2_mk (x y : X) : distSym2 (s(x, y)) = dist x y :=
  Sym2.lift_mk _ _ _

/-- `nu P` is the number of unordered pairs `{x, y}` of distinct points of `P` at
distance exactly `1`. Encoded as the number of non-diagonal elements of `Finset.sym2 P`
(each unordered pair drawn from `P` occurs exactly once there) whose two endpoints are
at distance `1`. -/
noncomputable def nu (P : Finset X) : ℕ :=
  (P.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1)).card

/-- The maximum number of unit distances realized by an `n`-point set in the Euclidean
plane `ℝ² = EuclideanSpace ℝ (Fin 2)`. Defined as the supremum, over all `n`-point
subsets `P`, of `nu P`. Because `nu P ≤ P.card.choose 2 = n.choose 2` the set of values
is bounded above, and it is nonempty for every `n` (the plane is infinite), so this
supremum is attained and finite. -/
noncomputable def nuMax (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ nu P = k}

/-- The standard linear isometry identifying the complex plane `ℂ` with the Euclidean
plane `EuclideanSpace ℝ (Fin 2)`, sending `z` to `(z.re, z.im)`. It preserves distances,
so it carries unit-distance configurations to unit-distance configurations. -/
noncomputable def toPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Transport a finite set of complex numbers to a finite set of points of the Euclidean
plane via the isometry `toPlane`. Bridges `nu` on `Finset ℂ` with `nu` on
`Finset (EuclideanSpace ℝ (Fin 2))`. -/
noncomputable def embedFinset (P : Finset ℂ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  P.image toPlane

end Workspace.Types.PlanarCounting

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

set_option maxHeartbeats 400000

open NumberField

namespace Workspace.Types.DiscriminantsClassNumber

/-!
Number-field invariants: root discriminant, class number, and the relative
discriminant ideal of a finite extension of number fields.  Definitions only,
a thin layer over Mathlib.
-/

/-- The root discriminant of a number field `K`:
`rd(K) = |D_K|^(1/[K:ℚ])`, a nonnegative real number, where `D_K = NumberField.discr K`
is the absolute discriminant and `[K:ℚ] = Module.finrank ℚ K`. -/
noncomputable def rootDiscriminant (K : Type*) [Field K] [NumberField K] : ℝ :=
  (|(NumberField.discr K : ℝ)|) ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))

/-- The class number `h(K)` of a number field `K`, i.e. the cardinality of the
ideal class group of `𝓞 K`.  Re-exposed from Mathlib's `NumberField.classNumber`. -/
noncomputable def classNumber (K : Type*) [Field K] [NumberField K] : ℕ :=
  NumberField.classNumber K

end Workspace.Types.DiscriminantsClassNumber

open Polynomial
open scoped ComplexConjugate

namespace Workspace.Types.CMAdjoinI

set_option maxHeartbeats 400000

/-!
# CM-extension data `K = L(i)`

This file formalises the CM-extension data `K = L(i)` of a totally real number field `L`
(Definition A.4 / Definition 2.1).

* `IsAdjoinI L K` : the predicate that `K` is obtained from `L` by adjoining a square root
  of `-1` (a generator `iota` with `iota ^ 2 = -1` that generates `K` over `L`).
* `conjAut h` : the nontrivial `L`-automorphism `c` of `K`, the complex conjugation sending
  `iota` to `-iota`.
* `relNorm_KL h u` : the relative norm `u * c(u)` as an element of `K`.
-/

section Def

variable (L K : Type*) [Field L] [Field K] [Algebra L K]

/-- `IsAdjoinI L K` holds when `K` is obtained from the field `L` by adjoining a square root
`iota` of `-1`, i.e. there is an element `iota : K` with `iota ^ 2 = -1` generating `K` over
`L`. When `L` is totally real this forces `iota ∉ L`, so `[K : L] = 2` and `K` is a
totally imaginary (CM) field. -/
def IsAdjoinI : Prop :=
  ∃ iota : K, iota ^ 2 = -1 ∧ IntermediateField.adjoin L {iota} = ⊤

end Def

section ConjAut

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K]

/-- The nontrivial `L`-algebra automorphism `c` of `K = L(i)`: the unique element of
`Gal(K/L)` different from the identity, i.e. complex conjugation, sending the chosen square
root `iota` of `-1` to `-iota` while fixing `L`.  It is constructed as the algebra
homomorphism `K → K` determined by sending the generator `iota` to the other root `-iota`
of the minimal polynomial `X ^ 2 + 1`; this map is bijective because `K` is a finite
extension of `L`. -/
noncomputable def conjAut (h : IsAdjoinI L K) : K ≃ₐ[L] K := by
  classical
  set iota := h.choose with hi
  have hsq : iota ^ 2 = -1 := h.choose_spec.1
  have hadj : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  -- `iota` is integral over `L`, being a root of the monic polynomial `X ^ 2 + 1`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota` does not lie in (the image of) `L`, because `L` is totally real.
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- Hence the minimal polynomial of `iota` over `L` is exactly `X ^ 2 + 1`.
  have hmin : minpoly L iota = X ^ 2 + 1 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : L[X]).natDegree ≤ (minpoly L iota).natDegree := by
      have h2 : 2 ≤ (minpoly L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd
      hdeg).symm
  -- `-iota` is a root of the minimal polynomial.
  have hroot : -iota ∈ (minpoly L iota).aroots K := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [hmin]
    simp [hsq]
  -- The algebra hom `L⟮iota⟯ →ₐ[L] K` sending the generator `iota` to `-iota`.
  let f : IntermediateField.adjoin L {iota} →ₐ[L] K :=
    (IntermediateField.algHomAdjoinIntegralEquiv L hint).symm ⟨-iota, hroot⟩
  -- Identify `L⟮iota⟯` with `K` via `IsAdjoinI`.
  let e : IntermediateField.adjoin L {iota} ≃ₐ[L] K :=
    (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
  let g : K →ₐ[L] K := f.comp e.symm.toAlgHom
  haveI hfd : FiniteDimensional L (IntermediateField.adjoin L {iota}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI : FiniteDimensional L K := e.toLinearEquiv.finiteDimensional
  have hinj : Function.Injective g := g.toRingHom.injective
  refine AlgEquiv.ofBijective g ⟨hinj, ?_⟩
  have hsurj : Function.Surjective (g.toLinearMap) :=
    (LinearMap.injective_iff_surjective).mp hinj
  exact hsurj

/-- The relative norm `N_{K/L}(u) = u * c(u)` as an element of `K`, where `c = conjAut h`.
The paper uses the equation `u * c(u) = 1` in `K` to express that all archimedean absolute
values of a unit `u` are `1`. -/
noncomputable def relNorm_KL (h : IsAdjoinI L K) (u : K) : K := u * conjAut h u

end ConjAut

end Workspace.Types.CMAdjoinI

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

set_option maxHeartbeats 400000

/-!
# Pro-`p` groups and their basic invariants

Formalization of the pro-`p` group conventions of the paper (Convention 0.8):
the predicate `IsProP`, the topological Frattini subgroup `frattiniOpen`, the
generator rank `dRank`, and topological finite generation `TopFinitelyGenerated`.

Everything here is a *definition*; the group-theoretic facts (normality/closedness
of `frattiniOpen`, `Φ(G) = closure of Gᵖ[G,G]`, elementary-abelian Frattini
quotient, etc.) are theorem statements formalized elsewhere.
-/

namespace Workspace.Types.ProPGroup

variable {G : Type*}

/-- A topological group `G` **is pro-`p`** when it is profinite (compact, Hausdorff,
totally disconnected topological group) and every *open normal* subgroup has index a
power of the prime `p`.  This is equivalent to being an inverse limit of finite
`p`-groups. -/
def IsProP (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  IsTopologicalGroup G ∧ CompactSpace G ∧ T2Space G ∧ TotallyDisconnectedSpace G ∧
    ∀ H : Subgroup G, H.Normal → IsOpen (H : Set G) → ∃ k : ℕ, H.index = p ^ k

/-- `H` is a **maximal proper open subgroup** of `G`: it is open, proper, and maximal
among open subgroups (no open subgroup lies strictly between `H` and the whole group). -/
def IsMaximalOpenSubgroup [Group G] [TopologicalSpace G] (H : Subgroup G) : Prop :=
  IsOpen (H : Set G) ∧ H ≠ ⊤ ∧
    ∀ K : Subgroup G, IsOpen (K : Set G) → H ≤ K → K = H ∨ K = ⊤

/-- The **topological Frattini subgroup** `Φ(G)`: the intersection of all maximal
proper open subgroups of `G`.  If there are none, this is (by the `sInf` convention in
a complete lattice) the whole group `⊤`.  For profinite `G` this subgroup is closed and
normal, but that is a theorem, not part of the definition. -/
def frattiniOpen (G : Type*) [Group G] [TopologicalSpace G] : Subgroup G :=
  sInf {H : Subgroup G | IsMaximalOpenSubgroup H}

/-- A subset `S ⊆ G` **topologically generates** `G` when the topological closure of the
(abstract) subgroup it generates is all of `G`. -/
def TopologicallyGenerates [Group G] [TopologicalSpace G] (S : Set G) : Prop :=
  _root_.closure ((Subgroup.closure S : Subgroup G) : Set G) = Set.univ

/-- The **generator rank** `d(G)`: the least cardinality of a finite subset of `G` that
topologically generates `G`, as an extended natural number.  If no finite subset
topologically generates `G`, the `sInf` of the empty set gives the junk value `⊤ = ∞`. -/
noncomputable def dRank (G : Type*) [Group G] [TopologicalSpace G] : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ S : Finset G, TopologicallyGenerates (S : Set G) ∧ (S.card : ℕ∞) = n}

/-- `G` is **topologically finitely generated** when some finite subset topologically
generates it. -/
def TopFinitelyGenerated (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ S : Finset G, TopologicallyGenerates (S : Set G)

end Workspace.Types.ProPGroup

set_option maxHeartbeats 400000

/-!
# Free pro-`p` groups, pro-`p` presentations, and the relation rank `r(G)`

Formalization of the free pro-`p` group on `n` generators (paper Convention 0.8),
of a pro-`p` presentation of a pro-`p` group, and of the relation rank `r(G)`.

The free pro-`p` group on `n` generators is constructed here as the pro-`p`
completion of the discrete free group `FreeGroup (Fin n)`: it is the topological
closure of the diagonal image of `FreeGroup (Fin n)` inside the product

  `∏_{N} (FreeGroup (Fin n) / N)`

taken over all normal subgroups `N` of `p`-power index (equivalently, over all
finite `p`-group quotients).  Each quotient carries the discrete topology, the
product carries the product topology (making it a profinite topological group),
and the completion is a closed subgroup of that product — this is the standard
"closure of the diagonal = inverse limit" model of a profinite completion,
restricted to the `p`-power quotients so as to obtain the *pro-`p`* completion.

Everything below is a *definition*; the pro-`p`-ness of `freeProP`, its universal
property, and the Golod–Shafarevich / Frattini facts are theorem statements
formalized elsewhere.
-/

namespace Workspace.Types.ProPPresentationRank

open Workspace.Types.ProPGroup

/-- A normal subgroup of `FreeGroup (Fin n)` of `p`-power (hence finite) index.
Bundled on top of Mathlib's `FiniteIndexNormalSubgroup`, whose projection
instances supply `Normal` and `FiniteIndex` for the underlying subgroup (so the
quotient is automatically a finite group). -/
structure PPowIndexSubgroup (p n : ℕ) where
  /-- The underlying finite-index normal subgroup. -/
  sub : FiniteIndexNormalSubgroup (FreeGroup (Fin n))
  /-- Its index is a power of `p`; together with finiteness of index this says the
  quotient is a finite `p`-group. -/
  isPPow : ∃ k : ℕ, sub.toSubgroup.index = p ^ k

variable {p n : ℕ}

/-- Each finite `p`-quotient is given the discrete topology. -/
instance instTopQuot (M : PPowIndexSubgroup p n) :
    TopologicalSpace (FreeGroup (Fin n) ⧸ M.sub.toSubgroup) := ⊥

instance instDiscQuot (M : PPowIndexSubgroup p n) :
    DiscreteTopology (FreeGroup (Fin n) ⧸ M.sub.toSubgroup) := ⟨rfl⟩

/-- The product of all finite `p`-group quotients of `FreeGroup (Fin n)`, with the
product topology.  This is a profinite topological group. -/
abbrev ProdQuot (p n : ℕ) : Type :=
  ∀ M : PPowIndexSubgroup p n, FreeGroup (Fin n) ⧸ M.sub.toSubgroup

/-- The canonical diagonal homomorphism `FreeGroup (Fin n) → ∏_N FreeGroup (Fin n)/N`,
sending `g` to the tuple of its images in each finite `p`-quotient. -/
def diagHom (p n : ℕ) : FreeGroup (Fin n) →* ProdQuot p n :=
  Pi.monoidHom (fun M => QuotientGroup.mk' M.sub.toSubgroup)

/-- The **free pro-`p` group** on `n` generators, as a closed subgroup of the product
of the finite `p`-group quotients: the topological closure of the diagonal image of
`FreeGroup (Fin n)`. -/
def freeProPSubgroup (p n : ℕ) : Subgroup (ProdQuot p n) :=
  (diagHom p n).range.topologicalClosure

/-- The **free pro-`p` group** on `n` generators, as a type. -/
def freeProP (p n : ℕ) : Type := (freeProPSubgroup p n)

instance : Group (freeProP p n) := inferInstanceAs (Group (freeProPSubgroup p n))

instance : TopologicalSpace (freeProP p n) :=
  inferInstanceAs (TopologicalSpace (freeProPSubgroup p n))

instance : IsTopologicalGroup (freeProP p n) :=
  inferInstanceAs (IsTopologicalGroup (freeProPSubgroup p n))

/-- A **pro-`p` presentation** of a (pro-`p`) group `G` with `d` generators and `k`
relations `rels`: a continuous surjective homomorphism `π` from the free pro-`p`
group on `d` generators onto `G`, whose kernel is the *closed normal closure* of
the relation family `rels` (the smallest closed normal subgroup containing them). -/
def IsProPPresentation (p d : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {k : ℕ}
    (π : freeProP p d →ₜ* G) (rels : Fin k → freeProP p d) : Prop :=
  Function.Surjective π ∧
    (Subgroup.normalClosure (Set.range rels)).topologicalClosure =
      MonoidHom.ker π.toMonoidHom

/-- The **relation rank** `r(G)` of a pro-`p` group `G`: the least number `k` of
relations over all pro-`p` presentations of `G` on exactly `d(G) = dRank G`
generators.  If `G` admits no such finite presentation the `sInf` of the empty set
gives the junk value `⊤ = ∞`. -/
noncomputable def relRank (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ℕ∞ :=
  sInf {k : ℕ∞ | ∃ (d : ℕ) (m : ℕ) (π : freeProP p d →ₜ* G) (rels : Fin m → freeProP p d),
    (d : ℕ∞) = dRank G ∧ IsProPPresentation p d π rels ∧ (m : ℕ∞) = k}

end Workspace.Types.ProPPresentationRank

/-!
# Cyclotomic fields, Dirichlet characters and cut-out fields

Concrete model (inside `ℂ`) of cyclotomic fields together with the canonical
Galois-to-units isomorphism, the subfield cut out by a Dirichlet character, the
cyclic cubic subfield of `ℚ(ζ_r)` for `r ≡ 1 (mod 3)`, and the character group
of an abelian subfield of `ℂ`.

All the number fields are realised as `IntermediateField ℚ ℂ`, so that composita
of the fields for different moduli make sense inside the fixed ambient field `ℂ`.
-/

open Complex IsCyclotomicExtension

namespace Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 400000

/-- For `m : ℕ+`, the natural-number underlying value is nonzero. -/
instance instNeZeroPNatVal (m : ℕ+) : NeZero (m : ℕ) := ⟨m.pos.ne'⟩

/-- The chosen primitive `m`-th root of unity `exp (2πi/m)` inside `ℂ`. -/
noncomputable def zetaC (m : ℕ+) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I / (m : ℕ))

/-- `zetaC m` is a primitive `m`-th root of unity. -/
theorem isPrimitiveRoot_zetaC (m : ℕ+) : IsPrimitiveRoot (zetaC m) (m : ℕ) :=
  Complex.isPrimitiveRoot_exp (m : ℕ) m.pos.ne'

/-- The `m`-th cyclotomic field, realised concretely as the subfield of `ℂ`
generated over `ℚ` by the primitive root of unity `zetaC m = exp (2πi/m)`. -/
noncomputable def cyclotomicField' (m : ℕ+) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {zetaC m}

/-- `cyclotomicField' m` really is an `m`-th cyclotomic extension of `ℚ`. -/
noncomputable instance instIsCyclotomic (m : ℕ+) :
    IsCyclotomicExtension {(m : ℕ)} ℚ (cyclotomicField' m) := by
  have hζ : IsPrimitiveRoot (zetaC m) (m : ℕ) := isPrimitiveRoot_zetaC m
  have halg : IsAlgebraic ℚ (zetaC m) := ((hζ.isIntegral m.pos).tower_top).isAlgebraic
  change IsCyclotomicExtension {(m : ℕ)} ℚ (cyclotomicField' m).toSubalgebra
  rw [cyclotomicField', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg]
  exact hζ.adjoin_isCyclotomicExtension ℚ

/-- `cyclotomicField' m` is a number field. -/
noncomputable instance instNumberField (m : ℕ+) :
    NumberField (cyclotomicField' m) :=
  IsCyclotomicExtension.numberField {(m : ℕ)} ℚ (cyclotomicField' m)

/-- `cyclotomicField' m / ℚ` is Galois. -/
noncomputable instance instIsGalois (m : ℕ+) :
    IsGalois ℚ (cyclotomicField' m) :=
  IsCyclotomicExtension.isGalois {(m : ℕ)} ℚ (cyclotomicField' m)

/-- The canonical isomorphism `Gal(ℚ(ζ_m)/ℚ) ≃* (ℤ/mℤ)ˣ` sending `σ` to the class
`a` such that `σ ζ = ζ ^ a`. -/
noncomputable def galToUnits (m : ℕ+) :
    (cyclotomicField' m ≃ₐ[ℚ] cyclotomicField' m) ≃* (ZMod (m : ℕ))ˣ :=
  IsCyclotomicExtension.Rat.galEquivZMod (m : ℕ) (cyclotomicField' m)

/-- The subfield of `ℂ` cut out by a Dirichlet character `χ` of modulus `m`: the
fixed field of the kernel of the composite
`Gal(ℚ(ζ_m)/ℚ) ≃ (ℤ/mℤ)ˣ --χ--> ℂˣ`. -/
noncomputable def cutOutField (m : ℕ+) (chi : DirichletCharacter ℂ (m : ℕ)) :
    IntermediateField ℚ ℂ :=
  IntermediateField.lift
    (IntermediateField.fixedField
      ((chi.toUnitHom.comp (galToUnits m).toMonoidHom).ker))

/-- The unique cyclic cubic subfield of `ℚ(ζ_r)` for a prime `r ≡ 1 (mod 3)`,
defined as the fixed field of the unique index-`3` subgroup of
`Gal(ℚ(ζ_r)/ℚ) ≃ (ℤ/rℤ)ˣ`, namely the subgroup of cubes (its preimage under
`galToUnits`). -/
noncomputable def cyclicCubicSubfield (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) : IntermediateField ℚ ℂ :=
  IntermediateField.lift
    (IntermediateField.fixedField
      (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
        (galToUnits r).toMonoidHom))

end Workspace.Types.CyclotomicCharacterFields

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

/-!
# Minkowski-embedding window setup (Section 2.1)

This file formalises the Minkowski-embedding *window* setup of Section 2.1 of the paper,
relative to a totally real number field `L` of degree `f` and its CM extension
`K = L(i)` (as bundled in `CMAdjoinI` / an `AdmissibleDatum`), together with a positive
integer denominator `DD` (in the paper `DD = D = Q ^ 2`).

Ingredients (definitions only — Lemmas 2.4–2.6 are stated elsewhere against these):

* `EmbeddingSelection L K f` : a choice of one complex embedding `σ_r : K → ℂ` per real
  embedding of `L`; the restrictions `σ_r|_L` form a bijection onto the (all real)
  embeddings of `L` into `ℂ`.
* `minkowskiMap sel : K →+* (Fin f → ℂ)` : the Minkowski map `Φ(x) = (σ_1 x, …, σ_f x)`.
* `lattice sel DD : AddSubgroup (Fin f → ℂ)` : the lattice `Λ = Φ(DD⁻¹ 𝓞_K)`.
* `supNorm z = ‖z‖` : the sup norm `‖z‖_∞ = max_r |z_r|` (the default `Pi` norm).
* `window R` : the polydisc `B_R = {z | ∀ r, |z_r| ≤ R}`.
* `Xset sel DD R a = (a + Λ) ∩ B_R`, `Ncount = |X_a|`, `Ecount U a = #{(x,x') ∈ X_a² | x'-x ∈ U}`.
* `discArea R = π R²`, `overlapArea R` = area of the intersection of two radius-`R` discs at
  centre distance `1`, `rho R = overlapArea R / discArea R`.
-/

open scoped NumberField
open MeasureTheory

namespace Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 400000

/-! ## The embedding selection -/

section EmbeddingSelection

variable (L K : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K]

/-- An **embedding selection** of size `f`: a choice, for each of the `f` real embeddings of
the totally real field `L`, of one complex embedding `σ_r : K → ℂ` of `K` extending it.

The defining property is that the restriction map `r ↦ σ_r|_L` is a *bijection* onto the set
of all embeddings `L → ℂ` (there are exactly `f = [L : ℚ]` of them since `L` is totally real),
and each restriction has real image (`IsReal`, i.e. it is fixed by complex conjugation).  This
captures "one extension chosen per real place of `L`". -/
structure EmbeddingSelection (f : ℕ) where
  /-- The chosen complex embedding of `K` for each `r`. -/
  sigma : Fin f → (K →+* ℂ)
  /-- The restrictions to `L` biject onto the embeddings `L → ℂ`. -/
  restrict_bijective :
    Function.Bijective (fun r : Fin f => (sigma r).comp (algebraMap L K))
  /-- Each restriction to `L` has real image (`L` is totally real). -/
  restrict_isReal :
    ∀ r : Fin f, NumberField.ComplexEmbedding.IsReal ((sigma r).comp (algebraMap L K))

end EmbeddingSelection

/-! ## The Minkowski map and lattice -/

section Maps

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- The **Minkowski map** `Φ : K → ℂ^f`, `Φ(x) = (σ_1 x, …, σ_f x)`, as a ring homomorphism
into the product `Fin f → ℂ`. -/
noncomputable def minkowskiMap (sel : EmbeddingSelection L K f) : K →+* (Fin f → ℂ) :=
  Pi.ringHom sel.sigma

/-- The additive homomorphism `𝓞_K → ℂ^f`, `y ↦ Φ(y / DD)`, whose range is the lattice
`Λ = Φ(DD⁻¹ 𝓞_K)`. -/
noncomputable def latticeHom (sel : EmbeddingSelection L K f) (DD : ℕ) :
    (𝓞 K) →+ (Fin f → ℂ) :=
  (minkowskiMap sel).toAddMonoidHom.comp
    ((AddMonoidHom.mulRight ((DD : K)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom)

/-- The **lattice** `Λ = Φ(DD⁻¹ 𝓞_K)`, the image under the Minkowski map of the fractional
`𝓞_K`-module `DD⁻¹ 𝓞_K = {x : K | ∃ y ∈ 𝓞_K, x = y / DD}`, as an additive subgroup of
`ℂ^f`. -/
noncomputable def lattice (sel : EmbeddingSelection L K f) (DD : ℕ) :
    AddSubgroup (Fin f → ℂ) :=
  (latticeHom sel DD).range

end Maps

/-! ## Sup norm and window -/

section Window

variable {f : ℕ}

/-- The **window** `B_R = {z | ∀ r, |z_r| ≤ R}`, a product of `f` closed discs of radius `R`. -/
def window (R : ℝ) : Set (Fin f → ℂ) := {z | ∀ r, ‖z r‖ ≤ R}

end Window

/-! ## Coset point counts -/

section Counts

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- The point set `X_a = (a + Λ) ∩ B_R` of a coset `a + Λ` intersected with the window. -/
def Xset (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ) (a : Fin f → ℂ) :
    Set (Fin f → ℂ) :=
  {z | z - a ∈ lattice sel DD} ∩ window R

/-- The count `N_a = |X_a|` of lattice-coset points in the window. -/
noncomputable def Ncount (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (a : Fin f → ℂ) : ℕ :=
  (Xset sel DD R a).ncard

/-- The count `E_a(U) = #{(x, x') ∈ X_a × X_a : x' - x ∈ U}` of ordered pairs in `X_a` whose
difference lies in the finite set `U`. -/
noncomputable def Ecount (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ) : ℕ :=
  {p : (Fin f → ℂ) × (Fin f → ℂ) |
      p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.ncard

end Counts

/-! ## Disc-overlap areas -/

section Areas

/-- The area `b(R) = π R²` of a disc of radius `R`. -/
noncomputable def discArea (R : ℝ) : ℝ := Real.pi * R ^ 2

/-- The area `a(R)` of the intersection of two closed discs of radius `R` whose centres are at
distance `1` (via the 2-dimensional Lebesgue/volume measure on `ℂ`). -/
noncomputable def overlapArea (R : ℝ) : ℝ :=
  (volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R)).toReal

/-- The ratio `ρ_R = a(R) / b(R)`. -/
noncomputable def rho (R : ℝ) : ℝ := overlapArea R / discArea R

end Areas

end Workspace.Types.MinkowskiWindow

/-!
# The maximal everywhere-unramified pro-`p` extension `F^{ur,p}` (Definition A.3)

Working inside a fixed algebraic closure `AlgebraicClosure F` of a number field `F`, we single
out the *defining family* of intermediate fields `E` (`F ≤ E ≤ AlgebraicClosure F`) that are

* finite-dimensional over `F`,
* Galois over `F`,
* everywhere unramified over `F` (`SplittingRamification.EverywhereUnramified`),
* with Galois group `Gal(E/F)` a finite `p`-group (`IsPGroup p`).

`maxUnramifiedProPExt p F` is the compositum (supremum in `IntermediateField F (AlgebraicClosure F)`)
of this family. Its Galois group `galUr p F = Gal(F^{ur,p}/F)` carries the Krull topology
(Mathlib's `krullTopology`, an instance, so `Group` and `TopologicalSpace` fire automatically).

The type also provides the fixed-field construction `fixedFieldOf` (used to extract the finite tower
layers `F_j`), the restriction homomorphisms `restrictTo` to finite Galois subextensions, and the
re-exposed Frobenius-representative predicate `IsFrobeniusRepAt` (via `FrobeniusSplitting`, applied
to `Ω = F^{ur,p}`).

That `galUr p F` is pro-`p`, and that its open-normal quotients correspond to the finite
everywhere-unramified `p`-group extensions, are *theorem statements* to be formalized elsewhere;
this file contains definitions only.
-/

set_option maxHeartbeats 400000

open scoped NumberField

namespace Workspace.Types.UnramifiedProPExtension

variable (p : ℕ) (F : Type*) [Field F] [NumberField F]

/-- The defining property of the family: an intermediate field `E` of `AlgebraicClosure F` over `F`
is a **finite Galois everywhere-unramified `p`-group subextension** when it is finite-dimensional
over `F`, Galois over `F`, everywhere unramified over `F`, and has `Gal(E/F)` a `p`-group.

The `NumberField ↥E` instance needed to state everywhere-unramifiedness is derived from finite
dimensionality of `E` over the number field `F`. -/
def IsFiniteUnramifiedProPExt (E : IntermediateField F (AlgebraicClosure F)) : Prop :=
  ∃ hfd : FiniteDimensional F E,
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    IsGalois F E ∧
      Workspace.Types.SplittingRamification.EverywhereUnramified F (E : Type _) ∧
        IsPGroup p (E ≃ₐ[F] E)

/-- The **maximal everywhere-unramified pro-`p` extension** `F^{ur,p}` of `F`: the compositum
(supremum) of all finite Galois everywhere-unramified `p`-group subextensions of
`AlgebraicClosure F` over `F`. -/
noncomputable def maxUnramifiedProPExt : IntermediateField F (AlgebraicClosure F) :=
  sSup {E | IsFiniteUnramifiedProPExt p F E}

/-- The **Galois group** `Gal(F^{ur,p}/F)` of the maximal everywhere-unramified pro-`p` extension.
As an `abbrev` it inherits the `Group` instance (`AlgEquiv.aut`) and the Krull `TopologicalSpace`
instance (`krullTopology`), together with whatever profinite instances Mathlib provides for the
Krull topology on algebraic Galois groups. -/
noncomputable abbrev galUr : Type _ :=
  (maxUnramifiedProPExt p F) ≃ₐ[F] (maxUnramifiedProPExt p F)

/-- The **fixed field** of a subgroup `H` of `galUr p F`, as an intermediate field of `F^{ur,p}/F`.
For an open normal subgroup this is a finite layer `F_H` of the tower, finite Galois over `F`. -/
noncomputable def fixedFieldOf (H : Subgroup (galUr p F)) :
    IntermediateField F (maxUnramifiedProPExt p F) :=
  IntermediateField.fixedField H

/-- A finite prime `q` of `F` has a **Frobenius representative** `σ` in `galUr p F` when `σ` is a
Frobenius representative for the extension `Ω = F^{ur,p}` at `q`, i.e. a compatible system of
Frobenii restricting to a Frobenius element on every finite Galois layer. -/
def IsFrobeniusRepAt (σ : galUr p F) (q : Ideal (𝓞 F)) : Prop :=
  Workspace.Types.FrobeniusSplitting.IsFrobeniusRepAt σ q

end Workspace.Types.UnramifiedProPExtension

open scoped NumberField
open scoped ComplexConjugate
open Polynomial
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

/-- **SublemmaDegKQ.** For an admissible datum `d` with totally real base field `L = d.L`
and CM extension `K = d.K = L(i)`, the degree of `K` over `ℚ` is twice the base-field
degree `f = deg d = dim_ℚ L`, i.e. `Module.finrank ℚ d.K = 2 * deg d`. -/
theorem SublemmaDegKQ (d : AdmissibleDatum) :
    Module.finrank ℚ d.K = 2 * deg d := by
  classical
  -- Abbreviations for the two fields.
  set L := d.L
  set K := d.K
  -- The generator `iota` of `K` over `L` with `iota ^ 2 = -1`.
  set iota := d.h_adjoin.choose with hi
  have hsq : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
  have hadj : IntermediateField.adjoin L {iota} = ⊤ := d.h_adjoin.choose_spec.2
  -- `iota` is integral over `L`, being a root of `X ^ 2 + 1`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota` does not lie in `L`, because `L` is totally real.
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- The minimal polynomial of `iota` over `L` has degree exactly `2`.
  have hdeg2 : (minpoly L iota).natDegree = 2 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hnz : (X ^ 2 + 1 : L[X]) ≠ 0 := by
      intro hz
      have : (X ^ 2 + 1 : L[X]).natDegree = 0 := by rw [hz]; simp
      have h2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    have hle : (minpoly L iota).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd hnz
      have h2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    have hge : 2 ≤ (minpoly L iota).natDegree :=
      (minpoly.two_le_natDegree_iff hint).mpr hne
    omega
  -- Hence `[K : L] = 2`.
  have hKL : Module.finrank L K = 2 := by
    have hadjfr := IntermediateField.adjoin.finrank hint
    rw [hadj, IntermediateField.finrank_top'] at hadjfr
    rw [hadjfr, hdeg2]
  -- Tower law: `[K : ℚ] = [L : ℚ] * [K : L]`.
  have htower := Module.finrank_mul_finrank ℚ L K
  rw [hKL] at htower
  -- Conclude.
  rw [deg, ← htower]
  ring

open Polynomial
open scoped NumberField
open scoped ComplexConjugate

open Workspace.Types.AdmissibleDatum Workspace.Types.CMAdjoinI

/-- **Local split generator.**

For an admissible datum `d` with base field `L = d.L`, CM field `K = d.K`, and
`d.h_adjoin : IsAdjoinI L K` (there is `iota ∈ K` with `iota² = -1` generating `K`
over `L`), there exists an element `ω` of the ring of integers `𝓞 K` whose image in
`K` squares to `-1`, that is integral over `𝓞 L` (under the scalar tower
`𝓞 L ⊆ 𝓞 K`), whose minimal polynomial over `𝓞 L` is `X² + 1`, and whose image in
`K` generates `K` over `L` (the `L`-intermediate field generated by it is `⊤`). Thus
`𝓞 L[ω]` is an order in `𝓞 K` with `[K : L] = 2` realized by the monic integral
generator `ω` with `ω² = -1`. -/
theorem LocalSplitGenerator (d : Workspace.Types.AdmissibleDatum.AdmissibleDatum) :
    ∃ ω : 𝓞 d.K,
      (algebraMap (𝓞 d.K) d.K ω) ^ 2 = -1 ∧
      IsIntegral (𝓞 d.L) ω ∧
      minpoly (𝓞 d.L) ω = X ^ 2 + 1 ∧
      IntermediateField.adjoin d.L {algebraMap (𝓞 d.K) d.K ω} = ⊤ := by
  classical
  obtain ⟨iota, hsq, hadj⟩ := d.h_adjoin
  have hintZ : IsIntegral ℤ iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  set ω : 𝓞 d.K :=
    NumberField.RingOfIntegers.restrict (fun _ : Unit => iota) (fun _ => hintZ) () with hω
  have hcoe : (algebraMap (𝓞 d.K) d.K ω) = iota := rfl
  -- `iota` is integral over `L`, being a root of the monic polynomial `X ^ 2 + 1`.
  have hint : IsIntegral d.L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota ∉ L` because `L` is totally real, so `-1` is not a square in `L`.
  have hne : iota ∉ (algebraMap d.L d.K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap d.L d.K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (d.L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- Hence the minimal polynomial of `iota` over `L` is exactly `X ^ 2 + 1`.
  have hmin : minpoly d.L iota = X ^ 2 + 1 := by
    have hdvd : minpoly d.L iota ∣ (X ^ 2 + 1 : d.L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hmonic : (X ^ 2 + 1 : d.L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : d.L[X]).natDegree ≤ (minpoly d.L iota).natDegree := by
      have h2 : 2 ≤ (minpoly d.L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : d.L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd hdeg).symm
  -- `ω` is integral over `𝓞 L` since it is integral over `ℤ`.
  have hωint : IsIntegral (𝓞 d.L) ω := (NumberField.RingOfIntegers.isIntegral ω).tower_top
  refine ⟨ω, ?_, hωint, ?_, ?_⟩
  · rw [hcoe]; exact hsq
  · -- Transfer `minpoly d.L iota = X² + 1` down to `minpoly (𝓞 L) ω = X² + 1`.
    have hfield :
        minpoly d.L ((algebraMap (𝓞 d.K) d.K) ω) =
          map (algebraMap (𝓞 d.L) d.L) (minpoly (𝓞 d.L) ω) :=
      minpoly.isIntegrallyClosed_eq_field_fractions d.L d.K hωint
    have h1 : map (algebraMap (𝓞 d.L) d.L) (minpoly (𝓞 d.L) ω) = X ^ 2 + 1 := by
      rw [← hfield, hcoe, hmin]
    have hmapinj : Function.Injective (Polynomial.map (algebraMap (𝓞 d.L) d.L)) :=
      Polynomial.map_injective _ (IsFractionRing.injective (𝓞 d.L) d.L)
    apply hmapinj
    rw [h1]
    simp
  · rw [hcoe]; exact hadj

open scoped NumberField
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem LocalSplitResidueFactors
    (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hf : Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) 𝔮 = 1) :
    Nat.card (𝓞 d.L ⧸ 𝔮) = d.q b ∧
    ∃ a : (𝓞 d.L ⧸ 𝔮), a ^ 2 = -1 ∧ a ≠ -a ∧
      (Polynomial.X ^ 2 + 1 : Polynomial (𝓞 d.L ⧸ 𝔮)) =
        (Polynomial.X - Polynomial.C a) * (Polynomial.X + Polynomial.C a) := by
  obtain ⟨hqp, hqlo⟩ := h𝔮
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := hqlo
  have hqb_ne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  have hq_ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  have hprime_int : Prime (d.q b : ℤ) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
  haveI hpP : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast (d.hq_prime b).ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(d.q b : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  -- Establish the module structure BEFORE the Field instance to avoid a diamond
  letI hMod : Module (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) := inferInstance
  haveI hFinF : Finite (𝓞 d.L ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 hq_ne
  haveI hFtF : Fintype (𝓞 d.L ⧸ 𝔮) := Fintype.ofFinite (𝓞 d.L ⧸ 𝔮)
  haveI hFinZ : Finite (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ hqb_ne
  haveI hFtZ : Fintype (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) :=
    Fintype.ofFinite (ℤ ⧸ Ideal.span {(d.q b : ℤ)})
  letI hFieldZ : Field (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) := Ideal.Quotient.field _
  -- finrank = inertiaDeg = 1
  have hfr : Module.finrank (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) = 1 := by
    have h := Ideal.inertiaDeg_algebraMap (Ideal.span {(d.q b : ℤ)}) 𝔮
    rw [hf] at h; exact h.symm
  -- cardinality of the residue field
  have hcard : Fintype.card (𝓞 d.L ⧸ 𝔮)
      = Fintype.card (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) ^
          Module.finrank (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮) :=
    Module.card_eq_pow_finrank
  rw [hfr, pow_one] at hcard
  have hcardZ : Fintype.card (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) = d.q b := by
    haveI : NeZero (d.q b) := ⟨(d.hq_prime b).ne_zero⟩
    rw [Fintype.card_congr (Int.quotientSpanEquivZMod (d.q b : ℤ)).toEquiv, ZMod.card]
    exact Int.natAbs_natCast (d.q b)
  rw [hcardZ] at hcard
  have hcardF : Nat.card (𝓞 d.L ⧸ 𝔮) = d.q b := by
    rw [Nat.card_eq_fintype_card]; exact hcard
  refine ⟨hcardF, ?_⟩
  -- Part (ii): X² + 1 splits into distinct linear factors.
  letI hFieldF : Field (𝓞 d.L ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  -- -1 is a square since card ≡ 1 (mod 4)
  have hsq : IsSquare (-1 : 𝓞 d.L ⧸ 𝔮) := by
    exact (FiniteField.isSquare_neg_one_iff (F := 𝓞 d.L ⧸ 𝔮)).mpr
      (by rw [hcard]; have h4 := d.hq_mod4 b; omega)
  obtain ⟨a, ha⟩ := hsq
  have ha2 : a ^ 2 = -1 := by rw [sq]; exact ha.symm
  -- The residue field has characteristic q_b (odd), hence 2 ≠ 0.
  haveI : Fact (Nat.Prime (d.q b)) := ⟨d.hq_prime b⟩
  have hnonunit : ((d.q b : ℕ) : ℤ) ∈ nonunits ℤ :=
    mem_nonunits_iff.mpr hprime_int.not_unit
  haveI hCharPZ : CharP (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (d.q b) :=
    CharP.quotient ℤ (d.q b) hnonunit
  have hinj : Function.Injective
      (algebraMap (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮)) :=
    RingHom.injective (algebraMap (ℤ ⧸ Ideal.span {(d.q b : ℤ)}) (𝓞 d.L ⧸ 𝔮))
  haveI hCharP : CharP (𝓞 d.L ⧸ 𝔮) (d.q b) := charP_of_injective_algebraMap hinj (d.q b)
  have htwo : ((2 : ℕ) : 𝓞 d.L ⧸ 𝔮) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (𝓞 d.L ⧸ 𝔮) (d.q b) 2] at h
    have h2 := (d.hq_prime b).two_le
    have h4 := d.hq_mod4 b
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have htwo' : (2 : 𝓞 d.L ⧸ 𝔮) ≠ 0 := by exact_mod_cast htwo
  -- factorization identity
  have hCa : (Polynomial.C a) ^ 2 = -1 := by
    rw [← Polynomial.C_pow, ha2, map_neg, map_one]
  refine ⟨a, ha2, ?_, ?_⟩
  · -- a ≠ -a
    intro hcon
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at ha2
    have h2a : (2 : 𝓞 d.L ⧸ 𝔮) * a = 0 := by linear_combination hcon
    rcases mul_eq_zero.mp h2a with h | h
    · exact htwo' h
    · exact ha0 h
  · -- X² + 1 = (X - C a)(X + C a)
    have expand : (Polynomial.X - Polynomial.C a) * (Polynomial.X + Polynomial.C a)
        = Polynomial.X ^ 2 - (Polynomial.C a) ^ 2 := by ring
    rw [expand, hCa, sub_neg_eq_add]

open scoped NumberField
open Polynomial

open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 1000000

/-- **Coprimality of the conductor to a split prime `𝔮` (Local splitting, step 2).**

For an admissible datum `d`, let `ω : 𝓞 d.K` be an integral generator with `ω² = -1` and
minimal polynomial `X² + 1` over `𝓞 d.L` (the conclusion of `LocalSplitGenerator`, taken here
as hypotheses).  Let `b : Fin d.t`, so `q_b = d.q b` is an odd rational prime, and let `𝔮` be a
prime of `𝓞 d.L` lying over `(q_b)`.  Then the conductor `𝔣 = conductor (𝓞 d.L) ω` of the order
`𝓞 d.L[ω] ⊆ 𝓞 d.K` is coprime to `𝔮`: the pullback of `𝔣` to `𝓞 d.L` (its `comap` along the
ring-of-integers algebra map) together with `𝔮` generates the unit ideal.

Mathematically `2 ∈ 𝔣` (the different of `X² + 1` is `(2ω)`, discriminant `-4`), while `2 ∉ 𝔮`
because `𝔮` lies over the odd prime `q_b`; hence `𝔮` cannot contain the conductor pullback and
the two ideals are coprime. -/
theorem LocalSplitConductorCoprime
    (d : AdmissibleDatum)
    (ω : 𝓞 d.K)
    (hω_sq : ω ^ 2 = -1)
    (hω_min : minpoly (𝓞 d.L) ω = X ^ 2 + 1)
    (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L)) :
    (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ⊔ 𝔮 = ⊤ := by
  -- relative-extension instances
  have i3 : IsScalarTower (𝓞 d.L) d.L d.K :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [← IsScalarTower.algebraMap_apply])
  have i4 : IsScalarTower (𝓞 d.L) (𝓞 d.K) d.K :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [← IsScalarTower.algebraMap_apply])
  have i5 : IsIntegralClosure (𝓞 d.K) (𝓞 d.L) d.K :=
    NumberField.RingOfIntegers.instIsIntegralClosure d.L d.K
  have i8 : Module.IsTorsionFree (𝓞 d.L) (𝓞 d.K) := inferInstance
  -- ω as an element of the field d.K
  set ω' : d.K := algebraMap (𝓞 d.K) d.K ω with hω'def
  have hω'sq : ω' ^ 2 = -1 := by
    rw [hω'def, ← map_pow, hω_sq, map_neg, map_one]
  have hω'int : IsIntegral d.L ω' := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hω'sq]
  have hpoly : (aeval ω') (X ^ 2 + 1 : d.L[X]) = 0 := by simp [hω'sq]
  have hωint : IsIntegral (𝓞 d.L) ω := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hω_sq]
  -- minpoly of ω' over d.L is X²+1
  have hmin' : minpoly d.L ω' = X ^ 2 + 1 := by
    have := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 d.L) (S := 𝓞 d.K)
      d.L d.K hωint
    rw [hω'def, this, hω_min]
    simp [Polynomial.map_add, Polynomial.map_pow]
  -- ω' generates d.K over d.L
  obtain ⟨iota, hiota_sq, hiota_adj⟩ := d.h_adjoin
  have hfac : (ω' - iota) * (ω' + iota) = 0 := by
    have h2 : ω' ^ 2 - iota ^ 2 = 0 := by rw [hω'sq, hiota_sq]; ring
    linear_combination h2
  have hxIF : IntermediateField.adjoin d.L {ω'} = ⊤ := by
    rcases mul_eq_zero.mp hfac with h | h
    · have : ω' = iota := by linear_combination h
      rw [this, hiota_adj]
    · have hneg : ω' = -iota := by linear_combination h
      rw [hneg]
      apply top_le_iff.mp
      rw [← hiota_adj]
      apply IntermediateField.adjoin_le_iff.mpr
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      rw [hy]
      have : (-iota) ∈ IntermediateField.adjoin d.L {-iota} :=
        IntermediateField.mem_adjoin_simple_self d.L (-iota)
      simpa using neg_mem this
  have hx : Algebra.adjoin d.L {ω'} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_integral hω'int, hxIF]
    exact IntermediateField.top_toSubalgebra
  -- conductor * different = span {2ω}  (Kummer–Dedekind / different of X²+1)
  have hcond := conductor_mul_differentIdeal (𝓞 d.L) d.L d.K ω hx
  rw [hω_min] at hcond
  have hd : derivative (X ^ 2 + 1 : (𝓞 d.L)[X]) = 2 * X := by
    simp only [derivative_add, derivative_X_pow, derivative_one, add_zero, Nat.cast_ofNat,
      Nat.reduceSub, pow_one, map_ofNat]
  have hderiv : (aeval ω) (derivative (X ^ 2 + 1 : (𝓞 d.L)[X])) = 2 * ω := by
    rw [hd, map_mul, map_ofNat, aeval_X]
  rw [hderiv] at hcond
  -- 2ω ∈ conductor, hence 2 ∈ conductor
  have hspan_le : Ideal.span {2 * ω} ≤ conductor (𝓞 d.L) ω := by
    rw [← hcond]; exact Ideal.mul_le_right
  have h2ω : 2 * ω ∈ conductor (𝓞 d.L) ω :=
    hspan_le (Ideal.mem_span_singleton_self _)
  have h2 : (2 : 𝓞 d.K) ∈ conductor (𝓞 d.L) ω := by
    have hmul := Ideal.mul_mem_left (conductor (𝓞 d.L) ω) (-ω) h2ω
    have heq : (-ω) * (2 * ω) = (2 : 𝓞 d.K) := by linear_combination (-2 : 𝓞 d.K) * hω_sq
    rwa [heq] at hmul
  have h2comap : (2 : 𝓞 d.L) ∈ (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) := by
    rw [Ideal.mem_comap, map_ofNat]; exact h2
  -- 2 ∉ 𝔮 (𝔮 lies over the odd prime q_b)
  have hqdvd : ¬ (d.q b ∣ 2) := by
    intro hdvd
    have heq2 : d.q b = 2 := (Nat.prime_dvd_prime_iff_eq (d.hq_prime b) Nat.prime_two).mp hdvd
    have hm := d.hq_mod4 b
    rw [heq2] at hm; norm_num at hm
  have hinj : Function.Injective (algebraMap ℤ (𝓞 d.L)) := RingHom.injective_int _
  have h2not : (2 : 𝓞 d.L) ∉ 𝔮 := by
    intro hmem
    have h2int : (2 : ℤ) ∈ Ideal.under ℤ 𝔮 := by
      show algebraMap ℤ (𝓞 d.L) (2 : ℤ) ∈ 𝔮
      simpa using hmem
    rw [← h𝔮.2.over, Ideal.mem_span_singleton] at h2int
    have : d.q b ∣ 2 := by exact_mod_cast h2int
    exact hqdvd this
  -- 𝔮 is maximal (nonzero prime in a Dedekind domain)
  have hqne : 𝔮 ≠ ⊥ := by
    rintro rfl
    have hlo : Ideal.span {(d.q b : ℤ)} = ⊥ :=
      (h𝔮.2.over).trans (Ideal.comap_bot_of_injective _ hinj)
    have hq0 : (d.q b : ℤ) = 0 := (Ideal.span_singleton_eq_bot).mp hlo
    have hp := d.hq_prime b
    simp only [Nat.cast_eq_zero] at hq0
    rw [hq0] at hp
    exact Nat.not_prime_zero hp
  have hmax : 𝔮.IsMaximal := (h𝔮.1).isMaximal hqne
  -- combine: 2 ∈ pullback but 2 ∉ 𝔮, and 𝔮 maximal ⇒ sup = ⊤
  by_contra hne
  have hsub : (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ≤ 𝔮 := by
    have heqq := hmax.eq_of_le hne le_sup_right
    rw [heqq]; exact le_sup_left
  exact h2not (hsub h2comap)

open scoped NumberField
open Polynomial UniqueFactorizationMonoid Classical

attribute [local instance] Ideal.Quotient.field

theorem LocalSplitKummerCount
    (d : Workspace.Types.AdmissibleDatum.AdmissibleDatum)
    (b : Fin d.t)
    (ω : 𝓞 d.K)
    (hω_sq : ω ^ 2 = -1)
    (hω_int : IsIntegral (𝓞 d.L) ω)
    (hω_min : minpoly (𝓞 d.L) ω = X ^ 2 + 1)
    (hω_gen : IntermediateField.adjoin d.L {algebraMap (𝓞 d.K) d.K ω} = ⊤)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hcop : (conductor (𝓞 d.L) ω).comap (algebraMap (𝓞 d.L) (𝓞 d.K)) ⊔ 𝔮 = ⊤)
    (hres : ∃ r : (𝓞 d.L) ⧸ 𝔮, r ^ 2 = -1 ∧ r ≠ -r) :
    (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2 ∧
      ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.ramificationIdx 𝔮 𝔓 = 1 := by
  classical
  obtain ⟨h𝔮_prime, h𝔮_lies⟩ := h𝔮
  haveI : 𝔮.IsPrime := h𝔮_prime
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := h𝔮_lies
  -- `(q_b) ≠ ⊥`
  have hqbne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  -- `𝔮 ≠ ⊥`
  have hI' : 𝔮 ≠ ⊥ := by
    intro h
    apply hqbne
    have hover := Ideal.LiesOver.over (p := Ideal.span {(d.q b : ℤ)}) (P := 𝔮)
    rw [h] at hover
    rw [hover]
    exact Ideal.under_bot ℤ (𝓞 d.L)
  -- `𝔮` is maximal
  haveI hImax : 𝔮.IsMaximal := h𝔮_prime.isMaximal hI'
  -- residue field `𝓞 d.L ⧸ 𝔮` is a field via the local instance `Ideal.Quotient.field`
  -- normalized factors of `𝔮 · 𝓞_K` and of `(X²+1) mod 𝔮`
  set MI := normalizedFactors (Ideal.map (algebraMap (𝓞 d.L) (𝓞 d.K)) 𝔮) with hMI_def
  set MP := normalizedFactors (Polynomial.map (Ideal.Quotient.mk 𝔮) (minpoly (𝓞 d.L) ω)) with hMP_def
  obtain ⟨r, hr2, hrne⟩ := hres
  -- `(X²+1) mod 𝔮 = (X - C r)(X - C (-r))`
  have hpoly : Polynomial.map (Ideal.Quotient.mk 𝔮) (minpoly (𝓞 d.L) ω)
      = (X - C r) * (X - C (-r)) := by
    have hpow : (C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ^ 2 = -1 := by
      rw [← map_pow, hr2]; simp
    rw [hω_min]
    have hmap : Polynomial.map (Ideal.Quotient.mk 𝔮) ((X : (𝓞 d.L)[X]) ^ 2 + 1)
        = (X : ((𝓞 d.L) ⧸ 𝔮)[X]) ^ 2 + 1 := by simp
    rw [hmap, map_neg]
    linear_combination hpow
  have hne1 : (X - C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ 0 := (monic_X_sub_C r).ne_zero
  have hne2 : (X - C (-r) : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ 0 := (monic_X_sub_C (-r)).ne_zero
  have hMP_eq : MP = {X - C r} + {X - C (-r)} := by
    rw [hMP_def, hpoly, normalizedFactors_mul hne1 hne2,
        normalizedFactors_irreducible (irreducible_X_sub_C r),
        normalizedFactors_irreducible (irreducible_X_sub_C (-r)),
        (monic_X_sub_C r).normalize_eq_self, (monic_X_sub_C (-r)).normalize_eq_self]
  have hdist : (X - C r : ((𝓞 d.L) ⧸ 𝔮)[X]) ≠ X - C (-r) := by
    intro hh
    rw [sub_right_inj] at hh
    exact hrne (C_inj.mp hh)
  have hMP_nodup : MP.Nodup := by
    rw [hMP_eq]
    simp only [Multiset.singleton_add, Multiset.nodup_cons, Multiset.mem_singleton,
      Multiset.nodup_singleton, and_true]
    exact hdist
  have hMP_card : Multiset.card MP = 2 := by
    rw [hMP_eq]; simp
  -- Kummer–Dedekind bijection: factors of `𝔮·𝓞_K` ↔ factors of `(X²+1) mod 𝔮`
  set e := KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hImax hI' hcop hω_int
    with he_def
  have hMI_eq : MI = Multiset.map (fun f => (↑(e.symm f) : Ideal (𝓞 d.K))) MP.attach :=
    KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map
      hImax hI' hcop hω_int
  have hg_inj : Function.Injective (fun f => (↑(e.symm f) : Ideal (𝓞 d.K))) := by
    intro a b hab
    exact e.symm.injective (Subtype.ext hab)
  have hMI_nodup : MI.Nodup := by
    rw [hMI_eq]
    exact (Multiset.nodup_attach.mpr hMP_nodup).map hg_inj
  have hMI_card : Multiset.card MI = 2 := by
    rw [hMI_eq, Multiset.card_map]
    exact Multiset.card_attach.trans hMP_card
  have hmapne : Ideal.map (algebraMap (𝓞 d.L) (𝓞 d.K)) 𝔮 ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI'
  refine ⟨?_, ?_⟩
  · -- exactly two primes over `𝔮`
    have hset : Ideal.primesOver 𝔮 (𝓞 d.K) = ↑(MI.toFinset) := by
      ext P
      rw [Finset.mem_coe, Multiset.mem_toFinset, hMI_def]
      exact Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hI'
    rw [hset, Set.ncard_coe_finset, Multiset.toFinset_card_of_nodup hMI_nodup]
    exact hMI_card
  · -- each is unramified
    intro P hP
    obtain ⟨hP_prime, hP_lies⟩ := hP
    haveI : P.IsPrime := hP_prime
    haveI : P.LiesOver 𝔮 := hP_lies
    have hPne : P ≠ ⊥ := by
      intro h
      apply hI'
      have hover := Ideal.LiesOver.over (p := 𝔮) (P := P)
      rw [h] at hover
      rw [hover]
      exact Ideal.under_bot (𝓞 d.L) (𝓞 d.K)
    have hPmem : P ∈ MI := by
      rw [hMI_def]
      exact (Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hI').mp ⟨hP_prime, hP_lies⟩
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapne hP_prime hPne,
        ← hMI_def]
    exact Multiset.count_eq_one_of_mem hMI_nodup hPmem

open scoped NumberField

open Workspace.Types.AdmissibleDatum

theorem LocalSplitInertiaFromIdentity
    (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (hcard : (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2)
    (hram : ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.ramificationIdx 𝔮 𝔓 = 1)
    (hdeg : Module.finrank d.L d.K = 2) :
    ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K), Ideal.inertiaDeg 𝔮 𝔓 = 1 := by
  -- Basic finiteness / integral-closure instances for 𝓞 L ⊆ 𝓞 K
  have hFin : FiniteDimensional d.L d.K := inferInstance
  haveI : Module.Finite (𝓞 d.L) (𝓞 d.K) :=
    IsIntegralClosure.finite (𝓞 d.L) d.L d.K (𝓞 d.K)
  -- Unpack that 𝔮 is prime and lies over (q_b)
  obtain ⟨hqp, hqlo⟩ := h𝔮
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(d.q b : ℤ)}) := hqlo
  -- (q_b) ≠ ⊥
  have hqb_ne : (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (d.hq_prime b).ne_zero
  -- 𝔮 ≠ ⊥
  have hq_ne : 𝔮 ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  -- The fundamental identity ∑ e·f = [K:L] = 2
  have hsum := Ideal.sum_ramification_inertia (𝓞 d.K) d.L d.K hq_ne
  rw [hdeg] at hsum
  -- Name the finite set of primes over 𝔮 and bridge to the `primesOver` set
  set F := IsDedekindDomain.primesOverFinset 𝔮 (𝓞 d.K) with hF
  have hcoe : (↑F : Set (Ideal (𝓞 d.K))) = 𝔮.primesOver (𝓞 d.K) :=
    IsDedekindDomain.coe_primesOverFinset hq_ne (𝓞 d.K)
  have hmem : ∀ P, P ∈ F ↔ P ∈ 𝔮.primesOver (𝓞 d.K) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  -- The cardinality of `F` is 2
  have hFcard : F.card = 2 := by
    have h2 : (↑F : Set (Ideal (𝓞 d.K))).ncard = 2 := by rw [hcoe]; exact hcard
    rwa [Set.ncard_coe_finset] at h2
  -- Each ramification index is 1, so the sum reduces to ∑ f = 2
  have hsum2 : ∑ P ∈ F, 𝔮.inertiaDeg P = 2 := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro P hP
    rw [hram P ((hmem P).mp hP), one_mul]
  -- Each residue degree is ≥ 1
  have hpos : ∀ P ∈ F, (1 : ℕ) ≤ 𝔮.inertiaDeg P := by
    intro P hP
    obtain ⟨hPp, hPlo⟩ := (hmem P).mp hP
    haveI : P.IsPrime := hPp
    haveI : P.LiesOver 𝔮 := hPlo
    have := Ideal.inertiaDeg_pos 𝔮 P
    omega
  -- Two terms, each ≥ 1, summing to 2 ⇒ each = 1
  have hall : ∀ P ∈ F, (1 : ℕ) = 𝔮.inertiaDeg P := by
    have hsumeq : ∑ _P ∈ F, (1 : ℕ) = ∑ P ∈ F, 𝔮.inertiaDeg P := by
      rw [Finset.sum_const, smul_eq_mul, mul_one, hFcard, hsum2]
    exact (Finset.sum_eq_sum_iff_of_le hpos).mp hsumeq
  intro 𝔓 h𝔓
  exact (hall 𝔓 ((hmem 𝔓).mpr h𝔓)).symm

open scoped NumberField

open Polynomial

open Workspace.Types.AdmissibleDatum Workspace.Types.CMAdjoinI Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaLocalSplitAtQ (d : AdmissibleDatum) (b : Fin d.t)
    (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L)) :
    (Ideal.primesOver 𝔮 (𝓞 d.K)).ncard = 2 ∧
      ∀ 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K),
        Ideal.ramificationIdx 𝔮 𝔓 = 1 ∧ Ideal.inertiaDeg 𝔮 𝔓 = 1 := by
  -- (2) inertiaDeg over ℚ = 1 from q_b splitting completely in L
  have hf : Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) 𝔮 = 1 :=
    ((d.hq_split b).2.2 𝔮 h𝔮).2
  -- (3) residue factorization
  obtain ⟨hcard_res, r, hr_sq, hr_ne, hr_factor⟩ := LocalSplitResidueFactors d b 𝔮 h𝔮 hf
  -- (1) generator ω
  obtain ⟨ω, hω_algsq, hω_int, hω_min, hω_gen⟩ := LocalSplitGenerator d
  have hω_sq : ω ^ 2 = -1 := by
    apply IsFractionRing.injective (𝓞 d.K) d.K
    rw [map_pow, map_neg, map_one]; exact hω_algsq
  -- (4) conductor coprime
  have hcop := LocalSplitConductorCoprime d ω hω_sq hω_min b 𝔮 h𝔮
  -- (5) count of primes over 𝔮 and ramification indices
  obtain ⟨hncard, hram⟩ :=
    LocalSplitKummerCount d b ω hω_sq hω_int hω_min hω_gen 𝔮 h𝔮 hcop ⟨r, hr_sq, hr_ne⟩
  -- degree [K : L] = 2
  have hdeg : Module.finrank d.L d.K = 2 := by
    set ω' := algebraMap (𝓞 d.K) d.K ω with hω'def
    have hω'sq : ω' ^ 2 = -1 := by rw [hω'def, ← map_pow, hω_sq, map_neg, map_one]
    have hω'int : IsIntegral d.L ω' := ⟨X ^ 2 + 1, by monicity!, by simp [hω'sq]⟩
    have hmin' : minpoly d.L ω' = X ^ 2 + 1 := by
      have hh := minpoly.isIntegrallyClosed_eq_field_fractions (R := 𝓞 d.L) (S := 𝓞 d.K)
        d.L d.K hω_int
      rw [hω'def, hh, hω_min]
      simp [Polynomial.map_add, Polynomial.map_pow]
    have h1 := IntermediateField.adjoin.finrank hω'int
    rw [hmin', hω_gen, IntermediateField.finrank_top'] at h1
    rw [h1]
    compute_degree!
  -- (6) inertiaDeg = 1
  have hinertia := LocalSplitInertiaFromIdentity d b 𝔮 h𝔮 hncard hram hdeg
  exact ⟨hncard, fun 𝔓 h𝔓 => ⟨hram 𝔓 h𝔓, hinertia 𝔓 h𝔓⟩⟩

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.SplittingRamification

theorem SublemmaDisjointCount (d : AdmissibleDatum)
    (hcount : ∀ b, (Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
      = 2 * deg d) :
    (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
      = 2 * d.t * deg d := by
  set S : Fin d.t → Set (Ideal (𝓞 d.K)) :=
    fun b => Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) with hS
  -- degree of L is positive
  have hdeg : 0 < deg d := by
    have h := Module.finrank_pos (R := ℚ) (M := d.L)
    simpa [deg] using h
  -- each block is finite (its ncard is nonzero)
  have hne : ∀ b, (S b).ncard ≠ 0 := by
    intro b
    rw [hcount b]
    omega
  have hfin : ∀ b, (S b).Finite := fun b => Set.finite_of_ncard_ne_zero (hne b)
  -- the blocks are pairwise disjoint
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro b b' hbb'
    simp only [Function.onFun]
    rw [Set.disjoint_left]
    intro P hP hP'
    rw [hS] at hP hP'
    simp only [Ideal.primesOver, Set.mem_setOf_eq] at hP hP'
    have hlies : P.LiesOver (Ideal.span {(d.q b : ℤ)}) := hP.2
    have hlies' : P.LiesOver (Ideal.span {(d.q b' : ℤ)}) := hP'.2
    have heq : Ideal.span {(d.q b : ℤ)} = Ideal.span {(d.q b' : ℤ)} :=
      hlies.over.trans hlies'.over.symm
    rw [Ideal.span_singleton_eq_span_singleton, Int.associated_iff_natAbs] at heq
    simp only [Int.natAbs_natCast] at heq
    exact hbb' (d.hq_distinct heq)
  rw [Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]
  have hcount' : ∀ i, (S i).ncard = 2 * deg d := hcount
  simp only [hcount', Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.SplittingRamification
open Workspace.Types.CMAdjoinI

theorem Fact215ConjugatePrimePairs (d : AdmissibleDatum) :
    (∀ b, SplitsCompletelyRat (d.q b) d.K) ∧
      (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard
        = 2 * d.t * deg d := by
  -- scalar tower ℤ → 𝓞 L → 𝓞 K (any two ℤ-algebras with a compatible map form a tower)
  haveI htower : IsScalarTower ℤ (𝓞 d.L) (𝓞 d.K) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  -- degree identity [K:ℚ] = 2·deg d
  have hdeg : Module.finrank ℚ d.K = 2 * deg d := SublemmaDegKQ d
  -- Claim 1: each rational prime q_b splits completely in K.
  have hsplit : ∀ b, SplitsCompletelyRat (d.q b) d.K := by
    intro b
    -- span (q_b) in ℤ is a nonzero maximal ideal
    have hqZprime : Prime ((d.q b : ℤ)) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
    have hqZne : ((d.q b : ℤ)) ≠ 0 := hqZprime.ne_zero
    have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
    have hspan_prime : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
      (Ideal.span_singleton_prime hqZne).mpr hqZprime
    haveI hspan_max : (Ideal.span {(d.q b : ℤ)}).IsMaximal :=
      hspan_prime.isMaximal hspan_ne
    -- L-level complete splitting data
    obtain ⟨hqL_prime, hqL_count, hqL_ef⟩ := d.hq_split b
    -- Ramification/residue over q_b in K: each prime P over q_b has e = f = 1 (tower assembly)
    have hef : ∀ P ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
        Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) P = 1 ∧
          Ideal.inertiaDeg (Ideal.span {(d.q b : ℤ)}) P = 1 := by
      intro P hP
      obtain ⟨hPp, hPo⟩ := hP
      haveI := hPp
      haveI := hPo
      -- the prime 𝔮 = P ∩ 𝓞_L below P, a prime of 𝓞_L over q_b
      have h𝔮mem : P.under (𝓞 d.L) ∈
          Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L) :=
        ⟨inferInstance, inferInstance⟩
      obtain ⟨he_q, hf_q⟩ := hqL_ef _ h𝔮mem
      obtain ⟨_, hloc_ef⟩ := SublemmaLocalSplitAtQ d b (P.under (𝓞 d.L)) h𝔮mem
      have hPmem : P ∈ Ideal.primesOver (P.under (𝓞 d.L)) (𝓞 d.K) :=
        ⟨inferInstance, inferInstance⟩
      obtain ⟨he_P, hf_P⟩ := hloc_ef P hPmem
      -- 𝔮 is a nonzero prime of the Dedekind domain 𝓞_L, hence maximal
      haveI h𝔮max : (P.under (𝓞 d.L)).IsMaximal :=
        (h𝔮mem.1).isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne _)
      refine ⟨?_, ?_⟩
      · -- e(q_b, P) = e(q_b, 𝔮) · e(𝔮, P) = 1·1
        rw [Ideal.ramificationIdx_algebra_tower' (Ideal.span {(d.q b : ℤ)})
          (P.under (𝓞 d.L)) P, he_q, he_P]
      · -- f(q_b, P) = f(q_b, 𝔮) · f(𝔮, P) = 1·1
        rw [Ideal.inertiaDeg_algebra_tower (Ideal.span {(d.q b : ℤ)})
          (P.under (𝓞 d.L)) P, hf_q, hf_P]
    -- assemble SplitsCompletelyRat: prime, count, ramification
    refine ⟨d.hq_prime b, ?_, hef⟩
    -- Count: #primesOver(q_b, K) = [K:ℚ] via the fundamental identity ∑ e·f = [K:ℚ]
    rw [← IsDedekindDomain.coe_primesOverFinset hspan_ne (𝓞 d.K), Set.ncard_coe_finset,
      ← Ideal.sum_ramification_inertia (𝓞 d.K) ℚ d.K hspan_ne, Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun P hP => ?_
    have hPmem : P ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) := by
      rw [← IsDedekindDomain.coe_primesOverFinset hspan_ne (𝓞 d.K)]
      exact Finset.mem_coe.mpr hP
    obtain ⟨he, hf⟩ := hef P hPmem
    rw [he, hf]
  -- Assemble the conjunction.
  refine ⟨hsplit, ?_⟩
  -- Count over all b: reduce to the disjoint-union sublemma via per-block counts.
  refine SublemmaDisjointCount d ?_
  intro b
  exact (hsplit b).2.1.trans hdeg

set_option maxHeartbeats 800000

theorem ResidueMapSurjectiveOfInertiaDegOne {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S] [Algebra R S] (p : Ideal R) (P : Ideal S)
    [p.IsMaximal] [P.IsMaximal] [P.LiesOver p] (h : Ideal.inertiaDeg p P = 1) :
    Function.Surjective ((Ideal.Quotient.mk P).comp (algebraMap R S)) := by
  letI hFp : Field (R ⧸ p) := Ideal.Quotient.field p
  letI hFP : Field (S ⧸ P) := Ideal.Quotient.field P
  haveI : Module.Free (R ⧸ p) (S ⧸ P) := Module.Free.of_divisionRing _ _
  have hfr : Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_algebraMap p P]; exact h
  have hbij : Function.Bijective (algebraMap (R ⧸ p) (S ⧸ P)) :=
    Module.Free.bijective_algebraMap_of_finrank_eq_one hfr
  intro z
  obtain ⟨y, hy⟩ := hbij.2 z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨r, ?_⟩
  rw [RingHom.comp_apply, ← Ideal.Quotient.algebraMap_mk_of_liesOver P p r, hy]

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 800000

theorem ConjAutSwapPrimeOverQ (d : AdmissibleDatum) (b : Fin d.t) (𝔮 : Ideal (𝓞 d.L))
    (h𝔮 : 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L))
    (𝔓 : Ideal (𝓞 d.K)) (h𝔓 : 𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K)) :
    Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) 𝔓
        ∈ Ideal.primesOver 𝔮 (𝓞 d.K) ∧
      Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) 𝔓 ≠ 𝔓 := by
  obtain ⟨h𝔓p, h𝔓o⟩ := h𝔓
  haveI := h𝔓p
  haveI := h𝔓o
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'def
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Ideal.map_isPrime_of_equiv c'
  · exact Ideal.map_equiv_liesOver 𝔓 𝔮 c'
  · intro hcontra
    -- 𝔮 is maximal (nonzero prime of Dedekind 𝓞_L)
    obtain ⟨h𝔮p, h𝔮o⟩ := h𝔮
    haveI := h𝔮p
    haveI := h𝔮o
    have hqZne : ((d.q b : ℤ)) ≠ 0 := by
      exact_mod_cast (d.hq_prime b).ne_zero
    have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
    haveI h𝔮max : 𝔮.IsMaximal := h𝔮p.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne 𝔮)
    -- conjAut negates every square root of -1
    set iota := d.h_adjoin.choose with hiota
    have hsqι : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
    have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := d.h_adjoin.choose_spec.2
    have hint : IsIntegral d.L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsqι]⟩
    have hci : conjAut d.h_adjoin iota = -iota := by
      have hgen : ((IntermediateField.equivOfEq hadjι).trans
          IntermediateField.topEquiv).symm iota
          = IntermediateField.AdjoinSimple.gen d.L iota := by
        apply Subtype.ext; simp [IntermediateField.AdjoinSimple.gen]
      unfold conjAut
      simp only [AlgEquiv.ofBijective_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe]
      erw [hgen, IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
    have hL5 : ∀ j : d.K, j ^ 2 = -1 → conjAut d.h_adjoin j = -j := by
      intro j hj
      have hfactor : (j - iota) * (j + iota) = 0 := by linear_combination hj - hsqι
      rcases mul_eq_zero.mp hfactor with hh | hh
      · have : j = iota := by linear_combination hh
        rw [this, hci]
      · have : j = -iota := by linear_combination hh
        rw [this, map_neg, hci, neg_neg]
    -- generator ω of 𝓞_K with ω² = -1 and c'(ω) = -ω
    obtain ⟨ω, hω_algsq, hω_int, hω_min, hω_gen⟩ := LocalSplitGenerator d
    have hcoinj : Function.Injective (algebraMap (𝓞 d.K) d.K) :=
      IsFractionRing.injective (𝓞 d.K) d.K
    have hω_sq : ω ^ 2 = -1 := by
      apply hcoinj; rw [map_pow, map_neg, map_one]; exact hω_algsq
    have hc'ω : c' ω = -ω := by
      apply hcoinj
      rw [map_neg, hc'def]
      have hcomm : algebraMap (𝓞 d.K) d.K (NumberField.RingOfIntegers.mapAlgEquiv
          (conjAut d.h_adjoin) ω) = conjAut d.h_adjoin (algebraMap (𝓞 d.K) d.K ω) := rfl
      rw [hcomm]
      exact hL5 (algebraMap (𝓞 d.K) d.K ω) hω_algsq
    -- residue field 𝓞_K/𝔓 = 𝓞_L/𝔮 (inertiaDeg = 1) ⇒ ω ≡ (an 𝓞_L element) mod 𝔓
    obtain ⟨_hram, hinertia⟩ := (SublemmaLocalSplitAtQ d b 𝔮 ⟨h𝔮p, h𝔮o⟩).2 𝔓 ⟨h𝔓p, h𝔓o⟩
    have h𝔮ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan_ne 𝔮
    haveI h𝔓max : 𝔓.IsMaximal :=
      h𝔓p.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot h𝔮ne 𝔓)
    -- residue map 𝓞_L → 𝓞_K/𝔓 is surjective (inertiaDeg = 1): the residue extension is degree 1
    have hsurj : Function.Surjective
        ((Ideal.Quotient.mk 𝔓).comp (algebraMap (𝓞 d.L) (𝓞 d.K))) :=
      ResidueMapSurjectiveOfInertiaDegOne 𝔮 𝔓 hinertia
    obtain ⟨l, hw⟩ := hsurj (Ideal.Quotient.mk 𝔓 ω)
    have hmem1 : ω - algebraMap (𝓞 d.L) (𝓞 d.K) l ∈ 𝔓 := by
      rw [RingHom.comp_apply] at hw
      have hd := Ideal.Quotient.eq.mp hw
      have hn := neg_mem hd
      rwa [neg_sub] at hn
    -- c' preserves 𝔓 (from hcontra) and fixes 𝓞_L
    have hc'mem : ∀ x ∈ 𝔓, c' x ∈ 𝔓 := by
      intro x hx
      have := Ideal.mem_map_of_mem c' hx
      rwa [hcontra] at this
    have hc'l : c' (algebraMap (𝓞 d.L) (𝓞 d.K) l) = algebraMap (𝓞 d.L) (𝓞 d.K) l :=
      c'.commutes l
    have hmem2 : (-ω) - algebraMap (𝓞 d.L) (𝓞 d.K) l ∈ 𝔓 := by
      have := hc'mem _ hmem1
      rwa [map_sub, hc'ω, hc'l] at this
    -- 2ω ∈ 𝔓
    have h2ω : (2 : 𝓞 d.K) * ω ∈ 𝔓 := by
      have hd := Ideal.sub_mem 𝔓 hmem1 hmem2
      have : ω - algebraMap (𝓞 d.L) (𝓞 d.K) l - (-ω - algebraMap (𝓞 d.L) (𝓞 d.K) l)
          = 2 * ω := by ring
      rwa [this] at hd
    -- contradiction: 2ω ∉ 𝔓
    rcases h𝔓p.mem_or_mem h2ω with h2 | hω
    · -- 2 ∈ 𝔓, but 𝔓 lies over q_b (odd) : contradiction
      haveI htower : IsScalarTower ℤ (𝓞 d.L) (𝓞 d.K) :=
        IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
      haveI : 𝔓.LiesOver (Ideal.span {(d.q b : ℤ)}) := Ideal.LiesOver.trans 𝔓 𝔮 _
      have h2Z : (2 : ℤ) ∈ Ideal.span {(d.q b : ℤ)} := by
        have hcomap : (2 : ℤ) ∈ 𝔓.under ℤ := by
          rw [Ideal.mem_comap]
          have : (algebraMap ℤ (𝓞 d.K)) 2 = (2 : 𝓞 d.K) := by simp
          rw [this]; exact h2
        rwa [← Ideal.LiesOver.over (p := Ideal.span {(d.q b : ℤ)}) (P := 𝔓)] at hcomap
      rw [Ideal.mem_span_singleton] at h2Z
      have : (d.q b : ℤ) ∣ 2 := h2Z
      have hqle : (d.q b : ℕ) ∣ 2 := by exact_mod_cast this
      have := (Nat.prime_dvd_prime_iff_eq (d.hq_prime b) Nat.prime_two).mp hqle
      have hmod := d.hq_mod4 b
      omega
    · -- ω ∈ 𝔓, but ω is a unit (ω² = -1) : contradiction
      have h1 : (-1 : 𝓞 d.K) ∈ 𝔓 := by
        have := Ideal.mul_mem_left 𝔓 ω hω
        rwa [← sq, hω_sq] at this
      have : (1 : 𝓞 d.K) ∈ 𝔓 := by
        have := neg_mem h1; rwa [neg_neg] at this
      exact h𝔓p.ne_top (Ideal.eq_top_of_isUnit_mem 𝔓 this isUnit_one)

open scoped NumberField
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 800000

theorem MultiplicityPrimeOverRationalPrime (d : AdmissibleDatum) (P : Ideal (𝓞 d.K))
    [hPp : P.IsPrime] (hPne : P ≠ ⊥) (b : Fin d.t)
    (hram : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
      Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1) :
    (P.LiesOver (Ideal.span {(d.q b : ℤ)}) →
        multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = 1) ∧
    (¬ P.LiesOver (Ideal.span {(d.q b : ℤ)}) →
        multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = 0) := by
  classical
  have hqZprime : Prime ((d.q b : ℤ)) := Nat.prime_iff_prime_int.mp (d.hq_prime b)
  have hqZne : ((d.q b : ℤ)) ≠ 0 := hqZprime.ne_zero
  have hspan_ne : Ideal.span {(d.q b : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZne
  haveI hspan_prime : (Ideal.span {(d.q b : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime hqZne).mpr hqZprime
  haveI hspan_max : (Ideal.span {(d.q b : ℤ)}).IsMaximal := hspan_prime.isMaximal hspan_ne
  have hinj : Function.Injective (algebraMap ℤ (𝓞 d.K)) := RingHom.injective_int _
  have hspaneq : Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}
      = Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmapne : Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hinj]; exact hspan_ne
  have hbridge : multiplicity P (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)})
      = Multiset.count P (UniqueFactorizationMonoid.normalizedFactors
          (Ideal.map (algebraMap ℤ (𝓞 d.K)) (Ideal.span {(d.q b : ℤ)}))) := by
    rw [hspaneq]
    apply multiplicity_eq_of_emultiplicity_eq_some
    have h := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime hPne hPp).irreducible hmapne
    rwa [normalize_eq] at h
  refine ⟨?_, ?_⟩
  · intro hlies
    rw [hbridge,
      ← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count hmapne hPp hPne]
    exact hram P ⟨hPp, hlies⟩
  · intro hnlies
    rw [hbridge, Multiset.count_eq_zero]
    intro hmem
    apply hnlies
    exact ((Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 d.K) hspan_ne).mpr hmem).2

set_option maxHeartbeats 800000

/-- **Multiplicity is transported by a ring automorphism (property-5 core for `ConjugatePairIndexing`).** -/
theorem MultiplicityTransportConjAut {A : Type*} [CommRing A] {F : Type*}
    [EquivLike F A A] [RingEquivClass F A A] (e : F) (p I : Ideal A) :
    multiplicity (Ideal.map e p) (Ideal.map e I) = multiplicity p I := by
  let g : Ideal A ≃* Ideal A :=
    { toFun := Ideal.map e
      invFun := Ideal.comap e
      left_inv := fun J => Ideal.comap_map_of_bijective e (EquivLike.bijective e)
      right_inv := fun J => Ideal.map_comap_of_surjective e (EquivLike.surjective e) J
      map_mul' := fun J K => Ideal.map_mul e J K }
  exact multiplicity_map_eq g (a := p) (b := I)

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

/-- **Tower step for conjugate-pair indexing.** A prime `𝔓` of `𝓞 K` lying over the rational
prime `q_b` lies over a prime `𝔮 := 𝔓 ∩ 𝓞 L` of `𝓞 L`, which itself lies over `q_b`. -/
theorem PrimeOverQbLiesOverPrimeOverQ (d : AdmissibleDatum) (b : Fin d.t)
    (𝔓 : Ideal (𝓞 d.K)) (h𝔓 : 𝔓 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)) :
    ∃ 𝔮 : Ideal (𝓞 d.L), 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L) ∧
      𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K) := by
  obtain ⟨h𝔓p, h𝔓o⟩ := h𝔓
  haveI := h𝔓p
  haveI := h𝔓o
  set 𝔮 : Ideal (𝓞 d.L) := 𝔓.under (𝓞 d.L) with h𝔮def
  haveI h𝔮p : 𝔮.IsPrime := inferInstance
  haveI h𝔓o' : 𝔓.LiesOver 𝔮 := ⟨rfl⟩
  refine ⟨𝔮, ⟨h𝔮p, ⟨?_⟩⟩, ⟨h𝔓p, h𝔓o'⟩⟩
  show Ideal.span {(d.q b : ℤ)} = 𝔮.under ℤ
  rw [h𝔮def, Ideal.under_under]
  exact h𝔓o.over

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

open Classical in
/-- Enumerate a fixed-point-free involution on a finite set into representative pairs. -/
private theorem pairEnum {α : Type*} [LinearOrder α] (T : Finset α) (c : α → α)
    (hcT : ∀ a ∈ T, c a ∈ T) (hinv : ∀ a ∈ T, c (c a) = a) (hfree : ∀ a ∈ T, c a ≠ a) :
    ∃ (P Pc : Fin (T.card / 2) → α),
      (∀ s, P s ∈ T) ∧ (∀ s, c (P s) = Pc s) ∧ (∀ s, Pc s ≠ P s) ∧
      Function.Injective (Sum.elim P Pc) ∧
      (Finset.univ.image P ∪ Finset.univ.image Pc = T) := by
  set R := T.filter (fun a => a < c a) with hR
  set Q := T.filter (fun a => c a < a) with hQ
  have hcRQ : ∀ a ∈ R, c a ∈ Q := by
    intro a ha
    rw [hR, Finset.mem_filter] at ha
    rw [hQ, Finset.mem_filter]
    refine ⟨hcT a ha.1, ?_⟩
    rw [hinv a ha.1]; exact ha.2
  have hcQR : ∀ a ∈ Q, c a ∈ R := by
    intro a ha
    rw [hQ, Finset.mem_filter] at ha
    rw [hR, Finset.mem_filter]
    refine ⟨hcT a ha.1, ?_⟩
    rw [hinv a ha.1]; exact ha.2
  have hRQcard : R.card = Q.card := by
    apply Finset.card_bij' (fun a _ => c a) (fun a _ => c a) hcRQ hcQR
    · intro a ha; rw [hR, Finset.mem_filter] at ha; exact hinv a ha.1
    · intro a ha; rw [hQ, Finset.mem_filter] at ha; exact hinv a ha.1
  have hRQdisj : Disjoint R Q := by
    rw [Finset.disjoint_filter]
    intro a _ h; exact not_lt.mpr (le_of_lt h)
  have hRQunion : R ∪ Q = T := by
    rw [hR, hQ, ← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro a ha
    rcases lt_trichotomy a (c a) with h | h | h
    · exact Or.inl h
    · exact absurd h.symm (hfree a ha)
    · exact Or.inr h
  have hTcard : T.card = 2 * R.card := by
    rw [← hRQunion, Finset.card_union_of_disjoint hRQdisj, hRQcard]; ring
  have hRcard : R.card = T.card / 2 := by rw [hTcard]; omega
  let e := R.orderIsoOfFin hRcard
  have hmem : ∀ s : Fin (T.card / 2), (e s : α) ∈ T ∧ (e s : α) < c (e s : α) :=
    fun s => Finset.mem_filter.mp (e s).2
  refine ⟨fun s => (e s : α), fun s => c (e s : α), ?_, ?_, ?_, ?_, ?_⟩
  · intro s; exact (hmem s).1
  · intro s; rfl
  · intro s; exact (ne_of_lt (hmem s).2).symm
  · rintro (s | s) (t | t) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
    · exact congrArg Sum.inl (e.injective (Subtype.ext h))
    · exfalso
      have h1 : (e s : α) ∈ R := (e s).2
      have h2 : c (e t : α) ∈ Q := hcRQ _ (e t).2
      rw [← h] at h2
      exact (Finset.disjoint_left.mp hRQdisj h1) h2
    · exfalso
      have h1 : (e t : α) ∈ R := (e t).2
      have h2 : c (e s : α) ∈ Q := hcRQ _ (e s).2
      rw [h] at h2
      exact (Finset.disjoint_left.mp hRQdisj h1) h2
    · have hi := congrArg c h
      rw [hinv _ (hmem s).1, hinv _ (hmem t).1] at hi
      exact congrArg Sum.inr (e.injective (Subtype.ext hi))
  · ext x
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨s, hs⟩ | ⟨s, hs⟩)
      · rw [← hs]; exact (hmem s).1
      · rw [← hs]; exact (Finset.mem_filter.mp (hcRQ _ (e s).2)).1
    · intro hxT
      rw [← hRQunion, Finset.mem_union] at hxT
      rcases hxT with hxR | hxQ
      · exact Or.inl ⟨e.symm ⟨x, hxR⟩, by rw [e.apply_symm_apply]⟩
      · refine Or.inr ⟨e.symm ⟨c x, hcQR x hxQ⟩, ?_⟩
        rw [e.apply_symm_apply]
        exact hinv x (Finset.mem_filter.mp hxQ).1

open Polynomial in
/-- `conjAut` induces an involution on ideals of `𝓞 K`. -/
private theorem conjIdealInvol (d : AdmissibleDatum) (I : Ideal (𝓞 d.K)) :
    Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin))
      (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I) = I := by
  set h := d.h_adjoin
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := h.choose_spec.2
  have hint : IsIntegral d.L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsqι]⟩
  have halg : IsAlgebraic d.L iota := hint.isAlgebraic
  have hcι2 : (conjAut h iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
  have hcases : conjAut h iota = iota ∨ conjAut h iota = -iota := by
    have hfac : (conjAut h iota - iota) * (conjAut h iota + iota) = 0 := by
      have hz : (conjAut h iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
      linear_combination hz
    rcases mul_eq_zero.mp hfac with hh | hh
    · left; exact sub_eq_zero.mp hh
    · right; linear_combination hh
  have hinvι : conjAut h (conjAut h iota) = iota := by
    rcases hcases with hh | hh
    · rw [hh, hh]
    · rw [hh, map_neg, hh, neg_neg]
  have hadjalg : Algebra.adjoin d.L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  have hinv : ∀ y : d.K, conjAut h (conjAut h y) = y := by
    have hEq : ((conjAut h).toAlgHom.comp (conjAut h).toAlgHom) = AlgHom.id d.L d.K := by
      apply AlgHom.ext_of_adjoin_eq_top hadjalg
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinvι
    intro y
    have := AlgHom.congr_fun hEq y
    simpa using this
  -- lift to 𝓞 K then to ideals
  have hnat : ∀ y : 𝓞 d.K, algebraMap (𝓞 d.K) d.K
      (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) y)
        = conjAut h (algebraMap (𝓞 d.K) d.K y) := by
    intro y
    simp [NumberField.RingOfIntegers.mapAlgEquiv, NumberField.RingOfIntegers.mapAlgHom]
  have hOinv : ∀ x : 𝓞 d.K,
      NumberField.RingOfIntegers.mapAlgEquiv (conjAut h)
        (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) x) = x := by
    intro x
    refine IsFractionRing.injective (𝓞 d.K) d.K ?_
    rw [hnat, hnat, hinv]
  show Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K)
      (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K) I) = I
  rw [Ideal.map_map]
  have hcomp : ((NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K).comp
      (NumberField.RingOfIntegers.mapAlgEquiv (conjAut h) : 𝓞 d.K →+* 𝓞 d.K)) = RingHom.id _ := by
    ext x; simpa using hOinv x
  rw [hcomp, Ideal.map_id]

/-- **Conjugate-pair indexing (Step 0 of Prop 2.2).** -/
theorem ConjugatePairIndexing (d : AdmissibleDatum)
    (hfact : (∀ b, SplitsCompletelyRat (d.q b) d.K) ∧
      (⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)).ncard = 2 * d.t * deg d) :
    ∃ (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
      (bidx : Fin (d.t * deg d) → Fin d.t)
      (S : Finset (Ideal (𝓞 d.K))),
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective
        (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      ((↑S : Set (Ideal (𝓞 d.K))) =
          ⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)) ∧
      S.card = 2 * (d.t * deg d) ∧
      (S = (Finset.univ.image (fun s => (P s).asIdeal)) ∪
           (Finset.univ.image (fun s => (Pc s).asIdeal))) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I) := by
  classical
  obtain ⟨hsplit, hcardU⟩ := hfact
  set φ := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hφdef
  set c : Ideal (𝓞 d.K) → Ideal (𝓞 d.K) := fun I => Ideal.map φ I with hcdef
  -- maximality of (q_b)
  have hmax : ∀ b : Fin d.t, (Ideal.span {(d.q b : ℤ)}).IsMaximal := by
    intro b
    exact PrincipalIdealRing.isMaximal_of_irreducible
      (Nat.prime_iff_prime_int.mp (d.hq_prime b)).irreducible
  -- nonzero
  have hqne : ∀ b : Fin d.t, (Ideal.span {(d.q b : ℤ)}) ≠ ⊥ := by
    intro b hbot
    rw [Ideal.span_singleton_eq_bot] at hbot
    exact (d.hq_prime b).ne_zero (by exact_mod_cast hbot)
  -- finiteness of the union
  set U : Set (Ideal (𝓞 d.K)) :=
    ⋃ b, Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) with hUdef
  have hUfin : U.Finite := by
    rw [hUdef]
    apply Set.finite_iUnion
    intro b
    haveI := hmax b
    exact primesOver_finite (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)
  set T := hUfin.toFinset with hTdef
  -- membership characterization
  have hTmem : ∀ a : Ideal (𝓞 d.K), a ∈ T ↔
      ∃ b : Fin d.t, a ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K) := by
    intro a
    rw [hTdef, Set.Finite.mem_toFinset, hUdef, Set.mem_iUnion]
  -- T card
  have hTcard : T.card = 2 * (d.t * deg d) := by
    have h1 : T.card = U.ncard := by
      rw [hTdef, Set.ncard_eq_toFinset_card']
      congr 1
      exact (Set.Finite.toFinset_eq_toFinset hUfin).symm ▸ rfl
    rw [h1, hUdef, hcardU]; ring
  -- primality and nonzeroness of members
  have hTprime : ∀ a ∈ T, a.IsPrime := by
    intro a ha; exact ((hTmem a).mp ha).choose_spec.1
  have hTne : ∀ a ∈ T, a ≠ ⊥ := by
    intro a ha
    obtain ⟨b, hbp, hbo⟩ := (hTmem a).mp ha
    intro hbot
    subst hbot
    have : (Ideal.span {(d.q b : ℤ)}) = ⊥ := by
      rw [hbo.over, Ideal.under_bot]
    exact hqne b this
  -- LinearOrder for pairEnum
  letI : LinearOrder (Ideal (𝓞 d.K)) := linearOrderOfSTO WellOrderingRel
  -- involution / stability / freeness
  have hinvT : ∀ a ∈ T, c (c a) = a := by
    intro a _; rw [hcdef]; exact conjIdealInvol d a
  have hcTT : ∀ a ∈ T, c a ∈ T := by
    intro a ha
    obtain ⟨b, hbp, hbo⟩ := (hTmem a).mp ha
    haveI := hbp; haveI := hbo
    rw [hTmem]
    refine ⟨b, ?_, ?_⟩
    · rw [hcdef]; exact Ideal.map_isPrime_of_equiv φ
    · rw [hcdef]
      exact Ideal.map_equiv_liesOver a (Ideal.span {(d.q b : ℤ)}) (φ.restrictScalars ℤ)
  have hfreeT : ∀ a ∈ T, c a ≠ a := by
    intro a ha
    obtain ⟨b, hb⟩ := (hTmem a).mp ha
    obtain ⟨𝔮, h𝔮, h𝔓o⟩ := PrimeOverQbLiesOverPrimeOverQ d b a ⟨hb.1, hb.2⟩
    rw [hcdef]
    exact (ConjAutSwapPrimeOverQ d b 𝔮 h𝔮 a h𝔓o).2
  -- enumerate
  obtain ⟨P₀, Pc₀, hmem₀, hswap₀, hne₀, hinj₀, himg₀⟩ := pairEnum T c hcTT hinvT hfreeT
  have hdiv : T.card / 2 = d.t * deg d := by rw [hTcard]; omega
  let cs : Fin (d.t * deg d) ≃ Fin (T.card / 2) := finCongr hdiv.symm
  have hcsmem : ∀ s, P₀ (cs s) ∈ T := fun s => hmem₀ (cs s)
  -- bidx
  let bidx : Fin (d.t * deg d) → Fin d.t := fun s => ((hTmem (P₀ (cs s))).mp (hcsmem s)).choose
  have hbidx : ∀ s, P₀ (cs s) ∈
      Ideal.primesOver (Ideal.span {(d.q (bidx s) : ℤ)}) (𝓞 d.K) :=
    fun s => ((hTmem (P₀ (cs s))).mp (hcsmem s)).choose_spec
  -- Pc₀ membership
  have hPcmem : ∀ s, Pc₀ (cs s) ∈ T := by
    intro s; rw [← hswap₀ (cs s)]; exact hcTT _ (hcsmem s)
  -- wrap
  let P : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) := fun s =>
    ⟨P₀ (cs s), (hbidx s).1, hTne _ (hcsmem s)⟩
  let Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) := fun s =>
    ⟨Pc₀ (cs s), hTprime _ (hPcmem s), hTne _ (hPcmem s)⟩
  set S : Finset (Ideal (𝓞 d.K)) :=
    (Finset.univ.image (fun s => (P s).asIdeal)) ∪
      (Finset.univ.image (fun s => (Pc s).asIdeal)) with hSdef
  refine ⟨P, Pc, bidx, S, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- property 1: swap
    intro s
    refine ⟨?_, ?_⟩
    · show Ideal.map φ (P₀ (cs s)) = Pc₀ (cs s)
      exact hswap₀ (cs s)
    · exact hne₀ (cs s)
  · -- property 2: injective
    have : (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal))
        = (Sum.elim P₀ Pc₀) ∘ (Sum.map cs cs) := by
      ext (s | s) <;> rfl
    rw [this]
    exact hinj₀.comp (cs.injective.sumMap cs.injective)
  · -- property 3: ramification/multiplicity
    intro s
    have hPo : (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) := (hbidx s).2
    have hPco : (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) := by
      have : (Pc s).asIdeal = c ((P s).asIdeal) := (hswap₀ (cs s)).symm
      rw [this, hcdef]
      haveI := (hbidx s).1
      exact Ideal.map_equiv_liesOver (P₀ (cs s)) (Ideal.span {(d.q (bidx s) : ℤ)})
        (φ.restrictScalars ℤ)
    refine ⟨hPo, hPco, ?_, ?_⟩
    · intro b
      haveI := (P s).isPrime
      have hram_b : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
          Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1 :=
        fun Q hQ => ((hsplit b).2.2 Q hQ).1
      have hM := MultiplicityPrimeOverRationalPrime d (P s).asIdeal (P s).ne_bot b hram_b
      by_cases hb : b = bidx s
      · subst hb
        rw [if_pos rfl]; exact hM.1 hPo
      · rw [if_neg hb]
        apply hM.2
        intro hcon
        apply hb
        have heq : (Ideal.span {(d.q b : ℤ)}) = (Ideal.span {(d.q (bidx s) : ℤ)}) := by
          rw [hcon.over, hPo.over]
        have : (d.q b : ℤ) = (d.q (bidx s) : ℤ) := by
          rcases (Ideal.span_singleton_eq_span_singleton.mp heq) with hu
          rcases Int.associated_iff.mp hu with h | h
          · exact h
          · exfalso
            have := (d.hq_prime b).pos
            have := (d.hq_prime (bidx s)).pos
            omega
        exact d.hq_distinct (by exact_mod_cast this)
    · intro b
      haveI := (Pc s).isPrime
      have hram_b : ∀ Q ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K),
          Ideal.ramificationIdx (Ideal.span {(d.q b : ℤ)}) Q = 1 :=
        fun Q hQ => ((hsplit b).2.2 Q hQ).1
      have hM := MultiplicityPrimeOverRationalPrime d (Pc s).asIdeal (Pc s).ne_bot b hram_b
      by_cases hb : b = bidx s
      · subst hb
        rw [if_pos rfl]; exact hM.1 hPco
      · rw [if_neg hb]
        apply hM.2
        intro hcon
        apply hb
        have heq : (Ideal.span {(d.q b : ℤ)}) = (Ideal.span {(d.q (bidx s) : ℤ)}) := by
          rw [hcon.over, hPco.over]
        have : (d.q b : ℤ) = (d.q (bidx s) : ℤ) := by
          rcases Int.associated_iff.mp (Ideal.span_singleton_eq_span_singleton.mp heq) with h | h
          · exact h
          · exfalso
            have := (d.hq_prime b).pos
            have := (d.hq_prime (bidx s)).pos
            omega
        exact d.hq_distinct (by exact_mod_cast this)
  · -- property 4a: S as set = union
    have hST : S = T := by
      apply Finset.coe_injective
      have hcoeT : (↑T : Set (Ideal (𝓞 d.K))) = Set.range P₀ ∪ Set.range Pc₀ := by
        have hh := congrArg Finset.toSet himg₀
        simpa only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
          using hh.symm
      rw [hSdef, hcoeT]
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have hrP : Set.range (fun s => (P s).asIdeal) = Set.range P₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      have hrPc : Set.range (fun s => (Pc s).asIdeal) = Set.range Pc₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      rw [hrP, hrPc]
    rw [hST, hTdef, Set.Finite.coe_toFinset]
  · -- property 4b: S.card
    have hST : S = T := by
      apply Finset.coe_injective
      have hcoeT : (↑T : Set (Ideal (𝓞 d.K))) = Set.range P₀ ∪ Set.range Pc₀ := by
        have hh := congrArg Finset.toSet himg₀
        simpa only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
          using hh.symm
      rw [hSdef, hcoeT]
      simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ]
      have hrP : Set.range (fun s => (P s).asIdeal) = Set.range P₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      have hrPc : Set.range (fun s => (Pc s).asIdeal) = Set.range Pc₀ := by
        ext y; constructor
        · rintro ⟨s, rfl⟩; exact ⟨cs s, rfl⟩
        · rintro ⟨s, rfl⟩; exact ⟨cs.symm s, by exact congrArg _ (cs.apply_symm_apply s)⟩
      rw [hrP, hrPc]
    rw [hST]; exact hTcard
  · -- property 6: S = image ∪ image
    rfl
  · -- property 5: valuation transport
    intro I s
    constructor
    · have hmap : Ideal.map φ (Pc s).asIdeal = (P s).asIdeal := by
        show Ideal.map φ (Pc₀ (cs s)) = P₀ (cs s)
        rw [← hswap₀ (cs s)]; exact conjIdealInvol d (P₀ (cs s))
      have := MultiplicityTransportConjAut φ (Pc s).asIdeal I
      rw [hmap] at this
      exact this
    · have hmap : Ideal.map φ (P s).asIdeal = (Pc s).asIdeal := hswap₀ (cs s)
      have := MultiplicityTransportConjAut φ (P s).asIdeal I
      rw [hmap] at this
      exact this

open scoped Classical

/-- Abstract fiber pigeonhole (Step 1 of Prop 2.2).

Given nonempty finite types `D` and `C` and any function `Φ : D → C`, there is an
element `η ∈ D` whose fiber `{x | Φ x = Φ η}` has cardinality `|F|` satisfying
`|F| · |C| ≥ |D|`, equivalently `(|F| : ℝ) ≥ |D| / |C|`. -/
theorem IdealClassPigeonholeFiber
    {D C : Type*} [Fintype D] [Fintype C] [Nonempty D] [Nonempty C]
    (Φ : D → C) :
    ∃ η : D,
      Fintype.card {x : D // Φ x = Φ η} * Fintype.card C ≥ Fintype.card D ∧
      (Fintype.card D : ℝ) / (Fintype.card C : ℝ)
        ≤ (Fintype.card {x : D // Φ x = Φ η} : ℝ) := by
  classical
  -- fiber size as a function of the target value
  set g : C → ℕ := fun c => Fintype.card {x : D // Φ x = c} with hg
  -- pick the target with the maximal fiber
  obtain ⟨c₀, hc₀⟩ := Finite.exists_max g
  -- the fibers partition `D`, so their sizes sum to `|D|`
  have hsum : ∑ c : C, g c = Fintype.card D := by
    have hmaps : Set.MapsTo Φ (Finset.univ : Finset D) (Finset.univ : Finset C) := by
      intro x _; exact Finset.mem_univ _
    have hcard := Finset.card_eq_sum_card_fiberwise hmaps
    rw [Finset.card_univ] at hcard
    rw [hcard]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [hg]
    dsimp only
    rw [Fintype.card_subtype]
  -- max fiber times `|C|` dominates the sum, which is `|D|`
  have hle : Fintype.card D ≤ g c₀ * Fintype.card C := by
    rw [← hsum]
    calc ∑ c : C, g c ≤ ∑ _c : C, g c₀ := Finset.sum_le_sum (fun c _ => hc₀ c)
      _ = g c₀ * Fintype.card C := by rw [Finset.sum_const, Finset.card_univ]; ring
  -- max fiber is nonempty
  have hpos : 0 < g c₀ := by
    rcases Nat.eq_zero_or_pos (g c₀) with h | h
    · rw [h, Nat.zero_mul] at hle
      have := Fintype.card_pos (α := D)
      omega
    · exact h
  have hne : Nonempty {x : D // Φ x = c₀} := by
    rw [← Fintype.card_pos_iff]
    exact hpos
  obtain ⟨η, hη⟩ := hne
  -- the fiber over `Φ η` is exactly the max fiber
  have hfib : Fintype.card {x : D // Φ x = Φ η} = g c₀ := by
    simp only [hg, hη]
  refine ⟨η, ?_, ?_⟩
  · rw [hfib, ge_iff_le]
    exact hle
  · have hCpos : (0 : ℝ) < (Fintype.card C : ℝ) := by
      exact_mod_cast Fintype.card_pos (α := C)
    rw [hfib, div_le_iff₀ hCpos]
    exact_mod_cast hle

open scoped NumberField nonZeroDivisors
open NumberField

set_option maxHeartbeats 4000000

theorem PrincipalGeneratorOfClassEquality
    (K : Type*) [Field K] [NumberField K]
    (A B : Ideal (𝓞 K)) (hA : A ≠ 0) (hB : B ≠ 0)
    (h : ClassGroup.mk0 ⟨A, mem_nonZeroDivisors_of_ne_zero hA⟩
        = ClassGroup.mk0 ⟨B, mem_nonZeroDivisors_of_ne_zero hB⟩) :
    ∃ α : K, α ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 K)⁰ α
        = (↑A : FractionalIdeal (𝓞 K)⁰ K) * (↑B : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  have hax : algebraMap (𝓞 K) K x ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hx
  have hay : algebraMap (𝓞 K) K y ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr hy
  refine ⟨algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K x, div_ne_zero hay hax, ?_⟩
  have hcoe : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) *
        (↑A : FractionalIdeal (𝓞 K)⁰ K)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) *
        (↑B : FractionalIdeal (𝓞 K)⁰ K) := by
    have hh := congrArg (fun I : Ideal (𝓞 K) => (I : FractionalIdeal (𝓞 K)⁰ K)) hxy
    simpa only [FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_span_singleton] using hh
  have hBne : (↑B : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hB
  have haxne : FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x) ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hax
  have hsplit : FractionalIdeal.spanSingleton (𝓞 K)⁰
        (algebraMap (𝓞 K) K y / algebraMap (𝓞 K) K x)
      = FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K y) *
        (FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K x))⁻¹ := by
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.spanSingleton_inv]
  rw [hsplit, ← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff haxne hBne,
    mul_comm (↑A : FractionalIdeal (𝓞 K)⁰ K)]
  exact hcoe.symm

open scoped NumberField
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 2000000

theorem ConjQuotientRelNormOne {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (α : K) (hα : α ≠ 0) :
    relNorm_KL h (α / conjAut h α) = 1 := by
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  -- `iota` is integral, hence algebraic, over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqι]
  have halg : IsAlgebraic L iota := hint.isAlgebraic
  -- `conjAut h (iota)² = -1`, so `conjAut h iota = ± iota`.
  have hcι2 : (conjAut h iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
  have hcases : conjAut h iota = iota ∨ conjAut h iota = -iota := by
    have hfac : (conjAut h iota - iota) * (conjAut h iota + iota) = 0 := by
      have hz : (conjAut h iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
      linear_combination hz
    rcases mul_eq_zero.mp hfac with hh | hh
    · left; exact sub_eq_zero.mp hh
    · right; linear_combination hh
  -- `conjAut h` is an involution on the generator.
  have hinvι : conjAut h (conjAut h iota) = iota := by
    rcases hcases with hh | hh
    · rw [hh, hh]
    · rw [hh, map_neg, hh, neg_neg]
  -- Hence `conjAut h ∘ conjAut h = id`.
  have hadjalg : Algebra.adjoin L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  have hinv : ∀ y : K, conjAut h (conjAut h y) = y := by
    have hEq : ((conjAut h).toAlgHom.comp (conjAut h).toAlgHom) = AlgHom.id L K := by
      apply AlgHom.ext_of_adjoin_eq_top hadjalg
      intro z hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      simpa using hinvι
    intro y
    have := AlgHom.congr_fun hEq y
    simpa using this
  -- `conjAut h α ≠ 0`.
  have hcαne : conjAut h α ≠ 0 := by
    intro hh
    exact hα ((conjAut h).injective (by rw [hh, map_zero]))
  -- Compute the relative norm.
  unfold relNorm_KL
  rw [map_div₀, hinv α]
  field_simp

open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI
open Polynomial

set_option maxHeartbeats 2000000

theorem ConjIsComplexConjugationUnderEmbedding {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (σ : K →+* ℂ) (x : K) :
    σ (conjAut h x) = (starRingEnd ℂ) (σ x) := by
  set iota := h.choose with hiota
  have hsqι : iota ^ 2 = -1 := h.choose_spec.1
  have hadjι : IntermediateField.adjoin L {iota} = ⊤ := h.choose_spec.2
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqι]
  have halg : IsAlgebraic L iota := hint.isAlgebraic
  have hadjalg : Algebra.adjoin L {iota} = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element halg hadjι
  -- The crux: `conjAut h` sends `iota` to `-iota`.
  have hci : conjAut h iota = -iota := by
    have hgen : ((IntermediateField.equivOfEq hadjι).trans
        IntermediateField.topEquiv).symm iota
        = IntermediateField.AdjoinSimple.gen L iota := by
      apply Subtype.ext
      simp [IntermediateField.AdjoinSimple.gen]
    unfold conjAut
    simp only [AlgEquiv.ofBijective_apply, AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe]
    erw [hgen, IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen]
  -- `L` totally real: `σ` restricted to `L` has real image.
  have hreal : ∀ l : L, (starRingEnd ℂ) (σ (algebraMap L K l)) = σ (algebraMap L K l) := by
    intro l
    have hr : NumberField.ComplexEmbedding.IsReal (σ.comp (algebraMap L K)) :=
      NumberField.IsTotallyReal.complexEmbedding_isReal _
    have he : NumberField.ComplexEmbedding.conjugate (σ.comp (algebraMap L K))
        = σ.comp (algebraMap L K) :=
      NumberField.ComplexEmbedding.isReal_iff.mp hr
    have := RingHom.congr_fun he l
    rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at this
  -- Give `ℂ` the `L`-algebra structure induced by `σ|_L`.
  letI algLC : Algebra L ℂ := (σ.comp (algebraMap L K)).toAlgebra
  have halgmap : ∀ l : L, algebraMap L ℂ l = σ (algebraMap L K l) := fun _ => rfl
  -- Two `L`-algebra homs `K →ₐ[L] ℂ`: `σ ∘ conjAut h` and `conj ∘ σ`.
  let ψ₁ : K →ₐ[L] ℂ :=
    { σ.comp (conjAut h).toRingHom with
      commutes' := fun l => by
        show σ (conjAut h (algebraMap L K l)) = algebraMap L ℂ l
        rw [(conjAut h).commutes l]; exact (halgmap l).symm }
  let ψ₂ : K →ₐ[L] ℂ :=
    { (starRingEnd ℂ).comp σ with
      commutes' := fun l => by
        show (starRingEnd ℂ) (σ (algebraMap L K l)) = algebraMap L ℂ l
        rw [hreal l]; exact (halgmap l).symm }
  have hψ : ψ₁ = ψ₂ := by
    apply AlgHom.ext_of_adjoin_eq_top hadjalg
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    show σ (conjAut h iota) = (starRingEnd ℂ) (σ iota)
    rw [hci, map_neg]
    -- `σ iota` is purely imaginary (its square is `-1`), so `conj (σ iota) = -(σ iota)`.
    have hz2 : (σ iota) ^ 2 = -1 := by rw [← map_pow, hsqι, map_neg, map_one]
    have hre : (σ iota).re = 0 := by
      have h1 : ((σ iota) ^ 2).im = 0 := by rw [hz2]; simp
      have h2 : ((σ iota) ^ 2).re = -1 := by rw [hz2]; simp
      simp only [pow_two, Complex.mul_re, Complex.mul_im] at h1 h2
      nlinarith [sq_nonneg (σ iota).re, sq_nonneg (σ iota).im, h1, h2]
    apply Complex.ext
    · simp [Complex.conj_re, hre]
    · simp [Complex.conj_im]
  have := AlgHom.congr_fun hψ x
  simpa using this

open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 2000000

theorem ConjQuotientUnitModulus {L K : Type*} [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] [Field K] [NumberField K] [Algebra L K]
    (h : IsAdjoinI L K) (σ : K →+* ℂ) (α : K) (hα : α ≠ 0) :
    ‖σ (α / conjAut h α)‖ = 1 := by
  -- `σ (conjAut h α) = conj (σ α)`.
  have hcc : σ (conjAut h α) = (starRingEnd ℂ) (σ α) :=
    ConjIsComplexConjugationUnderEmbedding h σ α
  have hσα : σ α ≠ 0 := by
    intro hh
    exact hα (σ.injective (by rw [hh, map_zero]))
  rw [map_div₀, hcc, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.mpr hσα)]

open scoped NumberField nonZeroDivisors

set_option maxHeartbeats 800000

theorem AdicValuationEqNegCount (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (- FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  have hrs' : IsLocalization.mk' K r s = x := hrs
  have hs0 : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hrs'
    exact hx hrs'.symm
  have hspan : FractionalIdeal.spanSingleton (𝓞 K)⁰ x
      = (↑(Ideal.span {r}) : FractionalIdeal (𝓞 K)⁰ K) *
        (↑(Ideal.span {(s : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      ← hrs', IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  have hspanR : (Ideal.span {r} : Ideal (𝓞 K)) ≠ 0 :=
    fun hc => hr0 (Ideal.span_singleton_eq_bot.mp hc)
  have hspanS : (Ideal.span {(s : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 :=
    fun hc => hs0 (Ideal.span_singleton_eq_bot.mp hc)
  have hcr : (↑(Ideal.span {r}) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hspanR
  have hcs : (↑(Ideal.span {(s : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
    (FractionalIdeal.coeIdeal_ne_zero).mpr hspanS
  rw [← hrs', IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    v.intValuation_if_neg hr0, v.intValuation_if_neg hs0, hrs', hspan,
    FractionalIdeal.count_mul K v hcr (inv_ne_zero hcs),
    FractionalIdeal.count_inv, FractionalIdeal.count_coe K v hspanR,
    FractionalIdeal.count_coe K v hspanS]
  rw [← WithZero.exp_sub]
  congr 1
  ring

open scoped NumberField nonZeroDivisors

set_option maxHeartbeats 800000

/-- **Reconciliation of the integral multiplicity and the fractional-ideal count.** For a number
field `K`, a height-one prime `v` of `𝓞 K`, and a nonzero integral ideal `I`, the multiplicity of
`v.asIdeal` in `I` (as a natural number, cast to `ℤ`) equals Mathlib's signed adic count
`FractionalIdeal.count K v` of the coerced fractional ideal `↑I`. Both are computed from the same
normalized-factorization count of `I`. -/
theorem MultiplicityEqFractionalCount (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) :
    (multiplicity v.asIdeal I : ℤ)
      = FractionalIdeal.count K v (↑I : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hI0 : I ≠ 0 := by rwa [Ideal.zero_eq_bot]
  have hbridge : multiplicity v.asIdeal I
      = Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors I) := by
    apply multiplicity_eq_of_emultiplicity_eq_some
    have h := UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      (Ideal.prime_of_isPrime v.ne_bot v.isPrime).irreducible hI0
    rwa [normalize_eq] at h
  rw [hbridge, FractionalIdeal.count_coe K v hI0,
      Ideal.count_associates_factors_eq hI0 v.isPrime v.ne_bot]

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

/-- **Count-level `conjAut` transport (equation-(4) building block for Prop 2.2).** -/
theorem ConjAutSpanSingletonCountSwap (d : AdmissibleDatum)
    (P Pc : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (α : d.K) (hα : α ≠ 0)
    (htrans : ∀ I : Ideal (𝓞 d.K),
      multiplicity Pc.asIdeal
          (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
        = multiplicity P.asIdeal I) :
    FractionalIdeal.count d.K Pc
        (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α))
      = FractionalIdeal.count d.K P
        (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α) := by
  classical
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'
  -- naturality: algebraMap ∘ c' = conjAut ∘ algebraMap
  have hnat : ∀ x : 𝓞 d.K, algebraMap (𝓞 d.K) d.K (c' x)
      = conjAut d.h_adjoin (algebraMap (𝓞 d.K) d.K x) := by
    intro x
    simp [hc', NumberField.RingOfIntegers.mapAlgEquiv, NumberField.RingOfIntegers.mapAlgHom]
  -- write α = mk' a s0
  obtain ⟨⟨a, s0⟩, hα_eq⟩ := IsLocalization.mk'_surjective (𝓞 d.K)⁰ α
  have hαmk : α = IsLocalization.mk' d.K a s0 := hα_eq.symm
  have ha : a ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hαmk
    exact hα hαmk
  have hs0 : (s0 : 𝓞 d.K) ≠ 0 := nonZeroDivisors.ne_zero s0.prop
  -- c' preserves the denominator's nonzero-divisor membership
  have hmem : (c' (s0 : 𝓞 d.K)) ∈ (𝓞 d.K)⁰ := by
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    exact hs0 (c'.injective (by rw [h, map_zero]))
  set t0 : (𝓞 d.K)⁰ := ⟨c' (s0 : 𝓞 d.K), hmem⟩ with ht0
  have ht0coe : ((t0 : 𝓞 d.K)) = c' (s0 : 𝓞 d.K) := rfl
  -- conjAut α = mk' (c' a) t0
  have hconj : conjAut d.h_adjoin α = IsLocalization.mk' d.K (c' a) t0 := by
    rw [hαmk, IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div, ht0coe, map_div₀,
      hnat a, hnat (s0 : 𝓞 d.K)]
  -- c' a ≠ 0
  have hca : c' a ≠ 0 := fun h => ha (c'.injective (by rw [h, map_zero]))
  have hcs0 : c' (s0 : 𝓞 d.K) ≠ 0 := nonZeroDivisors.ne_zero hmem
  -- image ideals under c' are the span singletons of images
  have himgA : Ideal.map c' (Ideal.span ({a} : Set (𝓞 d.K))) = Ideal.span {c' a} := by
    rw [Ideal.map_span, Set.image_singleton]
  have himgS : Ideal.map c' (Ideal.span ({(s0 : 𝓞 d.K)} : Set (𝓞 d.K)))
      = Ideal.span {c' (s0 : 𝓞 d.K)} := by
    rw [Ideal.map_span, Set.image_singleton]
  -- span-of-mk' decomposition
  have hspan : ∀ (b : 𝓞 d.K) (u : (𝓞 d.K)⁰),
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (IsLocalization.mk' d.K b u)
        = (↑(Ideal.span {b}) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(Ideal.span {(u : 𝓞 d.K)}) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro b u
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  -- generic count of coe J1 * (coe J2)⁻¹
  have key : ∀ (v : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K)) (J1 J2 : Ideal (𝓞 d.K)),
      J1 ≠ ⊥ → J2 ≠ ⊥ →
      FractionalIdeal.count d.K v
          ((↑J1 : FractionalIdeal (𝓞 d.K)⁰ d.K) * (↑J2 : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹)
        = (multiplicity v.asIdeal J1 : ℤ) - (multiplicity v.asIdeal J2 : ℤ) := by
    intro v J1 J2 h1 h2
    rw [FractionalIdeal.count_mul d.K v (FractionalIdeal.coeIdeal_ne_zero.mpr h1)
          (inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.mpr h2)),
        FractionalIdeal.count_inv,
        ← MultiplicityEqFractionalCount d.K v J1 h1,
        ← MultiplicityEqFractionalCount d.K v J2 h2]
    ring
  -- nonzero ideals
  have hbaneA : Ideal.span ({a} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hbaneS : Ideal.span ({(s0 : 𝓞 d.K)} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hcaneA : Ideal.span ({c' a} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  have hcaneS : Ideal.span ({c' (s0 : 𝓞 d.K)} : Set (𝓞 d.K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  -- LHS
  rw [hconj, hspan (c' a) t0]
  show FractionalIdeal.count d.K Pc
      ((↑(Ideal.span {c' a}) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
        (↑(Ideal.span {(t0 : 𝓞 d.K)}) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) = _
  rw [ht0coe, key Pc (Ideal.span {c' a}) (Ideal.span {c' (s0 : 𝓞 d.K)}) hcaneA hcaneS]
  -- RHS
  conv_rhs => rw [hαmk, hspan a s0, key P (Ideal.span {a}) (Ideal.span {(s0 : 𝓞 d.K)}) hbaneA hbaneS]
  -- transport multiplicities: mult Pc (span{c' a}) = mult P (span{a}), etc.
  rw [← himgA, ← himgS, htrans (Ideal.span {a}), htrans (Ideal.span {(s0 : 𝓞 d.K)})]

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

-- reconciliation: multiplicity = FractionalIdeal.count of coeIdeal (proved)
private theorem recon (K : Type*) [Field K] [NumberField K]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    (multiplicity v.asIdeal I : ℤ) = FractionalIdeal.count K v (↑I : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.count_coe K v hI]
  norm_cast
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors v.irreducible hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot]
  congr 1
  exact normalize_eq _

-- STEP A: count of A_δ at the prime P w0 (using distinctness prop 2).
private theorem countAδ_P {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)))
    (δ : Fin m → Bool) (w0 : Fin m) :
    FractionalIdeal.count K (P w0)
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = (if δ w0 then 1 else 0 : ℤ) := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [h, if_true]; exact (P t).ne_bot
    · simp only [h, if_false]; exact (Pc t).ne_bot
  have hPne : ∀ t, t ≠ w0 → (P t) ≠ (P w0) := by
    intro t ht hc
    apply ht
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl w0) := by
      simp only [Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inl_injective (hinj hh)
  have hPcne : ∀ t, (Pc t) ≠ (P w0) := by
    intro t hc
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl w0) := by
      simp only [Sum.elim_inr, Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inr_ne_inl (hinj hh)
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K (P w0) Finset.univ _ (fun t _ => hprodne t),
    Finset.sum_eq_single w0]
  · by_cases h : δ w0
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_pos rfl]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne w0)]
  · intro t _ hts
    by_cases h : δ t
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne t hts)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne t)]
  · intro hc; exact absurd (Finset.mem_univ w0) hc

-- helper: spanSingleton of a mk' as a quotient of coeIdeals of principal ideals
private theorem span_mk' (K : Type*) [Field K] [NumberField K]
    (a : 𝓞 K) (s0 : (𝓞 K)⁰) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰ (IsLocalization.mk' K a s0)
      = (↑(Ideal.span {a}) : FractionalIdeal (𝓞 K)⁰ K) *
        (↑(Ideal.span {(s0 : 𝓞 K)}) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
    IsFractionRing.mk'_eq_div, div_eq_mul_inv]

-- STEP A: count of A_δ at the prime Pc w0.
private theorem countAδ_Pc {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hinj : Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)))
    (δ : Fin m → Bool) (w0 : Fin m) :
    FractionalIdeal.count K (Pc w0)
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = (if δ w0 then 0 else 1 : ℤ) := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  have hPcne : ∀ t, t ≠ w0 → (Pc t) ≠ (Pc w0) := by
    intro t ht hc
    apply ht
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr w0) := by
      simp only [Sum.elim_inr]; exact congrArg _ hc
    exact Sum.inr_injective (hinj hh)
  have hPne : ∀ t, (P t) ≠ (Pc w0) := by
    intro t hc
    have hh : Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inl t)
        = Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal) (Sum.inr w0) := by
      simp only [Sum.elim_inr, Sum.elim_inl]; exact congrArg _ hc
    exact Sum.inl_ne_inr (hinj hh)
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K (Pc w0) Finset.univ _ (fun t _ => hprodne t),
    Finset.sum_eq_single w0]
  · by_cases h : δ w0
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne w0)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_pos rfl]
  · intro t _ hts
    by_cases h : δ t
    · simp only [if_pos h]
      rw [FractionalIdeal.count_maximal, if_neg (hPne t)]
    · simp only [if_neg h]
      rw [FractionalIdeal.count_maximal, if_neg (hPcne t hts)]
  · intro hc; exact absurd (Finset.mem_univ w0) hc

-- general multiplicity transport under a ring equiv
private theorem multMap {R : Type*} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (p I : Ideal R) :
    multiplicity (Ideal.map e p) (Ideal.map e I) = multiplicity p I := by
  have hmapdvd : ∀ (f : R ≃+* R) {J K : Ideal R},
      J ∣ K → Ideal.map f J ∣ Ideal.map f K := by
    rintro f J K ⟨L, rfl⟩
    exact ⟨Ideal.map f L, Ideal.map_mul f J L⟩
  have hcancel : ∀ J : Ideal R, Ideal.map e.symm (Ideal.map e J) = J := by
    intro J
    rw [Ideal.map_symm, Ideal.comap_map_of_bijective _ e.bijective]
  have hdvd : ∀ n : ℕ, (Ideal.map e p) ^ n ∣ (Ideal.map e I) ↔ p ^ n ∣ I := by
    intro n
    rw [← Ideal.map_pow]
    constructor
    · intro h
      have h2 := hmapdvd e.symm h
      rwa [hcancel, hcancel] at h2
    · exact fun h => hmapdvd e h
  have hemul : emultiplicity (Ideal.map e p) (Ideal.map e I) = emultiplicity p I := by
    rw [emultiplicity_eq_emultiplicity_iff]
    exact hdvd
  unfold multiplicity
  rw [hemul]

-- STEP A: count of A_δ at an off-family prime = 0.
private theorem countAδ_off {m : ℕ} (K : Type*) [Field K] [NumberField K]
    (P Pc : Fin m → IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (δ : Fin m → Bool) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hw : ∀ t, w ≠ P t ∧ w ≠ Pc t) :
    FractionalIdeal.count K w
        (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  classical
  have hprodne : ∀ t : Fin m, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal)
      : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    intro t
    rw [FractionalIdeal.coeIdeal_ne_zero]
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  have hcoe : (↑(∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K)
      = ∏ t, (↑(if δ t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← FractionalIdeal.coeIdealHom_apply (𝓞 K)⁰ K, map_prod]
    simp only [FractionalIdeal.coeIdealHom_apply]
  rw [hcoe, FractionalIdeal.count_prod K w Finset.univ _ (fun t _ => hprodne t)]
  apply Finset.sum_eq_zero
  intro t _
  by_cases h : δ t
  · simp only [if_pos h]
    rw [FractionalIdeal.count_maximal, if_neg (fun hc => (hw t).1 hc.symm)]
  · simp only [if_neg h]
    rw [FractionalIdeal.count_maximal, if_neg (fun hc => (hw t).2 hc.symm)]

theorem ConjQuotientValuationFormula (d : AdmissibleDatum)
    (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (bidx : Fin (d.t * deg d) → Fin d.t)
    (hfam :
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I))
    (η ε : Fin (d.t * deg d) → Bool)
    (α : d.K) (hα : α ≠ 0)
    (hgen : FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
      (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K) *
      (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    (∀ s, (P s).valuation d.K (α / conjAut d.h_adjoin α)
            = WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) ∧
          (Pc s).valuation d.K (α / conjAut d.h_adjoin α)
            = WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) ∧
      (∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
          (∀ s, w ≠ P s ∧ w ≠ Pc s) → w.valuation d.K (α / conjAut d.h_adjoin α) = 1) := by
  classical
  obtain ⟨hswap, hinj, hram, htransfam⟩ := hfam
  set c' := NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin) with hc'
  have hcα0 : conjAut d.h_adjoin α ≠ 0 :=
    (map_ne_zero_iff _ (conjAut d.h_adjoin).injective).mpr hα
  have hquot0 : α / conjAut d.h_adjoin α ≠ 0 := div_ne_zero hα hcα0
  have hprodne : ∀ (δ : Fin (d.t * deg d) → Bool),
      (∏ t, if δ t then (P t).asIdeal else (Pc t).asIdeal) ≠ 0 := by
    intro δ
    rw [Finset.prod_ne_zero_iff]
    intro t _
    by_cases h : δ t
    · simp only [if_pos h]; exact (P t).ne_bot
    · simp only [if_neg h]; exact (Pc t).ne_bot
  -- count of span(α/cα) at w = count(span α) - count(span(conjAut α))
  have hcountq : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      FractionalIdeal.count d.K w
          (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (α / conjAut d.h_adjoin α))
        = FractionalIdeal.count d.K w (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α)
          - FractionalIdeal.count d.K w
              (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α)) := by
    intro w
    rw [show FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (α / conjAut d.h_adjoin α)
          = FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α *
            (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ (conjAut d.h_adjoin α))⁻¹ from by
        rw [FractionalIdeal.spanSingleton_inv,
          FractionalIdeal.spanSingleton_mul_spanSingleton, ← div_eq_mul_inv],
      FractionalIdeal.count_mul d.K w
        (by rwa [FractionalIdeal.spanSingleton_ne_zero_iff])
        (inv_ne_zero (by rwa [FractionalIdeal.spanSingleton_ne_zero_iff])),
      FractionalIdeal.count_inv]
    ring
  -- count of span α at w = count(↑A_ε) - count(↑A_η)
  have hcountα : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      FractionalIdeal.count d.K w (FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α)
        = FractionalIdeal.count d.K w
            (↑(∏ t, if ε t then (P t).asIdeal else (Pc t).asIdeal) : FractionalIdeal (𝓞 d.K)⁰ d.K)
          - FractionalIdeal.count d.K w
            (↑(∏ t, if η t then (P t).asIdeal else (Pc t).asIdeal)) := by
    intro w
    rw [hgen, FractionalIdeal.count_mul d.K w
        ((FractionalIdeal.coeIdeal_ne_zero).mpr (hprodne ε))
        (inv_ne_zero ((FractionalIdeal.coeIdeal_ne_zero).mpr (hprodne η))),
      FractionalIdeal.count_inv]
    ring
  refine ⟨fun s => ⟨?_, ?_⟩, ?_⟩
  · -- (P s) valuation
    rw [AdicValuationEqNegCount d.K (P s) (α / conjAut d.h_adjoin α) hquot0, hcountq (P s),
      hcountα (P s), countAδ_P d.K P Pc hinj ε s, countAδ_P d.K P Pc hinj η s,
      ConjAutSpanSingletonCountSwap d (Pc s) (P s) α hα (fun I => (htransfam I s).1),
      hcountα (Pc s), countAδ_Pc d.K P Pc hinj ε s, countAδ_Pc d.K P Pc hinj η s]
    congr 1
    cases ε s <;> cases η s <;> simp <;> ring
  · -- (Pc s) valuation
    rw [AdicValuationEqNegCount d.K (Pc s) (α / conjAut d.h_adjoin α) hquot0, hcountq (Pc s),
      hcountα (Pc s), countAδ_Pc d.K P Pc hinj ε s, countAδ_Pc d.K P Pc hinj η s,
      ConjAutSpanSingletonCountSwap d (P s) (Pc s) α hα (fun I => (htransfam I s).2),
      hcountα (P s), countAδ_P d.K P Pc hinj ε s, countAδ_P d.K P Pc hinj η s]
    congr 1
    cases ε s <;> cases η s <;> simp <;> ring
  · -- off-family
    intro w hw
    have hwne : w.asIdeal ≠ ⊥ := w.ne_bot
    haveI hwp : w.asIdeal.IsPrime := w.isPrime
    -- `conjAut` is an involution on the field `d.K`.
    have hinvfield : ∀ y : d.K, conjAut d.h_adjoin (conjAut d.h_adjoin y) = y := by
      set iota := d.h_adjoin.choose with hiota
      have hsqι : iota ^ 2 = -1 := d.h_adjoin.choose_spec.1
      have hadjι : IntermediateField.adjoin d.L {iota} = ⊤ := d.h_adjoin.choose_spec.2
      have hint : IsIntegral d.L iota := by
        refine ⟨Polynomial.X ^ 2 + 1, ?_, ?_⟩
        · monicity!
        · simp [hsqι]
      have halg : IsAlgebraic d.L iota := hint.isAlgebraic
      have hcι2 : (conjAut d.h_adjoin iota) ^ 2 = -1 := by
        rw [← map_pow, hsqι, map_neg, map_one]
      have hcases : conjAut d.h_adjoin iota = iota ∨ conjAut d.h_adjoin iota = -iota := by
        have hfac : (conjAut d.h_adjoin iota - iota) * (conjAut d.h_adjoin iota + iota) = 0 := by
          have hz : (conjAut d.h_adjoin iota) ^ 2 - iota ^ 2 = 0 := by rw [hcι2, hsqι]; ring
          linear_combination hz
        rcases mul_eq_zero.mp hfac with hh | hh
        · left; exact sub_eq_zero.mp hh
        · right; linear_combination hh
      have hinvι : conjAut d.h_adjoin (conjAut d.h_adjoin iota) = iota := by
        rcases hcases with hh | hh
        · rw [hh, hh]
        · rw [hh, map_neg, hh, neg_neg]
      have hadjalg : Algebra.adjoin d.L {iota} = ⊤ :=
        Algebra.adjoin_eq_top_of_primitive_element halg hadjι
      have hEq : ((conjAut d.h_adjoin).toAlgHom.comp (conjAut d.h_adjoin).toAlgHom)
          = AlgHom.id d.L d.K := by
        apply AlgHom.ext_of_adjoin_eq_top hadjalg
        intro z hz
        simp only [Set.mem_singleton_iff] at hz
        subst hz
        simpa using hinvι
      intro y
      have := AlgHom.congr_fun hEq y
      simpa using this
    -- Transport the involution to `𝓞 d.K` and then to ideals.
    have hnat : ∀ x : 𝓞 d.K,
        (algebraMap (𝓞 d.K) d.K) (c' x) = conjAut d.h_adjoin ((algebraMap (𝓞 d.K) d.K) x) :=
      fun _ => rfl
    have hinvring : ∀ x : 𝓞 d.K, c' (c' x) = x := by
      intro x
      apply IsFractionRing.injective (𝓞 d.K) d.K
      rw [hnat, hnat, hinvfield]
    have hbridge : ∀ I : Ideal (𝓞 d.K),
        Ideal.map c' I = Ideal.map (c' : 𝓞 d.K →+* 𝓞 d.K) I := fun _ => rfl
    have hbridge2 : ∀ I : Ideal (𝓞 d.K),
        Ideal.map c'.toRingEquiv I = Ideal.map c' I := fun _ => rfl
    have hcomp : (c' : 𝓞 d.K →+* 𝓞 d.K).comp (c' : 𝓞 d.K →+* 𝓞 d.K) = RingHom.id _ := by
      ext x
      simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
      exact_mod_cast hinvring x
    have hinvideal : ∀ I : Ideal (𝓞 d.K), Ideal.map c' (Ideal.map c' I) = I := by
      intro I
      rw [hbridge, hbridge, Ideal.map_map, hcomp, Ideal.map_id]
    -- `P' = c'(w)` is an off-family prime whose `c'`-image is `w`.
    have hnebot : Ideal.map c' w.asIdeal ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective c'.injective]
      exact hwne
    haveI hprime : (Ideal.map c' w.asIdeal).IsPrime := Ideal.map_isPrime_of_equiv c'
    set P' : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K) :=
      ⟨Ideal.map c' w.asIdeal, hprime, hnebot⟩ with hP'
    have hmapP' : Ideal.map c' P'.asIdeal = w.asIdeal := by
      rw [hP']; exact hinvideal w.asIdeal
    have htransw : ∀ I : Ideal (𝓞 d.K),
        multiplicity w.asIdeal (Ideal.map c' I) = multiplicity P'.asIdeal I := by
      intro I
      have he := multMap c'.toRingEquiv P'.asIdeal I
      rw [hbridge2, hbridge2, hmapP'] at he
      exact he
    have hP'off : ∀ t, P' ≠ P t ∧ P' ≠ Pc t := by
      intro t
      constructor
      · intro hc
        apply (hw t).2
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rw [← hmapP', hc]
        exact (hswap t).1
      · intro hc
        apply (hw t).1
        apply IsDedekindDomain.HeightOneSpectrum.ext
        rw [← hmapP', hc, ← (hswap t).1, hinvideal]
    rw [AdicValuationEqNegCount d.K w (α / conjAut d.h_adjoin α) hquot0, hcountq w,
      hcountα w, countAδ_off d.K P Pc ε w hw, countAδ_off d.K P Pc η w hw,
      ConjAutSpanSingletonCountSwap d P' w α hα htransw,
      hcountα P', countAδ_off d.K P Pc ε P' hP'off, countAδ_off d.K P Pc η P' hP'off]
    simp

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

theorem QSquaredClearsConjQuotient (d : AdmissibleDatum)
    (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (bidx : Fin (d.t * deg d) → Fin d.t)
    (hfam :
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I))
    (η ε : Fin (d.t * deg d) → Bool)
    (α : d.K) (hα : α ≠ 0)
    (hgen : FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
      (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K) *
      (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
          FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    IsIntegral ℤ ((Dq d : d.K) * (α / conjAut d.h_adjoin α)) := by
  set u := α / conjAut d.h_adjoin α with hu_def
  have hform := ConjQuotientValuationFormula d P Pc bidx hfam η ε α hα hgen
  -- Crux: any prime `w` lying over `(q_b)` has `w.valuation Dq ≤ exp(-2)`, since `q_b² ∣ Dq`.
  have hcrux : ∀ (w : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K)) (b : Fin d.t),
      w.asIdeal.LiesOver (Ideal.span {(d.q b : ℤ)}) →
      w.valuation d.K (Dq d : d.K) ≤ WithZero.exp (-2) := by
    intro w b hlo
    have hcast : (Dq d : d.K) = algebraMap (𝓞 d.K) d.K ((Dq d : ℕ) : 𝓞 d.K) := by
      rw [map_natCast]
    rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
        show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num,
        IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]
    -- Goal: `((Dq d : ℕ) : 𝓞 K) ∈ w.asIdeal ^ 2`.
    have hqmem : ((d.q b : ℕ) : 𝓞 d.K) ∈ w.asIdeal := by
      have hmem_int : (d.q b : ℤ) ∈ Ideal.under ℤ w.asIdeal := by
        rw [← hlo.over]; exact Ideal.mem_span_singleton_self _
      have h2 : algebraMap ℤ (𝓞 d.K) (d.q b : ℤ) ∈ w.asIdeal := hmem_int
      simpa using h2
    have hQmem : ((Qprod d : ℕ) : 𝓞 d.K) ∈ w.asIdeal := by
      have hQ : ((Qprod d : ℕ) : 𝓞 d.K) = ∏ b', ((d.q b' : ℕ) : 𝓞 d.K) := by
        rw [show Qprod d = ∏ b', d.q b' from rfl]; push_cast; rfl
      rw [hQ, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b)]
      exact Ideal.mul_mem_right _ _ hqmem
    have hDqQ : ((Dq d : ℕ) : 𝓞 d.K) = ((Qprod d : ℕ) : 𝓞 d.K) ^ 2 := by
      rw [show Dq d = (Qprod d) ^ 2 from rfl]; push_cast; ring
    rw [hDqQ, pow_two, pow_two]
    exact Ideal.mul_mem_mul hQmem hQmem
  -- All adic valuations of `Dq · u` are `≤ 1`, so `Dq · u` is an algebraic integer.
  have hval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 d.K),
      v.valuation d.K ((Dq d : d.K) * u) ≤ 1 := by
    intro v
    rw [map_mul]
    by_cases hv : ∃ s, v = P s ∨ v = Pc s
    · obtain ⟨s, hs⟩ := hv
      have hbound_ε : ((ε s).toNat : ℤ) ≤ 1 ∧ 0 ≤ ((ε s).toNat : ℤ) := by
        rcases ε s <;> simp
      have hbound_η : ((η s).toNat : ℤ) ≤ 1 ∧ 0 ≤ ((η s).toNat : ℤ) := by
        rcases η s <;> simp
      rcases hs with hs | hs
      · subst hs
        rw [(hform.1 s).1]
        calc (P s).valuation d.K (Dq d : d.K)
                * WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))))
            ≤ WithZero.exp (-2)
                * WithZero.exp (-(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) :=
              mul_le_mul_right' (hcrux (P s) (bidx s) (hfam.2.2.1 s).1) _
          _ = WithZero.exp (-2 + -(2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))) :=
              (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
          _ = 1 := WithZero.exp_zero
      · subst hs
        rw [(hform.1 s).2]
        calc (Pc s).valuation d.K (Dq d : d.K)
                * WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ)))
            ≤ WithZero.exp (-2)
                * WithZero.exp (2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))) :=
              mul_le_mul_right' (hcrux (Pc s) (bidx s) (hfam.2.2.1 s).2.1) _
          _ = WithZero.exp (-2 + 2 * (((ε s).toNat : ℤ) - ((η s).toNat : ℤ))) :=
              (WithZero.exp_add _ _).symm
          _ ≤ WithZero.exp 0 := by rw [WithZero.exp_le_exp]; omega
          _ = 1 := WithZero.exp_zero
    · push_neg at hv
      rw [hform.2 v hv, mul_one]
      -- `Dq` is an integer, so its valuation is `≤ 1`.
      have hcast : (Dq d : d.K) = algebraMap (𝓞 d.K) d.K ((Dq d : ℕ) : 𝓞 d.K) := by
        rw [map_natCast]
      rw [hcast, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one v _
  obtain ⟨y, hy⟩ :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one d.K
      ((Dq d : d.K) * u) hval
  rw [← hy]
  exact NumberField.RingOfIntegers.isIntegral_coe y

open scoped NumberField nonZeroDivisors
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 4000000

theorem ValuationVectorInjective (d : AdmissibleDatum)
    (P Pc : Fin (d.t * deg d) → IsDedekindDomain.HeightOneSpectrum (𝓞 d.K))
    (bidx : Fin (d.t * deg d) → Fin d.t)
    (hfam :
      (∀ s, Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) (P s).asIdeal
              = (Pc s).asIdeal ∧ (Pc s).asIdeal ≠ (P s).asIdeal) ∧
      Function.Injective (Sum.elim (fun s => (P s).asIdeal) (fun s => (Pc s).asIdeal)) ∧
      (∀ s, (P s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (Pc s).asIdeal.LiesOver (Ideal.span {(d.q (bidx s) : ℤ)}) ∧
            (∀ b, multiplicity (P s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0) ∧
            (∀ b, multiplicity (Pc s).asIdeal
                (Ideal.span {(algebraMap ℤ (𝓞 d.K)) (d.q b)}) = if b = bidx s then 1 else 0)) ∧
      (∀ (I : Ideal (𝓞 d.K)) (s : Fin (d.t * deg d)),
          multiplicity (P s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (Pc s).asIdeal I ∧
          multiplicity (Pc s).asIdeal
              (Ideal.map (NumberField.RingOfIntegers.mapAlgEquiv (conjAut d.h_adjoin)) I)
            = multiplicity (P s).asIdeal I))
    (η : Fin (d.t * deg d) → Bool)
    (F : Finset (Fin (d.t * deg d) → Bool))
    (u : (Fin (d.t * deg d) → Bool) → d.K)
    (hu : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧ u ε = α / conjAut d.h_adjoin α ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α =
        (↑(∏ s, if ε s then (P s).asIdeal else (Pc s).asIdeal) :
            FractionalIdeal (𝓞 d.K)⁰ d.K) *
        (↑(∏ s, if η s then (P s).asIdeal else (Pc s).asIdeal) :
            FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹) :
    Set.InjOn u ↑F := by
  intro ε₁ hε₁ ε₂ hε₂ heq
  obtain ⟨α₁, hα₁, huε₁, hgen₁⟩ := hu ε₁ (Finset.mem_coe.mp hε₁)
  obtain ⟨α₂, hα₂, huε₂, hgen₂⟩ := hu ε₂ (Finset.mem_coe.mp hε₂)
  funext s
  -- valuation of `u ε_i` at `P s`
  have hv₁ := ((ConjQuotientValuationFormula d P Pc bidx hfam η ε₁ α₁ hα₁ hgen₁).1 s).1
  have hv₂ := ((ConjQuotientValuationFormula d P Pc bidx hfam η ε₂ α₂ hα₂ hgen₂).1 s).1
  -- both valuations are `exp` of the corresponding integer exponent, and are equal
  have hchain :
      WithZero.exp (-(2 * (((ε₁ s).toNat : ℤ) - ((η s).toNat : ℤ))))
        = WithZero.exp (-(2 * (((ε₂ s).toNat : ℤ) - ((η s).toNat : ℤ)))) := by
    rw [← hv₁, ← hv₂, ← huε₁, ← huε₂, heq]
  -- injectivity of `exp` recovers the exponent, hence `ε₁ s = ε₂ s`
  have hE := WithZero.exp_inj.mp hchain
  have hnat : (ε₁ s).toNat = (ε₂ s).toNat := by omega
  rcases hb₁ : ε₁ s <;> rcases hb₂ : ε₂ s <;> simp_all

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

theorem FiberCountToExpBound (d : AdmissibleDatum) (H : ℝ) (hH : 0 < H) (Fcard : ℕ)
    (hh : 0 < classNumber d.K)
    (hfiber : ((2 : ℝ) ^ (d.t * deg d)) / (classNumber d.K : ℝ) ≤ (Fcard : ℝ))
    (hclass : (classNumber d.K : ℝ) ≤ H ^ (deg d)) :
    Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ)) ≤ (Fcard : ℝ) := by
  have hh' : (0 : ℝ) < (classNumber d.K : ℝ) := by exact_mod_cast hh
  have hHf : (0 : ℝ) < H ^ (deg d) := by positivity
  have h2 : (2 : ℝ) ^ (d.t * deg d) = Real.exp (Real.log 2 * (↑(d.t * deg d))) := by
    rw [← Real.rpow_natCast (2 : ℝ) (d.t * deg d), Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  have hHf' : H ^ (deg d) = Real.exp (Real.log H * (↑(deg d))) := by
    rw [← Real.rpow_natCast H (deg d), Real.rpow_def_of_pos hH]
  have hexp : Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ))
      = (2 : ℝ) ^ (d.t * deg d) / H ^ (deg d) := by
    rw [h2, hHf', ← Real.exp_sub]
    congr 1
    push_cast
    ring
  rw [hexp]
  have hstep1 : (2 : ℝ) ^ (d.t * deg d) / H ^ (deg d)
      ≤ (2 : ℝ) ^ (d.t * deg d) / (classNumber d.K : ℝ) :=
    div_le_div_of_nonneg_left (by positivity) hh' hclass
  exact le_trans hstep1 hfiber

open scoped NumberField nonZeroDivisors
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum

set_option maxHeartbeats 4000000

theorem Prop22NormOneElements (d : AdmissibleDatum) (H : ℝ) (hH : 0 < H)
    (hclass : (classNumber d.K : ℝ) ≤ H ^ (deg d)) :
    ∃ U : Finset d.K,
      (∀ u ∈ U, IsIntegral ℤ ((Dq d : d.K) * u)) ∧
      (∀ u ∈ U, relNorm_KL d.h_adjoin u = 1) ∧
      (∀ u ∈ U, ∀ σ : d.K →+* ℂ, ‖σ u‖ = 1) ∧
      (U.card : ℝ) ≥ Real.exp (((d.t : ℝ) * Real.log 2 - Real.log H) * (deg d : ℝ)) := by
  classical
  -- Step 0: the conjugate-pair family
  obtain ⟨P, Pc, bidx, S, hswap, hinj, hram, hSset, hScard, hSeq, htrans⟩ :=
    ConjugatePairIndexing d (Fact215ConjugatePrimePairs d)
  -- the family-property block consumed by the downstream sublemmas
  have hfam := And.intro hswap (And.intro hinj (And.intro hram htrans))
  -- Step 1: the ideals A_δ
  set A : (Fin (d.t * deg d) → Bool) → Ideal (𝓞 d.K) :=
    fun δ => ∏ s, if δ s then (P s).asIdeal else (Pc s).asIdeal with hAdef
  have hAne : ∀ δ, A δ ≠ 0 := by
    intro δ
    rw [hAdef]
    simp only
    rw [Finset.prod_ne_zero_iff]
    intro s _
    by_cases hδ : δ s
    · simp only [hδ, if_true]; exact (P s).ne_bot
    · simp only [hδ, if_false]; exact (Pc s).ne_bot
  -- the class map
  set Φ : (Fin (d.t * deg d) → Bool) → ClassGroup (𝓞 d.K) :=
    fun δ => ClassGroup.mk0 ⟨A δ, mem_nonZeroDivisors_of_ne_zero (hAne δ)⟩ with hΦdef
  -- Step 1: pigeonhole
  obtain ⟨η, hηprod, hηreal⟩ := IdealClassPigeonholeFiber Φ
  set F : Finset (Fin (d.t * deg d) → Bool) :=
    Finset.univ.filter (fun ε => Φ ε = Φ η) with hFdef
  -- Step 2: generators α_ε for ε ∈ F
  have hgen : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α
        = (↑(A ε) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(A η) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro ε hε
    have hΦ : Φ ε = Φ η := (Finset.mem_filter.mp hε).2
    exact PrincipalGeneratorOfClassEquality d.K (A ε) (A η) (hAne ε) (hAne η) hΦ
  -- the conjugate-quotient map
  set u : (Fin (d.t * deg d) → Bool) → d.K :=
    fun ε => if hε : ε ∈ F then
      (Classical.choose (hgen ε hε)) / conjAut d.h_adjoin (Classical.choose (hgen ε hε))
    else 0 with hudef
  have hu : ∀ ε ∈ F, ∃ α : d.K, α ≠ 0 ∧ u ε = α / conjAut d.h_adjoin α ∧
      FractionalIdeal.spanSingleton (𝓞 d.K)⁰ α
        = (↑(A ε) : FractionalIdeal (𝓞 d.K)⁰ d.K) *
          (↑(A η) : FractionalIdeal (𝓞 d.K)⁰ d.K)⁻¹ := by
    intro ε hε
    refine ⟨Classical.choose (hgen ε hε), (Classical.choose_spec (hgen ε hε)).1, ?_,
      (Classical.choose_spec (hgen ε hε)).2⟩
    rw [hudef]; simp only [hε, dif_pos]
  refine ⟨F.image u, ?_, ?_, ?_, ?_⟩
  · -- integrality
    intro v hv
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact QSquaredClearsConjQuotient d P Pc bidx hfam η ε α hα hspan
  · -- relative norm one
    intro v hv
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact ConjQuotientRelNormOne d.h_adjoin α hα
  · -- unit modulus
    intro v hv σ
    obtain ⟨ε, hε, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨α, hα, hue, hspan⟩ := hu ε hε
    rw [hue]
    exact ConjQuotientUnitModulus d.h_adjoin σ α hα
  · -- count bound
    have hInj : Set.InjOn u ↑F :=
      ValuationVectorInjective d P Pc bidx hfam η F u hu
    have hcardU : (F.image u).card = F.card := Finset.card_image_of_injOn hInj
    have hFcard : F.card = Fintype.card {x : (Fin (d.t * deg d) → Bool) // Φ x = Φ η} := by
      rw [hFdef]; exact (Fintype.card_subtype _).symm
    have hcardD : Fintype.card (Fin (d.t * deg d) → Bool) = 2 ^ (d.t * deg d) := by
      simp [Fintype.card_fun]
    have hcardC : Fintype.card (ClassGroup (𝓞 d.K)) = classNumber d.K := rfl
    have hh : 0 < classNumber d.K := by
      rw [← hcardC]; exact Fintype.card_pos
    have hfiber : ((2 : ℝ) ^ (d.t * deg d)) / (classNumber d.K : ℝ) ≤ (F.card : ℝ) := by
      rw [hFcard]
      have hthis := hηreal
      rw [hcardD, hcardC] at hthis
      exact_mod_cast hthis
    have hbound := FiberCountToExpBound d H hH F.card hh hfiber hclass
    rw [ge_iff_le, hcardU]
    exact hbound

open scoped NumberField
open scoped ComplexConjugate
open Workspace.Types.MinkowskiWindow Workspace.Types.CMAdjoinI

open Polynomial

namespace Workspace.ProofLemmas

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Step 1 (Lemma 2.6, norm-product identity).**  In the CM setting `K = L(i)`
(`hcm : IsAdjoinI L K`), for every nonzero algebraic integer `β ∈ 𝓞 K` the product of the
moduli of the images of `β` under the `f` selected complex embeddings equals the square root of
the absolute value of the field norm `N_{K/ℚ}(β)`, and this quantity is at least `1`:
`∏ r, ‖σ_r β‖ = √|N_{K/ℚ}(β)| ≥ 1`. -/
theorem SublemmaNormProduct (hcm : IsAdjoinI L K) (sel : EmbeddingSelection L K f)
    (β : 𝓞 K) (hβ : β ≠ 0) :
    (∏ r, ‖sel.sigma r (β : K)‖) = Real.sqrt (|Algebra.norm ℚ (β : K)|)
      ∧ 1 ≤ ∏ r, ‖sel.sigma r (β : K)‖ := by
  classical
  obtain ⟨iota, hsq, hadj⟩ := hcm
  -- Every complex embedding of `K` is non-real (it sends `iota` to `±i`).
  have hemb : ∀ φ : K →+* ℂ, ¬ NumberField.ComplexEmbedding.IsReal φ := by
    intro φ hφ
    have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
      (NumberField.ComplexEmbedding.isReal_iff).mp hφ
    have hI : (φ iota) ^ 2 = -1 := by rw [← map_pow, hsq, map_neg, map_one]
    have hconj : (starRingEnd ℂ) (φ iota) = φ iota := by
      have h2 := RingHom.congr_fun h1 iota
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hz2 : (φ iota) * (starRingEnd ℂ) (φ iota) = ((Complex.normSq (φ iota) : ℝ) : ℂ) :=
      Complex.mul_conj _
    rw [hconj, ← pow_two, hI] at hz2
    have hcast : Complex.normSq (φ iota) = -1 := by exact_mod_cast hz2.symm
    have hnn := Complex.normSq_nonneg (φ iota)
    linarith
  -- Hence `K` is totally complex.
  haveI htc : NumberField.IsTotallyComplex K := by
    apply NumberField.IsTotallyComplex.mk
    intro v
    rw [NumberField.InfinitePlace.isComplex_iff]
    exact hemb v.embedding
  -- `iota` is integral over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota ∉ L` because `L` is totally real.
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- Minimal polynomial of `iota` over `L` is `X² + 1`, so `[K : L] = 2`.
  have hmin : minpoly L iota = X ^ 2 + 1 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd; simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : L[X]).natDegree ≤ (minpoly L iota).natDegree := by
      have h2 : 2 ≤ (minpoly L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd hdeg).symm
  have hnd : (minpoly L iota).natDegree = 2 := by rw [hmin]; compute_degree!
  have hfinLK : Module.finrank L K = 2 := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [hnd, hadj, IntermediateField.finrank_top'] at h1
    exact h1
  -- `[L : ℚ] = f` from the bijection of restrictions.
  have hcard_emb : f = Fintype.card (L →+* ℂ) := by
    have := Fintype.card_of_bijective sel.restrict_bijective
    simpa using this
  have hfinL : Module.finrank ℚ L = f := by
    rw [← NumberField.Embeddings.card L ℂ, ← hcard_emb]
  have hfinK : Module.finrank ℚ K = 2 * f := by
    have htower := Module.finrank_mul_finrank ℚ L K
    rw [hfinL, hfinLK] at htower
    omega
  have hcardIP : Fintype.card (NumberField.InfinitePlace K) = f := by
    rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyComplex.nrRealPlaces_eq_zero]
    have hf2 := NumberField.IsTotallyComplex.finrank K
    rw [hfinK] at hf2
    omega
  -- The map `r ↦ mk (σ_r)` is a bijection `Fin f ≃ InfinitePlace K`.
  set W : Fin f → NumberField.InfinitePlace K :=
    fun r => NumberField.InfinitePlace.mk (sel.sigma r) with hW
  have hWinj : Function.Injective W := by
    intro r r' h
    rw [hW] at h
    simp only at h
    rw [NumberField.InfinitePlace.mk_eq_iff] at h
    have hrestr : (sel.sigma r).comp (algebraMap L K) = (sel.sigma r').comp (algebraMap L K) := by
      rcases h with h | h
      · rw [h]
      · ext x
        have hreal := sel.restrict_isReal r
        have hri : NumberField.ComplexEmbedding.conjugate ((sel.sigma r).comp (algebraMap L K))
            = (sel.sigma r).comp (algebraMap L K) :=
          (NumberField.ComplexEmbedding.isReal_iff).mp hreal
        have h2 := RingHom.congr_fun hri x
        rw [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
        rw [← h]
        simp only [RingHom.comp_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
        exact h2.symm
    exact sel.restrict_bijective.injective hrestr
  have hWbij : Function.Bijective W :=
    (Fintype.bijective_iff_injective_and_card W).mpr
      ⟨hWinj, by rw [Fintype.card_fin, hcardIP]⟩
  -- The product-of-moduli squared equals |N|.
  have e2 : ∏ r, (W r) (β : K) ^ (W r).mult = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [Function.Bijective.prod_comp hWbij (fun w => w (β : K) ^ w.mult)]
    exact NumberField.InfinitePlace.prod_eq_abs_norm _
  have e3 : ∏ r, ‖sel.sigma r (β : K)‖ ^ 2 = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [← e2]
    apply Finset.prod_congr rfl
    intro r _
    rw [hW]
    simp only [NumberField.InfinitePlace.apply, NumberField.IsTotallyComplex.mult_eq]
  have hnn : (0 : ℝ) ≤ ∏ r, ‖sel.sigma r (β : K)‖ :=
    Finset.prod_nonneg (fun _ _ => norm_nonneg _)
  have hsq_eq : (∏ r, ‖sel.sigma r (β : K)‖) ^ 2 = (↑|Algebra.norm ℚ (β : K)| : ℝ) := by
    rw [← Finset.prod_pow]; exact e3
  have hpart1 : (∏ r, ‖sel.sigma r (β : K)‖) = Real.sqrt (|(↑(Algebra.norm ℚ (β : K)) : ℝ)|) := by
    rw [← Rat.cast_abs, ← hsq_eq, Real.sqrt_sq hnn]
  refine ⟨hpart1, ?_⟩
  rw [hpart1]
  -- `|N| ≥ 1` since `β` is a nonzero algebraic integer.
  have hNint : (Algebra.norm ℤ β) ≠ 0 := (Algebra.norm_ne_zero_iff).mpr hβ
  have hge1 : (1 : ℝ) ≤ |(↑(Algebra.norm ℚ (β : K)) : ℝ)| := by
    rw [← Rat.cast_abs]
    have h0 : (1 : ℤ) ≤ |Algebra.norm ℤ β| := Int.one_le_abs hNint
    have hq : (1 : ℚ) ≤ |Algebra.norm ℚ (β : K)| := by
      rw [← Algebra.coe_norm_int β, ← Int.cast_abs]
      exact_mod_cast h0
    exact_mod_cast hq
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (|(↑(Algebra.norm ℚ (β : K)) : ℝ)|) := Real.sqrt_le_sqrt hge1

end MinkowskiLemmas

end Workspace.ProofLemmas

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeNormBound (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    ∀ v ∈ lattice sel DD, v ≠ 0 → (DD : ℝ)⁻¹ ≤ ‖v‖ := by
  intro v hv hne
  obtain ⟨β, hβ⟩ := hv
  -- `β ≠ 0` since `v ≠ 0`.
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβ
    exact hne hβ.symm
  -- Coordinate-wise, `v_r = σ_r β · DD⁻¹`.
  have hcoord : ∀ r, v r = sel.sigma r (β : K) * ((DD : ℂ))⁻¹ := by
    intro r
    have hr := congr_fun hβ r
    rw [← hr]
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hnorm : ∀ r, ‖v r‖ = ‖sel.sigma r (β : K)‖ * (DD : ℝ)⁻¹ := by
    intro r
    rw [hcoord r, norm_mul, norm_inv, Complex.norm_natCast]
  have hprod : (∏ r, ‖v r‖) = (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f := by
    rw [Finset.prod_congr rfl (fun r _ => hnorm r), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnp := (Workspace.ProofLemmas.SublemmaNormProduct hcm sel β hβ0).2
  have hpow_nonneg : (0 : ℝ) ≤ ((DD : ℝ)⁻¹) ^ f := by positivity
  have hprodge : ((DD : ℝ)⁻¹) ^ f ≤ (∏ r, ‖v r‖) := by
    rw [hprod]
    calc ((DD : ℝ)⁻¹) ^ f = 1 * ((DD : ℝ)⁻¹) ^ f := (one_mul _).symm
      _ ≤ (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f :=
          mul_le_mul_of_nonneg_right hnp hpow_nonneg
  -- Sup-norm lower bound by contradiction.
  by_contra hcon
  replace hcon : ‖v‖ < (DD : ℝ)⁻¹ := not_le.mp hcon
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    exact hne (funext (fun i => i.elim0))
  · have hle : (∏ r, ‖v r‖) ≤ ‖v‖ ^ f := by
      calc (∏ r, ‖v r‖) ≤ ∏ _r : Fin f, ‖v‖ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun r _ => norm_le_pi_norm _ r)
        _ = ‖v‖ ^ f := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlt : ‖v‖ ^ f < ((DD : ℝ)⁻¹) ^ f :=
      pow_lt_pow_left₀ hcon (norm_nonneg _) hfpos.ne'
    exact absurd hprodge (not_le.mpr (lt_of_le_of_lt hle hlt))

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeDiscreteTopology (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) := by
  have hbound := SublemmaLatticeNormBound hcm sel DD hDD
  have hDD0 : (0 : ℝ) < (DD : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hDD
  have hDDpos : (0 : ℝ) < (DD : ℝ)⁻¹ := inv_pos.mpr hDD0
  apply discreteTopology_of_isOpen_singleton_zero
  have hset : {(0 : ↥(AddSubgroup.toIntSubmodule (lattice sel DD)))}
      = Subtype.val ⁻¹' (Metric.ball (0 : Fin f → ℂ) ((DD : ℝ)⁻¹)) := by
    ext x
    simp only [Set.mem_singleton_iff, Set.mem_preimage, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl; simpa using hDDpos
    · intro hx
      by_contra hne
      have hxne : (x : Fin f → ℂ) ≠ 0 := fun h => hne (Subtype.ext h)
      have hxlat : (x : Fin f → ℂ) ∈ lattice sel DD := x.2
      exact absurd hx (not_lt.mpr (hbound (x : Fin f → ℂ) hxlat hxne))
  rw [hset]
  exact Metric.isOpen_ball.preimage continuous_subtype_val

end MinkowskiLemmas

set_option maxHeartbeats 4000000

open scoped NumberField ComplexConjugate
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Polynomial

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeRankFull (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) = 2 * f := by
  -- `f = [L : ℚ]`.
  have hfL : f = Module.finrank ℚ L := by
    have h1 : Fintype.card (Fin f) = Fintype.card (L →+* ℂ) :=
      Fintype.card_of_bijective sel.restrict_bijective
    rw [Fintype.card_fin] at h1
    rw [h1, NumberField.Embeddings.card L ℂ]
  have hfpos : 0 < f := by rw [hfL]; exact Module.finrank_pos
  -- `[K : L] = 2`.
  obtain ⟨iota, hsq, hadj⟩ := hcm
  have hint : IsIntegral L iota := ⟨X ^ 2 + 1, by monicity!, by simp [hsq]⟩
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  have hmin_deg : (minpoly L iota).natDegree = 2 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := minpoly.dvd L iota (by simp [hsq])
    have h2le : 2 ≤ (minpoly L iota).natDegree := (minpoly.two_le_natDegree_iff hint).mpr hne
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg2 : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    have hle := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
    omega
  -- `FiniteDimensional L K` (for the tower).
  haveI hfdadj : FiniteDimensional L ↥(IntermediateField.adjoin L {iota}) :=
    IntermediateField.adjoin.finiteDimensional hint
  haveI hfdK : FiniteDimensional L K := by
    have e : ↥(IntermediateField.adjoin L {iota}) ≃ₐ[L] K :=
      (IntermediateField.equivOfEq hadj).trans IntermediateField.topEquiv
    exact e.toLinearEquiv.finiteDimensional
  have hfrankKL : Module.finrank L K = 2 := by
    have h1 : Module.finrank L ↥(IntermediateField.adjoin L {iota}) = (minpoly L iota).natDegree :=
      IntermediateField.adjoin.finrank hint
    rw [hmin_deg, hadj, IntermediateField.finrank_top'] at h1
    exact h1
  -- `[K : ℚ] = 2f`.
  have hfrankQ : Module.finrank ℚ K = 2 * f := by
    have htower := Module.finrank_mul_finrank ℚ L K
    rw [← hfL, hfrankKL] at htower
    omega
  -- `latticeHom` is injective.
  have hcoord : ∀ (γ : 𝓞 K) (r : Fin f),
      latticeHom sel DD γ r = sel.sigma r (γ : K) * ((DD : ℂ))⁻¹ := by
    intro γ r
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hinj : Function.Injective (latticeHom sel DD) := by
    intro β β' hββ'
    have hDDne : (DD : ℂ)⁻¹ ≠ 0 := by
      apply inv_ne_zero
      exact_mod_cast (by omega : DD ≠ 0)
    obtain ⟨r0⟩ : Nonempty (Fin f) := ⟨⟨0, hfpos⟩⟩
    have h0 := congr_fun hββ' r0
    rw [hcoord β r0, hcoord β' r0] at h0
    have hσ : sel.sigma r0 (β : K) = sel.sigma r0 (β' : K) := mul_right_cancel₀ hDDne h0
    have hβK : (β : K) = (β' : K) := (sel.sigma r0).injective hσ
    exact NumberField.RingOfIntegers.coe_injective hβK
  -- Assemble the ℤ-rank chain.
  have hchain : Module.finrank ℤ ↥(AddSubgroup.toIntSubmodule (lattice sel DD))
      = Module.finrank ℤ (𝓞 K) := by
    have e := AddMonoidHom.ofInjective hinj
    rw [show (AddSubgroup.toIntSubmodule (lattice sel DD) : Submodule ℤ (Fin f → ℂ)) =
        AddSubgroup.toIntSubmodule (latticeHom sel DD).range from rfl]
    exact (LinearEquiv.finrank_eq (AddEquiv.toIntLinearEquiv e)).symm
  rw [hchain, NumberField.RingOfIntegers.rank]
  exact hfrankQ

end MinkowskiLemmas

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaMinkowskiMapIsFullLattice (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) ∧
      @IsZLattice ℝ _ _ _ _ (AddSubgroup.toIntSubmodule (lattice sel DD))
        (SublemmaLatticeDiscreteTopology hcm sel DD hDD) := by
  haveI hdisc : DiscreteTopology ↥(AddSubgroup.toIntSubmodule (lattice sel DD)) :=
    SublemmaLatticeDiscreteTopology hcm sel DD hDD
  refine ⟨hdisc, ?_⟩
  set Lsub : Submodule ℤ (Fin f → ℂ) := AddSubgroup.toIntSubmodule (lattice sel DD) with hLsub
  set s : Set (Fin f → ℂ) := (↑Lsub : Set (Fin f → ℂ)) with hs
  -- `span ℤ s = Lsub` since `Lsub` is already a `ℤ`-submodule.
  have hspanZ : Submodule.span ℤ s = Lsub := Submodule.span_eq Lsub
  haveI hdisc' : DiscreteTopology ↥(Submodule.span ℤ s) := by rw [hspanZ]; exact hdisc
  -- discreteness ⇒ `dim_ℝ (span ℝ s) = rank_ℤ (span ℤ s)`.
  have hfr : Set.finrank ℝ s = Set.finrank ℤ s :=
    Real.finrank_eq_int_finrank_of_discrete hdisc'
  -- `rank_ℤ = 2f`.
  have hZ : Set.finrank ℤ s = 2 * f := by
    show Module.finrank ℤ ↥(Submodule.span ℤ s) = 2 * f
    rw [hspanZ]; exact SublemmaLatticeRankFull hcm sel DD hDD
  -- ambient dimension is also `2f`.
  have hfrankE : Module.finrank ℝ (Fin f → ℂ) = 2 * f := by
    rw [Module.finrank_pi_fintype ℝ]
    simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  -- Hence `span ℝ s = ⊤`.
  have hspanR_top : Submodule.span ℝ s = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    show Module.finrank ℝ ↥(Submodule.span ℝ s) = Module.finrank ℝ (Fin f → ℂ)
    rw [← Set.finrank, hfr, hZ, hfrankE]
  exact IsZLattice.mk hspanR_top

end MinkowskiLemmas

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeFundamentalDomain (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    ∃ F : Set (Fin f → ℂ),
      MeasureTheory.IsAddFundamentalDomain (↥(lattice sel DD)) F volume ∧
        0 < volume F ∧ volume F < ⊤ := by
  obtain ⟨hdisc, hzl⟩ := SublemmaMinkowskiMapIsFullLattice hcm sel DD hDD
  letI := hdisc
  letI := hzl
  set Lsub : Submodule ℤ (Fin f → ℂ) := AddSubgroup.toIntSubmodule (lattice sel DD) with hLsub
  haveI : Module.Free ℤ ↥Lsub := ZLattice.module_free ℝ Lsub
  haveI : Module.Finite ℤ ↥Lsub := ZLattice.module_finite ℝ Lsub
  set b : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥Lsub) ℤ ↥Lsub :=
    Module.Free.chooseBasis ℤ ↥Lsub with hb
  set bR : Module.Basis (Module.Free.ChooseBasisIndex ℤ ↥Lsub) ℝ (Fin f → ℂ) :=
    Module.Basis.ofZLatticeBasis ℝ Lsub b with hbR
  refine ⟨ZSpan.fundamentalDomain bR, ?_, ?_, ?_⟩
  · exact ZLattice.isAddFundamentalDomain b volume
  · exact pos_iff_ne_zero.mpr (ZSpan.measure_fundamentalDomain_ne_zero bR)
  · exact (ZSpan.fundamentalDomain_isBounded bR).measure_lt_top

end MinkowskiLemmas

open scoped NumberField
open Workspace.Types.MinkowskiWindow Workspace.Types.CMAdjoinI

namespace Workspace.ProofLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaSeparation (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (a : Fin f → ℂ) :
    ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      ‖x - x'‖ ≥ (DD : ℝ)⁻¹ := by
  intro x hx x' hx' hne
  -- `x - x'` is a lattice vector, hence `= latticeHom sel DD β` for some `β ∈ 𝓞 K`.
  have hlat : x - x' ∈ lattice sel DD := by
    have h1 : x - a ∈ lattice sel DD := hx.1
    have h2 : x' - a ∈ lattice sel DD := hx'.1
    have h3 := AddSubgroup.sub_mem _ h1 h2
    simpa [sub_sub_sub_cancel_right] using h3
  obtain ⟨β, hβ⟩ := hlat
  -- `β ≠ 0` since `x ≠ x'`.
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβ
    exact hne (sub_eq_zero.mp hβ.symm)
  -- Coordinate-wise, `(x - x')_r = σ_r β · DD⁻¹`.
  have hcoord : ∀ r, (x - x') r = sel.sigma r (β : K) * ((DD : ℂ))⁻¹ := by
    intro r
    have hr := congr_fun hβ r
    rw [← hr]
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hnorm : ∀ r, ‖(x - x') r‖ = ‖sel.sigma r (β : K)‖ * (DD : ℝ)⁻¹ := by
    intro r
    rw [hcoord r, norm_mul, norm_inv, Complex.norm_natCast]
  -- Product of coordinate moduli.
  have hprod : (∏ r, ‖(x - x') r‖)
      = (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f := by
    rw [Finset.prod_congr rfl (fun r _ => hnorm r), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Lower bound `≥ DD^{-f}` from `SublemmaNormProduct`.
  have hnp := (Workspace.ProofLemmas.SublemmaNormProduct hcm sel β hβ0).2
  have hpow_nonneg : (0 : ℝ) ≤ ((DD : ℝ)⁻¹) ^ f := by positivity
  have hprodge : ((DD : ℝ)⁻¹) ^ f ≤ (∏ r, ‖(x - x') r‖) := by
    rw [hprod]
    calc ((DD : ℝ)⁻¹) ^ f = 1 * ((DD : ℝ)⁻¹) ^ f := (one_mul _).symm
      _ ≤ (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f :=
          mul_le_mul_of_nonneg_right hnp hpow_nonneg
  -- Separation by contradiction.
  by_contra hcon
  replace hcon : ‖x - x'‖ < (DD : ℝ)⁻¹ := not_le.mp hcon
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    exact hne (funext (fun i => i.elim0))
  · have hle : (∏ r, ‖(x - x') r‖) ≤ ‖x - x'‖ ^ f := by
      calc (∏ r, ‖(x - x') r‖) ≤ ∏ _r : Fin f, ‖x - x'‖ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun r _ => norm_le_pi_norm _ r)
        _ = ‖x - x'‖ ^ f := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlt : ‖x - x'‖ ^ f < ((DD : ℝ)⁻¹) ^ f :=
      pow_lt_pow_left₀ hcon (norm_nonneg _) hfpos.ne'
    exact absurd hprodge (not_le.mpr (lt_of_le_of_lt hle hlt))

end Workspace.ProofLemmas

open scoped NumberField
open MeasureTheory
open Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 800000

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaPacking
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 0 < R) (a : Fin f → ℂ)
    (hsep : ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      (DD : ℝ)⁻¹ ≤ ‖x - x'‖) :
    (Xset sel DD R a).Finite ∧
      (Ncount sel DD R a : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := by
  have hDD0 : (0 : ℝ) < (DD : ℝ) := by exact_mod_cast hDD
  set ρ : ℝ := (DD : ℝ)⁻¹ / 2 with hρ_def
  have hρ : 0 < ρ := by rw [hρ_def]; positivity
  -- Volume constants.
  set V : ENNReal := (ENNReal.ofReal ρ ^ 2 * (NNReal.pi : ENNReal)) ^ f with hV_def
  set Vbig : ENNReal := (ENNReal.ofReal (R + ρ) ^ 2 * (NNReal.pi : ENNReal)) ^ f with hVbig_def
  have hV_ne : V ≠ ⊤ := by rw [hV_def]; finiteness
  have hVbig_ne : Vbig ≠ ⊤ := by rw [hVbig_def]; finiteness
  have hVtoReal : V.toReal = (ρ ^ 2 * Real.pi) ^ f := by
    rw [hV_def, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρ.le, ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hVbigtoReal : Vbig.toReal = ((R + ρ) ^ 2 * Real.pi) ^ f := by
    rw [hVbig_def, ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ R + ρ), ENNReal.coe_toReal, NNReal.coe_real_pi]
  have hVtoReal_pos : 0 < V.toReal := by rw [hVtoReal]; positivity
  -- Volume of a small ball (constant, translation-invariant).
  have hballvol : ∀ x : Fin f → ℂ, volume (Metric.ball x ρ) = V := by
    intro x
    rw [ball_pi x hρ, volume_pi, Measure.pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hV_def]
  -- Volume of the enlarged window ball.
  have hbigvol : volume (Metric.ball (0 : Fin f → ℂ) (R + ρ)) = Vbig := by
    rw [ball_pi (0 : Fin f → ℂ) (by positivity : (0:ℝ) < R + ρ), volume_pi, Measure.pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hVbig_def]
  -- The core packing bound on every finite subset.
  have hbound : ∀ S : Finset (Fin f → ℂ), (↑S ⊆ Xset sel DD R a) →
      (S.card : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := by
    intro S hSsub
    -- Disjointness of the balls of radius ρ.
    have hdisj : (↑S : Set (Fin f → ℂ)).PairwiseDisjoint (fun x => Metric.ball x ρ) := by
      intro x hx y hy hxy
      apply Metric.ball_disjoint_ball
      rw [dist_eq_norm]
      have hs := hsep x (hSsub hx) y (hSsub hy) hxy
      have hρsum : ρ + ρ = (DD : ℝ)⁻¹ := by rw [hρ_def]; ring
      rw [hρsum]; exact hs
    have hmeas : ∀ b ∈ S, MeasurableSet (Metric.ball b ρ) := fun b _ => measurableSet_ball
    -- Containment in the enlarged window ball.
    have hsub : (⋃ x ∈ S, Metric.ball x ρ) ⊆ Metric.ball (0 : Fin f → ℂ) (R + ρ) := by
      intro y hy
      simp only [Set.mem_iUnion] at hy
      obtain ⟨x, hxS, hyx⟩ := hy
      rw [Metric.mem_ball, dist_zero_right]
      rw [Metric.mem_ball, dist_eq_norm] at hyx
      have hxwin : ‖x‖ ≤ R := by
        have hxX : x ∈ Xset sel DD R a := hSsub hxS
        rw [pi_norm_le_iff_of_nonneg hR.le]
        intro i
        exact hxX.2 i
      have htri : ‖y‖ ≤ ‖x‖ + ‖y - x‖ := by
        have := norm_add_le x (y - x)
        simpa using this
      linarith
    -- Packing inequality in ENNReal.
    have hpack : (S.card : ENNReal) * V ≤ Vbig := by
      calc (S.card : ENNReal) * V
          = ∑ _x ∈ S, V := by rw [Finset.sum_const, nsmul_eq_mul]
        _ = ∑ x ∈ S, volume (Metric.ball x ρ) := by
            exact (Finset.sum_congr rfl (fun x _ => (hballvol x).symm))
        _ = volume (⋃ x ∈ S, Metric.ball x ρ) := (measure_biUnion_finset hdisj hmeas).symm
        _ ≤ volume (Metric.ball (0 : Fin f → ℂ) (R + ρ)) := measure_mono hsub
        _ = Vbig := hbigvol
    -- Convert to reals.
    have hpackR : (S.card : ℝ) * V.toReal ≤ Vbig.toReal := by
      have hle : ((S.card : ENNReal) * V).toReal ≤ Vbig.toReal :=
        (ENNReal.toReal_le_toReal (by finiteness) hVbig_ne).mpr hpack
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle
    -- Ratio identity.
    have hkey : (1 + 2 * R * (DD : ℝ)) * ρ = R + ρ := by
      rw [hρ_def]; field_simp; ring
    have hratio : Vbig.toReal = (1 + 2 * R * (DD : ℝ)) ^ (2 * f) * V.toReal := by
      rw [hVbigtoReal, hVtoReal, pow_mul, ← mul_pow]
      congr 1
      have hsq : ((1 + 2 * R * (DD : ℝ)) ^ 2) * ρ ^ 2 = (R + ρ) ^ 2 := by
        rw [← mul_pow, hkey]
      rw [← hsq]; ring
    rw [hratio] at hpackR
    exact le_of_mul_le_mul_right hpackR hVtoReal_pos
  -- Finiteness from the uniform bound.
  have hfin : (Xset sel DD R a).Finite := by
    by_contra hinf
    rw [Set.not_finite] at hinf
    obtain ⟨S, hSsub, hScard⟩ :=
      hinf.exists_subset_card_eq (⌈(1 + 2 * R * (DD : ℝ)) ^ (2 * f)⌉₊ + 1)
    have hb := hbound S hSsub
    rw [hScard] at hb
    have hceil : (1 + 2 * R * (DD : ℝ)) ^ (2 * f) ≤ (⌈(1 + 2 * R * (DD : ℝ)) ^ (2 * f)⌉₊ : ℝ) :=
      Nat.le_ceil _
    push_cast at hb
    linarith
  refine ⟨hfin, ?_⟩
  -- Cardinality bound.
  have hcard_eq : Ncount sel DD R a = hfin.toFinset.card := by
    rw [Ncount, Set.ncard_eq_toFinset_card _ hfin]
  rw [hcard_eq]
  exact hbound hfin.toFinset (Set.Finite.coe_toFinset hfin).subset

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeDiscrete (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ) :
    (∀ a : Fin f → ℂ, (Xset sel DD R a).Finite) ∧
      (∀ (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ),
        {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.Finite) := by
  -- Every window intersection is finite.
  have hXfin : ∀ a : Fin f → ℂ, (Xset sel DD R a).Finite := by
    intro a
    by_cases hR : R ≤ 0
    · -- If `R ≤ 0` the window is contained in `{0}` (each coordinate norm is forced to `0`),
      -- so the coset intersection is finite.
      have hwin : (window (f := f) R).Finite := by
        apply Set.Finite.subset (Set.finite_singleton (0 : Fin f → ℂ))
        intro z hz
        simp only [window, Set.mem_setOf_eq] at hz
        rw [Set.mem_singleton_iff]
        funext r
        have hzr : ‖z r‖ = 0 := le_antisymm (le_trans (hz r) hR) (norm_nonneg _)
        simpa using norm_eq_zero.mp hzr
      exact Set.Finite.subset hwin (fun z hz => hz.2)
    · -- If `R > 0`, use the lattice separation bound and the packing count.
      rw [not_le] at hR
      have hsep := Workspace.ProofLemmas.SublemmaSeparation hcm sel DD hDD R a
      exact (SublemmaPacking sel DD hDD R hR a hsep).1
  refine ⟨hXfin, ?_⟩
  -- The `Ecount` index set is a subset of `Xset × Xset`, hence finite.
  intro U a
  apply Set.Finite.subset ((hXfin a).prod (hXfin a))
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

end MinkowskiLemmas

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaNcountEqTsum (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ)
    (a : Fin f → ℂ) :
    (Ncount sel DD R a : ℝ) = ∑' l : ↥(lattice sel DD),
      (window R).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
  classical
  -- The lattice points landing in the window.
  set T : Set (↥(lattice sel DD)) :=
    {l | a + (l : Fin f → ℂ) ∈ window R} with hTdef
  have he_inj : Function.Injective (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) :=
    fun l1 l2 h => Subtype.ext (add_left_cancel h)
  -- The window-indicator periodization equals `T.indicator 1`.
  have hT : ∀ l : ↥(lattice sel DD),
      (window R).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ))
        = T.indicator (fun _ => (1 : ℝ)) l := by
    intro l
    simp only [Set.indicator_apply, hTdef, Set.mem_setOf_eq]
  -- Collapse the tsum to the cardinality of `T`.
  rw [tsum_congr hT, ← tsum_subtype]
  simp only [tsum_const, nsmul_eq_mul, mul_one, Nat.card_coe_set_eq]
  -- `T.ncard = (Xset ...).ncard`.
  have himg : (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) '' T = Xset sel DD R a := by
    ext z
    constructor
    · rintro ⟨l, hl, rfl⟩
      refine ⟨?_, hl⟩
      show (a + (l : Fin f → ℂ)) - a ∈ lattice sel DD
      rw [add_sub_cancel_left]; exact l.2
    · rintro ⟨hz1, hz2⟩
      refine ⟨⟨z - a, hz1⟩, ?_, ?_⟩
      · show a + (z - a) ∈ window R
        rw [show a + (z - a) = z from by abel]; exact hz2
      · show a + (z - a) = z
        abel
  have hncard : (Xset sel DD R a).ncard = T.ncard := by
    rw [← himg]; exact Set.ncard_image_of_injective T he_inj
  show ((Xset sel DD R a).ncard : ℝ) = (T.ncard : ℝ)
  exact_mod_cast hncard

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaEcountDecomp (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ) (hfin : (Xset sel DD R a).Finite) :
    Ecount sel DD R U a =
      ∑ u ∈ U, {x | x ∈ Xset sel DD R a ∧ x + u ∈ Xset sel DD R a}.ncard := by
  classical
  set X := Xset sel DD R a with hXdef
  set XF := hfin.toFinset with hXFdef
  have hmem : ∀ x, x ∈ XF ↔ x ∈ X := fun x => Set.Finite.mem_toFinset hfin
  -- The `Ecount` index set as a `Finset`.
  set IF : Finset ((Fin f → ℂ) × (Fin f → ℂ)) :=
    (XF ×ˢ XF).filter (fun p => p.2 - p.1 ∈ U) with hIFdef
  have hIFmem : ∀ p, p ∈ IF ↔ (p.1 ∈ X ∧ p.2 ∈ X ∧ p.2 - p.1 ∈ U) := by
    intro p
    rw [hIFdef, Finset.mem_filter, Finset.mem_product, hmem, hmem]
    tauto
  -- `Ecount = IF.card`.
  have hEcard : Ecount sel DD R U a = IF.card := by
    have hE : Ecount sel DD R U a =
        {p : (Fin f → ℂ) × (Fin f → ℂ) | p.1 ∈ X ∧ p.2 ∈ X ∧ p.2 - p.1 ∈ U}.ncard := rfl
    rw [hE, ← Set.ncard_coe_finset IF]
    congr 1
    ext p
    rw [Set.mem_setOf_eq, Finset.mem_coe, hIFmem]
  rw [hEcard]
  -- Fiber the pairs over their difference `u = p.2 - p.1`.
  have hmaps : Set.MapsTo (fun p : (Fin f → ℂ) × (Fin f → ℂ) => p.2 - p.1) ↑IF ↑U := by
    intro p hp
    rw [Finset.mem_coe] at hp
    rw [Finset.mem_coe]
    exact ((hIFmem p).1 hp).2.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro u hu
  -- The `u`-fiber count equals the shift-count `#{x ∈ X | x + u ∈ X}`.
  set AF : Finset (Fin f → ℂ) := XF.filter (fun x => x + u ∈ X) with hAFdef
  have hAFmem : ∀ x, x ∈ AF ↔ (x ∈ X ∧ x + u ∈ X) := by
    intro x; rw [hAFdef, Finset.mem_filter, hmem]
  have hAcard : {x | x ∈ X ∧ x + u ∈ X}.ncard = AF.card := by
    rw [← Set.ncard_coe_finset AF]
    congr 1
    ext x
    rw [Set.mem_setOf_eq, Finset.mem_coe, hAFmem]
  rw [hAcard]
  -- Bijection `p ↦ p.1` between the `u`-fiber and `AF`, inverse `x ↦ (x, x + u)`.
  apply Finset.card_nbij' (fun p => p.1) (fun x => (x, x + u))
  · -- maps the fiber into `AF`
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨hpIF, hpu⟩ := hp
    rw [Finset.mem_coe, hAFmem]
    have hx : p.1 ∈ X := ((hIFmem p).1 hpIF).1
    have hp2 : p.2 ∈ X := ((hIFmem p).1 hpIF).2.1
    have hsum : p.1 + u = p.2 := by rw [← hpu]; ring
    exact ⟨hx, by rw [hsum]; exact hp2⟩
  · -- maps `AF` into the fiber
    intro x hx
    rw [Finset.mem_coe, hAFmem] at hx
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨(hIFmem (x, x + u)).2 ⟨hx.1, ?_, ?_⟩, ?_⟩
    · exact hx.2
    · simpa using hu
    · simp
  · -- left inverse on the fiber
    intro p hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    obtain ⟨_, hpu⟩ := hp
    have hsum : p.1 + u = p.2 := by rw [← hpu]; ring
    apply Prod.ext
    · rfl
    · simpa using hsum
  · -- right inverse on `AF`
    intro x _
    rfl

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaEcountEqSumTsum (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (a : Fin f → ℂ) :
    (Ecount sel DD R U a : ℝ) = ∑ u ∈ U, ∑' l : ↥(lattice sel DD),
      (window R ∩ (window R - {u})).indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
  classical
  have hfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
  have he_inj : Function.Injective (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) :=
    fun l1 l2 h => Subtype.ext (add_left_cancel h)
  -- General periodization bridge (same as Ncount, for an arbitrary window set `S`).
  have hgen : ∀ S : Set (Fin f → ℂ),
      (({z | z - a ∈ lattice sel DD} ∩ S).ncard : ℝ)
        = ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) := by
    intro S
    set T : Set (↥(lattice sel DD)) := {l | a + (l : Fin f → ℂ) ∈ S} with hTdef
    have hT : ∀ l : ↥(lattice sel DD),
        S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ)) = T.indicator (fun _ => (1 : ℝ)) l := by
      intro l; simp only [Set.indicator_apply, hTdef, Set.mem_setOf_eq]
    rw [tsum_congr hT, ← tsum_subtype]
    simp only [tsum_const, nsmul_eq_mul, mul_one, Nat.card_coe_set_eq]
    have himg : (fun l : ↥(lattice sel DD) => a + (l : Fin f → ℂ)) '' T
        = {z | z - a ∈ lattice sel DD} ∩ S := by
      ext z
      constructor
      · rintro ⟨l, hl, rfl⟩
        refine ⟨?_, hl⟩
        show (a + (l : Fin f → ℂ)) - a ∈ lattice sel DD
        rw [add_sub_cancel_left]; exact l.2
      · rintro ⟨hz1, hz2⟩
        refine ⟨⟨z - a, hz1⟩, ?_, ?_⟩
        · show a + (z - a) ∈ S
          rw [show a + (z - a) = z from by abel]; exact hz2
        · show a + (z - a) = z
          abel
    have hncard : ({z | z - a ∈ lattice sel DD} ∩ S).ncard = T.ncard := by
      rw [← himg]; exact Set.ncard_image_of_injective T he_inj
    exact_mod_cast hncard
  -- Expand `Ecount` via the finite fiber decomposition, then bridge each fiber.
  rw [SublemmaEcountDecomp sel DD R U a hfin]
  push_cast
  apply Finset.sum_congr rfl
  intro u hu
  -- For this `u ∈ U` (so `u ∈ Λ`), rewrite the fiber set and apply the periodization bridge.
  have hu_lat := hU_lat u hu
  have hsub_iff : ∀ y : Fin f → ℂ, y ∈ window R - {u} ↔ y + u ∈ window R := by
    intro y
    rw [Set.mem_sub]
    constructor
    · rintro ⟨p, hp, q, hq, hpq⟩
      rw [Set.mem_singleton_iff] at hq; subst hq
      rw [← hpq]; simpa using hp
    · intro hy
      exact ⟨y + u, hy, u, Set.mem_singleton u, by abel⟩
  have hset : {x | x ∈ Xset sel DD R a ∧ x + u ∈ Xset sel DD R a}
      = {z | z - a ∈ lattice sel DD} ∩ (window R ∩ (window R - {u})) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Xset]
    constructor
    · rintro ⟨⟨hxΛ, hxw⟩, _, hxuw⟩
      exact ⟨hxΛ, hxw, (hsub_iff x).mpr hxuw⟩
    · rintro ⟨hxΛ, hxw, hxsub⟩
      have hxuw : x + u ∈ window R := (hsub_iff x).mp hxsub
      refine ⟨⟨hxΛ, hxw⟩, ?_, hxuw⟩
      rw [show x + u - a = (x - a) + u from by abel]
      exact AddSubgroup.add_mem _ hxΛ hu_lat
  rw [hset, hgen]

end MinkowskiLemmas

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaHaarUnfolding (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (F : Set (Fin f → ℂ))
    (hF : IsAddFundamentalDomain (↥(lattice sel DD)) F)
    (S : Set (Fin f → ℂ)) (hS : MeasurableSet S) (hSbdd : Bornology.IsBounded S) :
    ∫ a in F, (∑' l : ↥(lattice sel DD),
        (S.indicator (fun _ => (1 : ℝ))) (a + (l : Fin f → ℂ)))
      = (volume S).toReal := by
  classical
  -- Countability of the lattice (needed by the unfolding lemmas).
  haveI hcountOK : Countable (𝓞 K) := by
    have b := Module.Free.chooseBasis ℤ (𝓞 K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI hcountLat : Countable (↥(lattice sel DD)) := by
    have hc : ((lattice sel DD : Set (Fin f → ℂ))).Countable := by
      rw [lattice, AddMonoidHom.coe_range]; exact Set.countable_range _
    exact hc.to_subtype
  set g : (Fin f → ℂ) → ℝ := S.indicator (fun _ => (1 : ℝ)) with hgdef
  have hgmeas : Measurable g := by rw [hgdef]; exact measurable_const.indicator hS
  have hSvol : volume S ≠ ⊤ := hSbdd.measure_lt_top.ne
  -- `g` is integrable.
  have hgint : Integrable g volume := by
    rw [hgdef, integrable_indicator_iff hS]
    exact integrableOn_const hSvol (by simp)
  -- `∫ g = vol S`.
  have hInt : ∫ x, g x = (volume S).toReal := by
    have hg1 : g = S.indicator (1 : (Fin f → ℂ) → ℝ) := by rw [hgdef, Pi.one_def]
    rw [hg1, integral_indicator_one hS]; rfl
  -- The unfolding identity `∫ g = ∑' l, ∫_F g (l +ᵥ x)`.
  have hUnfold := hF.integral_eq_tsum'' g hgint
  -- AE-strong measurability of each shifted summand.
  have haemeas : ∀ l : ↥(lattice sel DD),
      AEStronglyMeasurable (fun a => g (l +ᵥ a)) (volume.restrict F) :=
    fun l => (hgmeas.comp (measurable_const_vadd l)).aestronglyMeasurable
  -- Summability bound for swapping the sum and the integral.
  have hsum_ne : ∑' l : ↥(lattice sel DD),
      ∫⁻ a, ‖g (l +ᵥ a)‖ₑ ∂(volume.restrict F) ≠ ⊤ := by
    rw [← hF.lintegral_eq_tsum'' (fun x => ‖g x‖ₑ)]
    have hnorm : (fun x => ‖g x‖ₑ) = S.indicator (1 : (Fin f → ℂ) → ENNReal) := by
      funext x
      by_cases hx : x ∈ S <;> simp [hgdef, Set.indicator_apply, hx]
    rw [hnorm, lintegral_indicator_one hS]
    exact hSvol
  -- Convert the goal's `a + ↑l` into the `+ᵥ` action, then unfold.
  have hpt : ∀ (a : Fin f → ℂ) (l : ↥(lattice sel DD)),
      g (a + (l : Fin f → ℂ)) = g (l +ᵥ a) := by
    intro a l
    rw [show (l +ᵥ a) = (l : Fin f → ℂ) + a from rfl, add_comm]
  simp only [hpt]
  rw [integral_tsum haemeas hsum_ne, ← hUnfold]
  exact hInt

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem SublemmaWindowVolume {f : ℕ} (R : ℝ) (hR : 0 ≤ R) :
    volume (window (f := f) R) = ENNReal.ofReal (discArea R ^ f) := by
  -- `window R` is the product of `f` closed discs of radius `R` centred at `0`.
  have hwin : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext z
    simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  rw [hwin, volume_pi, Measure.pi_pi]
  simp only [Complex.volume_closedBall]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [discArea, ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ Real.pi * R ^ 2)]
  congr 1
  have hpi : (↑NNReal.pi : ENNReal) = ENNReal.ofReal Real.pi := by
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [ENNReal.ofReal_mul Real.pi_nonneg, ← ENNReal.ofReal_pow hR, hpi, mul_comm]

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaOverlapVolume (hcm : IsAdjoinI L K)
    (R : ℝ) (u : Fin f → ℂ) (hU_coord : ∀ r, ‖u r‖ = 1) :
    volume (window (f := f) R ∩ (window (f := f) R - {u})) =
      ENNReal.ofReal (overlapArea R ^ f) := by
  -- Per-coordinate: the overlap of two radius-`R` discs at centre distance `1`
  -- has the same volume as the reference pair `(0, 1)`, by rotation invariance.
  have hcoordVol : ∀ c : ℂ, ‖c‖ = 1 →
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = ENNReal.ofReal (overlapArea R) := by
    intro c hc
    set a : Circle := ⟨c, mem_sphere_zero_iff_norm.mpr hc⟩ with ha
    have hac : (a : ℂ) = c := rfl
    have hiso : Isometry (rotation a) := (rotation a).isometry
    have h0 : (rotation a) 0 = 0 := by rw [rotation_apply, mul_zero]
    have h1 : (rotation a) 1 = c := by rw [rotation_apply, mul_one, hac]
    have e0 : (rotation a) ⁻¹' Metric.closedBall (0 : ℂ) R = Metric.closedBall (0 : ℂ) R := by
      have h := hiso.preimage_closedBall 0 R
      rwa [h0] at h
    have e1 : (rotation a) ⁻¹' Metric.closedBall c R = Metric.closedBall (1 : ℂ) R := by
      have h := hiso.preimage_closedBall 1 R
      rwa [h1] at h
    have hpre : (rotation a) ⁻¹' (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R := by
      rw [Set.preimage_inter, e0, e1]
    have hmeas : MeasurableSet (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R) :=
      measurableSet_closedBall.inter measurableSet_closedBall
    have hmp := (rotation a).measurePreserving
    have hcoord : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R)
        = volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) := by
      have hh := hmp.measure_preimage
        (s := Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall c R) hmeas.nullMeasurableSet
      rw [hpre] at hh
      exact hh.symm
    have hfin1 : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
      apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
      rw [Complex.volume_closedBall]; finiteness
    rw [hcoord, overlapArea, ENNReal.ofReal_toReal hfin1]
  -- `window R` and its `u`-translate as products of discs.
  have hwin : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
    ext z
    simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
  have hwinu : window (f := f) R - {u}
      = Set.univ.pi (fun r : Fin f => Metric.closedBall (-u r) R) := by
    ext z
    constructor
    · rw [Set.mem_sub]
      rintro ⟨x, hx, y, hy, hxy⟩
      rw [Set.mem_singleton_iff] at hy
      subst y
      subst hxy
      simp only [window, Set.mem_setOf_eq] at hx
      simp only [Set.mem_univ_pi, Metric.mem_closedBall]
      intro r
      rw [Complex.dist_eq, Pi.sub_apply]
      have hxx : x r - u r - -u r = x r := by ring
      rw [hxx]; exact hx r
    · intro hz
      simp only [Set.mem_univ_pi, Metric.mem_closedBall] at hz
      rw [Set.mem_sub]
      refine ⟨z + u, ?_, u, Set.mem_singleton u, by ring⟩
      simp only [window, Set.mem_setOf_eq]
      intro r
      have hzr := hz r
      rw [Complex.dist_eq] at hzr
      rw [Pi.add_apply]
      have hzz : z r - -u r = z r + u r := by ring
      rw [hzz] at hzr
      exact hzr
  -- Assemble via Fubini.
  rw [hwinu, hwin, ← Set.pi_inter_distrib, volume_pi, Measure.pi_pi]
  have hfactor : ∀ r : Fin f,
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (-u r) R)
        = ENNReal.ofReal (overlapArea R) :=
    fun r => hcoordVol (-u r) (by rw [norm_neg]; exact hU_coord r)
  simp only [hfactor]
  have hnn : (0 : ℝ) ≤ overlapArea R := ENNReal.toReal_nonneg
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hnn]

end MinkowskiLemmas

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory

section MinkowskiLemmas

variable {f : ℕ}

theorem SublemmaAveragingPigeonhole
    (F : Set (Fin f → ℂ)) (hFpos : 0 < volume F) (hFfin : volume F < ⊤)
    (N E : (Fin f → ℂ) → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hNmeas : Measurable N) (hEmeas : Measurable E)
    (hNnonneg : ∀ a, 0 ≤ N a) (hEnonneg : ∀ a, 0 ≤ E a)
    (hNint : MeasureTheory.IntegrableOn N F volume)
    (hEint : MeasureTheory.IntegrableOn E F volume)
    (hempty : ∀ a, N a = 0 → E a = 0)
    (hEq : ∫ a in F, E a = c * ∫ a in F, N a)
    (hNpos : 0 < ∫ a in F, N a) :
    ∃ a, 0 < N a ∧ c * N a ≤ E a := by
  by_contra hcon
  push_neg at hcon
  -- `hcon : ∀ a, 0 < N a → E a < c * N a`
  set g : (Fin f → ℂ) → ℝ := fun a => c * N a - E a with hgdef
  have hgnonneg : ∀ a, 0 ≤ g a := by
    intro a
    rcases eq_or_lt_of_le (hNnonneg a) with h0 | hpos
    · have hE0 := hempty a h0.symm
      simp [hgdef, ← h0, hE0]
    · have hlt := hcon a hpos
      simp only [hgdef]; linarith
  have hgint : IntegrableOn g F volume := by
    simpa [hgdef] using (hNint.const_mul c).sub hEint
  -- `∫_F g = 0`.
  have hgint0 : ∫ a in F, g a = 0 := by
    have h1 : ∫ a in F, g a = (∫ a in F, c * N a) - ∫ a in F, E a :=
      integral_sub (hNint.const_mul c) hEint
    rw [integral_const_mul] at h1
    rw [h1, hEq]; ring
  -- Support of `N` (within `F`) has positive measure.
  have hNae : (0 : (Fin f → ℂ) → ℝ) ≤ᶠ[ae (volume.restrict F)] N := ae_of_all _ hNnonneg
  have hNsupp : 0 < volume (Function.support N ∩ F) :=
    (setIntegral_pos_iff_support_of_nonneg_ae hNae hNint).mp hNpos
  -- `support N ⊆ support g` (within `F`).
  have hsubset : Function.support N ∩ F ⊆ Function.support g ∩ F := by
    rintro a ⟨ha1, ha2⟩
    refine ⟨?_, ha2⟩
    rw [Function.mem_support] at ha1 ⊢
    have hNa : 0 < N a := lt_of_le_of_ne (hNnonneg a) (Ne.symm ha1)
    have hlt := hcon a hNa
    simp only [hgdef]
    intro hg0; linarith
  -- Hence `∫_F g > 0`, contradicting `∫_F g = 0`.
  have hgae : (0 : (Fin f → ℂ) → ℝ) ≤ᶠ[ae (volume.restrict F)] g := ae_of_all _ hgnonneg
  have hgpos : 0 < ∫ a in F, g a := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae hgae hgint]
    exact lt_of_lt_of_le hNsupp (measure_mono hsubset)
  linarith

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open MeasureTheory Pointwise

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaAveragingExists (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R)
    (U : Finset (Fin f → ℂ))
    (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (hU_ne : ∀ u ∈ U, u ≠ 0)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1) :
    ∃ a : Fin f → ℂ, (Xset sel DD R a).Nonempty ∧
      (Ecount sel DD R U a : ℝ) ≥
        (U.card : ℝ) * rho R ^ f * (Ncount sel DD R a : ℝ) := by
  classical
  obtain ⟨F, hFfund, hFpos, hFfin⟩ := SublemmaLatticeFundamentalDomain hcm sel DD hDD
  -- Countability of the lattice.
  haveI hcountOK : Countable (𝓞 K) := by
    have b := Module.Free.chooseBasis ℤ (𝓞 K)
    exact Countable.of_equiv _ b.equivFun.toEquiv.symm
  haveI hcountLat : Countable (↥(lattice sel DD)) := by
    have hc : ((lattice sel DD : Set (Fin f → ℂ))).Countable := by
      rw [lattice, AddMonoidHom.coe_range]; exact Set.countable_range _
    exact hc.to_subtype
  -- Periodization function.
  set P : Set (Fin f → ℂ) → (Fin f → ℂ) → ℝ :=
    fun S a => ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ℝ)) (a + (l : Fin f → ℂ))
    with hP
  -- Helper: for a bounded measurable `S`, `P S` is measurable, integrable on `F`, and
  -- `∫_F P S = (vol S).toReal`.
  have helper : ∀ (S : Set (Fin f → ℂ)), MeasurableSet S → Bornology.IsBounded S →
      Measurable (P S) ∧ IntegrableOn (P S) F volume ∧ ∫ a in F, P S a = (volume S).toReal := by
    intro S hSmeas hSbdd
    set M : (Fin f → ℂ) → ENNReal :=
      fun a => ∑' l : ↥(lattice sel DD), S.indicator (fun _ => (1 : ENNReal)) (a + (l : Fin f → ℂ))
      with hM
    have hsummeas : ∀ l : ↥(lattice sel DD),
        Measurable (fun a : Fin f → ℂ => S.indicator (fun _ => (1 : ENNReal)) (a + (l : Fin f → ℂ))) :=
      fun l => (measurable_const.indicator hSmeas).comp (measurable_add_const _)
    have hMmeas : Measurable M := Measurable.ennreal_tsum hsummeas
    have hNM : ∀ a, P S a = (M a).toReal := by
      intro a
      rw [hP, hM, ENNReal.tsum_toReal_eq (fun l => ?_)]
      · exact tsum_congr fun l => by
          by_cases h : a + (l : Fin f → ℂ) ∈ S <;> simp [h]
      · by_cases h : a + (l : Fin f → ℂ) ∈ S <;> simp [h]
    have hPmeas : Measurable (P S) := by
      have : P S = fun a => (M a).toReal := funext hNM
      rw [this]; exact hMmeas.ennreal_toReal
    have hPnonneg : ∀ a, 0 ≤ P S a :=
      fun a => tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
    -- `∫⁻_F M = vol S`.
    have hMlint : ∫⁻ a in F, M a ∂volume = volume S := by
      have hconv : ∫⁻ a in F, M a ∂volume
          = ∫⁻ a in F, (∑' l : ↥(lattice sel DD),
              S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ a)) ∂volume := by
        apply lintegral_congr
        intro a; rw [hM]
        exact tsum_congr fun l => by
          rw [show (l +ᵥ a : Fin f → ℂ) = (l : Fin f → ℂ) + a from rfl, add_comm]
      rw [hconv,
        lintegral_tsum (fun l =>
          (show AEMeasurable (fun a => S.indicator (fun _ => (1 : ENNReal)) (l +ᵥ a))
              (volume.restrict F) from
            ((measurable_const.indicator hSmeas).comp (measurable_const_vadd l)).aemeasurable)),
        ← hFfund.lintegral_eq_tsum'' (S.indicator (fun _ => (1 : ENNReal)))]
      exact lintegral_indicator_one hSmeas
    have hPint : IntegrableOn (P S) F volume := by
      refine ⟨hPmeas.aestronglyMeasurable, ?_⟩
      rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ hPnonneg)]
      have hle : ∀ a, ENNReal.ofReal (P S a) ≤ M a := fun a => by
        rw [hNM a]; exact ENNReal.ofReal_toReal_le
      calc ∫⁻ a in F, ENNReal.ofReal (P S a) ∂volume
          ≤ ∫⁻ a in F, M a ∂volume := lintegral_mono hle
        _ = volume S := hMlint
        _ < ⊤ := hSbdd.measure_lt_top
    have hPval : ∫ a in F, P S a = (volume S).toReal :=
      SublemmaHaarUnfolding hcm sel DD hDD F hFfund S hSmeas hSbdd
    exact ⟨hPmeas, hPint, hPval⟩
  -- The window and overlap sets.
  have hWmeas : MeasurableSet (window (f := f) R) := by
    have : window (f := f) R = Set.univ.pi (fun _ : Fin f => Metric.closedBall (0 : ℂ) R) := by
      ext z
      simp only [window, Set.mem_setOf_eq, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
    rw [this]; exact MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  have hWbdd : Bornology.IsBounded (window (f := f) R) := by
    have : window (f := f) R ⊆ Metric.closedBall (0 : Fin f → ℂ) R := by
      intro z hz
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by linarith : (0:ℝ) ≤ R)]
      exact hz
    exact Metric.isBounded_closedBall.subset this
  have hRpos : (0 : ℝ) < R := by linarith
  have hdisc_pos : 0 < discArea R := by
    rw [discArea]; positivity
  -- `N := P (window R)`, `E := ∑_{u∈U} P (overlap_u)`.
  set N : (Fin f → ℂ) → ℝ := P (window R) with hNdef
  set E : (Fin f → ℂ) → ℝ :=
    fun a => ∑ u ∈ U, P (window R ∩ (window R - {u})) a with hEdef
  obtain ⟨hNmeas, hNint, hNval0⟩ := helper (window R) hWmeas hWbdd
  -- per-`u` overlap facts
  have hOmeas : ∀ u : Fin f → ℂ, MeasurableSet (window (f := f) R ∩ (window R - {u})) := by
    intro u
    refine hWmeas.inter ?_
    have : (window (f := f) R - {u}) = (fun x => x + u) ⁻¹' window R := by
      ext y; simp only [Set.mem_sub, Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro ⟨p, hp, q, rfl, rfl⟩; simpa using hp
      · intro hy; exact ⟨y + u, hy, u, rfl, by abel⟩
    rw [this]; exact hWmeas.preimage (by fun_prop)
  have hObdd : ∀ u : Fin f → ℂ, Bornology.IsBounded (window (f := f) R ∩ (window R - {u})) :=
    fun u => hWbdd.subset Set.inter_subset_left
  have hOhelper : ∀ u ∈ U,
      Measurable (P (window R ∩ (window R - {u}))) ∧
        IntegrableOn (P (window R ∩ (window R - {u}))) F volume ∧
        ∫ a in F, P (window R ∩ (window R - {u})) a =
          (volume (window (f := f) R ∩ (window R - {u}))).toReal :=
    fun u _ => helper _ (hOmeas u) (hObdd u)
  -- Measurability + integrability of `E`.
  have hEmeas : Measurable E := by
    rw [hEdef]; exact Finset.measurable_sum U (fun u hu => (hOhelper u hu).1)
  have hEint : IntegrableOn E F volume := by
    rw [hEdef]
    exact MeasureTheory.integrable_finset_sum U (fun u hu => (hOhelper u hu).2.1)
  have hNnonneg : ∀ a, 0 ≤ N a := fun a =>
    tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hEnonneg : ∀ a, 0 ≤ E a := fun a =>
    Finset.sum_nonneg fun u _ => tsum_nonneg fun l => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  -- `∫_F N = discArea^f`.
  have hNval : ∫ a in F, N a = discArea R ^ f := by
    rw [hNdef, hNval0, SublemmaWindowVolume R hRpos.le, ENNReal.toReal_ofReal (by positivity)]
  -- `∫_F E = U.card * overlapArea^f`.
  have hoverlap_nn : (0 : ℝ) ≤ overlapArea R := ENNReal.toReal_nonneg
  have hEval : ∫ a in F, E a = (U.card : ℝ) * overlapArea R ^ f := by
    rw [hEdef, integral_finset_sum U (fun u hu => (hOhelper u hu).2.1)]
    have hterm : ∀ u ∈ U, ∫ a in F, P (window R ∩ (window R - {u})) a = overlapArea R ^ f := by
      intro u hu
      rw [(hOhelper u hu).2.2, SublemmaOverlapVolume hcm R u (hU_coord u hu),
        ENNReal.toReal_ofReal (by positivity)]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  -- Relate the two integrals via `rho`.
  set c : ℝ := (U.card : ℝ) * rho R ^ f with hc
  have hEq : ∫ a in F, E a = c * ∫ a in F, N a := by
    rw [hEval, hNval, hc]
    have hrho : overlapArea R ^ f = rho R ^ f * discArea R ^ f := by
      rw [rho, div_pow, div_mul_cancel₀]
      positivity
    rw [hrho]; ring
  have hNpos : 0 < ∫ a in F, N a := by rw [hNval]; positivity
  have hchc : (0 : ℝ) ≤ c := by
    rw [hc]
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (by rw [rho]; exact div_nonneg hoverlap_nn hdisc_pos.le) f)
  -- `E` vanishes where `N` does.
  have hempty : ∀ a, N a = 0 → E a = 0 := by
    intro a hNa
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    rw [hNa] at hNc
    have hNc0 : Ncount sel DD R a = 0 := by exact_mod_cast hNc
    have hXfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
    have hXempty : Xset sel DD R a = ∅ := by
      rw [← Set.ncard_eq_zero hXfin]; exact hNc0
    have hEc0 : Ecount sel DD R U a = 0 := by
      have hidx : {p : (Fin f → ℂ) × (Fin f → ℂ) |
          p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro p hp; rw [hXempty] at hp; exact hp.1
      show {p : (Fin f → ℂ) × (Fin f → ℂ) |
          p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.ncard = 0
      rw [hidx, Set.ncard_empty]
    have hEc : (Ecount sel DD R U a : ℝ) = E a := SublemmaEcountEqSumTsum hcm sel DD hDD R U hU_lat a
    rw [← hEc, hEc0]; simp
  -- Pigeonhole.
  obtain ⟨a, hNa_pos, hEa⟩ :=
    SublemmaAveragingPigeonhole F hFpos hFfin N E c hchc hNmeas hEmeas hNnonneg hEnonneg
      hNint hEint hempty hEq hNpos
  refine ⟨a, ?_, ?_⟩
  · -- `Xset` nonempty.
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    have hNcpos : 0 < Ncount sel DD R a := by
      have : (0 : ℝ) < (Ncount sel DD R a : ℝ) := by rw [hNc]; exact hNa_pos
      exact_mod_cast this
    have hXfin : (Xset sel DD R a).Finite := (SublemmaLatticeDiscrete hcm sel DD hDD R).1 a
    rw [Set.nonempty_iff_ne_empty]
    intro hXe
    rw [Ncount, hXe, Set.ncard_empty] at hNcpos
    exact lt_irrefl 0 hNcpos
  · -- `Ecount ≥ c * Ncount`.
    have hNc : (Ncount sel DD R a : ℝ) = N a := SublemmaNcountEqTsum hcm sel DD hDD R a
    have hEc : (Ecount sel DD R U a : ℝ) = E a := SublemmaEcountEqSumTsum hcm sel DD hDD R U hU_lat a
    rw [ge_iff_le, hEc, hNc]
    exact hEa

end MinkowskiLemmas

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem SublemmaArithmeticBound {f : ℕ} (R : ℝ) (hR : 1 / 2 < R) (γ : ℝ) (hγ : 0 < γ)
    (U : Finset (Fin f → ℂ)) (hU_card : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ)))
    (hρ : Real.log (rho R) > -γ / 2) :
    (U.card : ℝ) * rho R ^ f ≥ Real.exp (γ * (f : ℝ) / 2) := by
  -- Geometric positivity of `rho R` (independent of `hρ`).
  have hRpos : (0 : ℝ) < R := by linarith
  have hε : (0 : ℝ) < R - 1 / 2 := by linarith
  have hdisc_pos : 0 < discArea R := by
    rw [discArea]; exact mul_pos Real.pi_pos (pow_pos hRpos 2)
  -- the sub-disc centred at 1/2 sits inside the overlap
  have hsub : Metric.closedBall (1 / 2 : ℂ) (R - 1 / 2) ⊆
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    have h0 : dist (1 / 2 : ℂ) 0 = 1 / 2 := by simp
    have h1 : dist (1 / 2 : ℂ) 1 = 1 / 2 := by rw [Complex.dist_eq]; norm_num
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall]
      calc dist w 0 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 0 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h0]; exact add_le_add hw le_rfl
        _ = R := by ring
    · rw [Metric.mem_closedBall]
      calc dist w 1 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 1 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h1]; exact add_le_add hw le_rfl
        _ = R := by ring
  have hball_pos : (0 : ENNReal) < volume (Metric.closedBall (1 / 2 : ℂ) (R - 1 / 2)) :=
    Metric.measure_closedBall_pos volume (1 / 2 : ℂ) hε
  have hvol_pos : (0 : ENNReal) <
      volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) :=
    lt_of_lt_of_le hball_pos (measure_mono hsub)
  have hvol_ne_top : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
    rw [Complex.volume_closedBall]; finiteness
  have hoverlap_pos : 0 < overlapArea R := by
    rw [overlapArea]; exact ENNReal.toReal_pos hvol_pos.ne' hvol_ne_top
  have hrho_pos : 0 < rho R := by
    rw [rho]; exact div_pos hoverlap_pos hdisc_pos
  -- `rho R ^ f = exp (f * log (rho R))`
  have hrf : Real.exp ((f : ℝ) * Real.log (rho R)) = rho R ^ f := by
    rw [Real.exp_nat_mul, Real.exp_log hrho_pos]
  -- lower bound on `rho R ^ f`
  have h2 : Real.exp ((f : ℝ) * (-γ / 2)) ≤ rho R ^ f := by
    rw [← hrf, Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hρ.le (Nat.cast_nonneg f)
  -- combine with the cardinality bound
  have hprod : Real.exp (γ * (f : ℝ)) * Real.exp ((f : ℝ) * (-γ / 2)) ≤
      (U.card : ℝ) * rho R ^ f :=
    mul_le_mul hU_card h2 (Real.exp_pos _).le (Nat.cast_nonneg _)
  calc Real.exp (γ * (f : ℝ) / 2)
      = Real.exp (γ * (f : ℝ)) * Real.exp ((f : ℝ) * (-γ / 2)) := by
        rw [← Real.exp_add]; congr 1; ring
    _ ≤ (U.card : ℝ) * rho R ^ f := hprod

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem Lemma24Averaging (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R) (γ : ℝ) (hγ : 0 < γ)
    (U : Finset (Fin f → ℂ))
    (hU_lat : ∀ u ∈ U, u ∈ lattice sel DD)
    (hU_ne : ∀ u ∈ U, u ≠ 0)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1)
    (hU_card : (U.card : ℝ) ≥ Real.exp (γ * (f : ℝ)))
    (hρ : Real.log (rho R) > -γ / 2) :
    ∃ a : Fin f → ℂ, (Xset sel DD R a).Nonempty ∧
      (Ecount sel DD R U a : ℝ) ≥ Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ) := by
  obtain ⟨a, hne, hE⟩ :=
    SublemmaAveragingExists hcm sel DD hDD R hR U hU_lat hU_ne hU_coord
  have harith : (U.card : ℝ) * rho R ^ f ≥ Real.exp (γ * (f : ℝ) / 2) :=
    SublemmaArithmeticBound R hR γ hγ U hU_card hρ
  refine ⟨a, hne, ?_⟩
  -- Ncount ≥ 0
  have hN : (0 : ℝ) ≤ (Ncount sel DD R a : ℝ) := Nat.cast_nonneg _
  -- exp(γf/2) * Ncount ≤ (U.card * rho^f) * Ncount ≤ Ecount
  calc Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ)
      ≤ (U.card : ℝ) * rho R ^ f * (Ncount sel DD R a : ℝ) :=
        mul_le_mul_of_nonneg_right harith hN
    _ ≤ (Ecount sel DD R U a : ℝ) := hE

end MinkowskiLemmas

open scoped NumberField
open Workspace.Types.MinkowskiWindow

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Lemma 2.5, part 1 (projection injectivity).** The first-coordinate projection
`z ↦ z 0` is injective on every coset `a + Λ` of the lattice. -/
theorem Lemma25ProjectionInjective [NeZero f] (sel : EmbeddingSelection L K f) (DD : ℕ)
    (a : Fin f → ℂ) :
    Set.InjOn (fun z : Fin f → ℂ => z 0) {z : Fin f → ℂ | z - a ∈ lattice sel DD} := by
  intro z hz z' hz' h
  simp only [Set.mem_setOf_eq] at hz hz'
  have hzz : z 0 = z' 0 := h
  -- Step 1: z - z' lies in the lattice.
  have hdiff : z - z' ∈ lattice sel DD := by
    have hsub := (lattice sel DD).sub_mem hz hz'
    have heq : (z - a) - (z' - a) = z - z' := by ring
    rwa [heq] at hsub
  obtain ⟨β, hβ⟩ := hdiff
  -- Unfold latticeHom applied to β.
  have key : latticeHom sel DD β
      = minkowskiMap sel ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹) := by
    simp [latticeHom]
  -- Step 2: the 0-th coordinate of the difference vanishes.
  have h0 : sel.sigma 0 ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹) = 0 := by
    have hcoord : (minkowskiMap sel ((algebraMap (𝓞 K) K β) * (DD : K)⁻¹)) 0 = (z - z') 0 := by
      rw [← key, hβ]
    simp only [minkowskiMap, Pi.ringHom_apply] at hcoord
    rw [hcoord]
    simp [Pi.sub_apply, hzz]
  -- Step 3: injectivity of the field embedding forces the field element to be 0.
  have hx : (algebraMap (𝓞 K) K β) * (DD : K)⁻¹ = 0 := by
    have hinj := RingHom.injective (sel.sigma 0)
    apply hinj
    rw [h0, map_zero]
  -- Step 4: the whole difference vector vanishes, so z = z'.
  have hzero : z - z' = 0 := by
    rw [← hβ, key, hx, map_zero]
  exact sub_eq_zero.mp hzero

end MinkowskiLemmas

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.PlanarCounting

/-- Counting identity: the number of *ordered* pairs of distinct points at distance `1`
drawn from a finite set `Q` in the plane is exactly twice the number of *unordered* such
pairs (which is `nu Q`). Each unordered unit segment `{a,b}` has precisely two orientations
`(a,b)` and `(b,a)`. -/
lemma card_ordered_unit (Q : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1)).card
      = 2 * nu Q := by
  classical
  set W := Q.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1) with hW
  set T := (Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1) with hT
  -- The `Sym2.mk` map sends `T` into `W`.
  have H : Set.MapsTo (fun pq : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
      s(pq.1, pq.2)) ↑T ↑W := by
    intro pq hpq
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne, hd⟩ := hpq
    rw [Finset.mem_coe, hW, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mk_mem_sym2_iff]; exact ⟨h1, h2⟩
    · rw [Sym2.mk_isDiag_iff]; exact hne
    · rw [distSym2_mk]; exact hd
  -- Each fibre has exactly two elements.
  have hfib : ∀ w ∈ W, ({a ∈ T | s(a.1, a.2) = w}).card = 2 := by
    intro w
    induction w using Sym2.ind with
    | _ a b =>
      intro hw
      rw [hW, Finset.mem_filter] at hw
      obtain ⟨hmem, hdiag, hdist⟩ := hw
      rw [Finset.mk_mem_sym2_iff] at hmem
      rw [Sym2.mk_isDiag_iff] at hdiag
      rw [distSym2_mk] at hdist
      have hne : a ≠ b := hdiag
      have hset : {p ∈ T | s(p.1, p.2) = s(a, b)} = ({(a, b), (b, a)} : Finset _) := by
        ext p
        rw [Finset.mem_filter, hT, Finset.mem_filter, Finset.mem_product,
            Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro ⟨⟨⟨_, _⟩, _, _⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
          · left; rfl
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨⟨⟨hmem.1, hmem.2⟩, hne, hdist⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨⟨⟨hmem.2, hmem.1⟩, fun h => hne h.symm, by rw [dist_comm]; exact hdist⟩,
              Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h
      exact hne (congrArg Prod.fst h)
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_congr rfl hfib, Finset.sum_const,
      smul_eq_mul]
  have hnu : W.card = nu Q := by rw [hW, nu]; congr!
  rw [hnu, Nat.mul_comm]

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem Lemma25PlanarCount [NeZero f] (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (a : Fin f → ℂ) (γ : ℝ)
    (U : Finset (Fin f → ℂ))
    (X : Finset (Fin f → ℂ)) (hX : (X : Set (Fin f → ℂ)) = Xset sel DD R a)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1)
    (hE : (Ecount sel DD R U a : ℝ) ≥ Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ)) :
    (nu (embedFinset (X.image (fun z => z 0))) : ℝ)
      ≥ (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * ((X.image (fun z => z 0)).card : ℝ) := by
  classical
  set P := X.image (fun z => z 0) with hP
  -- Step 1: the projection is injective on `X`, hence `|P| = |X|`.
  have hXsub : (↑X : Set (Fin f → ℂ)) ⊆ {z | z - a ∈ lattice sel DD} := by
    rw [hX]; intro z hz; exact hz.1
  have hinjX : Set.InjOn (fun z : Fin f → ℂ => z 0) ↑X :=
    (Lemma25ProjectionInjective sel DD a).mono hXsub
  have hPcard : P.card = X.card := by
    rw [hP]; exact Finset.card_image_of_injOn hinjX
  -- `Ncount = |X|`.
  have hNcard : Ncount sel DD R a = X.card := by
    rw [Ncount, ← hX, Set.ncard_coe_finset]
  -- `Ecount = |SF|` where `SF` is the finset of counted pairs.
  set SF := (X ×ˢ X).filter (fun p => p.2 - p.1 ∈ U) with hSF
  have hEcard : Ecount sel DD R U a = SF.card := by
    rw [Ecount]
    have hScoe : {p : (Fin f → ℂ) × (Fin f → ℂ) |
        p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U} = (↑SF : Set _) := by
      ext p
      simp only [hSF, Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq, ← hX,
        Finset.mem_coe]
      tauto
    rw [hScoe, Set.ncard_coe_finset]
  -- The projection map into the plane injects `SF` into the ordered unit pairs `T`.
  set T := ((embedFinset P) ×ˢ (embedFinset P)).filter
      (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1) with hT
  have hmaps : Set.MapsTo (fun p : (Fin f → ℂ) × (Fin f → ℂ) =>
      (toPlane (p.1 0), toPlane (p.2 0))) ↑SF ↑T := by
    intro p hp
    rw [Finset.mem_coe, hSF, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1X, hp2X⟩, hpU⟩ := hp
    have hnorm : ‖p.2 0 - p.1 0‖ = 1 := by
      have := hU_coord (p.2 - p.1) hpU 0
      rwa [Pi.sub_apply] at this
    have hP1 : p.1 0 ∈ P := by rw [hP]; exact Finset.mem_image_of_mem _ hp1X
    have hP2 : p.2 0 ∈ P := by rw [hP]; exact Finset.mem_image_of_mem _ hp2X
    have hd : dist (toPlane (p.1 0)) (toPlane (p.2 0)) = 1 := by
      rw [toPlane.isometry.dist_eq, dist_eq_norm, norm_sub_rev, hnorm]
    rw [Finset.mem_coe]
    dsimp only
    rw [hT, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Finset.mem_image_of_mem _ hP1, Finset.mem_image_of_mem _ hP2⟩, ?_, hd⟩
    dsimp only
    intro h
    rw [h, dist_self] at hd
    norm_num at hd
  have hinj : Set.InjOn (fun p : (Fin f → ℂ) × (Fin f → ℂ) =>
      (toPlane (p.1 0), toPlane (p.2 0))) ↑SF := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, hSF, Finset.mem_filter, Finset.mem_product] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨he1, he2⟩ := hpq
    have e1 : p.1 0 = q.1 0 := toPlane.injective he1
    have e2 : p.2 0 = q.2 0 := toPlane.injective he2
    have f1 : p.1 = q.1 := hinjX hp.1.1 hq.1.1 e1
    have f2 : p.2 = q.2 := hinjX hp.1.2 hq.1.2 e2
    exact Prod.ext f1 f2
  have hle : SF.card ≤ T.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hTnu : T.card = 2 * nu (embedFinset P) := by rw [hT]; exact card_ordered_unit (embedFinset P)
  have hEle : Ecount sel DD R U a ≤ 2 * nu (embedFinset P) := by
    rw [hEcard, ← hTnu]; exact hle
  -- Real arithmetic.
  have hEle' : (Ecount sel DD R U a : ℝ) ≤ 2 * (nu (embedFinset P) : ℝ) := by
    exact_mod_cast hEle
  have hcastN : (Ncount sel DD R a : ℝ) = (P.card : ℝ) := by rw [hNcard, ← hPcard]
  have hE2 : Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ) ≤ (Ecount sel DD R U a : ℝ) := by
    rw [← hcastN]; exact hE
  have hcombine : Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)
      ≤ 2 * (nu (embedFinset P) : ℝ) := le_trans hE2 hEle'
  rw [ge_iff_le, show (1 / 2 : ℝ) * Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)
      = (1 / 2) * (Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)) by ring]
  linarith [hcombine]

end MinkowskiLemmas

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Lemma 2.6 (size bound / packing).** With `R > 1/2` and denominator `DD ≥ 1`, the number
of coset points in the window is bounded: `N_a ≤ (4·R·DD)^{2f} = e^{Bf}`, `B = 2 log(4RD)`. -/
theorem Lemma26SizeBound (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R) (a : Fin f → ℂ) :
    (Ncount sel DD R a : ℝ) ≤ (4 * R * (DD : ℝ)) ^ (2 * f) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hDD1 : (1 : ℝ) ≤ (DD : ℝ) := by exact_mod_cast hDD
  -- Separation of distinct window points.
  have hsep : ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      (DD : ℝ)⁻¹ ≤ ‖x - x'‖ := by
    intro x hx x' hx' hne
    exact Workspace.ProofLemmas.SublemmaSeparation hcm sel DD hDD R a x hx x' hx' hne
  -- Packing bound.
  have hpack := SublemmaPacking sel DD hDD R hR0 a hsep
  have hbound : (Ncount sel DD R a : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := hpack.2
  -- Monotonicity of the base.
  have hbase : 1 + 2 * R * (DD : ℝ) ≤ 4 * R * (DD : ℝ) := by
    have h1 : (1 : ℝ) ≤ 2 * R * (DD : ℝ) := by nlinarith [hR, hDD1]
    nlinarith [h1]
  have hnonneg : (0 : ℝ) ≤ 1 + 2 * R * (DD : ℝ) := by positivity
  have hmono : (1 + 2 * R * (DD : ℝ)) ^ (2 * f) ≤ (4 * R * (DD : ℝ)) ^ (2 * f) :=
    pow_le_pow_left₀ hnonneg hbase (2 * f)
  exact le_trans hbound hmono

end MinkowskiLemmas

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum

theorem Thm23EmbeddingSelectionExists (d : AdmissibleDatum) :
    Nonempty (EmbeddingSelection d.L d.K (deg d)) := by
  -- There are exactly `deg d = [L : ℚ]` embeddings `L → ℂ`.
  have hcard : Fintype.card (d.L →+* ℂ) = deg d := by
    unfold deg; rw [NumberField.Embeddings.card d.L ℂ]
  let e : Fin (deg d) ≃ (d.L →+* ℂ) := (Fintype.equivFinOfCardEq hcard).symm
  -- Every `L → ℂ` embedding extends to a `K → ℂ` embedding.
  have hext : ∀ ψ : d.L →+* ℂ, ∃ σ : d.K →+* ℂ, σ.comp (algebraMap d.L d.K) = ψ := by
    intro ψ
    letI : Algebra d.L ℂ := ψ.toAlgebra
    haveI : Algebra.IsAlgebraic d.L d.K := Algebra.IsAlgebraic.of_finite d.L d.K
    let σA : d.K →ₐ[d.L] ℂ := IsAlgClosed.lift
    refine ⟨σA.toRingHom, ?_⟩
    ext x
    show σA (algebraMap d.L d.K x) = ψ x
    rw [AlgHom.commutes]; rfl
  refine ⟨⟨fun r => (hext (e r)).choose, ?_, ?_⟩⟩
  · -- restriction map is bijective
    have hspec : (fun r => ((hext (e r)).choose).comp (algebraMap d.L d.K)) = ⇑e :=
      funext fun r => (hext (e r)).choose_spec
    rw [hspec]; exact e.bijective
  · -- each restriction is real
    intro r
    rw [(hext (e r)).choose_spec]
    exact NumberField.IsTotallyReal.complexEmbedding_isReal (e r)

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open MeasureTheory

theorem Thm23RadiusChoice (γ : ℝ) (hγ : 0 < γ) :
    ∃ R : ℝ, 1 / 2 < R ∧ 1 ≤ R ∧ Real.log (rho R) > -γ / 2 := by
  -- `c := e^{-γ/4} < 1`.
  set c : ℝ := Real.exp (-γ / 4) with hcdef
  have hc0 : 0 < c := Real.exp_pos _
  have hc1 : c < 1 := by
    rw [hcdef]
    have := Real.exp_lt_exp.mpr (show -γ / 4 < 0 by linarith)
    rwa [Real.exp_zero] at this
  have h1c : 0 < 1 - c := by linarith
  -- Choose `R` large.
  set R : ℝ := 1 + 1 / (2 * (1 - c)) with hRdef
  have hRpos : (0 : ℝ) < R := by rw [hRdef]; positivity
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    have hpos : 0 < 1 / (2 * (1 - c)) := by positivity
    linarith
  have hRhalf : 1 / 2 < R := by linarith
  have hRne : R ≠ 0 := hRpos.ne'
  -- volume of a complex closed ball as a real.
  have hcbvol : ∀ (cc : ℂ) (ρ : ℝ), 0 ≤ ρ →
      (volume (Metric.closedBall cc ρ)).toReal = Real.pi * ρ ^ 2 := by
    intro cc ρ hρ
    rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hρ, ENNReal.coe_toReal, NNReal.coe_real_pi]
    ring
  -- overlap contains the ball of radius `R - 1/2` centred at `1/2`.
  have hsub : Metric.closedBall (1 / 2 : ℂ) (R - 1 / 2) ⊆
      Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    have h0 : dist (1 / 2 : ℂ) 0 = 1 / 2 := by simp
    have h1 : dist (1 / 2 : ℂ) 1 = 1 / 2 := by rw [Complex.dist_eq]; norm_num
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall]
      calc dist w 0 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 0 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h0]; exact add_le_add hw le_rfl
        _ = R := by ring
    · rw [Metric.mem_closedBall]
      calc dist w 1 ≤ dist w (1 / 2 : ℂ) + dist (1 / 2 : ℂ) 1 := dist_triangle _ _ _
        _ ≤ (R - 1 / 2) + 1 / 2 := by rw [h1]; exact add_le_add hw le_rfl
        _ = R := by ring
  have hne : volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono Set.inter_subset_left)
    rw [Complex.volume_closedBall]; finiteness
  -- overlapArea lower bound.
  have hoverlap_lb : Real.pi * (R - 1 / 2) ^ 2 ≤ overlapArea R := by
    rw [overlapArea, ← hcbvol (1 / 2) (R - 1 / 2) (by linarith)]
    exact ENNReal.toReal_mono hne (measure_mono hsub)
  -- `rho R ≥ (1 - 1/(2R))²`.
  have hrho_lb : (1 - 1 / (2 * R)) ^ 2 ≤ rho R := by
    rw [rho, discArea, le_div_iff₀ (by positivity : (0 : ℝ) < Real.pi * R ^ 2)]
    calc (1 - 1 / (2 * R)) ^ 2 * (Real.pi * R ^ 2)
          = Real.pi * (R - 1 / 2) ^ 2 := by field_simp
      _ ≤ overlapArea R := hoverlap_lb
  -- `c < 1 - 1/(2R)`.
  have hlin : c < 1 - 1 / (2 * R) := by
    have h2R : 0 < 2 * R := by positivity
    have hkey : (1 - c) * (2 * R) = 2 * (1 - c) + 1 := by rw [hRdef]; field_simp
    rw [lt_sub_comm, div_lt_iff₀ h2R, hkey]
    linarith
  -- `rho R > e^{-γ/2}`.
  have hrho_gt : Real.exp (-γ / 2) < rho R := by
    have hsq : c ^ 2 < (1 - 1 / (2 * R)) ^ 2 :=
      pow_lt_pow_left₀ hlin hc0.le (by norm_num)
    have hcsq : c ^ 2 = Real.exp (-γ / 2) := by
      rw [hcdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    calc Real.exp (-γ / 2) = c ^ 2 := hcsq.symm
      _ < (1 - 1 / (2 * R)) ^ 2 := hsq
      _ ≤ rho R := hrho_lb
  refine ⟨R, hRhalf, hR1, ?_⟩
  have := Real.log_lt_log (Real.exp_pos _) hrho_gt
  rwa [Real.log_exp] at this

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.PlanarCounting
open Filter

theorem Thm23FinalBound (γ B : ℝ) (hγ : 0 < γ) (hB : 0 < B)
    (fseq : ℕ → ℕ) (nseq : ℕ → ℕ) (Pseq : ℕ → Finset (EuclideanSpace ℝ (Fin 2)))
    (hf : Filter.Tendsto fseq Filter.atTop Filter.atTop)
    (hcard : ∀ j, (Pseq j).card = nseq j)
    (hnu : ∀ j, (nu (Pseq j) : ℝ) ≥ (1 / 2) * Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ))
    (hsize : ∀ j, (nseq j : ℝ) ≤ Real.exp (B * (fseq j : ℝ)))
    (hlb : ∀ j, Real.exp (γ * (fseq j : ℝ) / 2) ≤ (nseq j : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  set δ : ℝ := γ / (4 * B) with hδdef
  have hδ : 0 < δ := by rw [hδdef]; positivity
  refine ⟨δ, hδ, ?_⟩
  -- `n_j ≥ 1`.
  have hn1R : ∀ j, (1 : ℝ) ≤ (nseq j : ℝ) := by
    intro j
    refine le_trans ?_ (hlb j)
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (div_nonneg (mul_nonneg hγ.le (Nat.cast_nonneg _)) (by norm_num))
  have hn1 : ∀ j, 1 ≤ nseq j := fun j => by exact_mod_cast hn1R j
  have hnpos : ∀ j, (0 : ℝ) < (nseq j : ℝ) := fun j => lt_of_lt_of_le one_pos (hn1R j)
  -- Per-`j` bound: `nu (Pseq j) ≥ ½ n_j^{1+2δ}`.
  have hper : ∀ j, (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) ≤ (nu (Pseq j) : ℝ) := by
    intro j
    have hexp_ge : (nseq j : ℝ) ^ (2 * δ) ≤ Real.exp (γ * (fseq j : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos (hnpos j)]
      apply Real.exp_le_exp.mpr
      have hlog : Real.log (nseq j) ≤ B * (fseq j : ℝ) :=
        (Real.log_le_iff_le_exp (hnpos j)).mpr (hsize j)
      have h2δ : (2 : ℝ) * δ = γ / (2 * B) := by rw [hδdef]; field_simp; ring
      rw [h2δ]
      calc Real.log (nseq j) * (γ / (2 * B))
            ≤ (B * (fseq j : ℝ)) * (γ / (2 * B)) :=
              mul_le_mul_of_nonneg_right hlog (div_nonneg hγ.le (by positivity))
        _ = γ * (fseq j : ℝ) / 2 := by field_simp
    calc (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ)
        = (1 / 2) * ((nseq j : ℝ) ^ (2 * δ) * (nseq j : ℝ)) := by
          rw [show (1 : ℝ) + 2 * δ = 2 * δ + 1 from by ring, Real.rpow_add (hnpos j),
            Real.rpow_one]
      _ ≤ (1 / 2) * (Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_right hexp_ge (hnpos j).le
      _ = (1 / 2) * Real.exp (γ * (fseq j : ℝ) / 2) * (nseq j : ℝ) := by ring
      _ ≤ (nu (Pseq j) : ℝ) := hnu j
  -- `n_j → ∞`.
  have htexp : Tendsto (fun j => Real.exp (γ * (fseq j : ℝ) / 2)) atTop atTop := by
    have hfR : Tendsto (fun j => (fseq j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp hf
    have hg : Tendsto (fun j => (fseq j : ℝ) * (γ / 2)) atTop atTop :=
      hfR.atTop_mul_const (half_pos hγ)
    have hg' : Tendsto (fun j => γ * (fseq j : ℝ) / 2) atTop atTop := hg.congr (fun j => by ring)
    exact Real.tendsto_exp_atTop.comp hg'
  have htn : Tendsto (fun j => (nseq j : ℝ)) atTop atTop :=
    tendsto_atTop_mono hlb htexp
  -- `BddAbove` of the `nuMax` value set.
  have hbdd : ∀ n : ℕ,
      BddAbove {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ nu P = k} := by
    intro n
    refine ⟨(n + 1).choose 2, ?_⟩
    rintro k ⟨P, hPc, rfl⟩
    calc nu P ≤ P.sym2.card := by
          have heq : nu P = (P.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1)).card := by
            unfold nu; congr!
          rw [heq]
          exact Finset.card_filter_le _ _
      _ = (P.card + 1).choose 2 := Finset.card_sym2 P
      _ = (n + 1).choose 2 := by rw [hPc]
  -- Conclusion.
  intro N
  obtain ⟨j, hj⟩ := (htn.eventually_ge_atTop (max (N : ℝ) ((2 : ℝ) ^ (1 / δ)))).exists
  refine ⟨nseq j, ?_, hn1 j, ?_⟩
  · have : (N : ℝ) ≤ (nseq j : ℝ) := le_trans (le_max_left _ _) hj
    exact_mod_cast this
  · -- `nuMax (nseq j) ≥ (nseq j)^{1+δ}`.
    have hmem : nu (Pseq j) ∈ {k : ℕ | ∃ P, P.card = nseq j ∧ nu P = k} :=
      ⟨Pseq j, hcard j, rfl⟩
    have hnumaxR : (nu (Pseq j) : ℝ) ≤ (nuMax (nseq j) : ℝ) := by
      exact_mod_cast le_csSup (hbdd (nseq j)) hmem
    have hn2δ : (2 : ℝ) ≤ (nseq j : ℝ) ^ δ := by
      have h2δpow : ((2 : ℝ) ^ (1 / δ)) ^ δ = 2 := by
        rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hδ.ne', Real.rpow_one]
      rw [← h2δpow]
      exact Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hj) hδ.le
    have hnδpos : (0 : ℝ) ≤ (nseq j : ℝ) ^ (1 + δ) := Real.rpow_nonneg (hnpos j).le _
    have hfinal : (nseq j : ℝ) ^ (1 + δ) ≤ (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) := by
      have hsplit : (nseq j : ℝ) ^ (1 + 2 * δ) = (nseq j : ℝ) ^ (1 + δ) * (nseq j : ℝ) ^ δ := by
        rw [← Real.rpow_add (hnpos j)]; congr 1; ring
      rw [hsplit]
      nlinarith [hn2δ, hnδpos, mul_nonneg hnδpos (sub_nonneg.mpr hn2δ)]
    calc (nseq j : ℝ) ^ ((1 : ℝ) + δ) = (nseq j : ℝ) ^ (1 + δ) := by norm_num
      _ ≤ (1 / 2) * (nseq j : ℝ) ^ (1 + 2 * δ) := hfinal
      _ ≤ (nu (Pseq j) : ℝ) := hper j
      _ ≤ (nuMax (nseq j) : ℝ) := hnumaxR

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.PlanarCounting
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.AdmissibleDatum
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Filter

theorem Theorem23GeometricCriterion
    (t : ℕ) (ht : 0 < t) (q : Fin t → ℕ)
    (data : ℕ → AdmissibleDatum)
    (hshare_t : ∀ j, (data j).t = t)
    (hshare_q : ∀ j, HEq (data j).q q)
    (hdeg : Filter.Tendsto (fun j => deg (data j)) Filter.atTop Filter.atTop)
    (H : ℝ) (hH : 0 < H)
    (hclass : ∀ j, (classNumber (data j).K : ℝ) ≤ H ^ (deg (data j)))
    (hgamma : 0 < (t : ℝ) * Real.log 2 - Real.log H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  classical
  set γ : ℝ := (t : ℝ) * Real.log 2 - Real.log H with hγdef
  have hγ : 0 < γ := hgamma
  -- `∏ q_b ≥ 1` and `D₀ ≥ 1` (`j`-independent).
  have hprod_pos : 1 ≤ ∏ b : Fin t, q b := by
    have key : (∏ b : Fin (data 0).t, (data 0).q b) = ∏ b : Fin t, q b := by
      have ht0 := hshare_t 0
      subst ht0
      rw [eq_of_heq (hshare_q 0)]
    rw [← key]
    exact Finset.one_le_prod' (fun b _ => ((data 0).hq_prime b).one_lt.le)
  set D0 : ℕ := (∏ b : Fin t, q b) ^ 2 with hD0def
  have hD0_pos : 1 ≤ D0 := by rw [hD0def]; exact Nat.one_le_pow _ _ hprod_pos
  -- Every `data j` has `Dq (data j) = D₀`.
  have hDq : ∀ j, Dq (data j) = D0 := by
    intro j
    have key : (∏ b : Fin (data j).t, (data j).q b) = ∏ b : Fin t, q b := by
      have htj := hshare_t j
      subst htj
      rw [eq_of_heq (hshare_q j)]
    simp only [Dq, Qprod, hD0def, key]
  -- radius `R`.
  obtain ⟨R, hRhalf, hR1, hρ⟩ := Thm23RadiusChoice γ hγ
  have hRpos : (0 : ℝ) < R := by linarith
  -- constant `B`.
  set B : ℝ := 2 * Real.log (4 * R * (D0 : ℝ)) with hBdef
  have h4RD0 : (1 : ℝ) < 4 * R * (D0 : ℝ) := by
    have hD0R : (1 : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hD0_pos
    nlinarith
  have hB : 0 < B := by rw [hBdef]; have := Real.log_pos h4RD0; linarith
  -- Per-`j` construction.
  have hperj : ∀ j : ℕ, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ((1 / 2) * Real.exp (γ * (deg (data j) : ℝ) / 2) * (P.card : ℝ) ≤ (nu P : ℝ)) ∧
      ((P.card : ℝ) ≤ Real.exp (B * (deg (data j) : ℝ))) ∧
      (Real.exp (γ * (deg (data j) : ℝ) / 2) ≤ (P.card : ℝ)) := by
    intro j
    set d := data j with hddef
    set f := deg d with hfdef
    have hcm : IsAdjoinI d.L d.K := d.h_adjoin
    -- `NeZero f`.
    haveI hNZ : NeZero f := ⟨(Module.finrank_pos (R := ℚ) (M := d.L)).ne'⟩
    have hDD1 : 1 ≤ Dq d := by rw [hDq j]; exact hD0_pos
    have hDDne : (Dq d : d.K) ≠ 0 := by
      have : Dq d ≠ 0 := by omega
      exact_mod_cast this
    -- embedding selection.
    obtain ⟨sel⟩ := Thm23EmbeddingSelectionExists d
    -- norm-one set from Prop 2.2.
    obtain ⟨U0, hU0_int, -, hU0_unit, hU0_card⟩ := Prop22NormOneElements d H hH (hclass j)
    set U' : Finset (Fin f → ℂ) := U0.image (minkowskiMap sel) with hU'def
    -- `Φ` is injective.
    have hΦinj : Function.Injective (minkowskiMap sel) := by
      intro x y hxy
      have hne : Nonempty (Fin f) := ⟨⟨0, (Module.finrank_pos (R := ℚ) (M := d.L))⟩⟩
      obtain ⟨r0⟩ := hne
      have := congr_fun hxy r0
      simp only [minkowskiMap, Pi.ringHom_apply] at this
      exact (sel.sigma r0).injective this
    -- `U' ⊆ Λ`.
    have hU_lat : ∀ z ∈ U', z ∈ lattice sel (Dq d) := by
      intro z hz
      rw [hU'def, Finset.mem_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨ω, hω⟩ : ∃ ω : 𝓞 d.K, algebraMap (𝓞 d.K) d.K ω = (Dq d : d.K) * u :=
        ⟨NumberField.RingOfIntegers.restrict (fun _ : Unit => (Dq d : d.K) * u)
          (fun _ => hU0_int u hu) (), rfl⟩
      rw [lattice, AddMonoidHom.mem_range]
      refine ⟨ω, ?_⟩
      show latticeHom sel (Dq d) ω = minkowskiMap sel u
      simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply]
      congr 1
      rw [hω, mul_right_comm, mul_inv_cancel₀ hDDne, one_mul]
    -- unit-modulus coordinates.
    have hU_coord : ∀ z ∈ U', ∀ r, ‖z r‖ = 1 := by
      intro z hz r
      rw [hU'def, Finset.mem_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      show ‖minkowskiMap sel u r‖ = 1
      simp only [minkowskiMap, Pi.ringHom_apply]
      exact hU0_unit u hu (sel.sigma r)
    -- nonzero.
    have hU_ne : ∀ z ∈ U', z ≠ 0 := by
      intro z hz hz0
      obtain ⟨r0⟩ : Nonempty (Fin f) := ⟨⟨0, (Module.finrank_pos (R := ℚ) (M := d.L))⟩⟩
      have := hU_coord z hz r0
      rw [hz0] at this
      simp at this
    -- cardinality.
    have hU'card : (U'.card : ℝ) ≥ Real.exp (γ * (f : ℝ)) := by
      rw [hU'def, Finset.card_image_of_injective _ hΦinj]
      refine le_trans ?_ hU0_card
      rw [hγdef, hfdef]
      apply le_of_eq
      rw [hshare_t j]
    -- Averaging (Lemma 2.4).
    obtain ⟨a, ha_ne, hE⟩ := Lemma24Averaging hcm sel (Dq d) hDD1 R hRhalf γ hγ U'
      hU_lat hU_ne hU_coord hU'card hρ
    -- `X_a` is finite.
    have hXfin : (Xset sel (Dq d) R a).Finite :=
      (SublemmaLatticeDiscrete hcm sel (Dq d) hDD1 R).1 a
    set X : Finset (Fin f → ℂ) := hXfin.toFinset with hXdef
    have hXeq : (X : Set (Fin f → ℂ)) = Xset sel (Dq d) R a := hXfin.coe_toFinset
    have hNc : Ncount sel (Dq d) R a = X.card := by
      rw [Ncount, Set.ncard_eq_toFinset_card _ hXfin]
    -- projection injective ⇒ `|π(X)| = |X|`.
    have hprojcard : (X.image (fun z => z 0)).card = X.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hxX : x ∈ Xset sel (Dq d) R a := by rw [← hXeq]; exact hx
      have hyX : y ∈ Xset sel (Dq d) R a := by rw [← hXeq]; exact hy
      exact Lemma25ProjectionInjective sel (Dq d) a hxX.1 hyX.1 hxy
    -- planar count (Lemma 2.5).
    have hplanar := Lemma25PlanarCount sel (Dq d) R a γ U' X hXeq hU_coord hE
    set P : Finset (EuclideanSpace ℝ (Fin 2)) := embedFinset (X.image (fun z => z 0)) with hPdef
    have hPcard : P.card = X.card := by
      rw [hPdef, embedFinset, Finset.card_image_of_injective _ toPlane.injective, hprojcard]
    -- size bound (Lemma 2.6).
    have hsize26 : (Ncount sel (Dq d) R a : ℝ) ≤ (4 * R * (Dq d : ℝ)) ^ (2 * f) :=
      Lemma26SizeBound hcm sel (Dq d) hDD1 R hRhalf a
    refine ⟨P, ?_, ?_, ?_⟩
    · -- `nu P ≥ ½ e^{γf/2} |P|`.
      rw [hPdef] at *
      rw [hPcard]
      calc (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * (X.card : ℝ)
          = (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * ((X.image (fun z => z 0)).card : ℝ) := by
            rw [hprojcard]
        _ ≤ (nu (embedFinset (X.image (fun z => z 0))) : ℝ) := hplanar
    · -- `|P| ≤ e^{B f}`.
      rw [hPcard, ← hNc]
      calc (Ncount sel (Dq d) R a : ℝ) ≤ (4 * R * (Dq d : ℝ)) ^ (2 * f) := hsize26
        _ = Real.exp (B * (f : ℝ)) := by
            rw [hDq j, hBdef, ← Real.rpow_natCast (4 * R * (D0:ℝ)) (2 * f),
              Real.rpow_def_of_pos (by linarith)]
            congr 1
            push_cast
            ring
    · -- `e^{γf/2} ≤ |P|`.
      rw [hPcard, ← hNc]
      -- `E_a ≤ Ncount²`, combined with `hE`, and `Ncount ≥ 1`.
      have hNpos : 1 ≤ Ncount sel (Dq d) R a := by
        rw [hNc]
        rw [Finset.one_le_card, ← Finset.coe_nonempty, hXeq]
        exact ha_ne
      have hE2 : (Ecount sel (Dq d) R U' a : ℝ) ≤ (Ncount sel (Dq d) R a : ℝ) ^ 2 := by
        have hEfin : {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel (Dq d) R a ∧ p.2 ∈ Xset sel (Dq d) R a ∧ p.2 - p.1 ∈ U'}.Finite :=
          (SublemmaLatticeDiscrete hcm sel (Dq d) hDD1 R).2 U' a
        have hsub : {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel (Dq d) R a ∧ p.2 ∈ Xset sel (Dq d) R a ∧ p.2 - p.1 ∈ U'}
            ⊆ Xset sel (Dq d) R a ×ˢ Xset sel (Dq d) R a :=
          fun p hp => ⟨hp.1, hp.2.1⟩
        have : Ecount sel (Dq d) R U' a ≤ (Ncount sel (Dq d) R a) ^ 2 := by
          rw [Ecount, Ncount, sq, ← Set.ncard_prod]
          exact Set.ncard_le_ncard hsub (hXfin.prod hXfin)
        calc (Ecount sel (Dq d) R U' a : ℝ) ≤ ((Ncount sel (Dq d) R a) ^ 2 : ℕ) := by exact_mod_cast this
          _ = (Ncount sel (Dq d) R a : ℝ) ^ 2 := by push_cast; ring
      -- from hE : Ecount ≥ exp(γf/2) Ncount, and hE2 : Ecount ≤ Ncount²
      have hNcR : (1 : ℝ) ≤ (Ncount sel (Dq d) R a : ℝ) := by exact_mod_cast hNpos
      have hkey : Real.exp (γ * (f : ℝ) / 2) * (Ncount sel (Dq d) R a : ℝ)
          ≤ (Ncount sel (Dq d) R a : ℝ) ^ 2 := le_trans hE hE2
      nlinarith [hkey, hNcR, sq_nonneg ((Ncount sel (Dq d) R a : ℝ))]
  -- Extract the sequences and apply the final bound.
  choose Pseq hPnu hPsize hPlb using hperj
  exact Thm23FinalBound γ B hγ hB (fun j => deg (data j)) (fun j => (Pseq j).card) Pseq
    hdeg (fun j => rfl) hPnu hPsize hPlb

/-- For every `ℓ : ℕ` there is a strictly increasing enumeration `r : Fin ℓ → ℕ+`
of the first `ℓ` primes congruent to `1 mod 3`: each `r i` is prime with
`(r i) % 3 = 1`, and the minimality clause holds — any prime `p ≡ 1 mod 3` that
is not among the `r i` exceeds every `r i`. -/
theorem SublemmaFirstEllPrimes :
    ∀ (ℓ : ℕ), ∃ r : Fin ℓ → ℕ+,
      StrictMono r ∧
      (∀ i, ((r i : ℕ)).Prime) ∧
      (∀ i, (r i : ℕ) % 3 = 1) ∧
      (∀ p : ℕ, p.Prime → p % 3 = 1 → (¬ ∃ i, (r i : ℕ) = p) → ∀ i, (r i : ℕ) < p) := by
  intro ℓ
  classical
  set pred : ℕ → Prop := fun n => n.Prime ∧ n % 3 = 1 with hpred
  -- The set of primes ≡ 1 mod 3 is infinite (Dirichlet).
  have hinf : {n | pred n}.Infinite := by
    have h := Nat.infinite_setOf_prime_and_modEq (q := 3) (a := 1) (by norm_num) (by decide)
    have hset : {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD 3]} = {n | pred n} := by
      ext n
      simp only [Set.mem_setOf_eq, hpred, Nat.ModEq]
    rwa [hset] at h
  have hmem : ∀ n, pred (Nat.nth pred n) := fun n => Nat.nth_mem_of_infinite hinf n
  have hmono : StrictMono (Nat.nth pred) := Nat.nth_strictMono hinf
  refine ⟨fun i => ⟨Nat.nth pred i, (hmem i).1.pos⟩, ?_, ?_, ?_, ?_⟩
  · -- StrictMono r
    intro i j hij
    exact hmono hij
  · intro i; exact (hmem i).1
  · intro i; exact (hmem i).2
  · intro p hp hmp hnotin i
    have hpp : pred p := ⟨hp, hmp⟩
    have hcount : Nat.nth pred (Nat.count pred p) = p := Nat.nth_count hpp
    have hkge : ℓ ≤ Nat.count pred p := by
      by_contra hlt
      push_neg at hlt
      exact hnotin ⟨⟨Nat.count pred p, hlt⟩, hcount⟩
    have hik : (i : ℕ) < Nat.count pred p := lt_of_lt_of_le i.isLt hkge
    have hlt2 := hmono hik
    rw [hcount] at hlt2
    exact hlt2

theorem SublemmaCubicCharacterOfConductorR :
    ∀ (r : ℕ+), (r : ℕ).Prime → (r : ℕ) % 3 = 1 →
      ∃ ψ : DirichletCharacter ℂ (r : ℕ),
        orderOf ψ = 3 ∧ DirichletCharacter.conductor ψ = (r : ℕ) := by
  intro r hp hm
  haveI : Fact (Nat.Prime (r : ℕ)) := ⟨hp⟩
  have hcard : Fintype.card (ZMod (r : ℕ)) = (r : ℕ) := ZMod.card (r : ℕ)
  have h3dvd : (3 : ℕ) ∣ Fintype.card (ZMod (r : ℕ)) - 1 := by
    rw [hcard]; omega
  have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / 3)) 3 :=
    Complex.isPrimitiveRoot_exp 3 (by norm_num)
  obtain ⟨ψ, hψ⟩ := MulChar.exists_mulChar_orderOf (ZMod (r : ℕ)) h3dvd hζ
  refine ⟨ψ, hψ, ?_⟩
  have hdvd : DirichletCharacter.conductor ψ ∣ (r : ℕ) :=
    DirichletCharacter.conductor_dvd_level ψ
  rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | hr
  · exfalso
    have hft : DirichletCharacter.FactorsThrough ψ 1 :=
      h1 ▸ DirichletCharacter.factorsThrough_conductor ψ
    have hψ1 : ψ = 1 := (DirichletCharacter.factorsThrough_one_iff ψ).mp hft
    rw [hψ1] at hψ
    simp [orderOf_one] at hψ
  · exact hr

open DirichletCharacter

theorem SublemmaChangeLevelPreservesConductorAndOrder
    {D : ℕ} :
    ∀ {r : ℕ} [NeZero D] (ψ : DirichletCharacter ℂ r) (hr : r ∣ D),
      DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ)
        = DirichletCharacter.conductor ψ
      ∧ orderOf ((DirichletCharacter.changeLevel hr) ψ) = orderOf ψ := by
  intro r _ ψ hr
  haveI hrne : NeZero r :=
    ⟨fun h => (NeZero.ne D) (Nat.eq_zero_of_zero_dvd (h ▸ hr))⟩
  -- Direction 1: conductor of the lifted character divides conductor of ψ.
  have h1 : DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ)
      ∣ DirichletCharacter.conductor ψ := by
    obtain ⟨hc, ψ₀, hψ₀⟩ := DirichletCharacter.factorsThrough_conductor ψ
    refine DirichletCharacter.conductor_dvd_of_mem_conductorSet _ ?_
    refine ⟨dvd_trans hc hr, ψ₀, ?_⟩
    conv_lhs => rw [hψ₀]
    exact (DirichletCharacter.changeLevel_trans ψ₀ hc hr).symm
  -- Direction 2: conductor of ψ divides conductor of the lifted character.
  have h2 : DirichletCharacter.conductor ψ
      ∣ DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ) := by
    obtain ⟨heD, χ₀, hχ₀⟩ :=
      DirichletCharacter.factorsThrough_conductor ((DirichletCharacter.changeLevel hr) ψ)
    have er : DirichletCharacter.conductor ((DirichletCharacter.changeLevel hr) ψ) ∣ r :=
      h1.trans (DirichletCharacter.conductor_dvd_level ψ)
    refine DirichletCharacter.conductor_dvd_of_mem_conductorSet _ ?_
    refine ⟨er, χ₀, ?_⟩
    apply DirichletCharacter.changeLevel_injective hr
    conv_lhs => rw [hχ₀]
    exact DirichletCharacter.changeLevel_trans χ₀ er hr
  refine ⟨Nat.dvd_antisymm h1 h2, ?_⟩
  exact orderOf_injective (DirichletCharacter.changeLevel hr)
    (DirichletCharacter.changeLevel_injective hr) ψ

-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Ch. 3 (Thm 3.11);
-- J. Neukirch, Algebraic Number Theory, Springer, 1999, Ch. VI.
-- Paper label: Proposition A.11(ii)
-- NL statement: For a finite family of Dirichlet characters of the same (positive) modulus with pairwise
-- coprime conductors, the conductor of the product equals the product of the conductors.
--
-- Proved purely from Mathlib. The reverse divisibility direction is elementary: since (χ·ψ)·ψ⁻¹ = χ,
-- `conductor_mul_dvd_lcm_conductor` applied to (χ·ψ, ψ⁻¹) with `conductor_inv` and coprimality yields
-- `conductor χ ∣ conductor(χ·ψ)` (symmetrically for ψ).
--
-- The `[NeZero n]` hypothesis is necessary: at n = 0, k = 0 the statement fails, since
-- LHS = conductor(1 : DirichletCharacter ℂ 0) = 0 but RHS = (empty product) = 1. A "modulus" in the
-- paper is a positive integer, so `[NeZero n]` is the faithful reading.

open scoped NumberField
open DirichletCharacter

set_option maxHeartbeats 800000

/-- Number theory helper: `a ∣ lcm b d` together with `Coprime a d` gives `a ∣ b`. -/
private theorem cmf_lcmHelper (a b d : ℕ) (hlcm : a ∣ Nat.lcm b d) (hcop : Nat.Coprime a d) :
    a ∣ b := by
  have h1 : Nat.lcm b d ∣ b * d := Dvd.intro_left (Nat.gcd b d) (Nat.gcd_mul_lcm b d)
  exact hcop.dvd_of_dvd_mul_right (hlcm.trans h1)

/-- Binary coprime-conductor multiplicativity. -/
private theorem cmf_binary (n : ℕ) [NeZero n] (χ ψ : DirichletCharacter ℂ n)
    (hcop : Nat.Coprime (conductor χ) (conductor ψ)) :
    conductor (χ * ψ) = conductor χ * conductor ψ := by
  apply Nat.dvd_antisymm
  · have h := conductor_mul_dvd_lcm_conductor χ ψ
    rwa [hcop.lcm_eq_mul] at h
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop
    · have h1 := conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
      rw [conductor_inv] at h1
      have he : (χ * ψ) * ψ⁻¹ = χ := mul_inv_cancel_right χ ψ
      rw [he] at h1
      exact cmf_lcmHelper _ _ _ h1 hcop
    · have h1 := conductor_mul_dvd_lcm_conductor (χ * ψ) χ⁻¹
      rw [conductor_inv] at h1
      have he : (χ * ψ) * χ⁻¹ = ψ := by rw [mul_comm χ ψ]; exact mul_inv_cancel_right ψ χ
      rw [he] at h1
      exact cmf_lcmHelper _ _ _ h1 hcop.symm

/-- Family version over an arbitrary `Finset`, by induction. -/
private theorem cmf_family (n : ℕ) [NeZero n] {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (χ : ι → DirichletCharacter ℂ n)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      Nat.Coprime (conductor (χ i)) (conductor (χ j))) :
    conductor (∏ i ∈ s, χ i) = ∏ i ∈ s, conductor (χ i) := by
  induction s using Finset.induction with
  | empty => simp [conductor_one]
  | @insert a s ha ih =>
    have hsub : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
        Nat.Coprime (conductor (χ i)) (conductor (χ j)) :=
      fun i hi j hj hij => h i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    have ihs := ih hsub
    have hcopprod : Nat.Coprime (conductor (χ a)) (∏ i ∈ s, conductor (χ i)) := by
      apply Nat.Coprime.prod_right
      intro i hi
      exact h a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi)
        (fun hcon => ha (hcon ▸ hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcop' : Nat.Coprime (conductor (χ a)) (conductor (∏ i ∈ s, χ i)) := by
      rw [ihs]; exact hcopprod
    rw [cmf_binary n (χ a) (∏ i ∈ s, χ i) hcop', ihs]

theorem ConductorMultiplicativeFamily (n : ℕ) [NeZero n] (k : ℕ)
    (χ : Fin k → DirichletCharacter ℂ n)
    (h : ∀ i j, i ≠ j →
      Nat.Coprime (DirichletCharacter.conductor (χ i)) (DirichletCharacter.conductor (χ j))) :
    DirichletCharacter.conductor (∏ i, χ i)
      = ∏ i, DirichletCharacter.conductor (χ i) := by
  exact cmf_family n Finset.univ χ (fun i _ j _ hij => h i j hij)

open scoped NumberField

/-- For a family of cubic characters `χ_i` (order 3) of common modulus `D` with pairwise
coprime conductors `r_i`, whose product of conductors is `D` with `1 < D`, the product
`χ = ∏ χ_i` has conductor `D` and order `3`. -/
theorem SublemmaCharacterProductOrderConductor
    (ℓ : ℕ) (D : ℕ) (r : Fin ℓ → ℕ+)
    (χ : Fin ℓ → DirichletCharacter ℂ D)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (r i : ℕ) (r j : ℕ))
    (hcond : ∀ i, DirichletCharacter.conductor (χ i) = (r i : ℕ))
    (hord : ∀ i, orderOf (χ i) = 3)
    (hD : D = ∏ i, (r i : ℕ))
    (hD1 : 1 < D) :
    DirichletCharacter.conductor (∏ i, χ i) = D ∧ orderOf (∏ i, χ i) = 3 := by
  haveI : NeZero D := ⟨by omega⟩
  -- conductor of the product equals D
  have hcondprod : DirichletCharacter.conductor (∏ i, χ i) = D := by
    have hcopcond : ∀ i j, i ≠ j →
        Nat.Coprime (DirichletCharacter.conductor (χ i))
          (DirichletCharacter.conductor (χ j)) := by
      intro i j hij
      rw [hcond i, hcond j]
      exact hcop i j hij
    rw [ConductorMultiplicativeFamily D ℓ χ hcopcond]
    have hprod : ∏ i, DirichletCharacter.conductor (χ i) = ∏ i, (r i : ℕ) :=
      Finset.prod_congr rfl (fun i _ => hcond i)
    rw [hprod]
    exact hD.symm
  refine ⟨hcondprod, ?_⟩
  -- the product is a cube, hence order divides 3
  have hcube : (∏ i, χ i) ^ 3 = 1 := by
    rw [← Finset.prod_pow]
    have : ∀ i ∈ Finset.univ, (χ i) ^ 3 = 1 := by
      intro i _
      have := pow_orderOf_eq_one (χ i)
      rwa [hord i] at this
    rw [Finset.prod_congr rfl this]
    exact Finset.prod_const_one
  have hdvd : orderOf (∏ i, χ i) ∣ 3 := orderOf_dvd_of_pow_eq_one hcube
  -- the product is nontrivial since its conductor is D > 1
  have hne : (∏ i, χ i) ≠ 1 := by
    intro h
    rw [h, DirichletCharacter.conductor_one] at hcondprod
    omega
  have hordne : orderOf (∏ i, χ i) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact hne
  rcases (Nat.prime_three).eq_one_or_self_of_dvd _ hdvd with h1 | h3
  · exact absurd h1 hordne
  · exact h3

set_option maxHeartbeats 800000

theorem DirichletCharacterRangeCardEqOrder {N : ℕ} (chi : DirichletCharacter ℂ N) :
    Nat.card ↥(chi.toUnitHom.range) = orderOf chi := by
  set f := chi.toUnitHom with hf
  -- `f` corresponds to `chi` under the multiplicative equiv `mulEquivToUnitHom`
  have hfm : f = MulChar.mulEquivToUnitHom chi := by
    rw [hf, MulChar.toUnitHom_eq, MulChar.mulEquivToUnitHom_apply]
  have hbridge : ∀ k, f ^ k = 1 ↔ chi ^ k = 1 := by
    intro k
    rw [hfm, ← map_pow]
    constructor
    · intro h
      have : MulChar.mulEquivToUnitHom (chi ^ k) = MulChar.mulEquivToUnitHom 1 := by
        rw [map_one]; exact h
      exact MulChar.mulEquivToUnitHom.injective this
    · intro h; rw [h, map_one]
  have horder : orderOf f = orderOf chi := by
    apply Nat.dvd_antisymm
    · exact orderOf_dvd_of_pow_eq_one ((hbridge (orderOf chi)).mpr (pow_orderOf_eq_one chi))
    · exact orderOf_dvd_of_pow_eq_one ((hbridge (orderOf f)).mp (pow_orderOf_eq_one f))
  rw [← horder]
  -- `Nat.card (range) = orderOf f`, via exponent of the cyclic image
  haveI : Finite ↥(f.range) :=
    Finite.of_surjective _ (MonoidHom.rangeRestrict_surjective f)
  haveI : IsCyclic ↥(f.range) := inferInstance
  have hcard : Nat.card ↥(f.range) = Monoid.exponent ↥(f.range) :=
    IsCyclic.exponent_eq_card.symm
  rw [hcard]
  apply Nat.dvd_antisymm
  · -- exponent of the range divides orderOf f
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    rintro ⟨_, u, rfl⟩
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← MonoidHom.pow_apply f (orderOf f) u, pow_orderOf_eq_one, MonoidHom.one_apply]
  · -- orderOf f divides the exponent of the range
    apply orderOf_dvd_of_pow_eq_one
    apply MonoidHom.ext
    intro u
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    have hmem : f u ∈ f.range := ⟨u, rfl⟩
    have h := Monoid.pow_exponent_eq_one (⟨f u, hmem⟩ : ↥(f.range))
    have h2 : ((⟨f u, hmem⟩ : ↥(f.range)) : ℂˣ) ^ Monoid.exponent ↥(f.range) = 1 := by
      rw [← SubmonoidClass.coe_pow, h, OneMemClass.coe_one]
    exact h2

-- Cited from: Def A.11(i) / Washington, Introduction to Cyclotomic Fields, Ch.3, Thm 3.11: for a prime r ≡ 1 (mod 3), the field cut out by an order-3 Dirichlet character of conductor r equals THE unique cyclic cubic subfield of ℚ(ζ_r).
-- Both fields are the fixed field (lifted to ℂ) of an
-- index-3 subgroup of Gal(ℚ(ζ_r)/ℚ) ≃ (ℤ/rℤ)ˣ; via `galToUnits` the problem reduces to a
-- subgroup identity in the finite cyclic group (ℤ/rℤ)ˣ (order r-1, divisible by 3):
--   ker(ψ.toUnitHom) = range(x ↦ x^3).
-- The cubes are contained in the kernel (ψ has order 3), and both subgroups have index 3
-- (`Subgroup.index_ker` + `DirichletCharacterRangeCardEqOrder`, resp.
-- `IsCyclic.index_powMonoidHom_range`), hence equal cardinality, hence equal.



open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CutOutFieldEqCyclicCubic
    (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : orderOf ψ = 3) :
    cutOutField r ψ = cyclicCubicSubfield r hr hr3 := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  have hcardU : Nat.card (ZMod (r : ℕ))ˣ = (r : ℕ) - 1 := by
    rw [Nat.card_eq_fintype_card]; exact ZMod.card_units (r : ℕ)
  have hdvd : 3 ∣ Nat.card (ZMod (r : ℕ))ˣ := by
    rw [hcardU]; have hr2 : 2 ≤ (r : ℕ) := hr.two_le; omega
  have hQindex :
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range.index = 3 := by
    rw [IsCyclic.index_powMonoidHom_range (ZMod (r : ℕ))ˣ 3, Nat.gcd_eq_right hdvd]
  have hfindex : ψ.toUnitHom.ker.index = 3 := by
    rw [Subgroup.index_ker, DirichletCharacterRangeCardEqOrder ψ, hψ]
  have hf3 : ψ.toUnitHom ^ 3 = 1 := by
    have hbridge : ψ.toUnitHom = MulChar.mulEquivToUnitHom ψ := by
      rw [MulChar.toUnitHom_eq, MulChar.mulEquivToUnitHom_apply]
    rw [hbridge, ← map_pow]
    have hp : ψ ^ 3 = 1 := by rw [← hψ]; exact pow_orderOf_eq_one ψ
    rw [hp, map_one]
  have hle :
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range ≤ ψ.toUnitHom.ker := by
    rintro _ ⟨x, rfl⟩
    simp only [MonoidHom.mem_ker]
    rw [powMonoidHom_apply, map_pow, ← MonoidHom.pow_apply, hf3, MonoidHom.one_apply]
  have hcardeq :
      Nat.card ψ.toUnitHom.ker ≤
        Nat.card (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range := by
    have hcQ := Subgroup.card_mul_index
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    have hcK := Subgroup.card_mul_index ψ.toUnitHom.ker
    rw [hQindex] at hcQ
    rw [hfindex] at hcK
    omega
  have hcore :
      ψ.toUnitHom.ker = (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range :=
    (Subgroup.eq_of_le_of_card_ge hle hcardeq).symm
  have hsub : (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker
      = ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
          (galToUnits r).toMonoidHom := by
    rw [← MonoidHom.comap_ker, hcore]
  exact congrArg (fun H => IntermediateField.lift (IntermediateField.fixedField H)) hsub

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by an order-3 Dirichlet character of prime conductor
`r ≡ 1 (mod 3)` is the cyclic cubic subfield of `ℚ(ζ_r)`. -/
theorem SublemmaCutOutFieldCubicChar
    (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : orderOf ψ = 3) :
    cutOutField r ψ = cyclicCubicSubfield r hr hr3 :=
  CutOutFieldEqCyclicCubic r hr hr3 ψ hψ

-- Cited from: Def A.5 (field conductor / level-independence of the cut-out field), Washington, Introduction to Cyclotomic Fields, Ch. 3.
-- The field cut out by a Dirichlet character depends only on the character up to changeLevel (i.e. on the induced primitive character), not on the chosen modulus.
--
-- The classical content is Mathlib's cyclotomic Galois correspondence: the level-compatibility square
-- `IsCyclotomicExtension.Rat.galEquivZMod_restrictNormal_apply`, the fixed-field descent
-- `InfiniteGalois.restrict_fixedField` (packaged as the helper `fixedFieldDescent`, also proved from
-- Mathlib), and `DirichletCharacter.changeLevel_toUnitHom`.  The ℚ-algebra instance diamond on the
-- subfield-of-a-subfield `ℚ(ζ_r) ⊆ ℚ(ζ_D) ⊆ ℂ` (Mathlib uses `IntermediateField.algebra'` while the
-- cyclotomic setup forces `DivisionRing.toRatAlgebra`) is bridged via `Subsingleton (Algebra ℚ _)`.


open Complex
open Workspace.Types.CyclotomicCharacterFields
open IsCyclotomicExtension IsCyclotomicExtension.Rat

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

/-- `zetaC a` is a power of `zetaC b` whenever `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  congr 1
  obtain ⟨k, hk⟩ := h
  have hr0 : (a : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hm0 : (b : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
  have hkdiv : (b : ℕ) / (a : ℕ) = k := by rw [hk]; exact Nat.mul_div_cancel_left k a.pos
  rw [hkdiv]
  have hkc : (b : ℂ) = (a : ℂ) * (k : ℂ) := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hk
    exact_mod_cast this
  rw [hkc]
  field_simp

/-- Monotonicity of the concrete cyclotomic fields with respect to divisibility. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- Restricting a subfield `S ≤ ℚ(ζ_N)` to `ℚ(ζ_N)` and lifting back recovers `S`. -/
theorem comap_val_roundtrip_gen (S : IntermediateField ℚ ℂ) (N : ℕ+)
    (hSN : S ≤ cyclotomicField' N) :
    IntermediateField.lift (S.comap (cyclotomicField' N).val) = S := by
  show (S.comap (cyclotomicField' N).val).map (cyclotomicField' N).val = S
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
  exact hSN

/-- The `ℚ`-algebra isomorphism `ℚ(ζ_a) ⊆ ℚ(ζ_N)  ≃  ℚ(ζ_a)` when `a ∣ N`. -/
noncomputable def comapValEquiv (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ)) :
    ↥((cyclotomicField' a).comap (cyclotomicField' N).val) ≃ₐ[ℚ] ↥(cyclotomicField' a) :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq
      (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN)))

/-- The underlying complex number of `comapValEquiv a N haN x` is that of `x`. -/
theorem comapValEquiv_coe (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ))
    (x : ↥((cyclotomicField' a).comap (cyclotomicField' N).val)) :
    ((comapValEquiv a N haN x : ↥(cyclotomicField' a)) : ℂ) = (x : ℂ) := by
  have h1 : (comapValEquiv a N haN x : ↥(cyclotomicField' a))
      = IntermediateField.equivOfEq
          (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN))
          (IntermediateField.liftAlgEquiv _ x) := rfl
  rw [h1]
  have h2 : ((IntermediateField.equivOfEq
          (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN))
          (IntermediateField.liftAlgEquiv _ x) : ↥(cyclotomicField' a)) : ℂ)
      = ((IntermediateField.liftAlgEquiv
          ((cyclotomicField' a).comap (cyclotomicField' N).val) x :
            ↥(IntermediateField.lift ((cyclotomicField' a).comap (cyclotomicField' N).val))) : ℂ) :=
    rfl
  rw [h2, IntermediateField.liftAlgEquiv_apply]

/-- Transport of a fixed field along an algebra isomorphism `e` and the induced
`autCongr e` on Galois groups. -/
theorem fixedField_map_autCongr {k A B : Type*} [Field k] [Field A] [Field B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (H : Subgroup (A ≃ₐ[k] A)) :
    (IntermediateField.fixedField H).map e.toAlgHom
      = IntermediateField.fixedField (H.map (AlgEquiv.autCongr e).toMonoidHom) := by
  ext z
  simp only [IntermediateField.mem_map, IntermediateField.mem_fixedField_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    intro τ hτ
    rw [Subgroup.mem_map] at hτ
    obtain ⟨σ, hσ, rfl⟩ := hτ
    simp only [MulEquiv.coe_toMonoidHom, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
      AlgEquiv.coe_algHom, AlgEquiv.symm_apply_apply]
    rw [hy σ hσ]
  · intro hz
    refine ⟨e.symm z, ?_, by simp⟩
    intro σ hσ
    have hmem : (AlgEquiv.autCongr e σ) ∈ H.map (AlgEquiv.autCongr e).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hσ
    have hzz := hz _ hmem
    rw [AlgEquiv.autCongr_apply] at hzz
    simp only [AlgEquiv.trans_apply] at hzz
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    exact hzz

/-- Naturality of `galEquivZMod` across the isomorphism `comapValEquiv r D hr` between the
copy of `ℚ(ζ_r)` inside `ℚ(ζ_D)` and `ℚ(ζ_r)` itself. -/
theorem galEquivZMod_comapValEquiv (r D : ℕ+) (hr : (r : ℕ) ∣ (D : ℕ))
    [IsCyclotomicExtension {(r : ℕ)} ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val)]
    [NumberField ↥((cyclotomicField' r).comap (cyclotomicField' D).val)]
    (σ : ↥((cyclotomicField' r).comap (cyclotomicField' D).val)
        ≃ₐ[ℚ] ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) :
    galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
        (AlgEquiv.autCongr (comapValEquiv r D hr) σ)
      = galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ := by
  set ζL : ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsCyclotomicExtension.zeta (r : ℕ) ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val)
      with hζLdef
  have hζL : IsPrimitiveRoot ζL (r : ℕ) :=
    IsCyclotomicExtension.zeta_spec (r : ℕ) ℚ _
  have hζLpow : ζL ^ (r : ℕ) = 1 := hζL.pow_eq_one
  set ζF : ↥(cyclotomicField' r) := comapValEquiv r D hr ζL with hζFdef
  have hζFpow : ζF ^ (r : ℕ) = 1 := by rw [hζFdef, ← map_pow, hζLpow, map_one]
  have hζF : IsPrimitiveRoot ζF (r : ℕ) := by
    rw [hζFdef]; exact hζL.map_of_injective (comapValEquiv r D hr).injective
  have key : (AlgEquiv.autCongr (comapValEquiv r D hr) σ) ζF
      = ζF ^ (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ).val.val := by
    rw [AlgEquiv.autCongr_apply]
    simp only [AlgEquiv.trans_apply]
    rw [hζFdef, AlgEquiv.symm_apply_apply,
        galEquivZMod_apply_of_pow_eq (r : ℕ) _ σ hζLpow, map_pow]
  have key2 : (AlgEquiv.autCongr (comapValEquiv r D hr) σ) ζF
      = ζF ^ (galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
          (AlgEquiv.autCongr (comapValEquiv r D hr) σ)).val.val :=
    galEquivZMod_apply_of_pow_eq (r : ℕ) _ _ hζFpow
  have hpow : ζF ^ (galEquivZMod (r : ℕ) ↥(cyclotomicField' r)
        (AlgEquiv.autCongr (comapValEquiv r D hr) σ)).val.val
      = ζF ^ (galEquivZMod (r : ℕ)
          ↥((cyclotomicField' r).comap (cyclotomicField' D).val) σ).val.val := by
    rw [← key2, key]
  rw [(hζF.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζF.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff'] at hpow
  simp only [ZMod.natCast_val, ZMod.cast_id] at hpow
  exact Units.ext hpow

end Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

open Workspace.ProofLemmas.CutOutFieldLevelInvariantProof

/-- **Fixed-field descent (pure Galois theory).** For a normal intermediate field `L` of the finite
Galois extension `ℚ(ζ_D)/ℚ` and a subgroup `H ≤ Gal(L/ℚ)`, the fixed field of the pullback
`H.comap (restrictNormalHom L) ≤ Gal(ℚ(ζ_D)/ℚ)` is the lift to `ℚ(ζ_D)` of the fixed field of `H`.

Proved from Mathlib's `InfiniteGalois.restrict_fixedField`, composed with
`Subgroup.map_comap_eq_self_of_surjective` (the restriction map is surjective) and
`fixedField (H.comap (restrictNormalHom L)) ≤ L` (since that subgroup contains
`(restrictNormalHom L).ker = L.fixingSubgroup`, whose fixed field is `L`).  Stated over a generic
`L` so that `↥L` carries only its canonical `IntermediateField` ℚ-algebra structure — this avoids
the instance diamond that blocks the same argument inline (where `↥(cyclotomicField' D)` forces
`DivisionRing.toRatAlgebra`). -/
theorem fixedFieldDescent (D : ℕ+)
    (L : IntermediateField ℚ ↥(cyclotomicField' D)) [Normal ℚ ↥L]
    (H : Subgroup (↥L ≃ₐ[ℚ] ↥L)) :
    IntermediateField.fixedField (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L))
      = IntermediateField.lift (IntermediateField.fixedField H) := by
  -- Bridge the ℚ-algebra diamond: the Mathlib Galois lemmas below use `IntermediateField.algebra'`
  -- on `↥L`, so provide the `Normal` instance in that form (defeq to the ambient one).
  haveI hnorm : @Normal ℚ ↥L _ _ (IntermediateField.algebra' L) := by
    convert (inferInstance : Normal ℚ ↥L) using 2
  have hle : IntermediateField.fixedField
      (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L)) ≤ L := by
    have hker : (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker
        ≤ H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L) := by
      intro σ hσ
      rw [MonoidHom.mem_ker] at hσ
      rw [Subgroup.mem_comap, hσ]
      exact one_mem H
    have hkereq : (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker
        = L.fixingSubgroup := IntermediateField.restrictNormalHom_ker L
    calc IntermediateField.fixedField
            (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L))
        ≤ IntermediateField.fixedField
            (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L).ker :=
          IntermediateField.fixedField_le hker
      _ = IntermediateField.fixedField L.fixingSubgroup := by rw [hkereq]
      _ = L := IsGalois.fixedField_fixingSubgroup L
  have key := InfiniteGalois.restrict_fixedField
    (H.comap (AlgEquiv.restrictNormalHom (K₁ := ↥(cyclotomicField' D)) ↥L)) L
  rw [inf_eq_left.mpr hle] at key
  rw [key]
  exact congrArg (fun S => IntermediateField.lift (IntermediateField.fixedField S))
    (Subgroup.map_comap_eq_self_of_surjective
      (AlgEquiv.restrictNormalHom_surjective (K₁ := ↥L) (E := ↥(cyclotomicField' D))) H)

/-- **Def A.5 (level-independence of the cut-out field).** For `r ∣ D`, the subfield of `ℂ`
cut out by a Dirichlet character `ψ` of modulus `r` is the same whether we regard `ψ` at level
`r` or push it up to level `D` via `changeLevel`. Proved from Mathlib only. -/
theorem CutOutFieldLevelInvariant (r D : ℕ+) (ψ : DirichletCharacter ℂ (r : ℕ)) (hr : (r : ℕ) ∣ (D : ℕ)) :
    cutOutField D (DirichletCharacter.changeLevel hr ψ) = cutOutField r ψ := by
  haveI iscL : IsCyclotomicExtension {(r : ℕ)} ℚ
      ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsCyclotomicExtension.equiv {(r : ℕ)} ℚ (↥(cyclotomicField' r)) (comapValEquiv r D hr).symm
  haveI isgL : IsGalois ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    IsGalois.of_algEquiv (comapValEquiv r D hr).symm
  haveI finL : FiniteDimensional ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) :=
    Module.Finite.equiv (comapValEquiv r D hr).symm.toLinearEquiv
  haveI nfL : NumberField ↥((cyclotomicField' r).comap (cyclotomicField' D).val) := ⟨⟩
  haveI galD : IsGalois ℚ ↥(cyclotomicField' D) := inferInstance
  haveI norD : Normal ℚ ↥(cyclotomicField' D) := inferInstance
  haveI norL := isgL.to_normal
  -- Level-compatibility square: `unitsMap hr ∘ galToUnits D = galEquivZMod r L ∘ restrictNormalHom L`.
  have hmid : ((ZMod.unitsMap hr).comp (galToUnits D).toMonoidHom)
      = (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom.comp
          (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
    refine MonoidHom.ext fun σ => ?_
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, galToUnits]
    exact (galEquivZMod_restrictNormal_apply (D : ℕ) ↥(cyclotomicField' D)
      (F := ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) hr σ).symm
  -- Kernel identity: the level-`D` kernel is the pullback of the level-`L` kernel.
  have hA : ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = ((ψ.toUnitHom.comp
            (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).comap
          (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
    rw [DirichletCharacter.changeLevel_toUnitHom, MonoidHom.comp_assoc, hmid,
        ← MonoidHom.comp_assoc, MonoidHom.comap_ker]
  -- The image of the level-`D` kernel under restriction is exactly the level-`L` kernel.
  have hmapH : Subgroup.map
        (AlgEquiv.restrictNormalHom ↥((cyclotomicField' r).comap (cyclotomicField' D).val))
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker := by
    rw [hA]
    apply Subgroup.map_comap_eq_self_of_surjective
    exact AlgEquiv.restrictNormalHom_surjective _
  -- Descent of the fixed field along the tower `ℚ(ζ_D) / L / ℚ`.  This is the pure
  -- Galois-theory fact `InfiniteGalois.restrict_fixedField` (a fixed field descends along a
  -- normal intermediate field), specialised to our tower.  See `fixedFieldDescent` for the precise
  -- statement and the discussion there of the
  -- Mathlib ℚ-algebra instance diamond that blocks discharging it inline.
  have hB : IntermediateField.fixedField
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker
      = IntermediateField.lift
          (IntermediateField.fixedField
            (ψ.toUnitHom.comp
              (galEquivZMod (r : ℕ)
                ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker) := by
    rw [hA]
    haveI hn : @Normal ℚ ↥((cyclotomicField' r).comap (cyclotomicField' D).val) _ _
        (IntermediateField.algebra' ((cyclotomicField' r).comap (cyclotomicField' D).val)) := by
      convert norL using 2
    exact @fixedFieldDescent D ((cyclotomicField' r).comap (cyclotomicField' D).val) hn
      (ψ.toUnitHom.comp
        (galEquivZMod (r : ℕ) ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
  -- The two embeddings of `L` into `ℂ` agree: directly and through `comapValEquiv`.
  have hι : (cyclotomicField' D).val.comp
        ((cyclotomicField' r).comap (cyclotomicField' D).val).val
      = (cyclotomicField' r).val.comp (comapValEquiv r D hr).toAlgHom := by
    apply AlgHom.ext
    intro x
    have hx := comapValEquiv_coe r D hr x
    simpa only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_algHom]
      using hx.symm
  -- Naturality moves the level-`L` kernel to the level-`r` kernel across `comapValEquiv`.
  have hnat : (ψ.toUnitHom.comp
        (galEquivZMod (r : ℕ)
          ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
      = ((ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker).comap
          (AlgEquiv.autCongr (comapValEquiv r D hr)).toMonoidHom := by
    ext σ
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, galToUnits]
    rw [galEquivZMod_comapValEquiv r D hr σ]
  have hnat_map : Subgroup.map (AlgEquiv.autCongr (comapValEquiv r D hr)).toMonoidHom
        (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ)
            ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker
      = (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker := by
    rw [hnat, Subgroup.map_comap_eq_self_of_surjective
      (AlgEquiv.autCongr (comapValEquiv r D hr)).surjective _]
  have hmapfix : (IntermediateField.fixedField
        (ψ.toUnitHom.comp
          (galEquivZMod (r : ℕ)
            ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).map
        (comapValEquiv r D hr).toAlgHom
      = IntermediateField.fixedField (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker := by
    rw [fixedField_map_autCongr (comapValEquiv r D hr), hnat_map]
  -- Assemble.  Re-elaborate `cutOutField` in the current context (via `show`) so the fixed-field
  -- terms carry these instances and `hB` matches, then compose the two lift maps.
  have goalL : cutOutField D (DirichletCharacter.changeLevel hr ψ)
      = (IntermediateField.fixedField
          (ψ.toUnitHom.comp
            (galEquivZMod (r : ℕ)
              ↥((cyclotomicField' r).comap (cyclotomicField' D).val)).toMonoidHom).ker).map
          ((cyclotomicField' D).val.comp
            ((cyclotomicField' r).comap (cyclotomicField' D).val).val) := by
    show IntermediateField.lift (IntermediateField.fixedField
        ((DirichletCharacter.changeLevel hr ψ).toUnitHom.comp (galToUnits D).toMonoidHom).ker) = _
    erw [hB]
    exact IntermediateField.map_map _ _ _
  have goalR : cutOutField r ψ
      = (IntermediateField.fixedField (ψ.toUnitHom.comp (galToUnits r).toMonoidHom).ker).map
          (cyclotomicField' r).val := rfl
  rw [goalL, goalR, hι, ← hmapfix]
  exact (IntermediateField.map_map _ _ _).symm

open Complex
open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaCutOutChangeLevelInvariant
    (r D : ℕ+) (ψ : DirichletCharacter ℂ (r : ℕ)) (hr : (r : ℕ) ∣ (D : ℕ)) :
    cutOutField D (DirichletCharacter.changeLevel hr ψ) = cutOutField r ψ :=
  CutOutFieldLevelInvariant r D ψ hr

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by a product character `χ * χ'` is contained in the compositum
of the fields cut out by the factors: `cutOutField D (χ * χ') ≤ cutOutField D χ ⊔ cutOutField D χ'`.
This holds because `ker (χ * χ') ⊇ ker χ ∩ ker χ'`, and the fixed-field (Galois)
correspondence is antitone with `fixedField (H₁ ⊓ H₂) = fixedField H₁ ⊔ fixedField H₂`. -/
theorem SublemmaCutOutProductClosure
    (D : ℕ+) (χ χ' : DirichletCharacter ℂ (D : ℕ)) :
    cutOutField D (χ * χ') ≤ cutOutField D χ ⊔ cutOutField D χ' := by
  haveI : FiniteDimensional ℚ (cyclotomicField' D) := inferInstance
  -- General Galois-correspondence fact: if `Ha ⊓ Hb ≤ Hc` then
  -- `fixedField Hc ≤ fixedField Ha ⊔ fixedField Hb`.
  have core : ∀ (Ha Hb Hc : Subgroup (cyclotomicField' D ≃ₐ[ℚ] cyclotomicField' D)),
      Ha ⊓ Hb ≤ Hc →
      IntermediateField.fixedField Hc ≤
        IntermediateField.fixedField Ha ⊔ IntermediateField.fixedField Hb := by
    intro Ha Hb Hc hc
    set B := IntermediateField.fixedField Ha ⊔ IntermediateField.fixedField Hb with hB
    rw [← IsGalois.fixedField_fixingSubgroup B]
    apply IntermediateField.fixedField_antitone
    refine le_trans ?_ hc
    apply le_inf
    · have h1 : IntermediateField.fixedField Ha ≤ B := le_sup_left
      have := IntermediateField.fixingSubgroup_antitone h1
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
    · have h2 : IntermediateField.fixedField Hb ≤ B := le_sup_right
      have := IntermediateField.fixingSubgroup_antitone h2
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
  -- Kernel containment: `ker χ ⊓ ker χ' ≤ ker (χ * χ')`.
  have hker : (χ.toUnitHom.comp (galToUnits D).toMonoidHom).ker ⊓
      (χ'.toUnitHom.comp (galToUnits D).toMonoidHom).ker ≤
      ((χ * χ').toUnitHom.comp (galToUnits D).toMonoidHom).ker := by
    intro g hg
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulChar.toUnitHom_eq,
        MulChar.equivToUnitHom_mul_apply]
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulChar.toUnitHom_eq] at h1 h2
    rw [h1, h2, one_mul]
  -- Monotonicity of `IntermediateField.lift` (`lift E = map K.val E`).
  have lift_mono : ∀ {A B : IntermediateField ℚ ↥(cyclotomicField' D)}, A ≤ B →
      IntermediateField.lift A ≤ IntermediateField.lift B := by
    intro A B h
    exact IntermediateField.map_mono (cyclotomicField' D).val h
  -- Assemble.
  simp only [cutOutField]
  rw [← IntermediateField.lift_sup]
  apply lift_mono
  exact core _ _ _ hker

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaFsubsetM
    (ℓ : ℕ) (r : Fin ℓ → ℕ+) (D : ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime)
    (hm : ∀ i, (r i : ℕ) % 3 = 1)
    (hrd : ∀ i, (r i : ℕ) ∣ (D : ℕ))
    (ψ : ∀ i, DirichletCharacter ℂ (r i : ℕ))
    (hψord : ∀ i, orderOf (ψ i) = 3)
    (χ : Fin ℓ → DirichletCharacter ℂ (D : ℕ))
    (hχ : ∀ i, χ i = (DirichletCharacter.changeLevel (hrd i)) (ψ i))
    (chi : DirichletCharacter ℂ (D : ℕ))
    (hchi : chi = ∏ i, χ i) :
    cutOutField D chi ≤ ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) := by
  set M := ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) with hM
  -- Each factor's cut-out field equals a cyclic cubic subfield.
  have hcut : ∀ i, cutOutField D (χ i) = cyclicCubicSubfield (r i) (hp i) (hm i) := by
    intro i
    rw [hχ i, SublemmaCutOutChangeLevelInvariant (r i) D (ψ i) (hrd i),
        SublemmaCutOutFieldCubicChar (r i) (hp i) (hm i) (ψ i) (hψord i)]
  -- Each factor's cut-out field is ≤ M.
  have hfac : ∀ i, cutOutField D (χ i) ≤ M := by
    intro i
    rw [hcut i]
    exact le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i
  -- The trivial character cuts out ⊥.
  have h1 : cutOutField D (1 : DirichletCharacter ℂ (D : ℕ)) = ⊥ := by
    unfold cutOutField
    have hker : ((1 : DirichletCharacter ℂ (D : ℕ)).toUnitHom.comp
        (galToUnits D).toMonoidHom).ker = ⊤ := by
      rw [MonoidHom.ker_eq_top_iff]
      ext σ
      simp
    rw [hker]
    exact (congrArg IntermediateField.lift
      (IsGalois.fixedField_top (F := ℚ) (E := ↥(cyclotomicField' D)))).trans
        (IntermediateField.lift_bot ℚ (cyclotomicField' D))
  rw [hchi]
  refine Finset.prod_induction χ (fun x => cutOutField D x ≤ M) ?_ ?_ (fun i _ => hfac i)
  · intro a b ha hb
    exact le_trans (SublemmaCutOutProductClosure D a b) (sup_le ha hb)
  · show cutOutField D 1 ≤ M
    rw [h1]; exact bot_le

open NumberField

theorem SublemmaTotallyRealSubfield :
    ∀ (A B : IntermediateField ℚ ℂ) [NumberField ↥A] [NumberField ↥B],
      A ≤ B → NumberField.IsTotallyReal ↥B → NumberField.IsTotallyReal ↥A := by
  intro A B _ _ h hB
  letI : Algebra ↥A ↥B := (IntermediateField.inclusion h).toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ↥A ↥B := by infer_instance
  exact NumberField.IsTotallyReal.of_algebra ↥A ↥B

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by a Dirichlet character `χ` of modulus `m` is Galois
(indeed abelian) over `ℚ`. -/
theorem SublemmaCutOutFieldGalois (m : ℕ+) (χ : DirichletCharacter ℂ (m : ℕ)) :
    IsGalois ℚ ↥(cutOutField m χ) := by
  set H := (χ.toUnitHom.comp (galToUnits m).toMonoidHom).ker with hH
  haveI hg : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup _
  have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(cutOutField m χ) :=
    IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)
  exact IsGalois.of_algEquiv e

open NumberField

theorem SublemmaNoZeta3 (F : IntermediateField ℚ ℂ) [NumberField ↥F]
    (hF : NumberField.IsTotallyReal ↥F) :
    ¬ ∃ x : ↥F, IsPrimitiveRoot x 3 := by
  rintro ⟨x, hx⟩
  -- The natural embedding of F into ℂ.
  set φ : ↥F →+* ℂ := algebraMap ↥F ℂ with hφ
  have hinj : Function.Injective φ := φ.injective
  -- φ x is a primitive cube root of unity in ℂ.
  have hxc : IsPrimitiveRoot (φ x) 3 := hx.map_of_injective hinj
  -- φ is a real embedding, so φ x is real.
  have hreal : NumberField.ComplexEmbedding.IsReal φ := hF.complexEmbedding_isReal φ
  have hconj : (starRingEnd ℂ) (φ x) = φ x := by
    have := NumberField.ComplexEmbedding.isReal_iff.mp hreal
    exact RingHom.congr_fun this x
  have him : (φ x).im = 0 := by
    have := Complex.conj_eq_iff_im.mp hconj
    exact this
  -- Let r be the real part; φ x = r.
  set r : ℝ := (φ x).re with hr
  have hxr : φ x = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [him]
  -- (φ x) ^ 3 = 1
  have hpow : (φ x) ^ 3 = 1 := hxc.pow_eq_one
  rw [hxr] at hpow
  have hr3 : r ^ 3 = 1 := by
    have : ((r ^ 3 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination hpow
    exact_mod_cast this
  -- φ x ≠ 1
  have hne : φ x ≠ 1 := hxc.ne_one (by norm_num)
  rw [hxr] at hne
  have hrne : r ≠ 1 := by
    intro h; apply hne; rw [h]; norm_num
  -- Derive contradiction.
  have hfac : (r - 1) * (r ^ 2 + r + 1) = 0 := by linear_combination hr3
  have hquad : r ^ 2 + r + 1 = 0 := by
    rcases mul_eq_zero.mp hfac with h | h
    · exact absurd (by linarith : r = 1) hrne
    · exact h
  nlinarith [sq_nonneg (2 * r + 1), hquad]

-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the unique cyclic cubic subfield of Q(zeta_r) is totally real.
--   Proof idea: reduce `IsTotallyReal` of the lifted subfield to membership of the fixed field
--   `E = fixedField H` inside `maximalRealSubfield (ℚ(ζ_r))`. Since ℚ(ζ_r)/ℚ is Galois, every
--   complex embedding φ factors as `ι ∘ σ` (`Normal.algHomEquivAut`). Complex conjugation gives an
--   automorphism `c` with `c ∘ c = 1`; hence `galToUnits c` is its own cube (`g² = 1 ⇒ g³ = g`), so
--   `c ∈ H` (the cubes subgroup). The Galois group is abelian (`galToUnits` is a `MulEquiv` onto the
--   commutative group `(ZMod r)ˣ`), so `σ x ∈ E` whenever `x ∈ E`, and `c` fixes it — giving
--   `star (φ x) = φ x` for every embedding `φ`.


open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CyclicCubicSubfieldTotallyReal (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    [NumberField ↥(cyclicCubicSubfield r hr hr3)] :
    NumberField.IsTotallyReal ↥(cyclicCubicSubfield r hr hr3) := by
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom with hH
  have hlift : cyclicCubicSubfield r hr hr3
      = IntermediateField.lift (IntermediateField.fixedField H) := rfl
  rw [hlift]
  rw [← NumberField.isTotallyReal_iff_ofRingEquiv
        (IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)).toRingEquiv]
  refine (NumberField.isTotallyReal_iff_le_maximalRealSubfield
            (E := (IntermediateField.fixedField H).toSubfield)).mpr ?_
  set ι : cyclotomicField' r →+* ℂ := algebraMap (cyclotomicField' r) ℂ with hι
  have hιinj : Function.Injective ι := (algebraMap (cyclotomicField' r) ℂ).injective
  set eqv := Normal.algHomEquivAut ℚ ℂ (E := cyclotomicField' r) with heqv
  -- Every complex embedding factors through the Galois group: `g y = ι (eqv g y)`.
  have key : ∀ (g : cyclotomicField' r →ₐ[ℚ] ℂ) (y : cyclotomicField' r),
      g y = ι ((eqv g) y) := by
    intro g y
    have h1 : g = eqv.symm (eqv g) := (Equiv.symm_apply_apply _ g).symm
    conv_lhs => rw [h1]
    rw [heqv, Normal.algHomEquivAut_symm_apply]
    rfl
  -- The Galois group is abelian (it is `MulEquiv` to `(ZMod r)ˣ`).
  have hcomm : ∀ a b : cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r, a * b = b * a := by
    intro a b
    apply (galToUnits r).injective
    rw [map_mul, map_mul, mul_comm]
  intro x hx φ
  set φA : cyclotomicField' r →ₐ[ℚ] ℂ := φ.toRatAlgHom with hφA
  set ψR : cyclotomicField' r →+* ℂ := (starRingEnd ℂ).comp ι with hψR
  set ψA : cyclotomicField' r →ₐ[ℚ] ℂ := ψR.toRatAlgHom with hψA
  set σ := eqv φA with hσ
  set c := eqv ψA with hc
  -- Complex conjugation of the ambient field, transported to the automorphism `c`.
  have hcrel : ∀ y, ι (c y) = starRingEnd ℂ (ι y) := by
    intro y
    have hk := (key ψA y).symm
    rw [hc, hk, hψA, RingHom.toRatAlgHom_apply, hψR]
    rfl
  -- `c` is an involution.
  have hcinv : c * c = 1 := by
    apply AlgEquiv.ext
    intro y
    apply hιinj
    show ι ((c * c) y) = ι y
    rw [AlgEquiv.mul_apply, hcrel, hcrel, Complex.conj_conj]
  -- Since `galToUnits c` squares to `1`, it equals its own cube, so `c ∈ H`.
  have hcH : c ∈ H := by
    rw [hH]
    show (galToUnits r).toMonoidHom c
        ∈ (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    have hsq : (galToUnits r c) ^ 2 = 1 := by
      have h2 : galToUnits r (c * c) = (galToUnits r c) ^ 2 := by rw [map_mul, sq]
      rw [hcinv, map_one] at h2
      exact h2.symm
    refine ⟨galToUnits r c, ?_⟩
    show (galToUnits r c) ^ 3 = galToUnits r c
    rw [pow_succ, hsq, one_mul]
  -- `σ x` lies in the fixed field (abelian group ⇒ the fixed field is `σ`-stable).
  have hσx : σ x ∈ IntermediateField.fixedField H := by
    rw [IntermediateField.mem_fixedField_iff]
    intro h hhH
    have hhx : h x = x := (IntermediateField.mem_fixedField_iff H x).mp hx h hhH
    calc h (σ x) = (h * σ) x := (AlgEquiv.mul_apply h σ x).symm
      _ = (σ * h) x := by rw [hcomm]
      _ = σ (h x) := AlgEquiv.mul_apply σ h x
      _ = σ x := by rw [hhx]
  -- Therefore `c` fixes `σ x`.
  have hcfix : c (σ x) = σ x :=
    (IntermediateField.mem_fixedField_iff H (σ x)).mp hσx c hcH
  show star (φ x) = φ x
  have hφx : φ x = ι (σ x) := by
    have hxeq : φ x = φA x := (RingHom.toRatAlgHom_apply φ x).symm
    rw [hxeq, hσ]; exact key φA x
  rw [hφx, Complex.star_def, ← hcrel (σ x), hcfix]

-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the cyclic cubic subfield of Q(zeta_r) has degree 3 over Q.
--   Proof: the cyclic cubic subfield is `lift (fixedField H)` with
--   `H = comap galToUnits ((powMonoidHom 3).range)` inside `Gal(Q(zeta_r)/Q) ≃ (ZMod r)ˣ`.
--   `finrank Q (lift E) = finrank Q E` (via `IntermediateField.equivMap`), which equals `H.index`
--   (finite-Galois tower + `finrank_fixedField_eq_card` + `card_aut_eq_finrank` + `card_mul_index`),
--   and `H.index = (powMonoidHom 3).range.index = gcd (card (ZMod r)ˣ) 3 = gcd (r-1) 3 = 3`
--   using `Subgroup.index_comap_of_surjective` and `IsCyclic.index_powMonoidHom_range`
--   (with `ZMod.isCyclic_units_prime`).


open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 800000

theorem CyclicCubicSubfieldDegree (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3) = 3 := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom) with hH
  -- Step 1: transfer degree from `cyclicCubicSubfield = lift (fixedField H)` down to `fixedField H`.
  have key : Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3)
      = Module.finrank ℚ ↥(IntermediateField.fixedField H) := by
    have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ] ↥(cyclicCubicSubfield r hr hr3) :=
      IntermediateField.equivMap (IntermediateField.fixedField H) (cyclotomicField' r).val
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  rw [key]
  -- Step 2: finrank ℚ ↥(fixedField H) = H.index
  have hindex : Module.finrank ℚ ↥(IntermediateField.fixedField H) = H.index := by
    have h1 : Module.finrank ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
        = Nat.card ↥H := IntermediateField.finrank_fixedField_eq_card H
    have h2 : Module.finrank ℚ ↥(IntermediateField.fixedField H)
        * Module.finrank ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
        = Module.finrank ℚ ↥(cyclotomicField' r) :=
      Module.finrank_mul_finrank ℚ ↥(IntermediateField.fixedField H) ↥(cyclotomicField' r)
    have h3 : Nat.card (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r)
        = Module.finrank ℚ ↥(cyclotomicField' r) :=
      IsGalois.card_aut_eq_finrank ℚ ↥(cyclotomicField' r)
    have h4 : Nat.card ↥H * H.index
        = Nat.card (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) := Subgroup.card_mul_index H
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    have hL : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H
        = Module.finrank ℚ ↥(cyclotomicField' r) := by rw [← h1]; exact h2
    have hR : Nat.card ↥H * H.index = Module.finrank ℚ ↥(cyclotomicField' r) := by
      rw [h4, h3]
    have hcomb : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H
        = H.index * Nat.card ↥H := by
      rw [mul_comm H.index]; exact hL.trans hR.symm
    exact Nat.eq_of_mul_eq_mul_right hpos hcomb
  rw [hindex]
  -- Step 3+4: H.index = (powMonoidHom 3).range.index = gcd (card units) 3 = 3
  haveI : IsCyclic (ZMod (r : ℕ))ˣ := ZMod.isCyclic_units_prime hr
  have hsurj : Function.Surjective (galToUnits r).toMonoidHom := (galToUnits r).surjective
  rw [hH, Subgroup.index_comap_of_surjective _ hsurj, IsCyclic.index_powMonoidHom_range]
  have h3 : 3 ∣ Nat.card (ZMod (r : ℕ))ˣ := by
    have hc : Nat.card (ZMod (r : ℕ))ˣ = (r : ℕ) - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hr]
    rw [hc]; omega
  rw [Nat.gcd_eq_right h3]

-- Cited from: L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Springer, 1997, Chapter 3, especially Theorem 3.11; J. Neukirch, Algebraic Number Theory, Springer, 1999, Chapter VI.
-- Paper label: Proposition A.11(i)
-- NL statement: For a rational prime r congruent to 1 mod 3, the cyclic cubic subfield of Q(zeta_r) has field conductor exactly r: it embeds into Q(zeta_m) precisely when r divides m.
--
-- The classical content
-- is Mathlib's cyclotomic Galois correspondence in
-- `Mathlib.NumberTheory.NumberField.Cyclotomic.Galois`
-- (`intermediateFieldEquivSubgroupChar` and
-- `mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd`).


open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Complex IsCyclotomicExtension IsCyclotomicExtension.Rat

set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

namespace Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof

/-- `zetaC a` is a power of `zetaC b` whenever `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  congr 1
  obtain ⟨k, hk⟩ := h
  have hr0 : (a : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hm0 : (b : ℂ) ≠ 0 := by exact_mod_cast b.pos.ne'
  have hkdiv : (b : ℕ) / (a : ℕ) = k := by rw [hk]; exact Nat.mul_div_cancel_left k a.pos
  rw [hkdiv]
  have hkc : (b : ℂ) = (a : ℂ) * (k : ℂ) := by exact_mod_cast hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have : k ≠ 0 := by rintro rfl; simp at hk
    exact_mod_cast this
  rw [hkc]
  field_simp

/-- Monotonicity of the concrete cyclotomic fields with respect to divisibility. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- The subgroup of cubes in `(ℤ/rℤ)ˣ` is proper when `r ≡ 1 (mod 3)` is prime. -/
theorem cubes_range_ne_top (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range ≠ ⊤ := by
  haveI : Fact (r : ℕ).Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : (3 : ℕ) ∣ Fintype.card (ZMod (r : ℕ))ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hr]; omega
  intro htop
  have hsurj : Function.Surjective (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ) :=
    MonoidHom.range_eq_top.mp htop
  have hinj : Function.Injective (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ) :=
    (Finite.injective_iff_surjective).mpr hsurj
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 3 hcard
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x = 1 := hinj (by simpa [powMonoidHom] using hx3)
  rw [hx1] at hx; simp at hx

/-- Restricting a subfield `S ≤ ℚ(ζ_N)` to `ℚ(ζ_N)` and lifting back recovers `S`. -/
theorem comap_val_roundtrip_gen (S : IntermediateField ℚ ℂ) (N : ℕ+)
    (hSN : S ≤ cyclotomicField' N) :
    IntermediateField.lift (S.comap (cyclotomicField' N).val) = S := by
  show (S.comap (cyclotomicField' N).val).map (cyclotomicField' N).val = S
  rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
  exact hSN

/-- The `ℚ`-algebra isomorphism `ℚ(ζ_a) ⊆ ℚ(ζ_N)  ≃  ℚ(ζ_a)` when `a ∣ N`. -/
noncomputable def comapValEquiv (a N : ℕ+) (haN : (a : ℕ) ∣ (N : ℕ)) :
    ↥((cyclotomicField' a).comap (cyclotomicField' N).val) ≃ₐ[ℚ] ↥(cyclotomicField' a) :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq
      (comap_val_roundtrip_gen (cyclotomicField' a) N (cyclotomicField'_mono a N haN)))

/-- The cyclic cubic subfield of `ℚ(ζ_r)` is nontrivial (not equal to `ℚ`). -/
theorem cyclicCubicSubfield_ne_bot (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1) :
    cyclicCubicSubfield r hr hr3 ≠ ⊥ := by
  intro hbot
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    ((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom with hHdef
  have hbot' : IntermediateField.lift (IntermediateField.fixedField H) = ⊥ := hbot
  have hlbot : IntermediateField.lift (⊥ : IntermediateField ℚ ↥(cyclotomicField' r)) = ⊥ :=
    IntermediateField.map_bot _
  have hfixedbot : IntermediateField.fixedField H = ⊥ :=
    (IntermediateField.lift_inj _ _).mp (hbot'.trans hlbot.symm)
  have hHtop : H = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField H, hfixedbot,
      IntermediateField.fixingSubgroup_bot]
  have hf : Function.Surjective ⇑((galToUnits r).toMonoidHom) := (galToUnits r).surjective
  have hrange : (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range = ⊤ := by
    have hself := Subgroup.map_comap_eq_self_of_surjective hf
      (powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range
    rw [← hHdef, hHtop, Subgroup.map_top_of_surjective _ hf] at hself
    exact hself.symm
  exact cubes_range_ne_top r hr hr3 hrange

/-- Key direction: if the cyclic cubic subfield embeds in `ℚ(ζ_m)`, then `r ∣ m`. -/
theorem hardDir (r m : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (hle : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' m) : (r : ℕ) ∣ (m : ℕ) := by
  set N : ℕ+ := r * m with hN
  have hNcoe : (N : ℕ) = (r : ℕ) * (m : ℕ) := by rw [hN]; exact PNat.mul_coe r m
  have hrN : (r : ℕ) ∣ (N : ℕ) := by rw [hNcoe]; exact dvd_mul_right _ _
  have hmN : (m : ℕ) ∣ (N : ℕ) := by rw [hNcoe]; exact dvd_mul_left _ _
  haveI hER : HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod (N : ℕ))ˣ) := inferInstance
  haveI iscr : IsCyclotomicExtension {(r : ℕ)} ℚ
      ↥((cyclotomicField' r).comap (cyclotomicField' N).val) :=
    IsCyclotomicExtension.equiv {(r : ℕ)} ℚ (↥(cyclotomicField' r)) (comapValEquiv r N hrN).symm
  haveI isgr : IsGalois ℚ ↥((cyclotomicField' r).comap (cyclotomicField' N).val) :=
    IsGalois.of_algEquiv (comapValEquiv r N hrN).symm
  haveI iscm : IsCyclotomicExtension {(m : ℕ)} ℚ
      ↥((cyclotomicField' m).comap (cyclotomicField' N).val) :=
    IsCyclotomicExtension.equiv {(m : ℕ)} ℚ (↥(cyclotomicField' m)) (comapValEquiv m N hmN).symm
  haveI isgm : IsGalois ℚ ↥((cyclotomicField' m).comap (cyclotomicField' N).val) :=
    IsGalois.of_algEquiv (comapValEquiv m N hmN).symm
  have hLr0 : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' r := IntermediateField.lift_le _
  have hLK : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' N :=
    le_trans hLr0 (cyclotomicField'_mono r N hrN)
  have hround_L : IntermediateField.lift
      ((cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val)
      = cyclicCubicSubfield r hr hr3 := comap_val_roundtrip_gen _ N hLK
  have hFL_ne : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val ≠ ⊥ := by
    intro hbot
    apply cyclicCubicSubfield_ne_bot r hr hr3
    rw [← hround_L, hbot, IntermediateField.lift_bot]
  set Φ := intermediateFieldEquivSubgroupChar (N : ℕ) (↥(cyclotomicField' N)) ℂ with hΦ
  have hΦL_ne : Φ ((cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val) ≠ ⊥ := by
    rw [← OrderIso.map_bot Φ]
    intro h
    exact hFL_ne (Φ.injective h)
  obtain ⟨χ, hχmem, hχ1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hΦL_ne
  have hLr : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val
      ≤ (cyclotomicField' r).comap (cyclotomicField' N).val :=
    (IntermediateField.gc_map_comap (cyclotomicField' N).val).monotone_u hLr0
  have hLm : (cyclicCubicSubfield r hr hr3).comap (cyclotomicField' N).val
      ≤ (cyclotomicField' m).comap (cyclotomicField' N).val :=
    (IntermediateField.gc_map_comap (cyclotomicField' N).val).monotone_u hle
  have hχr : χ ∈ Φ ((cyclotomicField' r).comap (cyclotomicField' N).val) := Φ.monotone hLr hχmem
  have hχm : χ ∈ Φ ((cyclotomicField' m).comap (cyclotomicField' N).val) := Φ.monotone hLm hχmem
  have hiffr := @mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd (N : ℕ) _
    (↥(cyclotomicField' N)) _ _ _ ℂ _ _ _
    ((cyclotomicField' r).comap (cyclotomicField' N).val) (r : ℕ) _ isgr iscr hrN
  have hiffm := @mem_intermediateFieldEquivSubgroupChar_iff_conductor_dvd (N : ℕ) _
    (↥(cyclotomicField' N)) _ _ _ ℂ _ _ _
    ((cyclotomicField' m).comap (cyclotomicField' N).val) (m : ℕ) _ isgm iscm hmN
  rw [← hΦ] at hiffr hiffm
  have hcondr : χ.conductor ∣ (r : ℕ) := (hiffr χ).mp hχr
  have hcondm : χ.conductor ∣ (m : ℕ) := (hiffm χ).mp hχm
  have hcond1 : χ.conductor ≠ 1 := by
    intro h1
    apply hχ1
    have hft : χ.FactorsThrough 1 := by
      have hfc := DirichletCharacter.factorsThrough_conductor χ
      rwa [h1] at hfc
    exact (DirichletCharacter.factorsThrough_one_iff χ).mp hft
  have hcondeq : χ.conductor = (r : ℕ) := (hr.eq_one_or_self_of_dvd _ hcondr).resolve_left hcond1
  rw [← hcondeq]
  exact hcondm

end Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof

/-- **Proposition A.11(i).** For a rational prime `r ≡ 1 (mod 3)`, the cyclic cubic
subfield of `ℚ(ζ_r)` embeds into `ℚ(ζ_m)` iff `r ∣ m`; equivalently its field
conductor is exactly `r`. Proved from Mathlib's cyclotomic Galois correspondence. -/
theorem CyclicCubicSubfieldConductor (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) :
    ∀ m : ℕ+, cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' m ↔ (r : ℕ) ∣ (m : ℕ) := by
  intro m
  refine ⟨fun hle => ?_, fun hdvd => ?_⟩
  · exact Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof.hardDir r m hr hr3 hle
  · exact le_trans (IntermediateField.lift_le _)
      (Workspace.ProofLemmas.CyclicCubicSubfieldConductorProof.cyclotomicField'_mono r m hdvd)

open scoped NumberField

theorem CompositumSubfieldsGenerateTop {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [NumberField ↥(⨆ i, L i)] :
    (⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) =
      (⊤ : Subfield ↥(⨆ i, L i)) := by
  set N : IntermediateField ℚ ℂ := ⨆ i, L i with hN
  set ι : ↥N →+* ℂ := algebraMap ↥N ℂ with hι
  have hιinj : Function.Injective ι := (algebraMap ↥N ℂ).injective
  have hrange : ι.fieldRange = N.toSubfield := by
    ext c
    simp only [RingHom.mem_fieldRange, IntermediateField.mem_toSubfield]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hc; exact ⟨⟨c, hc⟩, rfl⟩
  -- comap ι ∘ map ι = id  (ι injective)
  have hcm : ∀ X : Subfield ↥N, Subfield.comap ι (Subfield.map ι X) = X := by
    intro X
    ext x
    simp only [Subfield.mem_comap, Subfield.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩; rwa [hιinj hax] at ha
    · intro hx; exact ⟨x, hx, rfl⟩
  cases isEmpty_or_nonempty (Fin ℓ) with
  | inl hempty =>
    have hN0 : N = ⊥ := by rw [hN, iSup_of_empty]
    rw [iSup_of_empty, eq_top_iff]
    intro x _
    have hxb : (x : ℂ) ∈ (⊥ : IntermediateField ℚ ℂ) := by rw [← hN0]; exact x.2
    obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp hxb
    have hxe : x = (q : ↥N) := by
      apply Subtype.ext
      rw [← hq]; simp
    rw [hxe]
    exact SubfieldClass.ratCast_mem _ q
  | inr hne =>
    have hmt : Subfield.map ι ⊤ = N.toSubfield := by
      rw [← hrange]; ext c; simp [Subfield.mem_map, RingHom.mem_fieldRange]
    have key : Subfield.map ι (⨆ i, Subfield.comap ι (L i).toSubfield) = Subfield.map ι ⊤ := by
      rw [hmt, (Subfield.gc_map_comap ι).l_iSup]
      have hstep : ∀ i, Subfield.map ι (Subfield.comap ι (L i).toSubfield) = (L i).toSubfield := by
        intro i
        rw [Subfield.map_comap_eq, hrange, inf_eq_left]
        intro c hc
        simp only [IntermediateField.mem_toSubfield] at hc ⊢
        exact (le_iSup L i) hc
      simp_rw [hstep]
      rw [← IntermediateField.iSup_toSubfield]
    rw [← hcm (⨆ i, Subfield.comap ι (L i).toSubfield), key, hcm]

open scoped NumberField

theorem SubfieldComapOfIntermediateTotallyReal {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [NumberField ↥(⨆ i, L i)] (i : Fin ℓ) [NumberField ↥(L i)]
    [NumberField.IsTotallyReal ↥(L i)] :
    NumberField.IsTotallyReal
      ↥(Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) := by
  set N : IntermediateField ℚ ℂ := ⨆ i, L i with hN
  set ι : ↥N →+* ℂ := algebraMap ↥N ℂ with hι
  set S : Subfield ↥N := Subfield.comap ι (L i).toSubfield with hS
  have hLiN : L i ≤ N := le_iSup L i
  have hιinj : Function.Injective ι := (algebraMap ↥N ℂ).injective
  -- the ring map ↥S → ↥(L i) induced by the inclusion ι : ↥N → ℂ
  have hmem : ∀ x : ↥S, (ι.comp (Subfield.subtype S)) x ∈ (L i).toSubfield := fun x => x.2
  let g : ↥S →+* ↥(L i) := RingHom.codRestrict (ι.comp (Subfield.subtype S))
    (L i).toSubfield.toSubsemiring hmem
  have hginj : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    apply hιinj
    have : (g a : ℂ) = (g b : ℂ) := congrArg _ h
    simpa [g, RingHom.codRestrict] using this
  have hgsurj : Function.Surjective g := by
    intro y
    refine ⟨⟨⟨(y : ℂ), hLiN y.2⟩, ?_⟩, ?_⟩
    · show ι ⟨(y : ℂ), hLiN y.2⟩ ∈ (L i).toSubfield
      exact y.2
    · apply Subtype.ext
      rfl
  let e : ↥S ≃+* ↥(L i) := RingEquiv.ofBijective g ⟨hginj, hgsurj⟩
  exact NumberField.IsTotallyReal.ofRingEquiv e.symm

open scoped NumberField

theorem SublemmaCompositumTotallyReal {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, NumberField ↥(L i)] [∀ i, NumberField.IsTotallyReal ↥(L i)]
    [NumberField ↥(⨆ i, L i)] :
    NumberField.IsTotallyReal ↥(⨆ i, L i) := by
  haveI : ∀ i, NumberField.IsTotallyReal
      ↥(Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) := fun i =>
    SubfieldComapOfIntermediateTotallyReal L i
  have htop : (⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) =
      (⊤ : Subfield ↥(⨆ i, L i)) := CompositumSubfieldsGenerateTop L
  have h1 : NumberField.IsTotallyReal
      ↥(⨆ i, Subfield.comap (algebraMap ↥(⨆ i, L i) ℂ) (L i).toSubfield) :=
    NumberField.isTotallyReal_iSup
  rw [htop] at h1
  haveI := h1
  exact NumberField.IsTotallyReal.ofRingEquiv Subfield.topEquiv

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaCyclicCubicSubfieldNormal (r : ℕ+) (hr : (r : ℕ).Prime)
    (hr3 : (r : ℕ) % 3 = 1) :
    IsGalois ℚ ↥(cyclicCubicSubfield r hr hr3) := by
  unfold cyclicCubicSubfield
  set H : Subgroup (cyclotomicField' r ≃ₐ[ℚ] cyclotomicField' r) :=
    (((powMonoidHom 3 : (ZMod (r : ℕ))ˣ →* (ZMod (r : ℕ))ˣ).range).comap
      (galToUnits r).toMonoidHom) with hH
  -- The Galois group is abelian (iso to `(ZMod r)ˣ`), so every subgroup is normal.
  haveI hnormal : H.Normal := by
    refine ⟨fun a ha g => ?_⟩
    have hcomm : g * a * g⁻¹ = a := by
      apply (galToUnits r).injective
      rw [map_mul, map_mul, map_inv]
      rw [mul_comm (galToUnits r g) (galToUnits r a), mul_assoc, mul_inv_cancel, mul_one]
    rwa [hcomm]
  have hgal : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
    IsGalois.of_fixedField_normal_subgroup H
  -- transfer across `lift = map val`
  have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ]
      ↥(IntermediateField.lift (IntermediateField.fixedField H)) :=
    IntermediateField.equivMap (IntermediateField.fixedField H) (cyclotomicField' r).val
  exact (AlgEquiv.transfer_galois e).mp hgal

set_option maxHeartbeats 800000

theorem SublemmaCompositumGalois {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, IsGalois ℚ ↥(L i)] [∀ i, FiniteDimensional ℚ ↥(L i)] :
    IsGalois ℚ ↥(⨆ i, L i) ∧
      Nat.card (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) = Module.finrank ℚ ↥(⨆ i, L i) := by
  haveI hn : ∀ i, Normal ℚ ↥(L i) := fun i => IsGalois.to_normal
  haveI hs : ∀ i, Algebra.IsSeparable ℚ ↥(L i) := fun i => IsGalois.to_isSeparable
  haveI hnsup : Normal ℚ ↥(⨆ i, L i) := IntermediateField.normal_iSup ℚ ℂ (t := L) (h := hn)
  haveI hssup : Algebra.IsSeparable ℚ ↥(⨆ i, L i) :=
    IntermediateField.isSeparable_iSup ℚ ℂ (t := L) (h := hs)
  haveI hgal : IsGalois ℚ ↥(⨆ i, L i) := ⟨⟩
  haveI hfd : FiniteDimensional ℚ ↥(⨆ i, L i) :=
    IntermediateField.finiteDimensional_iSup_of_finite (t := L)
  exact ⟨hgal, IsGalois.card_aut_eq_finrank ℚ ↥(⨆ i, L i)⟩

open Workspace.Types.CyclotomicCharacterFields
open scoped NumberField

set_option maxHeartbeats 800000

theorem SublemmaCutOutFieldDegreeThree (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    (n : ℕ) (hchi : orderOf chi = n) :
    Module.finrank ℚ ↥(cutOutField D chi) = n := by
  rw [← hchi]
  set K := cyclotomicField' D with hK
  set φ := chi.toUnitHom.comp (galToUnits D).toMonoidHom with hφ
  set H := φ.ker with hH
  -- lift preserves degree over ℚ
  have hlift : Module.finrank ℚ ↥(cutOutField D chi) =
      Module.finrank ℚ ↥(IntermediateField.fixedField H) := by
    have e := IntermediateField.equivMap (IntermediateField.fixedField H) (K.val)
    exact (LinearEquiv.finrank_eq e.toLinearEquiv).symm
  rw [hlift]
  -- fixed field degree = index of H
  have hidx : Module.finrank ℚ ↥(IntermediateField.fixedField H) = H.index := by
    have hcard : Module.finrank ↥(IntermediateField.fixedField H) K = Nat.card ↥H :=
      IntermediateField.finrank_fixedField_eq_card H
    have htower : Module.finrank ℚ ↥(IntermediateField.fixedField H) *
        Module.finrank ↥(IntermediateField.fixedField H) K = Module.finrank ℚ K :=
      Module.finrank_mul_finrank ℚ ↥(IntermediateField.fixedField H) K
    have hgal : Module.finrank ℚ K = Nat.card (K ≃ₐ[ℚ] K) :=
      (IsGalois.card_aut_eq_finrank ℚ K).symm
    have hcmi : Nat.card ↥H * H.index = Nat.card (K ≃ₐ[ℚ] K) := Subgroup.card_mul_index H
    rw [hcard, hgal] at htower
    have hpos : 0 < Nat.card ↥H := Nat.card_pos
    have hfin : Module.finrank ℚ ↥(IntermediateField.fixedField H) * Nat.card ↥H =
        H.index * Nat.card ↥H := by rw [htower, ← hcmi, mul_comm]
    exact Nat.eq_of_mul_eq_mul_right hpos hfin
  rw [hidx, Subgroup.index_ker]
  -- goal: Nat.card ↥φ.range = orderOf chi
  have hsurj : Function.Surjective (galToUnits D).toMonoidHom := (galToUnits D).surjective
  have hrange : φ.range = chi.toUnitHom.range := by
    ext x
    simp only [hφ, MonoidHom.mem_range, MonoidHom.coe_comp, Function.comp_apply]
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨b, rfl⟩; obtain ⟨a, rfl⟩ := hsurj b; exact ⟨a, rfl⟩
  rw [hrange]
  exact DirichletCharacterRangeCardEqOrder chi

open scoped NumberField
open NumberField NumberField.InfinitePlace

/-- If `F` and `M` are number fields with `M` an extension of `F`, and both are totally real,
then `M/F` is unramified at all infinite places. -/
theorem SublemmaInfinitePlacesUnramifiedTotallyReal
    (F M : Type*) [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [FiniteDimensional F M]
    [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal M] :
    IsUnramifiedAtInfinitePlaces F M := by
  refine ⟨fun w => ?_⟩
  refine NumberField.InfinitePlace.isUnramified_iff.2 (Or.inl ?_)
  exact NumberField.IsTotallyReal.isReal w

set_option maxHeartbeats 1000000

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaLinearDisjointFromDisjointRamification {ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (r : Fin ℓ → ℕ+) (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1)
    (hinj : Function.Injective r) :
    iSupIndep (fun i => (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra) ∧
      ∀ i, cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
          (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)) = ⊥ := by
  classical
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  have hdeg : ∀ i, Module.finrank ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) = 3 :=
    fun i => CyclicCubicSubfieldDegree (r i) (hp i) (hm i)
  -- CORE: each L i meets the compositum of the others trivially.
  have hbot : ∀ i, cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
      (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)) = ⊥ := by
    intro i
    set X := ⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j) with hXdef
    set N : ℕ+ := ∏ j ∈ Finset.univ.erase i, r j with hNdef
    have hNcoe : (N : ℕ) = ∏ j ∈ Finset.univ.erase i, (r j : ℕ) := by
      rw [hNdef]; exact Finset.PNat.coe_prod r (Finset.univ.erase i)
    -- the compositum of the L j (j ≠ i) sits inside ℚ(ζ_N).
    have hXle : X ≤ cyclotomicField' N := by
      rw [hXdef]
      refine iSup_le (fun j => iSup_le (fun hji => ?_))
      refine (CyclicCubicSubfieldConductor (r j) (hp j) (hm j) N).mpr ?_
      rw [hNcoe]
      exact Finset.dvd_prod_of_mem (fun j => (r j : ℕ))
        (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    -- degree of the intersection divides [L i : ℚ] = 3, so is 1 or 3.
    letI : Algebra ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X)
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
      (IntermediateField.inclusion inf_le_left).toRingHom.toAlgebra
    haveI : IsScalarTower ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X)
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
      IsScalarTower.of_algebraMap_eq (fun x =>
        ((IntermediateField.inclusion
          (inf_le_left : cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X ≤ _)).commutes x).symm)
    have htower := Module.finrank_mul_finrank ℚ
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X) ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
    rw [hdeg i] at htower
    have hdvd3 : Module.finrank ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X) ∣ 3 :=
      ⟨_, htower.symm⟩
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd3 with h1 | h3
    · exact IntermediateField.finrank_eq_one_iff.mp h1
    · exfalso
      have heq : cyclicCubicSubfield (r i) (hp i) (hm i) ⊓ X
          = cyclicCubicSubfield (r i) (hp i) (hm i) :=
        IntermediateField.eq_of_le_of_finrank_eq inf_le_left (by rw [h3, hdeg i])
      have hLiX : cyclicCubicSubfield (r i) (hp i) (hm i) ≤ X := heq ▸ inf_le_right
      have hri : (r i : ℕ) ∣ (N : ℕ) :=
        (CyclicCubicSubfieldConductor (r i) (hp i) (hm i) N).mp (le_trans hLiX hXle)
      rw [hNcoe] at hri
      obtain ⟨j, hjmem, hrij⟩ := (hp i).prime.exists_mem_finset_dvd hri
      have hji : j ≠ i := (Finset.mem_erase.mp hjmem).1
      have hrieq : (r i : ℕ) = (r j : ℕ) := (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp hrij
      exact hji (hinj (PNat.coe_injective hrieq)).symm
  refine ⟨?_, hbot⟩
  rw [iSupIndep_def]
  intro i
  rw [disjoint_iff]
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra)
      ≤ (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra := by
    refine iSup_le (fun j => iSup_le (fun hji => ?_))
    exact IntermediateField.toSubalgebra_le_toSubalgebra.mpr
      (le_iSup_of_le j (le_iSup_of_le hji le_rfl))
  refine le_antisymm ?_ bot_le
  calc (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra ⊓
        (⨆ j, ⨆ (_ : j ≠ i), (cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra)
      ≤ (cyclicCubicSubfield (r i) (hp i) (hm i)).toSubalgebra ⊓
        (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j)).toSubalgebra :=
        inf_le_inf_left _ hle
    _ = (cyclicCubicSubfield (r i) (hp i) (hm i) ⊓
        (⨆ j, ⨆ (_ : j ≠ i), cyclicCubicSubfield (r j) (hp j) (hm j))).toSubalgebra :=
        (IntermediateField.inf_toSubalgebra _ _).symm
    _ = (⊥ : IntermediateField ℚ ℂ).toSubalgebra := by rw [hbot i]
    _ = ⊥ := IntermediateField.bot_toSubalgebra

set_option maxHeartbeats 2000000

theorem SublemmaDegreeCompositumLinearlyDisjoint {ℓ : ℕ}
    (L : Fin ℓ → IntermediateField ℚ ℂ) [∀ i, FiniteDimensional ℚ ↥(L i)]
    [∀ i, IsGalois ℚ ↥(L i)]
    (hindep : iSupIndep (fun i => (L i).toSubalgebra))
    (hdisj : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥) :
    Module.finrank ℚ ↥(⨆ i, L i) = ∏ i, Module.finrank ℚ ↥(L i) := by
  have key : ∀ s : Finset (Fin ℓ),
      Module.finrank ℚ ↥(⨆ i ∈ s, L i) = ∏ i ∈ s, Module.finrank ℚ ↥(L i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        haveI : FiniteDimensional ℚ ↥(⨆ i ∈ s, L i) :=
          IntermediateField.finiteDimensional_iSup_of_finset
        have hsub : (⨆ i ∈ s, L i) ≤ (⨆ j, ⨆ (_ : j ≠ a), L j) := by
          refine iSup_le (fun i => iSup_le (fun his => ?_))
          have hia : i ≠ a := fun h => ha (h ▸ his)
          exact le_iSup_of_le i (le_iSup_of_le hia le_rfl)
        have hinf : L a ⊓ (⨆ i ∈ s, L i) = ⊥ :=
          le_bot_iff.mp (le_trans (inf_le_inf_left (L a) hsub) (le_of_eq (hdisj a)))
        have hga : IsGalois ℚ ↥(L a) := ‹∀ i, IsGalois ℚ ↥(L i)› a
        have hld : (L a).LinearDisjoint ↥(⨆ i ∈ s, L i) :=
          (@IntermediateField.LinearDisjoint.iff_inf_eq_bot ℚ ℂ _ _ _ (L a)
            (⨆ i ∈ s, L i) hga _ _).mpr hinf
        rw [Finset.iSup_insert, Finset.prod_insert ha,
          IntermediateField.LinearDisjoint.finrank_sup hld, ih]
  have h := key Finset.univ
  have huniv : (⨆ i, L i) = ⨆ i ∈ Finset.univ, L i := by simp
  rw [huniv]; exact h

set_option maxHeartbeats 4000000

theorem SublemmaGaloisGroupCompositumProduct {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, IsGalois ℚ ↥(L i)] [∀ i, FiniteDimensional ℚ ↥(L i)]
    (hindep : iSupIndep (fun i => (L i).toSubalgebra))
    (hdisj : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥)
    [∀ i, Algebra ↥(L i) ↥(⨆ i, L i)] [∀ i, IsScalarTower ℚ ↥(L i) ↥(⨆ i, L i)] :
    ∃ e : (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) ≃* (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)),
      ∀ (σ : ↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) (i : Fin ℓ),
        e σ i = AlgEquiv.restrictNormal σ ↥(L i) := by
  haveI hn : ∀ i, Normal ℚ ↥(L i) := fun i => IsGalois.to_normal
  haveI hgalM : IsGalois ℚ ↥(⨆ i, L i) := (SublemmaCompositumGalois L).1
  haveI hfdM : FiniteDimensional ℚ ↥(⨆ i, L i) :=
    IntermediateField.finiteDimensional_iSup_of_finite (t := L)
  -- the restriction map as a MonoidHom
  set ρ : (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) →* (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)) :=
    Pi.monoidHom (fun i => AlgEquiv.restrictNormalHom ↥(L i)) with hρ
  -- injectivity
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hσi : ∀ i, σ.restrictNormal ↥(L i) = 1 := by
      intro i
      have h := congrFun hσ i
      simpa [hρ, Pi.monoidHom_apply] using h
    have hgen : (⨆ i, (IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange)
        = (⊤ : IntermediateField ℚ ↥(⨆ i, L i)) := by
      apply IntermediateField.map_injective (IntermediateField.val (⨆ i, L i))
      have hR : IntermediateField.map (IntermediateField.val (⨆ i, L i))
          (⊤ : IntermediateField ℚ ↥(⨆ i, L i)) = ⨆ i, L i :=
        (AlgHom.fieldRange_eq_map _).symm.trans (IntermediateField.fieldRange_val _)
      have hL : IntermediateField.map (IntermediateField.val (⨆ i, L i))
          (⨆ i, (IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange) = ⨆ i, L i := by
        simp only [IntermediateField.map_iSup]
        refine iSup_congr (fun i => ?_)
        exact (AlgHom.map_fieldRange _ _).trans
          (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ (L i) (hn i) _)
      exact hL.trans hR.symm
    have hadj : Algebra.adjoin ℚ
        (⋃ i, ((IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange : Set ↥(⨆ i, L i))) = ⊤ := by
      apply IntermediateField.adjoin_eq_top_iff.mp
      rw [← IntermediateField.iSup_eq_adjoin]
      exact hgen
    have hEqOn : Set.EqOn (σ.toAlgHom) (AlgHom.id ℚ ↥(⨆ i, L i))
        (⋃ i, ((IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange : Set ↥(⨆ i, L i))) := by
      intro x hx
      simp only [Set.mem_iUnion, SetLike.mem_coe, AlgHom.mem_fieldRange] at hx
      obtain ⟨i, y, hy⟩ := hx
      have hc := AlgEquiv.restrictNormal_commutes σ ↥(L i) y
      rw [hσi i, AlgEquiv.one_apply] at hc
      show σ.toAlgHom x = AlgHom.id ℚ _ x
      rw [AlgHom.id_apply, ← hy]
      exact hc.symm
    have hEq : σ.toAlgHom = AlgHom.id ℚ ↥(⨆ i, L i) := AlgHom.ext_of_adjoin_eq_top hadj hEqOn
    ext x
    simpa using AlgHom.ext_iff.mp hEq x
  -- cardinality
  have hcard : Nat.card (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i))
      = Nat.card (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)) := by
    rw [Nat.card_pi, (SublemmaCompositumGalois L).2,
      SublemmaDegreeCompositumLinearlyDisjoint L hindep hdisj]
    exact Finset.prod_congr rfl (fun i _ => (IsGalois.card_aut_eq_finrank ℚ ↥(L i)).symm)
  have hbij : Function.Bijective ρ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  refine ⟨MulEquiv.ofBijective ρ hbij, fun σ i => ?_⟩
  rfl

/-- **Tower degree multiplicativity.** For `F, M : IntermediateField ℚ ℂ` with `F ≤ M`,
`F` a number field, `M/ℚ` finite, and the inclusion algebra structure (so that
`algebraMap ↥F ↥M` is the subfield inclusion), the degrees multiply in the tower
`ℚ ⊆ F ⊆ M`: `Module.finrank ℚ ↥M = Module.finrank ↥F ↥M * Module.finrank ℚ ↥F`. -/
theorem SublemmaTowerDegree (F M : IntermediateField ℚ ℂ) (hFM : F ≤ M)
    [NumberField ↥F] [FiniteDimensional ℚ ↥M]
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Module.finrank ℚ ↥M = Module.finrank ↥F ↥M * Module.finrank ℚ ↥F := by
  haveI : FiniteDimensional ℚ ↥F := inferInstance
  haveI : FiniteDimensional ↥F ↥M := Module.Finite.right ℚ ↥F ↥M
  rw [mul_comm, Module.finrank_mul_finrank ℚ ↥F ↥M]

/-!
# Unramifiedness at finite primes and the absolute discriminant

Mathlib-only bridge lemmas for the finiteness of the Frattini quotient of `Gal(F^{ur,3}/F)` and
for unramifiedness of a compositum of everywhere-unramified extensions.

* `differentIdeal_eq_top_of_unramified` — every ramification index `1` ⟹ trivial relative different;
* `ramIdx_one_of_differentIdeal_eq_top` — the converse;
* `natAbs_discr_of_unramified` — hence `|D_L| = |D_K| ^ [L : K]` for an everywhere-unramified `L/K`;
* `unramified_iff_natAbs_discr` — the two are equivalent, which makes unramifiedness transportable
  along ring isomorphisms (since `NumberField.discr` is);
* `residue_isSeparable` — residue-field extensions of number fields are separable.
-/

open scoped NumberField

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.UnramifiedDiscriminant

/-- If every nonzero prime of `𝓞 L` is unramified over `𝓞 K`, the relative different ideal is
trivial. -/
theorem differentIdeal_eq_top_of_unramified (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (h : ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) :
    differentIdeal (𝓞 K) (𝓞 L) = ⊤ := by
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  by_contra hne
  obtain ⟨P, hPmax, hPle⟩ := Ideal.exists_le_maximal _ hne
  haveI : P.IsMaximal := hPmax
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPmax
    (fun hf => (NumberField.RingOfIntegers.not_isField L) hf)
  have hdvd : P ∣ differentIdeal (𝓞 K) (𝓞 L) := Ideal.dvd_iff_le.mpr hPle
  have hunram : Algebra.IsUnramifiedAt (𝓞 K) P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot]
    have hlo : P.LiesOver (P.under (𝓞 K)) := ⟨rfl⟩
    haveI := hlo
    haveI : (P.under (𝓞 K)).IsPrime := Ideal.IsPrime.under _ P
    have hpbot : P.under (𝓞 K) ≠ ⊥ := by
      intro hcon
      exact hPbot (by
        simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 K) (S := 𝓞 L) (I := P) hcon)
    exact h (P.under (𝓞 K)) hpbot inferInstance P ⟨inferInstance, hlo⟩
  exact (not_dvd_differentIdeal_iff (A := 𝓞 K) (B := 𝓞 L) (P := P)).mpr hunram hdvd

/-- Trivial relative different implies every ramification index is `1`. -/
theorem ramIdx_one_of_differentIdeal_eq_top (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (hdiff : differentIdeal (𝓞 K) (𝓞 L) = ⊤) :
    ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1 := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  intro p hp hpp P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver p := hPlies
  have hnotdvd : ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
    rw [hdiff, Ideal.dvd_iff_le]
    intro hle
    exact hPprime.ne_top (top_le_iff.mp hle)
  haveI : Algebra.IsUnramifiedAt (𝓞 K) P := (not_dvd_differentIdeal_iff).mp hnotdvd
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  rw [hPlies.over]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (S := 𝓞 L) (p := P) hPne

/-- **Discriminant of an everywhere-unramified extension.**  If `L/K` is unramified at every
finite prime then `|D_L| = |D_K| ^ [L : K]`. -/
theorem natAbs_discr_of_unramified (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L]
    (h : ∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) :
    (NumberField.discr L).natAbs = (NumberField.discr K).natAbs ^ Module.finrank K L := by
  haveI : IsScalarTower ℚ K L :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L),
    differentIdeal_eq_top_of_unramified K L h, Ideal.absNorm_top, one_mul]

/-- **Unramifiedness at finite primes is exactly the discriminant identity.** -/
theorem unramified_iff_natAbs_discr (K : Type*) [Field K] [NumberField K]
    (L : Type*) [Field L] [NumberField L] [Algebra K L] :
    (∀ (p : Ideal (𝓞 K)), p ≠ ⊥ → p.IsPrime →
        ∀ P ∈ Ideal.primesOver p (𝓞 L), Ideal.ramificationIdx p P = 1) ↔
      (NumberField.discr L).natAbs = (NumberField.discr K).natAbs ^ Module.finrank K L := by
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K L := Module.Finite.right ℚ K L
  haveI : Module.Finite (𝓞 K) (𝓞 L) := IsIntegralClosure.finite (𝓞 K) K L (𝓞 L)
  refine ⟨natAbs_discr_of_unramified K L, fun h => ?_⟩
  have htower :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  rw [h] at htower
  have hDK : (NumberField.discr K).natAbs ^ Module.finrank K L ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hone : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) = 1 := by
    have hx : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) *
          (NumberField.discr K).natAbs ^ Module.finrank K L
        = 1 * (NumberField.discr K).natAbs ^ Module.finrank K L := by
      rw [one_mul]; exact htower.symm
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hDK) hx
  exact ramIdx_one_of_differentIdeal_eq_top K L (Ideal.absNorm_eq_one_iff.mp hone)

/-- Residue-field extensions of number fields are separable (extensions of finite, hence perfect,
fields). -/
theorem residue_isSeparable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] (p : Ideal (𝓞 K)) (hp : p ≠ ⊥) (P : Ideal (𝓞 L)) [hPp : P.IsPrime]
    [P.LiesOver p] (hP : P ≠ ⊥) :
    Algebra.IsSeparable (𝓞 K ⧸ p) (𝓞 L ⧸ P) := by
  haveI hpp : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  haveI : p.IsMaximal := hpp.isMaximal hp
  haveI : P.IsMaximal := hPp.isMaximal hP
  haveI : Finite (𝓞 K ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot _ hp
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP
  haveI : Finite p.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 K ⧸ p))
  haveI : Finite P.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 L ⧸ P))
  haveI : PerfectField p.ResidueField := PerfectField.ofFinite
  haveI : Module.Finite p.ResidueField P.ResidueField := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic p.ResidueField P.ResidueField := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  infer_instance

end Workspace.ProofLemmas.UnramifiedDiscriminant

/-!
# Inertia at a single prime

A prime-by-prime version of the Hilbert inertia argument used in
`Workspace.ProofLemmas.CompositumUnramified`.  The two statements are

* `card_inertia_eq_ramificationIdx` — `|I(P)| = e(P/p)`;
* `inertia_le_fixingSubgroup` — if the intermediate field `E` is unramified **at `p`** then the
  inertia group of `P` fixes `E` pointwise.

Together they give both directions we need: composita of extensions unramified at `p` are
unramified at `p`, and (conversely) a subfield fixed by the whole inertia group is unramified.
-/

open scoped NumberField

namespace Workspace.ProofLemmas.InertiaLocal

set_option maxHeartbeats 1000000

open Workspace.ProofLemmas.UnramifiedDiscriminant

variable {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
  [Algebra F M] [IsGalois F M]

/-! ### Ramification versus the discriminant -/

section Discr

/-- If a rational prime `r` is ramified in `E` then `r` divides `|disc E|`. -/
theorem dvd_discr_of_ramified (E : Type*) [Field E] [NumberField E]
    (r : ℕ) (hr : r.Prime) (Q : Ideal (𝓞 E)) [hQp : Q.IsPrime]
    [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥)
    (he : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1) :
    r ∣ (NumberField.discr E).natAbs := by
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact hrprime
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  haveI : Q.IsMaximal := hQp.isMaximal hQne
  have hdvd : Q ∣ differentIdeal ℤ (𝓞 E) := by
    by_contra hcon
    haveI : Algebra.IsUnramifiedAt ℤ Q := (not_dvd_differentIdeal_iff).mp hcon
    exact he (by
      rw [hQl.over]
      exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (S := 𝓞 E) hQne)
  have h2 := map_dvd Ideal.absNorm hdvd
  rw [NumberField.absNorm_differentIdeal E (𝓞 E),
    Ideal.absNorm_eq_pow_inertiaDeg Q hrprime, Int.natAbs_natCast] at h2
  refine dvd_trans ?_ h2
  exact dvd_pow_self _ (Ideal.inertiaDeg_pos (Ideal.span {(r : ℤ)}) Q).ne'

/-- Contrapositive: if `r ∤ |disc E|` then `r` is unramified in `E`. -/
theorem ramificationIdx_eq_one_of_not_dvd_discr (E : Type*) [Field E] [NumberField E]
    (r : ℕ) (hr : r.Prime) (Q : Ideal (𝓞 E)) [hQp : Q.IsPrime]
    [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥)
    (h : ¬ r ∣ (NumberField.discr E).natAbs) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 1 := by
  by_contra hcon
  exact h (dvd_discr_of_ramified E r hr Q hQne hcon)

end Discr

/-! ### The absolute case: base `ℤ ⊆ ℚ` -/

section Rat

/-- Residue extensions over `ℤ` are separable. -/
theorem residue_isSeparable_int {L : Type*} [Field L] [NumberField L]
    (p : Ideal ℤ) (hp : p ≠ ⊥) (P : Ideal (𝓞 L)) [hPp : P.IsPrime]
    [P.LiesOver p] (hP : P ≠ ⊥) :
    Algebra.IsSeparable (ℤ ⧸ p) (𝓞 L ⧸ P) := by
  haveI hpp : p.IsPrime := Ideal.over_def P p ▸ inferInstance
  haveI : p.IsMaximal := hpp.isMaximal hp
  haveI : P.IsMaximal := hPp.isMaximal hP
  haveI : Finite (ℤ ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot _ hp
  haveI : Finite (𝓞 L ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot _ hP
  haveI : Finite p.ResidueField := IsLocalization.finite _ (nonZeroDivisors (ℤ ⧸ p))
  haveI : Finite P.ResidueField := IsLocalization.finite _ (nonZeroDivisors (𝓞 L ⧸ P))
  haveI : PerfectField p.ResidueField := PerfectField.ofFinite
  haveI : Module.Finite p.ResidueField P.ResidueField := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic p.ResidueField P.ResidueField := Algebra.IsAlgebraic.of_finite _ _
  haveI : Algebra.IsSeparable p.ResidueField P.ResidueField := inferInstance
  infer_instance

variable (M : Type*) [Field M] [NumberField M] [IsGalois ℚ M]

/-- `|I(P)| = e(P/p)` over the base `ℤ`. -/
theorem card_inertia_eq_ramificationIdx_int
    (p : Ideal ℤ) (hp : p ≠ ⊥) [hpp : p.IsPrime]
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver p] (hPne : P ≠ ⊥) :
    Nat.card (P.inertia (M ≃ₐ[ℚ] M)) = Ideal.ramificationIdx p P := by
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
  haveI := residue_isSeparable_int p hp P hPne
  rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) p hp P,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[ℚ] M)]

/-- **Inertia fixes every intermediate field unramified at `p`** (absolute version). -/
theorem inertia_le_fixingSubgroup_int (E : IntermediateField ℚ M)
    (p : Ideal ℤ) (hp : p ≠ ⊥) [hpp : p.IsPrime]
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver p] (hPne : P ≠ ⊥)
    (hE : haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
      Ideal.ramificationIdx p (P.under (𝓞 ↥E)) = 1) :
    P.inertia (M ≃ₐ[ℚ] M) ≤ E.fixingSubgroup := by
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  haveI : IsGaloisGroup (M ≃ₐ[ℚ] M) ℤ (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ M
  haveI := residue_isSeparable_int p hp P hPne
  have hcardF : Nat.card (P.inertia (M ≃ₐ[ℚ] M)) = Ideal.ramificationIdx p P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[ℚ] M) p hp P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[ℚ] M)]
  intro σ hσ
  haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
  haveI : IsGalois ↥E M := IsGalois.tower_top_of_isGalois ℚ ↥E M
  haveI tower : IsScalarTower ℤ (𝓞 ↥E) (𝓞 M) := inferInstance
  haveI : IsGaloisGroup (M ≃ₐ[↥E] M) (𝓞 ↥E) (𝓞 M) :=
    IsGaloisGroup.of_isFractionRing _ _ _ (↥E) M
  set pE : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E) with hpE
  haveI : P.LiesOver pE := ⟨rfl⟩
  haveI : pE.IsPrime := Ideal.IsPrime.under _ P
  have hpEover : pE.under ℤ = p := by
    rw [hpE, Ideal.under_under]
    exact (Ideal.over_def P p).symm
  haveI : pE.LiesOver p := ⟨hpEover.symm⟩
  have hpEne : pE ≠ ⊥ := by
    intro hcon
    exact hp (by rw [← hpEover, hcon, Ideal.under_bot])
  haveI := residue_isSeparable pE hpEne P hPne
  have hcardE : Nat.card (P.inertia (M ≃ₐ[↥E] M)) = Ideal.ramificationIdx pE P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[↥E] M) pE hpEne P,
      Ideal.ramificationIdxIn_eq_ramificationIdx pE P (M ≃ₐ[↥E] M)]
  have htower : Ideal.ramificationIdx p P
      = Ideal.ramificationIdx p pE * Ideal.ramificationIdx pE P :=
    Ideal.ramificationIdx_algebra_tower' (R := ℤ) (S := 𝓞 ↥E) (T := 𝓞 M) p pE P
  rw [hE, one_mul] at htower
  have hsmul : ∀ (τ : M ≃ₐ[↥E] M) (x : 𝓞 M), (τ.restrictScalars ℚ) • x = τ • x := by
    intro τ x
    exact Subtype.ext rfl
  have hmaps : ∀ τ : M ≃ₐ[↥E] M, τ ∈ P.inertia (M ≃ₐ[↥E] M) →
      τ.restrictScalars ℚ ∈ P.inertia (M ≃ₐ[ℚ] M) := by
    intro τ hτ x
    rw [hsmul]
    exact hτ x
  set g : (P.inertia (M ≃ₐ[↥E] M)) → (P.inertia (M ≃ₐ[ℚ] M)) :=
    fun τ => ⟨(τ : M ≃ₐ[↥E] M).restrictScalars ℚ, hmaps _ τ.2⟩ with hg
  have hginj : Function.Injective g := by
    rintro ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩ h
    have h' : (τ₁.restrictScalars ℚ) = (τ₂.restrictScalars ℚ) := congrArg Subtype.val h
    ext x
    exact DFunLike.congr_fun h' x
  haveI : Finite (M ≃ₐ[ℚ] M) := inferInstance
  haveI : Finite (M ≃ₐ[↥E] M) := inferInstance
  haveI : Fintype (P.inertia (M ≃ₐ[↥E] M)) := Fintype.ofFinite _
  haveI : Fintype (P.inertia (M ≃ₐ[ℚ] M)) := Fintype.ofFinite _
  have hcards : Fintype.card (P.inertia (M ≃ₐ[↥E] M))
      = Fintype.card (P.inertia (M ≃ₐ[ℚ] M)) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hcardF, htower]
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcards⟩
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨σ, hσ⟩
  have hστ : σ = (τ : M ≃ₐ[↥E] M).restrictScalars ℚ := (congrArg Subtype.val hτ).symm
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  rw [hστ]
  exact (τ : M ≃ₐ[↥E] M).commutes (⟨x, hx⟩ : ↥E)

/-- **Discriminant form.**  If the rational prime `r` does not divide `|disc E|` then the inertia
group of any prime over `r` fixes `E`. -/
theorem inertia_le_fixingSubgroup_of_not_dvd_discr (E : IntermediateField ℚ M)
    (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 M)) [hPprime : P.IsPrime] [hPlies : P.LiesOver (Ideal.span {(r : ℤ)})]
    (hPne : P ≠ ⊥)
    (hE : haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
      ¬ r ∣ (NumberField.discr ↥E).natAbs) :
    P.inertia (M ≃ₐ[ℚ] M) ≤ E.fixingSubgroup := by
  haveI : NumberField ↥E := NumberField.of_module_finite (K := ℚ) (L := ↥E)
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  refine inertia_le_fixingSubgroup_int M E _ hrbot P hPne ?_
  haveI : (P.under (𝓞 ↥E)).IsPrime := Ideal.IsPrime.under _ P
  haveI : (P.under (𝓞 ↥E)).LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [Ideal.under_under]
    exact hPlies.over
  have hPEne : (P.under (𝓞 ↥E)) ≠ ⊥ := by
    intro hcon
    exact hPne (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 ↥E) (S := 𝓞 M) (I := P) hcon)
  exact ramificationIdx_eq_one_of_not_dvd_discr ↥E r hr _ hPEne hE

end Rat

end Workspace.ProofLemmas.InertiaLocal

/-!
# Counting integral ideals of bounded norm

This file carries out everything in `IdealCountByNormBound` except the combinatorial
ideal-to-divisor-tuple comparison, which is provided separately by
`Workspace.ProofLemmas.IdealCountInjection`.

* `D n m` — the `n`-tuples of positive naturals with product at most `m`;
* `card_D_le` — **`#(D n m) ≤ 2ⁿ m²`**, proved by induction on `n` by splitting off the first
  coordinate and using `∑_{c ≤ m} 1/c² ≤ 2`.  (The usual `X(log X)^{n-1}/(n-1)!` bound is not
  needed: the crude `2ⁿ X²` already beats `max{2, rd}^{Cn}` because the Minkowski bound itself is
  at most `max{2, rd}^{3n/2}`.)
* `MB_le` — **`MB K ≤ max{2, rd K} ^ (3n/2)`**, from `(4/π)^{r₂} ≤ 2ⁿ`, `n!/nⁿ ≤ 1` and
  `√|D_K| = rd(K)^{n/2}`;
* `idealCount_bound_of_inj` — combining the two: given the ideal-to-tuple injection, the number of
  nonzero ideals of norm at most `MB K` is at most `max{2, rd K} ^ (4n)`.
-/

open Finset
open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.IdealNormCount

namespace DivisorCount

/-- Tuples of positive naturals of length `n` with product at most `m`. -/
def D (n m : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.Icc 1 m)).filter (fun a => ∏ i, a i ≤ m)

theorem mem_D {n m : ℕ} {a : Fin n → ℕ} :
    a ∈ D n m ↔ (∀ i, 1 ≤ a i ∧ a i ≤ m) ∧ ∏ i, a i ≤ m := by
  simp [D, Fintype.mem_piFinset, Finset.mem_Icc]

/-- The membership condition simplifies: for positive entries with product `≤ m`, each entry is
automatically `≤ m`. -/
theorem mem_D_iff {n m : ℕ} (hm : 1 ≤ m) {a : Fin n → ℕ} :
    a ∈ D n m ↔ (∀ i, 1 ≤ a i) ∧ ∏ i, a i ≤ m := by
  rw [mem_D]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun i => (h1 i).1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ⟨h1 i, ?_⟩, h2⟩
    calc a i ≤ ∏ j, a j := Finset.single_le_prod' (fun j _ => h1 j) (Finset.mem_univ i)
      _ ≤ m := h2

/-- `∑_{c=1}^{m} 1/c² ≤ 2 - 1/m` for `m ≥ 1`. -/
theorem sum_inv_sq_le' : ∀ m : ℕ, 1 ≤ m →
    ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 ≤ 2 - 1 / (m : ℝ) := by
  intro m
  induction m with
  | zero => omega
  | succ k ih =>
      intro _
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · norm_num
      · have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
        rw [Finset.sum_Icc_succ_top (by omega)]
        have hstep : (1 : ℝ) / ((k + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (k : ℝ) - 1 / (((k + 1 : ℕ)) : ℝ) := by
          push_cast
          rw [div_sub_div _ _ (ne_of_gt hk0) (by positivity), div_le_div_iff₀ (by positivity)
            (by positivity)]
          ring_nf
          nlinarith
        linarith [ih hk]

/-- `∑_{c=1}^{m} 1/c² ≤ 2`. -/
theorem sum_inv_sq_le (m : ℕ) : ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 ≤ 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := sum_inv_sq_le' m hm
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
    linarith

/-- Splitting off the first coordinate. -/
theorem card_D_succ (n m : ℕ) (hm : 1 ≤ m) :
    (D (n + 1) m).card = ∑ c ∈ Finset.Icc 1 m, (D n (m / c)).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun a => a 0) (t := Finset.Icc 1 m) ?first]
  case first =>
    intro a ha
    simp only [Finset.mem_coe] at ha
    rw [mem_D_iff hm] at ha
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨ha.1 0, le_trans (Finset.single_le_prod' (fun j _ => ha.1 j) (Finset.mem_univ 0)) ha.2⟩
  refine Finset.sum_congr rfl ?_
  intro c hc
  simp only [Finset.mem_Icc] at hc
  have hc0 : 0 < c := hc.1
  refine Finset.card_bij' (fun a _ => Fin.tail a) (fun b _ => Fin.cons c b) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨haD, ha0⟩ := ha
    rw [mem_D_iff hm] at haD
    rw [mem_D_iff (Nat.one_le_div_iff hc0 |>.mpr hc.2)]
    refine ⟨fun i => haD.1 i.succ, ?_⟩
    have hprod : ∏ i : Fin (n + 1), a i = a 0 * ∏ i : Fin n, a i.succ := Fin.prod_univ_succ a
    rw [Nat.le_div_iff_mul_le hc0]
    have := haD.2
    rw [hprod, ha0] at this
    calc (∏ i : Fin n, Fin.tail a i) * c = c * ∏ i : Fin n, a i.succ := by
          simp [Fin.tail, mul_comm]
      _ ≤ m := this
  · intro b hb
    rw [mem_D_iff (Nat.one_le_div_iff hc0 |>.mpr hc.2)] at hb
    simp only [Finset.mem_filter]
    refine ⟨?_, by simp⟩
    rw [mem_D_iff hm]
    constructor
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hc0
      · intro j; simpa using hb.1 j
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      calc c * ∏ i : Fin n, b i ≤ c * (m / c) := by
            exact Nat.mul_le_mul_left c hb.2
        _ ≤ m := Nat.mul_div_le m c
  · intro a ha
    simp only [Finset.mem_filter] at ha
    show Fin.cons c (Fin.tail a) = a
    rw [show c = a 0 from ha.2.symm]
    exact Fin.cons_self_tail a
  · intro b _
    funext i
    simp [Fin.tail]

/-- **Divisor-tuple count.** The number of `n`-tuples of positive naturals with product at most `m`
is at most `2ⁿ m²`. -/
theorem card_D_le (n : ℕ) : ∀ m : ℕ, 1 ≤ m → ((D n m).card : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := by
  induction n with
  | zero =>
      intro m hm
      have : D 0 m = Finset.univ := by
        ext a
        simp only [mem_D_iff hm, Finset.mem_univ, iff_true]
        exact ⟨fun i => i.elim0, by simpa using hm⟩
      rw [this]
      have hcard : (Finset.univ : Finset (Fin 0 → ℕ)).card = 1 := by simp
      rw [hcard]
      have hm' : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      norm_num
      nlinarith
  | succ n ih =>
      intro m hm
      rw [card_D_succ n m hm]
      push_cast
      have hstep : ∀ c ∈ Finset.Icc 1 m,
          (((D n (m / c)).card : ℝ)) ≤ 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := by
        intro c hc
        simp only [Finset.mem_Icc] at hc
        have hc0 : 0 < c := hc.1
        have h1 : ((D n (m / c)).card : ℝ) ≤ 2 ^ n * ((m / c : ℕ) : ℝ) ^ 2 :=
          ih (m / c) (Nat.one_le_div_iff hc0 |>.mpr hc.2)
        have h2 : ((m / c : ℕ) : ℝ) ≤ (m : ℝ) / (c : ℝ) := Nat.cast_div_le
        have h3 : (0 : ℝ) ≤ ((m / c : ℕ) : ℝ) := Nat.cast_nonneg _
        calc ((D n (m / c)).card : ℝ) ≤ 2 ^ n * ((m / c : ℕ) : ℝ) ^ 2 := h1
          _ ≤ 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := by
              have hsq : ((m / c : ℕ) : ℝ) ^ 2 ≤ ((m : ℝ) / (c : ℝ)) ^ 2 := by
                gcongr
              nlinarith [pow_nonneg (le_of_lt (show (0:ℝ) < 2 from by norm_num)) n]
      calc (∑ c ∈ Finset.Icc 1 m, ((D n (m / c)).card : ℝ))
          ≤ ∑ c ∈ Finset.Icc 1 m, 2 ^ n * ((m : ℝ) / (c : ℝ)) ^ 2 := Finset.sum_le_sum hstep
        _ = 2 ^ n * (m : ℝ) ^ 2 * ∑ c ∈ Finset.Icc 1 m, (1 : ℝ) / (c : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [div_pow]
            ring
        _ ≤ 2 ^ n * (m : ℝ) ^ 2 * 2 := by
            have hpos : (0 : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := by positivity
            exact mul_le_mul_of_nonneg_left (sum_inv_sq_le m) hpos
        _ = 2 ^ (n + 1) * (m : ℝ) ^ 2 := by ring

end DivisorCount

section Arithmetic

open scoped NumberField
open DivisorCount

/-- The Minkowski bound appearing in the statement. -/
noncomputable def MB (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
    ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
      Real.sqrt |(NumberField.discr K : ℝ)|)

/-- `MB K ≤ max 2 (rootDiscriminant K) ^ ((3 / 2) * n)`. -/
theorem MB_le (K : Type) [Field K] [NumberField K] :
    MB K ≤ (max 2 (rootDiscriminant K)) ^ ((3 / 2 : ℝ) * (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  set R := max 2 (rootDiscriminant K) with hR
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR2
  have hD0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  -- `√|D| = rd ^ (n/2)`
  have hsqrt : Real.sqrt |(NumberField.discr K : ℝ)| = (rootDiscriminant K) ^ ((n : ℝ) / 2) := by
    rw [rootDiscriminant, ← Real.rpow_mul (le_of_lt hD0), Real.sqrt_eq_rpow]
    congr 1
    field_simp
    exact (div_self (ne_of_gt hnR)).symm
  have hrd0 : (0 : ℝ) ≤ rootDiscriminant K := Real.rpow_nonneg (le_of_lt hD0) _
  have hpi : (4 : ℝ) / Real.pi ≤ 2 := by
    have h3 := Real.pi_gt_three
    rw [div_le_iff₀ Real.pi_pos]
    linarith
  have hr2 : NumberField.InfinitePlace.nrComplexPlaces K ≤ n := by
    have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    omega
  have hstep1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ (n : ℝ) := by
    have h1 : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K
        ≤ R ^ NumberField.InfinitePlace.nrComplexPlaces K := by
      gcongr <;> first | positivity | linarith
    have h2 : R ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ n := by
      gcongr <;> first | positivity | linarith
    calc (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K ≤ R ^ n := le_trans h1 h2
      _ = R ^ (n : ℝ) := (Real.rpow_natCast R n).symm
  have hfact : ((Nat.factorial n : ℝ) / (n : ℝ) ^ n) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.factorial_le_pow n
  have hsq : Real.sqrt |(NumberField.discr K : ℝ)| ≤ R ^ ((n : ℝ) / 2) := by
    rw [hsqrt]
    exact Real.rpow_le_rpow hrd0 (le_max_right _ _) (by positivity)
  have hfact0 : (0 : ℝ) ≤ (Nat.factorial n : ℝ) / (n : ℝ) ^ n := by positivity
  calc MB K = (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        (((Nat.factorial n : ℝ) / (n : ℝ) ^ n) * Real.sqrt |(NumberField.discr K : ℝ)|) := rfl
    _ ≤ R ^ (n : ℝ) * (1 * R ^ ((n : ℝ) / 2)) := by
        gcongr <;>
          first | positivity | exact Real.sqrt_nonneg _ | linarith
    _ = R ^ ((3 / 2 : ℝ) * (n : ℝ)) := by
        rw [one_mul, ← Real.rpow_add hR0]
        ring_nf

/-- **Main arithmetic assembly.**  Given the ideal-to-divisor-tuple injection, the number of
nonzero ideals of norm at most the Minkowski bound is at most `max{2, rd(K)} ^ (4·[K:ℚ])`. -/
theorem idealCount_bound_of_inj
    (hinj : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ),
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
        ≤ (D (Module.finrank ℚ K) m).card)
    (K : Type) [Field K] [NumberField K] :
    (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB K} : ℝ)
      ≤ (max 2 (rootDiscriminant K)) ^ (4 * (Module.finrank ℚ K : ℝ)) := by
  set n := Module.finrank ℚ K with hn
  have hn0 : 0 < n := Module.finrank_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  set R := max 2 (rootDiscriminant K) with hR
  have hR2 : (2 : ℝ) ≤ R := le_max_left _ _
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR2
  have hD0 : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero K))
  have hMB0 : (0 : ℝ) ≤ MB K := by
    rw [MB]
    have : (0 : ℝ) ≤ 4 / Real.pi := by positivity
    positivity
  set m : ℕ := ⌊MB K⌋₊ with hm
  -- rewrite the index set
  have hset : Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB K}
      = Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun I => ?_)
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, Nat.le_floor h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, le_trans (by exact_mod_cast h2) (Nat.floor_le hMB0)⟩
  rw [hset]
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · -- no ideals at all
    have hempty : IsEmpty {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} := by
      constructor
      rintro ⟨I, hI, hIn⟩
      rw [hm0, Nat.le_zero, Ideal.absNorm_eq_zero_iff] at hIn
      exact hI hIn
    rw [Nat.card_eq_zero.mpr (Or.inl hempty)]
    simp only [Nat.cast_zero]
    positivity
  · have hcard : (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} : ℝ)
        ≤ ((D n m).card : ℝ) := by exact_mod_cast hinj K m
    have hDbd : ((D n m).card : ℝ) ≤ 2 ^ n * (m : ℝ) ^ 2 := card_D_le n m hm1
    have hmMB : (m : ℝ) ≤ MB K := Nat.floor_le hMB0
    have h2R : (2 : ℝ) ^ n ≤ R ^ (n : ℝ) := by
      rw [Real.rpow_natCast R n]
      gcongr <;> first | positivity | linarith
    have hMBsq : (m : ℝ) ^ 2 ≤ R ^ (3 * (n : ℝ)) := by
      have h1 : (m : ℝ) ^ 2 ≤ (MB K) ^ 2 := by
        have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
        nlinarith
      have h2 : (MB K) ^ 2 ≤ (R ^ ((3 / 2 : ℝ) * (n : ℝ))) ^ 2 := by
        have := MB_le K
        nlinarith [Real.rpow_nonneg (le_of_lt hR0) ((3 / 2 : ℝ) * (n : ℝ))]
      have h3 : (R ^ ((3 / 2 : ℝ) * (n : ℝ))) ^ 2 = R ^ (3 * (n : ℝ)) := by
        rw [← Real.rpow_natCast (R ^ ((3 / 2 : ℝ) * (n : ℝ))) 2, ← Real.rpow_mul (le_of_lt hR0)]
        norm_num
        ring_nf
      linarith [h1, h2, h3.le, h3.ge]
    calc (Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} : ℝ)
        ≤ 2 ^ n * (m : ℝ) ^ 2 := le_trans hcard hDbd
      _ ≤ R ^ (n : ℝ) * R ^ (3 * (n : ℝ)) := by
          have hpos : (0 : ℝ) ≤ (m : ℝ) ^ 2 := by positivity
          have hRn : (0 : ℝ) ≤ R ^ (n : ℝ) := le_of_lt (Real.rpow_pos_of_pos hR0 _)
          nlinarith
      _ = R ^ (4 * (n : ℝ)) := by rw [← Real.rpow_add hR0]; ring_nf

end Arithmetic

end Workspace.ProofLemmas.IdealNormCount

/-!
# `#{I : N(I) ≤ m} ≤ #{n-tuples of positive integers with product ≤ m}`

The combinatorial ideal-to-divisor-tuple comparison underlying `IdealCountByNormBound` (equivalently
the classical `#{I : N(I) = k} ≤ d_n(k)`), for `n = [K : ℚ]`.

The injection.  For a rational prime `q` there are at most `n` primes of `𝓞 K` above `q`
(`card_Sq_le`, from `∑_{P|q} e_P f_P = n`), so they can be indexed injectively by `Fin n` (`idxAt`).
Writing `q(P) = absNorm (P ∩ ℤ)` for the rational prime below `P`, every nonzero prime gets an index
`idx P`, and two nonzero primes with the same `q(·)` and the same index coincide (`idx_inj`).

For a nonzero ideal `I` put `Φ I i = ∏_{idx P = i} N(P)^{v_P(I)}` (a product over the multiset
`normalizedFactors I`).  Then

* `∏ i, Φ I i = N(I)` (`prod_Φ`), by partitioning the factor multiset and multiplicativity of
  `Ideal.absNorm`;
* `Φ` is injective on nonzero ideals (`Φ_inj`): since `N(P) = q(P)^{f(P)}`, reading the `q(P)`-adic
  valuation of `Φ I (idx P)` returns `v_P(I) · f(P)`, and `f(P) > 0`, so all the valuations of `I`
  — hence `normalizedFactors I`, hence `I` — are determined by `Φ I`.
-/

open scoped NumberField
open UniqueFactorizationMonoid

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.IdealCountInjection

variable (K : Type) [Field K] [NumberField K]

/-- The rational prime below a prime ideal, as a natural number. -/
noncomputable def qOf (P : Ideal (𝓞 K)) : ℕ := Ideal.absNorm (Ideal.under ℤ P)

/-- The finset of primes of `𝓞 K` above the rational prime `q`. -/
noncomputable def Sq (q : ℕ) : Finset (Ideal (𝓞 K)) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 K)

/-- There are at most `[K : ℚ]` primes above a rational prime. -/
theorem card_Sq_le (q : ℕ) (hq : q.Prime) : (Sq K q).card ≤ Module.finrank ℚ K := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI hmax : (Ideal.span {(q : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime q
  have hne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by simp [hq.ne_zero]
  have hsum := Ideal.sum_ramification_inertia (S := 𝓞 K) (K := ℚ) (L := K)
    (p := Ideal.span {(q : ℤ)}) hne
  rw [Sq, ← hsum, Finset.card_eq_sum_ones]
  refine Finset.sum_le_sum ?_
  intro P hP
  have hPmem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 K) := by
    rw [← IsDedekindDomain.coe_primesOverFinset hne (𝓞 K)] at *
    exact hP
  obtain ⟨hPprime, hPlies⟩ := hPmem
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlies
  have he : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hne
  have hf : 0 < Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P := Ideal.inertiaDeg_pos _ _
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero he (Nat.pos_iff_ne_zero.mp hf))

/-- The residue degree of a prime of `𝓞 K` over the rational prime below it. -/
noncomputable def fOf (P : Ideal (𝓞 K)) : ℕ := Ideal.inertiaDeg (Ideal.under ℤ P) P

variable {K}

theorem qOf_prime (P : Ideal (𝓞 K)) [P.IsPrime] (hP0 : P ≠ ⊥) : (qOf K P).Prime := by
  haveI : NeZero P := ⟨hP0⟩
  exact Nat.absNorm_under_prime P

theorem under_eq_span (P : Ideal (𝓞 K)) :
    Ideal.under ℤ P = Ideal.span {(qOf K P : ℤ)} := by
  rw [qOf, Int.ideal_span_absNorm_eq_self]

theorem liesOver_qOf (P : Ideal (𝓞 K)) : P.LiesOver (Ideal.span {(qOf K P : ℤ)}) :=
  Int.liesOver_span_absNorm P

theorem mem_Sq_qOf (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) : P ∈ Sq K (qOf K P) := by
  haveI := liesOver_qOf P
  have hq := qOf_prime P hP0
  haveI : Fact (qOf K P).Prime := ⟨hq⟩
  have hne : (Ideal.span {((qOf K P : ℕ) : ℤ)}) ≠ ⊥ := by simp [hq.ne_zero]
  rw [Sq, ← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hne (𝓞 K)]
  exact ⟨hP, inferInstance⟩

theorem absNorm_eq_qOf_pow (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) :
    Ideal.absNorm P = (qOf K P) ^ (fOf K P) := by
  haveI : NeZero P := ⟨hP0⟩
  have hpp : (Ideal.under ℤ P).IsPrime := Ideal.IsPrime.under ℤ P
  have hne : Ideal.under ℤ P ≠ ⊥ := by
    intro h
    exact hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : P.LiesOver (Ideal.under ℤ P) := ⟨rfl⟩
  exact Ideal.absNorm_eq_pow_inertiaDeg_of_liesOver P (Ideal.under ℤ P) hpp hne

theorem fOf_pos (P : Ideal (𝓞 K)) [hP : P.IsPrime] (hP0 : P ≠ ⊥) : 0 < fOf K P := by
  haveI : P.LiesOver (Ideal.under ℤ P) := ⟨rfl⟩
  have hpp : (Ideal.under ℤ P).IsPrime := Ideal.IsPrime.under ℤ P
  have hne : Ideal.under ℤ P ≠ ⊥ := fun h => hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  haveI : (Ideal.under ℤ P).IsMaximal := hpp.isMaximal hne
  exact Ideal.inertiaDeg_pos _ _

variable (K)

/-- An injective indexing of the primes above a fixed rational prime by `Fin [K:ℚ]`. -/
noncomputable def idxAt (q : ℕ) (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) :=
  if h : q.Prime ∧ P ∈ Sq K q then
    Fin.castLE (card_Sq_le K q h.1) ((Sq K q).equivFin ⟨P, h.2⟩)
  else ⟨0, Module.finrank_pos⟩

/-- The index of a prime of `𝓞 K`. -/
noncomputable def idx (P : Ideal (𝓞 K)) : Fin (Module.finrank ℚ K) := idxAt K (qOf K P) P

variable {K}

theorem idxAt_inj {q : ℕ} (hq : q.Prime) {P P' : Ideal (𝓞 K)}
    (hP : P ∈ Sq K q) (hP' : P' ∈ Sq K q) (h : idxAt K q P = idxAt K q P') : P = P' := by
  rw [idxAt, dif_pos ⟨hq, hP⟩, idxAt, dif_pos ⟨hq, hP'⟩] at h
  have h1 := Fin.castLE_injective (card_Sq_le K q hq) h
  have h2 := (Sq K q).equivFin.injective h1
  exact congrArg Subtype.val h2

/-- Two nonzero primes with the same rational prime below and the same index are equal. -/
theorem idx_inj {P P' : Ideal (𝓞 K)} [P.IsPrime] [P'.IsPrime] (hP0 : P ≠ ⊥) (hP'0 : P' ≠ ⊥)
    (hq : qOf K P = qOf K P') (h : idx K P = idx K P') : P = P' := by
  have hmem : P ∈ Sq K (qOf K P) := mem_Sq_qOf P hP0
  have hmem' : P' ∈ Sq K (qOf K P) := hq ▸ mem_Sq_qOf P' hP'0
  refine idxAt_inj (qOf_prime P hP0) hmem hmem' ?_
  rw [idx, idx, hq] at h
  rw [← hq] at h
  exact h

/-- Partitioning a multiset by a `Fin n`-valued function multiplies out. -/
theorem prod_fiber_prod {α : Type*} {n : ℕ} (f : α → Fin n) (g : α → ℕ) (s : Multiset α) :
    ∏ i : Fin n, ((s.filter (fun a => f a = i)).map g).prod = (s.map g).prod := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
      have key : ∀ i : Fin n, (((a ::ₘ t).filter (fun x => f x = i)).map g).prod
          = (if f a = i then g a else 1) * ((t.filter (fun x => f x = i)).map g).prod := by
        intro i
        by_cases h : f a = i
        · simp [Multiset.filter_cons, h]
        · simp [Multiset.filter_cons, h]
      rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, ih,
        Multiset.map_cons, Multiset.prod_cons]
      congr 1
      simpa using Finset.prod_ite_eq Finset.univ (f a) (fun _ => g a)

variable (K)

/-- The `i`-th coordinate of the divisor tuple attached to an ideal. -/
noncomputable def Φ (I : Ideal (𝓞 K)) (i : Fin (Module.finrank ℚ K)) : ℕ :=
  open Classical in
  (((normalizedFactors I).filter (fun P => idx K P = i)).map Ideal.absNorm).prod

variable {K}

theorem prod_Φ (I : Ideal (𝓞 K)) (hI : I ≠ 0) :
    ∏ i, Φ K I i = Ideal.absNorm I := by
  classical
  have h1 : ∏ i, Φ K I i = ((normalizedFactors I).map Ideal.absNorm).prod :=
    prod_fiber_prod (idx K) Ideal.absNorm (normalizedFactors I)
  rw [h1, ← map_multiset_prod, associated_iff_eq.mp (prod_normalizedFactors hI)]

/-- Every element of `normalizedFactors I` is a nonzero prime ideal. -/
theorem mem_normalizedFactors_prime {I P : Ideal (𝓞 K)} (hI : I ≠ 0)
    (hP : P ∈ normalizedFactors I) : P.IsPrime ∧ P ≠ ⊥ := by
  have hp : Prime P := prime_of_normalized_factor P hP
  refine ⟨Ideal.isPrime_of_prime hp, ?_⟩
  intro h
  apply zero_notMem_normalizedFactors I
  have h0 : (0 : Ideal (𝓞 K)) = P := by rw [h]; rfl
  rwa [h0]

theorem Φ_pos (I : Ideal (𝓞 K)) (hI : I ≠ 0) (i : Fin (Module.finrank ℚ K)) : 0 < Φ K I i := by
  classical
  rw [Φ]
  refine Multiset.prod_pos ?_
  intro a ha
  obtain ⟨P, hPmem, rfl⟩ := Multiset.mem_map.mp ha
  have hP := Multiset.mem_of_mem_filter hPmem
  have := mem_normalizedFactors_prime hI hP
  exact Nat.pos_of_ne_zero (fun h => this.2 (Ideal.absNorm_eq_zero_iff.mp h))

/-- The local weight of a prime at a rational prime `q`. -/
noncomputable def w (q : ℕ) (P : Ideal (𝓞 K)) : ℕ := if qOf K P = q then fOf K P else 0

theorem factorization_prod_map (q : ℕ) (hq : q.Prime) :
    ∀ (s : Multiset (Ideal (𝓞 K))), (∀ P ∈ s, P.IsPrime ∧ P ≠ ⊥) →
      ((s.map Ideal.absNorm).prod).factorization q = (s.map (w q)).sum := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P t ih =>
      intro hs
      have hP := hs P (Multiset.mem_cons_self P t)
      haveI : P.IsPrime := hP.1
      have ht : ∀ P' ∈ t, P'.IsPrime ∧ P' ≠ ⊥ := fun P' hP' => hs P' (Multiset.mem_cons_of_mem hP')
      have hne1 : Ideal.absNorm P ≠ 0 := fun h => hP.2 (Ideal.absNorm_eq_zero_iff.mp h)
      have hne2 : ((t.map Ideal.absNorm).prod) ≠ 0 := by
        refine Nat.pos_iff_ne_zero.mp (Multiset.prod_pos ?_)
        intro a ha
        obtain ⟨P', hP'mem, rfl⟩ := Multiset.mem_map.mp ha
        exact Nat.pos_of_ne_zero
          (fun h => (ht P' hP'mem).2 (Ideal.absNorm_eq_zero_iff.mp h))
      rw [Multiset.map_cons, Multiset.prod_cons, Nat.factorization_mul hne1 hne2]
      simp only [Finsupp.add_apply]
      rw [ih ht, Multiset.map_cons, Multiset.sum_cons]
      congr 1
      -- the local factorization of `absNorm P`
      rw [absNorm_eq_qOf_pow P hP.2, Nat.factorization_pow]
      have hqP : (qOf K P).Prime := qOf_prime P hP.2
      rw [hqP.factorization]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, w]
      by_cases h : qOf K P = q
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]

theorem sum_w_eq (P : Ideal (𝓞 K)) :
    ∀ (s : Multiset (Ideal (𝓞 K))), (∀ P' ∈ s, qOf K P' = qOf K P → P' = P) →
      (s.map (w (qOf K P))).sum = Multiset.count P s * fOf K P := by
  classical
  intro s
  induction s using Multiset.induction_on with
  | empty => simp
  | cons P' t ih =>
      intro hs
      have ht : ∀ P'' ∈ t, qOf K P'' = qOf K P → P'' = P :=
        fun P'' hP'' => hs P'' (Multiset.mem_cons_of_mem hP'')
      rw [Multiset.map_cons, Multiset.sum_cons, ih ht]
      by_cases h : P' = P
      · subst h
        rw [Multiset.count_cons_self, w, if_pos rfl]
        ring
      · have hq : qOf K P' ≠ qOf K P := fun hcon => h (hs P' (Multiset.mem_cons_self P' t) hcon)
        rw [w, if_neg hq, Multiset.count_cons_of_ne (Ne.symm h), zero_add]

open Workspace.ProofLemmas.IdealNormCount.DivisorCount in
theorem factorization_Φ (I : Ideal (𝓞 K)) (hI : I ≠ 0) (P : Ideal (𝓞 K)) [P.IsPrime]
    (hP0 : P ≠ ⊥) :
    (Φ K I (idx K P)).factorization (qOf K P)
      = Multiset.count P (normalizedFactors I) * fOf K P := by
  classical
  set s := (normalizedFactors I).filter (fun P' => idx K P' = idx K P) with hs
  have hprimes : ∀ P' ∈ s, P'.IsPrime ∧ P' ≠ ⊥ := fun P' hP' =>
    mem_normalizedFactors_prime hI (Multiset.mem_of_mem_filter hP')
  have hΦ : Φ K I (idx K P) = ((s.map Ideal.absNorm).prod) := rfl
  rw [hΦ, factorization_prod_map (qOf K P) (qOf_prime P hP0) s hprimes]
  have huniq : ∀ P' ∈ s, qOf K P' = qOf K P → P' = P := by
    intro P' hP' hq
    have h1 : idx K P' = idx K P := (Multiset.mem_filter.mp hP').2
    have h2 := hprimes P' hP'
    haveI : P'.IsPrime := h2.1
    exact idx_inj h2.2 hP0 hq h1
  rw [sum_w_eq P s huniq]
  congr 1
  rw [hs, Multiset.count_filter]
  simp

theorem Φ_inj {I J : Ideal (𝓞 K)} (hI : I ≠ 0) (hJ : J ≠ 0) (h : Φ K I = Φ K J) : I = J := by
  classical
  have hnf : normalizedFactors I = normalizedFactors J := by
    ext P
    by_cases hPp : P.IsPrime ∧ P ≠ ⊥
    · haveI : P.IsPrime := hPp.1
      have h1 := factorization_Φ I hI P hPp.2
      have h2 := factorization_Φ J hJ P hPp.2
      rw [h] at h1
      rw [h1] at h2
      have hf : 0 < fOf K P := fOf_pos P hPp.2
      exact Nat.eq_of_mul_eq_mul_right hf h2
    · have e1 : Multiset.count P (normalizedFactors I) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hPp (mem_normalizedFactors_prime hI hmem)
      have e2 : Multiset.count P (normalizedFactors J) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hPp (mem_normalizedFactors_prime hJ hmem)
      rw [e1, e2]
  have hIp : (normalizedFactors I).prod = I := associated_iff_eq.mp (prod_normalizedFactors hI)
  have hJp : (normalizedFactors J).prod = J := associated_iff_eq.mp (prod_normalizedFactors hJ)
  rw [← hIp, ← hJp, hnf]

open Workspace.ProofLemmas.IdealNormCount.DivisorCount in
/-- **The ideal-to-divisor-tuple comparison.**  The number of nonzero ideals of `𝓞 K` of norm at
most `m` is at most the number of `[K:ℚ]`-tuples of positive integers with product at most `m`. -/
theorem idealCount_le_D (m : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
      ≤ (D (Module.finrank ℚ K) m).card := by
  classical
  haveI : Finite ↥(D (Module.finrank ℚ K) m) := FinsetCoe.fintype _ |>.finite
  have hmap : ∀ (I : Ideal (𝓞 K)), I ≠ 0 → Ideal.absNorm I ≤ m → Φ K I ∈ D (Module.finrank ℚ K) m := by
    intro I hI hIm
    have hprod : ∏ i, Φ K I i = Ideal.absNorm I := prod_Φ I hI
    rw [mem_D]
    have hpos : ∀ i, 1 ≤ Φ K I i := fun i => Φ_pos I hI i
    refine ⟨fun i => ⟨hpos i, ?_⟩, by rw [hprod]; exact hIm⟩
    calc Φ K I i ≤ ∏ j, Φ K I j := Finset.single_le_prod' (fun j _ => hpos j) (Finset.mem_univ i)
      _ = Ideal.absNorm I := hprod
      _ ≤ m := hIm
  set g : {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m} → ↥(D (Module.finrank ℚ K) m) :=
    fun I => ⟨Φ K I.1, hmap I.1 I.2.1 I.2.2⟩ with hg
  have hginj : Function.Injective g := by
    rintro ⟨I, hI⟩ ⟨J, hJ⟩ hij
    have : Φ K I = Φ K J := congrArg Subtype.val hij
    exact Subtype.ext (Φ_inj hI.1 hJ.1 this)
  calc Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
      ≤ Nat.card ↥(D (Module.finrank ℚ K) m) := Nat.card_le_card_of_injective g hginj
    _ = (D (Module.finrank ℚ K) m).card := by simp

end Workspace.ProofLemmas.IdealCountInjection

/-!
# Primes not dividing the level are unramified, and the local conductor–discriminant identity is
# trivial there

* `not_dvd_discr_of_unramified` — if every prime of `𝓞 L` above `p` has ramification index `1`
  then `p ∤ |D_L|`.  (If `p` divided `|D_L| = N(𝔡_{L/ℚ})`, some prime factor `P` of the different
  would lie over `p`, and `P ∣ 𝔡` contradicts `not_dvd_differentIdeal_iff`.)
* `unramified_of_not_dvd` — for `L ≤ ℚ(ζ_m)` and `p ∤ m`, every prime of `𝓞 L` above `p` has
  ramification index `1` (Mathlib's `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd`
  plus tower multiplicativity).
* `local_of_not_dvd` — hence the local conductor–discriminant identity holds at every `p ∤ m`:
  the left side vanishes by the above and the right side because every conductor divides `m`.
-/

open scoped NumberField
open UniqueFactorizationMonoid
open Workspace.Types.CyclotomicCharacterFields
open Workspace.ProofLemmas.IdealCountInjection

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.UnramifiedOutsideLevel

/-- A prime unramified in `L` does not divide the absolute discriminant of `L`. -/
theorem not_dvd_discr_of_unramified (L : Type) [Field L] [NumberField L] (p : ℕ) (hp : p.Prime)
    (h : ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q = 1) :
    ¬ p ∣ (NumberField.discr L).natAbs := by
  classical
  intro hdvd
  rw [← NumberField.absNorm_differentIdeal L (𝓞 L)] at hdvd
  set 𝔡 : Ideal (𝓞 L) := differentIdeal ℤ (𝓞 L) with h𝔡
  have h𝔡ne : 𝔡 ≠ 0 := differentIdeal_ne_bot
  -- write the norm as a product over the prime factors
  have hfac : Ideal.absNorm 𝔡 = ((normalizedFactors 𝔡).map Ideal.absNorm).prod := by
    rw [← map_multiset_prod, associated_iff_eq.mp (prod_normalizedFactors h𝔡ne)]
  have hprimes : ∀ P ∈ normalizedFactors 𝔡, P.IsPrime ∧ P ≠ ⊥ := fun P hP =>
    mem_normalizedFactors_prime h𝔡ne hP
  have hnormne : Ideal.absNorm 𝔡 ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact h𝔡ne
  -- `p` divides the norm, so it appears in the factorisation
  have hfp : (Ideal.absNorm 𝔡).factorization p ≠ 0 := by
    have h1 := (Nat.Prime.dvd_iff_one_le_factorization hp hnormne).mp hdvd
    omega
  rw [hfac, factorization_prod_map p hp (normalizedFactors 𝔡) hprimes] at hfp
  -- hence some prime factor lies over `p`
  obtain ⟨P, hPmem, hPw⟩ : ∃ P ∈ normalizedFactors 𝔡, w p P ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hfp
    have : ((normalizedFactors 𝔡).map (w p)) = (normalizedFactors 𝔡).map (fun _ => 0) :=
      Multiset.map_congr rfl (fun P hP => hcon P hP)
    rw [this]
    simp
  have hPp := hprimes P hPmem
  haveI : P.IsPrime := hPp.1
  have hq : qOf L P = p := by
    by_contra hcon
    rw [w, if_neg hcon] at hPw
    exact hPw rfl
  -- `P` lies over `p` and divides the different ideal
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := by
    have := liesOver_qOf (K := L) P
    rwa [hq] at this
  have hPmemOver : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 L) := ⟨hPp.1, inferInstance⟩
  have hdvd𝔡 : P ∣ 𝔡 := dvd_of_mem_normalizedFactors hPmem
  -- but `P` is unramified, so it does not divide the different
  have hPbot : P ≠ ⊥ := hPp.2
  haveI : Algebra.IsUnramifiedAt ℤ P := by
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPbot]
    have hunder : Ideal.under ℤ P = Ideal.span {(p : ℤ)} := by
      rw [under_eq_span (K := L) P, hq]
    rw [hunder]
    exact h P hPmemOver
  exact (not_dvd_differentIdeal_iff (A := ℤ) (B := 𝓞 L) (P := P)).mpr inferInstance hdvd𝔡

/-- A prime not dividing `m` is unramified in every subfield of `ℚ(ζ_m)`. -/
theorem unramified_of_not_dvd (m : ℕ+) (L : IntermediateField ℚ ℂ) [NumberField ↥L]
    (hL : L ≤ cyclotomicField' m) (p : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ (m : ℕ)) :
    ∀ Q ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 ↥L),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  letI : Algebra ↥L ↥(cyclotomicField' m) := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ ↥L ↥(cyclotomicField' m) :=
    IsScalarTower.of_algebraMap_eq (fun x => ((IntermediateField.inclusion hL).commutes x).symm)
  intro Q hQ
  obtain ⟨hQprime, hQlies⟩ := hQ
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver (Ideal.span {(p : ℤ)}) := hQlies
  obtain ⟨⟨P, hPprime, hPlies⟩⟩ :=
    Q.nonempty_primesOver (S := 𝓞 ↥(cyclotomicField' m))
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver Q := hPlies
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := Ideal.LiesOver.trans P Q _
  have hPe := IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd (m := (m : ℕ)) p
    ↥(cyclotomicField' m) P hpm
  have htower : Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) Q * Ideal.ramificationIdx Q P :=
    Ideal.ramificationIdx_algebra_tower' (R := ℤ) (S := 𝓞 ↥L)
      (T := 𝓞 ↥(cyclotomicField' m)) _ _ _
  rw [hPe] at htower
  exact Nat.dvd_one.mp ⟨_, htower⟩

end Workspace.ProofLemmas.UnramifiedOutsideLevel

/-!
# The exact different exponent, propagated down a tower

Mathlib knows two things about the different ideal of a number field:

* `pow_sub_one_dvd_differentIdeal` : `P ^ (e - 1) ∣ 𝔡`;
* `not_dvd_differentIdeal_iff` : `P ∤ 𝔡` exactly when `P` is unramified.

It does **not** know the tame value `v_P(𝔡) = e - 1` (that is a local computation with higher
ramification groups).  The point of this file is that one does not need it for *subfields of a field
whose different exponent is already known*: in a tower `ℚ ⊆ L ⊆ K` the two Mathlib lower bounds for
`𝔡_{K/L}` and `𝔡_{L/ℚ}` already add up to `e(P/p) - 1`, so if `v_P(𝔡_K) = e(P/p) - 1` then **both**
must be equalities and in particular `v_{P∩L}(𝔡_L) = e(P∩L/p) - 1`.

This is the "forced equality" trick; it turns the single computation for `ℚ(ζ_m)` into the tame
conductor–discriminant input for every subfield of `ℚ(ζ_m)`.
-/

open scoped NumberField

namespace Workspace.ProofLemmas.TameDifferent

set_option maxHeartbeats 1000000

section Tower

variable (L K : Type*) [Field L] [NumberField L] [Field K] [NumberField K] [Algebra L K]

end Tower

/-- `e(P/p) ≤ [E:F]`. -/
theorem ramificationIdx_le_finrank (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E] [Algebra R E]
    [IsScalarTower R S E] [IsScalarTower R F E] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p] :
    Ideal.ramificationIdx p P ≤ Module.finrank F E := by
  have hsum := Ideal.sum_ramification_inertia (R := R) S F E hp
  have hmem : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp S).mpr ⟨inferInstance, inferInstance⟩
  have hle : Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset p S,
          Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q :=
    Finset.single_le_sum (f := fun Q => Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hsum] at hle
  have hf : 1 ≤ Ideal.inertiaDeg p P := Ideal.inertiaDeg_pos p P
  nlinarith [hle, hf]

/-- If `e(P/p) = [E:F]` then `f(P/p) = 1`. -/
theorem inertiaDeg_eq_one_of_totally_ramified
    (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (F : Type*) [Field F] [Algebra R F] [IsFractionRing R F]
    (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S] [Algebra R S]
    [Module.IsTorsionFree R S]
    (E : Type*) [Field E] [Algebra S E] [IsFractionRing S E] [Algebra F E] [Algebra R E]
    [IsScalarTower R S E] [IsScalarTower R F E] [Module.Finite R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) [P.IsPrime] [P.LiesOver p]
    (he : Ideal.ramificationIdx p P = Module.finrank F E) (hpos : 0 < Module.finrank F E) :
    Ideal.inertiaDeg p P = 1 := by
  have hsum := Ideal.sum_ramification_inertia (R := R) S F E hp
  have hmem : P ∈ IsDedekindDomain.primesOverFinset p S :=
    (IsDedekindDomain.mem_primesOverFinset_iff hp S).mpr ⟨inferInstance, inferInstance⟩
  have hle : Ideal.ramificationIdx p P * Ideal.inertiaDeg p P
      ≤ ∑ Q ∈ IsDedekindDomain.primesOverFinset p S,
          Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q :=
    Finset.single_le_sum (f := fun Q => Ideal.ramificationIdx p Q * Ideal.inertiaDeg p Q)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hsum, he] at hle
  have hf : 1 ≤ Ideal.inertiaDeg p P := Ideal.inertiaDeg_pos p P
  nlinarith [hle, hf, hpos]

section Subfield

variable (r : ℕ) [hr : Fact r.Prime]
variable (K : Type) [Field K] [NumberField K] [hcyc : IsCyclotomicExtension {r} ℚ K]
variable (L : Type) [Field L] [NumberField L] [Algebra L K]

theorem span_r_ne_bot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
  simp only [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast hr.out.ne_zero

instance span_r_isPrime : (Ideal.span {(r : ℤ)}).IsPrime := by
  rw [Ideal.span_singleton_prime (by exact_mod_cast hr.out.ne_zero)]
  exact Nat.prime_iff_prime_int.mp hr.out

instance span_r_isMaximal : (Ideal.span {(r : ℤ)}).IsMaximal :=
  Ideal.IsPrime.isMaximal inferInstance (span_r_ne_bot r)

/-- Every subfield of `ℚ(ζ_r)` is totally ramified at `r`. -/
theorem totally_ramified
    (P : Ideal (𝓞 K)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})] (hP : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) (P.under (𝓞 L)) = Module.finrank ℚ L
      ∧ Ideal.ramificationIdx (P.under (𝓞 L)) P = Module.finrank L K := by
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional L K := Module.Finite.right ℚ L K
  haveI : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  set PL : Ideal (𝓞 L) := P.under (𝓞 L) with hPLdef
  haveI : PL.IsPrime := Ideal.IsPrime.under _ P
  haveI : PL.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [hPLdef, Ideal.under_under]
    exact hPl.over
  haveI : P.LiesOver PL := ⟨rfl⟩
  have hrbot := span_r_ne_bot r
  have hPLbot : PL ≠ ⊥ := by
    intro hcon
    exact hP (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 L) (S := 𝓞 K) (I := P) hcon)
  haveI : PL.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPLbot
  -- the ramification index upstairs
  have heK : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = r - 1 :=
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime r K P
  -- degrees
  have hnK : Module.finrank ℚ K = r - 1 := by
    rw [IsCyclotomicExtension.Rat.finrank (K := K) (k := r), Nat.totient_prime hr.out]
  have hdeg : Module.finrank ℚ L * Module.finrank L K = r - 1 := by
    rw [Module.finrank_mul_finrank ℚ L K, hnK]
  -- tower multiplicativity of `e`
  have hinjL : Function.Injective (algebraMap (𝓞 L) (𝓞 K)) :=
    FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 K)
  have hinjZ : Function.Injective (algebraMap ℤ (𝓞 K)) :=
    FaithfulSMul.algebraMap_injective ℤ (𝓞 K)
  have htower : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL * Ideal.ramificationIdx PL P := by
    refine Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 L) (T := 𝓞 K) ?_ ?_ ?_
    · exact (Ideal.map_eq_bot_iff_of_injective hinjL).not.mpr hPLbot
    · exact (Ideal.map_eq_bot_iff_of_injective hinjZ).not.mpr hrbot
    · exact Ideal.map_le_of_le_comap le_rfl
  -- both factors are bounded by the corresponding degrees
  have h1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL ≤ Module.finrank ℚ L :=
    ramificationIdx_le_finrank ℤ ℚ (𝓞 L) L _ hrbot PL
  have h2 : Ideal.ramificationIdx PL P ≤ Module.finrank L K :=
    ramificationIdx_le_finrank (𝓞 L) L (𝓞 K) K _ hPLbot P
  rw [heK] at htower
  set a := Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) PL with hadef
  set b := Ideal.ramificationIdx PL P with hbdef
  set A := Module.finrank ℚ L with hAdef
  set B := Module.finrank L K with hBdef
  have hApos : 0 < A := Module.finrank_pos
  have hBpos : 0 < B := Module.finrank_pos
  have hab : a * b = A * B := (hdeg.trans htower).symm
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.mul_zero] at hab
      exact absurd hab.symm (Nat.mul_ne_zero hApos.ne' hBpos.ne')
    · exact h
  have hapos : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · rw [h, Nat.zero_mul] at hab
      exact absurd hab.symm (Nat.mul_ne_zero hApos.ne' hBpos.ne')
    · exact h
  refine ⟨?_, ?_⟩
  · by_contra hne
    have hlt : a < A := lt_of_le_of_ne h1 hne
    have hcon : a * b < A * B :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le hlt (le_refl b) hbpos)
        (Nat.mul_le_mul_left A h2)
    omega
  · by_contra hne
    have hlt : b < B := lt_of_le_of_ne h2 hne
    have hcon : a * b < A * B :=
      lt_of_lt_of_le (Nat.mul_lt_mul_of_le_of_lt h1 hlt hApos)
        (le_refl (A * B))
    omega

end Subfield

section Discr

/-- **Discriminant of a subfield of `ℚ(ζ_r)`.** -/
theorem natAbs_discr_subfield (r : ℕ) [hr : Fact r.Prime]
    (K : Type) [Field K] [NumberField K] [hcyc : IsCyclotomicExtension {r} ℚ K]
    (L : Type) [Field L] [NumberField L] [Algebra L K] :
    (NumberField.discr L).natAbs = r ^ (Module.finrank ℚ L - 1) := by
  haveI : IsScalarTower ℚ L K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional L K := Module.Finite.right ℚ L K
  haveI : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  have hrbot := span_r_ne_bot r
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr.out
  -- a prime of `𝓞 K` over `r`
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(r : ℤ)})
  haveI := hPmax
  haveI := hPlies
  haveI : P.IsPrime := hPmax.isPrime
  have hPbot : P ≠ ⊥ := by
    intro hcon
    subst hcon
    have : (Ideal.span {(r : ℤ)}) = ⊥ := by
      have := hPlies.over
      simpa using this
    exact hrbot this
  set PL : Ideal (𝓞 L) := P.under (𝓞 L) with hPLdef
  haveI : PL.IsPrime := Ideal.IsPrime.under _ P
  haveI : PL.LiesOver (Ideal.span {(r : ℤ)}) := by
    constructor
    rw [hPLdef, Ideal.under_under]
    exact hPlies.over
  haveI : P.LiesOver PL := ⟨rfl⟩
  have hPLbot : PL ≠ ⊥ := by
    intro hcon
    exact hPbot (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := 𝓞 L) (S := 𝓞 K) (I := P) hcon)
  haveI : PL.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hPLbot
  obtain ⟨he1, he2⟩ := totally_ramified r K L P hPbot
  set n := Module.finrank ℚ L with hn
  set m := Module.finrank L K with hm
  have hnpos : 0 < n := Module.finrank_pos
  have hmpos : 0 < m := Module.finrank_pos
  -- inertia degrees are `1`
  have hfK : Ideal.inertiaDeg (Ideal.span {(r : ℤ)}) P = 1 :=
    IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime r K P
  have hfL : Ideal.inertiaDeg (Ideal.span {(r : ℤ)}) PL = 1 :=
    inertiaDeg_eq_one_of_totally_ramified ℤ ℚ (𝓞 L) L _ hrbot PL he1 hnpos
  -- absolute norms
  have hNK : Ideal.absNorm P = r := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg P hrprime, hfK, pow_one, Int.natAbs_natCast]
  have hNL : Ideal.absNorm PL = r := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg PL hrprime, hfL, pow_one, Int.natAbs_natCast]
  -- lower bound
  have hlow : r ^ (n - 1) ∣ (NumberField.discr L).natAbs := by
    have h1 : PL ^ (n - 1) ∣ differentIdeal ℤ (𝓞 L) := by
      rw [← he1]
      exact pow_sub_one_dvd_differentIdeal ℤ PL _ hrbot
        (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    have h2 := map_dvd Ideal.absNorm h1
    rw [map_pow, hNL, NumberField.absNorm_differentIdeal L (𝓞 L)] at h2
    exact h2
  -- upper bound
  have hrel : (r : ℕ) ^ (m - 1) ∣ Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) := by
    have h1 : P ^ (m - 1) ∣ differentIdeal (𝓞 L) (𝓞 K) := by
      rw [← he2]
      exact pow_sub_one_dvd_differentIdeal (𝓞 L) P _ hPLbot
        (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    have h2 := map_dvd Ideal.absNorm h1
    rwa [map_pow, hNK] at h2
  have htow := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow L (𝓞 L) K (𝓞 K)
  have hdiscK : (NumberField.discr K).natAbs = r ^ (r - 2) := by
    rw [IsCyclotomicExtension.Rat.discr_prime r K]
    simp [Int.natAbs_mul, Int.natAbs_pow]
  have hnm : n * m = r - 1 := by
    rw [hn, hm, Module.finrank_mul_finrank ℚ L K,
      IsCyclotomicExtension.Rat.finrank (K := K) (k := r), Nat.totient_prime hr.out]
  set B := (NumberField.discr L).natAbs with hB
  obtain ⟨A', hA'⟩ := hrel
  rw [hdiscK, hA'] at htow
  have hdvd1 : r ^ (m - 1) * B ^ m ∣ r ^ (r - 2) := ⟨A', by rw [htow]; ring⟩
  have hr2 : 2 ≤ r := hr.out.two_le
  have hnm' : m * n = r - 1 := by rw [Nat.mul_comm]; exact hnm
  have hsub : m * (n - 1) = (r - 1) - m := by rw [Nat.mul_sub, Nat.mul_one, hnm']
  have hmle : m ≤ r - 1 := Nat.le_of_dvd (by omega) ⟨n, hnm'.symm⟩
  have hexp : r - 2 = (m - 1) + m * (n - 1) := by rw [hsub]; omega
  rw [hexp, pow_add] at hdvd1
  have hcancel : B ^ m ∣ r ^ (m * (n - 1)) :=
    (Nat.mul_dvd_mul_iff_left (pow_pos hr.out.pos (m - 1))).mp hdvd1
  have hcancel2 : B ^ m ∣ (r ^ (n - 1)) ^ m := by
    rw [← pow_mul, Nat.mul_comm]
    exact hcancel
  have hup : B ∣ r ^ (n - 1) := (Nat.pow_dvd_pow_iff hmpos.ne').mp hcancel2
  exact Nat.dvd_antisymm hup hlow

end Discr

end Workspace.ProofLemmas.TameDifferent

/-!
# The tame conductor–discriminant computation for subfields of `ℚ(ζ_D)`, `D` squarefree

This file replaces the Artin-conductor input of the classical conductor–discriminant formula by an
inertia argument that works whenever the level is squarefree (so all ramification is tame).

Main results:

* `conductor_dvd_of_cutOutField_le` — if `cutOutField D χ ⊆ ℚ(ζ_m)` then `f(χ) ∣ m`
  (the Galois correspondence plus `DirichletCharacter.factorsThrough_iff_ker_unitsMap`);
* `le_cyclotomicField_of_not_dvd_discr` — a subfield of `ℚ(ζ_D)` unramified at `r ‖ D` already
  lies in `ℚ(ζ_{D/r})` (the inertia group at `r` *is* `Gal(ℚ(ζ_D)/ℚ(ζ_{D/r}))`);
* `not_pow_totient_dvd_discr` — `r^{φ(D)} ∤ |disc ℚ(ζ_D)|`, from Mathlib's discriminant formula;
* `natAbs_discr_cutOutField` — **`|disc(cutOutField D χ)| = D²`** for `D` squarefree, `f(χ) = D`
  and `[cutOutField D χ : ℚ] = 3`.
-/

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.CyclotomicTameDiscriminant

open Workspace.ProofLemmas.InertiaLocal

/-- `ζ_a = ζ_b ^ (b / a)` for `a ∣ b`. -/
theorem zetaC_pow_of_dvd (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    zetaC a = zetaC b ^ ((b : ℕ) / (a : ℕ)) := by
  obtain ⟨c, hc⟩ := h
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hc
    exact b.pos.ne' hc
  have ha : ((a : ℕ) : ℂ) ≠ 0 := by exact_mod_cast a.pos.ne'
  have hcC : ((c : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hc0
  rw [zetaC, zetaC, ← Complex.exp_nat_mul, hc, Nat.mul_div_cancel_left _ a.pos]
  congr 1
  push_cast
  field_simp

/-- `ℚ(ζ_a) ⊆ ℚ(ζ_b)` for `a ∣ b`. -/
theorem cyclotomicField'_mono (a b : ℕ+) (h : (a : ℕ) ∣ (b : ℕ)) :
    cyclotomicField' a ≤ cyclotomicField' b := by
  unfold cyclotomicField'
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst hx
  rw [zetaC_pow_of_dvd a b h]
  exact pow_mem (IntermediateField.subset_adjoin ℚ {zetaC b} rfl) _

/-- If the field cut out by `chi` sits inside `ℚ(ζ_m)` then `chi` factors through level `m`;
in particular its conductor divides `m`. -/
theorem conductor_dvd_of_cutOutField_le (D m : ℕ+) (hmD : (m : ℕ) ∣ (D : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ))
    (h : cutOutField D chi ≤ cyclotomicField' m) :
    DirichletCharacter.conductor chi ∣ (m : ℕ) := by
  classical
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  set K := cyclotomicField' D with hK
  set H : Subgroup (↥K ≃ₐ[ℚ] ↥K) := (chi.toUnitHom.comp (galToUnits D).toMonoidHom).ker with hHdef
  -- `fixedField H` sits inside the copy of `ℚ(ζ_m)` inside `K`
  have hfix : IntermediateField.fixedField H ≤ (cyclotomicField' m).comap K.val := by
    intro x hx
    have hmem : (x : ℂ) ∈ cutOutField D chi := ⟨x, hx, rfl⟩
    exact h hmem
  -- every unit congruent to `1` mod `m` acts trivially on `ℚ(ζ_m)`
  have hker : (ZMod.unitsMap hmD).ker ≤ chi.toUnitHom.ker := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    set σ : ↥K ≃ₐ[ℚ] ↥K := (galToUnits D).symm a with hσ
    have hgal : galToUnits D σ = a := by rw [hσ]; exact (galToUnits D).apply_symm_apply a
    have hzmem : zetaC m ∈ K :=
      cyclotomicField'_mono m D hmD (IntermediateField.mem_adjoin_simple_self ℚ _)
    set y : ↥K := ⟨zetaC m, hzmem⟩ with hy
    have hym : y ^ (m : ℕ) = 1 := by
      apply Subtype.ext
      show (zetaC m) ^ (m : ℕ) = 1
      exact (isPrimitiveRoot_zetaC m).pow_eq_one
    have hyD : y ^ (D : ℕ) = 1 := by
      obtain ⟨c, hc⟩ := hmD
      apply Subtype.ext
      show (zetaC m) ^ (D : ℕ) = 1
      rw [hc, pow_mul, (isPrimitiveRoot_zetaC m).pow_eq_one, one_pow]
    have hact : σ y = y ^ ((galToUnits D σ : ZMod (D : ℕ))).val :=
      IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq (D : ℕ) ↥K σ hyD
    -- the exponent is `≡ 1 (mod m)`
    have hmod : ((a : ZMod (D : ℕ))).val % (m : ℕ) = 1 % (m : ℕ) := by
      have h1 : (ZMod.castHom hmD (ZMod (m : ℕ))) ((a : ZMod (D : ℕ))) = 1 := by
        have h0 := congrArg (fun u : (ZMod (m : ℕ))ˣ => (u : ZMod (m : ℕ))) ha
        simpa [ZMod.unitsMap, Units.coe_map] using h0
      have h2 : ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (m : ℕ)) = ((1 : ℕ) : ZMod (m : ℕ)) := by
        calc ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (m : ℕ))
            = ZMod.castHom hmD (ZMod (m : ℕ)) ((((a : ZMod (D : ℕ))).val : ℕ) : ZMod (D : ℕ)) :=
              (map_natCast _ _).symm
          _ = ZMod.castHom hmD (ZMod (m : ℕ)) ((a : ZMod (D : ℕ))) := by
              rw [ZMod.natCast_val, ZMod.cast_id]
          _ = 1 := h1
          _ = ((1 : ℕ) : ZMod (m : ℕ)) := by simp
      exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h2
    have hpow : ∀ k : ℕ, y ^ k = y ^ (k % (m : ℕ)) := by
      intro k
      conv_lhs => rw [← Nat.div_add_mod k (m : ℕ)]
      rw [pow_add, pow_mul, hym, one_pow, one_mul]
    have hfixy : σ y = y := by
      rw [hact, hgal, hpow, hmod, ← hpow 1, pow_one]
    -- hence `σ` fixes the copy of `ℚ(ζ_m)` pointwise
    set S : IntermediateField ℚ ↥K :=
      IntermediateField.fixedField (Subgroup.closure ({σ} : Set (↥K ≃ₐ[ℚ] ↥K))) with hS
    have hyS : y ∈ S := by
      rw [hS]
      refine (IntermediateField.mem_fixedField_iff _ y).mpr ?_
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
          simp only [Set.mem_singleton_iff] at hx
          subst hx
          exact hfixy
      | one => rfl
      | mul a b _ _ ha' hb' => rw [AlgEquiv.mul_apply, hb', ha']
      | inv a _ ha' =>
          have hinv : a⁻¹ (a y) = y := by simp
          rwa [ha'] at hinv
    have hlift : cyclotomicField' m ≤ IntermediateField.lift S := by
      show IntermediateField.adjoin ℚ {zetaC m} ≤ _
      rw [IntermediateField.adjoin_le_iff]
      rintro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨y, hyS, rfl⟩
    have hEle : ((cyclotomicField' m).comap K.val) ≤ S := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := hlift hx
      have hzex : z = x := Subtype.ext hzx
      rwa [← hzex]
    have hσfix : σ ∈ ((cyclotomicField' m).comap K.val).fixingSubgroup := by
      refine (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr ?_
      intro x hx
      have hxS := hEle hx
      rw [hS] at hxS
      exact (IntermediateField.mem_fixedField_iff _ x).mp hxS σ (Subgroup.subset_closure rfl)
    -- transfer along the Galois correspondence
    have hanti : ((cyclotomicField' m).comap K.val).fixingSubgroup
        ≤ (IntermediateField.fixedField H).fixingSubgroup := by
      intro τ hτ
      refine (IntermediateField.mem_fixingSubgroup_iff _ τ).mpr ?_
      intro x hx
      exact (IntermediateField.mem_fixingSubgroup_iff _ τ).mp hτ x (hfix hx)
    have hσH : σ ∈ H := by
      have := hanti hσfix
      rwa [IntermediateField.fixingSubgroup_fixedField] at this
    rw [hHdef, MonoidHom.mem_ker, MonoidHom.comp_apply] at hσH
    rw [← hgal]
    exact hσH
  have hfac : DirichletCharacter.FactorsThrough chi (m : ℕ) := by
    rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hmD]
    exact hker
  exact DirichletCharacter.conductor_dvd_of_mem_conductorSet (χ := chi) hfac

section Inertia

open Workspace.ProofLemmas.InertiaLocal

/-- The `ℚ`-isomorphism `↥(S.comap K.val) ≃ₐ[ℚ] ↥S` for `S ≤ K`. -/
noncomputable def comapEquiv (K S : IntermediateField ℚ ℂ) (hS : S ≤ K) :
    ↥(S.comap K.val) ≃ₐ[ℚ] ↥S :=
  (IntermediateField.liftAlgEquiv _).trans
    (IntermediateField.equivOfEq (by
      show (S.comap K.val).map K.val = S
      rw [IntermediateField.map_comap_eq, IntermediateField.fieldRange_val, inf_eq_left]
      exact hS))

theorem discr_comap (K S : IntermediateField ℚ ℂ) (hS : S ≤ K) [NumberField ↥S]
    [NumberField ↥(S.comap K.val)] :
    NumberField.discr ↥(S.comap K.val) = NumberField.discr ↥S :=
  NumberField.discr_eq_discr_of_algEquiv _ (comapEquiv K S hS)

/-- Abstract form of the inertia argument: if `S` and `E` are both unramified at `r` and the
fixing subgroup of `E` has exactly `e(P/r)` elements, then `S ≤ E`. -/
theorem le_of_inertia (K : Type) [Field K] [NumberField K] [hgal : IsGalois ℚ K]
    (r : ℕ) (hr : r.Prime)
    (P : Ideal (𝓞 K)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})] (hPne : P ≠ ⊥)
    (E S : IntermediateField ℚ K)
    (hdS : haveI : NumberField ↥S := NumberField.of_module_finite ℚ ↥S
      ¬ r ∣ (NumberField.discr ↥S).natAbs)
    (hdE : haveI : NumberField ↥E := NumberField.of_module_finite ℚ ↥E
      ¬ r ∣ (NumberField.discr ↥E).natAbs)
    (hfin : Module.finrank ↥E K = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P) :
    S ≤ E := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  have hIS := inertia_le_fixingSubgroup_of_not_dvd_discr K S r hr P hPne hdS
  have hIE := inertia_le_fixingSubgroup_of_not_dvd_discr K E r hr P hPne hdE
  have hcardI := card_inertia_eq_ramificationIdx_int K (Ideal.span {(r : ℤ)}) hrbot P hPne
  have hcardE : Nat.card ↥(E.fixingSubgroup) = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P := by
    rw [IsGalois.card_fixingSubgroup_eq_finrank E, hfin]
  have hIeq := Subgroup.eq_of_le_of_card_ge hIE (by rw [hcardI, hcardE])
  have h1 : E.fixingSubgroup ≤ S.fixingSubgroup := by rw [← hIeq]; exact hIS
  have h2 := (IntermediateField.le_iff_le (E.fixingSubgroup) S).mpr h1
  rwa [IsGalois.fixedField_fixingSubgroup] at h2

/-- **Only the ramified primes can cut a subfield down.**  If the rational prime `r` (with
`D = r·m`, `r ∤ m`) does not divide `|disc S|` for a subfield `S ≤ ℚ(ζ_D)`, then already
`S ≤ ℚ(ζ_m)`. -/
theorem le_cyclotomicField_of_not_dvd_discr (D : ℕ+) (r : ℕ) (hr : r.Prime) (m : ℕ+)
    (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ))
    (S : IntermediateField ℚ ℂ) [NumberField ↥S] (hS : S ≤ cyclotomicField' D)
    (hdisc : ¬ r ∣ (NumberField.discr ↥S).natAbs) :
    S ≤ cyclotomicField' m := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  haveI hrf : Fact r.Prime := ⟨hr⟩
  have hmD : (m : ℕ) ∣ (D : ℕ) := ⟨r, by rw [hD]; ring⟩
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  obtain ⟨P, hPmax, hPlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 ↥(cyclotomicField' D))
      (Ideal.span {(r : ℤ)})
  haveI := hPmax
  haveI := hPlies
  haveI : P.IsPrime := hPmax.isPrime
  have hPne : P ≠ ⊥ := by
    intro hcon
    subst hcon
    exact hrbot (by simpa using hPlies.over)
  have hmDle : cyclotomicField' m ≤ cyclotomicField' D := cyclotomicField'_mono m D hmD
  haveI : NumberField ↥(S.comap (cyclotomicField' D).val) := NumberField.of_module_finite ℚ _
  haveI : NumberField ↥((cyclotomicField' m).comap (cyclotomicField' D).val) :=
    NumberField.of_module_finite ℚ _
  have hdS : ¬ r ∣ (NumberField.discr ↥(S.comap (cyclotomicField' D).val)).natAbs := by
    rw [discr_comap (cyclotomicField' D) S hS]; exact hdisc
  have hdE : ¬ r ∣
      (NumberField.discr ↥((cyclotomicField' m).comap (cyclotomicField' D).val)).natAbs := by
    rw [discr_comap (cyclotomicField' D) (cyclotomicField' m) hmDle]
    refine Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified
      ↥(cyclotomicField' m) r hr ?_
    exact Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd m
      (cyclotomicField' m) le_rfl r hr hrm
  -- the degree computation
  have hcoprime : Nat.Coprime r (m : ℕ) := (Nat.Prime.coprime_iff_not_dvd hr).mpr hrm
  have htotD : (D : ℕ).totient = (r - 1) * (m : ℕ).totient := by
    rw [hD, Nat.totient_mul hcoprime, Nat.totient_prime hr]
  have hmpos : 0 < (m : ℕ).totient := Nat.totient_pos.mpr m.pos
  have hram : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = r - 1 := by
    have h := IsCyclotomicExtension.Rat.ramificationIdx_eq (n := (D : ℕ)) (p := r) (k := 0)
      (m := (m : ℕ)) ↥(cyclotomicField' D) P (by rw [hD]; ring) hrm
    rw [h, pow_zero, one_mul]
  have hfin : Module.finrank ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
      ↥(cyclotomicField' D) = Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P := by
    rw [hram]
    have h1 : Module.finrank ℚ ↥(cyclotomicField' D) = (D : ℕ).totient :=
      IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' D)) (k := (D : ℕ))
    have h2 : Module.finrank ℚ ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
        = (m : ℕ).totient := by
      rw [LinearEquiv.finrank_eq
        (comapEquiv (cyclotomicField' D) (cyclotomicField' m) hmDle).toLinearEquiv]
      exact IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' m)) (k := (m : ℕ))
    have h3 : Module.finrank ℚ ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
        * Module.finrank ↥((cyclotomicField' m).comap (cyclotomicField' D).val)
            ↥(cyclotomicField' D) = Module.finrank ℚ ↥(cyclotomicField' D) :=
      Module.finrank_mul_finrank ℚ _ ↥(cyclotomicField' D)
    rw [h1, h2, htotD] at h3
    exact Nat.eq_of_mul_eq_mul_left hmpos (by linarith [h3])
  -- apply the abstract lemma
  have hle := @le_of_inertia ↥(cyclotomicField' D) _ _ (instIsGalois D) r hr P _ _ hPne
    ((cyclotomicField' m).comap (cyclotomicField' D).val) (S.comap (cyclotomicField' D).val)
    hdS hdE hfin
  intro x hx
  have hxK : x ∈ cyclotomicField' D := hS hx
  exact hle (show (⟨x, hxK⟩ : ↥(cyclotomicField' D)) ∈ S.comap (cyclotomicField' D).val from hx)

end Inertia

section DiscrBound

/-- `r ^ φ(D)` does not divide the discriminant of `ℚ(ζ_D)` when `r ‖ D`. -/
theorem not_pow_totient_dvd_discr (D : ℕ+) (r : ℕ) (hr : r.Prime) (m : ℕ+)
    (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ)) :
    ¬ r ^ ((D : ℕ).totient) ∣ (NumberField.discr ↥(cyclotomicField' D)).natAbs := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  set N := (D : ℕ).totient with hN
  set Q := ∏ p ∈ (D : ℕ).primeFactors, p ^ (N / (p - 1)) with hQ
  have hQdvd : Q ∣ (D : ℕ) ^ N := Nat.prod_primeFactors_pow_totient_ediv_dvd D.pos
  have hdisc : (NumberField.discr ↥(cyclotomicField' D)).natAbs = (D : ℕ) ^ N / Q :=
    IsCyclotomicExtension.Rat.natAbs_discr (D : ℕ) ↥(cyclotomicField' D)
  have hmul : (NumberField.discr ↥(cyclotomicField' D)).natAbs * Q = (D : ℕ) ^ N := by
    rw [hdisc]
    exact Nat.div_mul_cancel hQdvd
  -- `r` divides `Q`
  have hrmem : r ∈ (D : ℕ).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨hr, ⟨(m : ℕ), hD⟩, D.pos.ne'⟩
  have hr1N : (r - 1) ∣ N := by
    rw [hN, ← Nat.totient_prime hr]
    exact Nat.totient_dvd_of_dvd ⟨(m : ℕ), hD⟩
  have hNpos : 0 < N := Nat.totient_pos.mpr D.pos
  have hr2 : 2 ≤ r := hr.two_le
  have hexp : 1 ≤ N / (r - 1) := by
    refine Nat.one_le_div_iff (by omega) |>.mpr ?_
    exact Nat.le_of_dvd hNpos hr1N
  have hrQ : r ∣ Q := by
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun p => p ^ (N / (p - 1))) hrmem)
    exact dvd_pow_self r (Nat.one_le_iff_ne_zero.mp hexp)
  -- conclude
  intro hcon
  obtain ⟨c, hc⟩ := hcon
  obtain ⟨d, hd⟩ := hrQ
  have hkey : r ^ (N + 1) ∣ (D : ℕ) ^ N := by
    refine ⟨c * d, ?_⟩
    rw [← hmul, hc, hd]
    ring
  rw [hD, mul_pow] at hkey
  have hcancel : r ∣ (m : ℕ) ^ N := by
    have h1 : r ^ N * r ∣ r ^ N * (m : ℕ) ^ N := by
      rw [← pow_succ]
      exact hkey
    exact (mul_dvd_mul_iff_left (pow_ne_zero N hr.ne_zero)).mp h1
  exact hrm (hr.dvd_of_dvd_pow hcancel)

end DiscrBound

/-- In a cubic Galois field, a ramified prime divides the discriminant to order at least `2`. -/
theorem sq_dvd_discr_of_dvd_discr (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (hdeg : Module.finrank ℚ F = 3) (r : ℕ) (hr : r.Prime)
    (hrA : r ∣ (NumberField.discr F).natAbs) :
    r ^ 2 ∣ (NumberField.discr F).natAbs := by
  have hrprime : Prime ((r : ℤ)) := Nat.prime_iff_prime_int.mp hr
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact hrprime
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  have hex : ∃ Q ∈ Ideal.primesOver (Ideal.span {(r : ℤ)}) (𝓞 F),
      Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified F r hr
      hcon) hrA
  obtain ⟨Q, hQmem, hQe⟩ := hex
  obtain ⟨hQp, hQl⟩ := hQmem
  haveI := hQp
  haveI := hQl
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hrbot Q
  have hcard := card_inertia_eq_ramificationIdx_int F (Ideal.span {(r : ℤ)}) hrbot Q hQne
  have hdvd3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ∣ 3 := by
    rw [← hcard, ← hdeg, ← IsGalois.card_aut_eq_finrank ℚ F]
    exact Subgroup.card_subgroup_dvd_card _
  have he3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 3 := by
    rcases (Nat.dvd_prime (by norm_num)).mp hdvd3 with h | h
    · exact absurd h hQe
    · exact h
  have h2 : Q ^ 2 ∣ differentIdeal ℤ (𝓞 F) := by
    have h := pow_sub_one_dvd_differentIdeal ℤ Q
      (Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q) hrbot
      (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx)
    rwa [he3] at h
  have h3 := map_dvd Ideal.absNorm h2
  rw [map_pow, NumberField.absNorm_differentIdeal F (𝓞 F),
    Ideal.absNorm_eq_pow_inertiaDeg Q hrprime, Int.natAbs_natCast, ← pow_mul] at h3
  refine dvd_trans ?_ h3
  refine pow_dvd_pow r ?_
  have := Ideal.inertiaDeg_pos (Ideal.span {(r : ℤ)}) Q
  omega

/-- A prime dividing the (squarefree) conductor really is ramified. -/
theorem dvd_discr_cutOutField (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    [NumberField ↥(cutOutField D chi)]
    (r : ℕ) (hr : r.Prime) (m : ℕ+) (hD : (D : ℕ) = r * (m : ℕ)) (hrm : ¬ r ∣ (m : ℕ))
    (hcond : DirichletCharacter.conductor chi = (D : ℕ)) :
    r ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs := by
  by_contra hcon
  have hle := le_cyclotomicField_of_not_dvd_discr D r hr m hD hrm (cutOutField D chi)
    (IntermediateField.lift_le _) hcon
  have hdvd := conductor_dvd_of_cutOutField_le D m ⟨r, by rw [hD]; ring⟩ chi hle
  rw [hcond] at hdvd
  have hDm : (D : ℕ) ≤ (m : ℕ) := Nat.le_of_dvd m.pos hdvd
  have h2 : 2 * (m : ℕ) ≤ r * (m : ℕ) := Nat.mul_le_mul_right _ hr.two_le
  have hmpos := m.pos
  omega

/-- **Discriminant of the cubic field cut out by a character of squarefree conductor `D`.** -/
theorem natAbs_discr_cutOutField (D : ℕ+) (chi : DirichletCharacter ℂ (D : ℕ))
    [NumberField ↥(cutOutField D chi)]
    (hsq : Squarefree (D : ℕ))
    (hcond : DirichletCharacter.conductor chi = (D : ℕ))
    (hdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3) :
    (NumberField.discr ↥(cutOutField D chi)).natAbs = (D : ℕ) ^ 2 := by
  haveI : NeZero (D : ℕ) := ⟨D.pos.ne'⟩
  haveI hgal : IsGalois ℚ ↥(cutOutField D chi) := SublemmaCutOutFieldGalois D chi
  have hFle : cutOutField D chi ≤ cyclotomicField' D := IntermediateField.lift_le _
  have hApos : (NumberField.discr ↥(cutOutField D chi)).natAbs ≠ 0 := by
    rw [Int.natAbs_ne_zero]
    exact NumberField.discr_ne_zero _
  haveI : NumberField ↥((cutOutField D chi).comap (cyclotomicField' D).val) :=
    NumberField.of_module_finite ℚ _
  have hdiscF' : (NumberField.discr ↥((cutOutField D chi).comap (cyclotomicField' D).val)).natAbs
      = (NumberField.discr ↥(cutOutField D chi)).natAbs := by
    rw [discr_comap (cyclotomicField' D) (cutOutField D chi) hFle]
  -- degrees
  have h3q : 3 * Module.finrank ↥((cutOutField D chi).comap (cyclotomicField' D).val)
      ↥(cyclotomicField' D) = (D : ℕ).totient := by
    have h1 : Module.finrank ℚ ↥(cyclotomicField' D) = (D : ℕ).totient :=
      IsCyclotomicExtension.Rat.finrank (K := ↥(cyclotomicField' D)) (k := (D : ℕ))
    have h2 : Module.finrank ℚ ↥((cutOutField D chi).comap (cyclotomicField' D).val) = 3 := by
      rw [LinearEquiv.finrank_eq
        (comapEquiv (cyclotomicField' D) (cutOutField D chi) hFle).toLinearEquiv]
      exact hdeg
    have h3 := Module.finrank_mul_finrank ℚ
      ↥((cutOutField D chi).comap (cyclotomicField' D).val) ↥(cyclotomicField' D)
    rw [h1, h2] at h3
    exact h3
  -- the tower divisibility
  have hAq : (NumberField.discr ↥(cutOutField D chi)).natAbs
      ^ (Module.finrank ↥((cutOutField D chi).comap (cyclotomicField' D).val)
          ↥(cyclotomicField' D))
      ∣ (NumberField.discr ↥(cyclotomicField' D)).natAbs := by
    have htow := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
      ↥((cutOutField D chi).comap (cyclotomicField' D).val)
      (𝓞 ↥((cutOutField D chi).comap (cyclotomicField' D).val))
      ↥(cyclotomicField' D) (𝓞 ↥(cyclotomicField' D))
    rw [hdiscF'] at htow
    exact ⟨_, by rw [htow]; ring⟩
  -- compare factorisations
  refine Nat.eq_of_factorization_eq hApos (by positivity) (fun p => ?_)
  by_cases hp : p.Prime
  · by_cases hpD : p ∣ (D : ℕ)
    · -- `p` is one of the (simple) prime factors of `D`
      obtain ⟨m, hm⟩ := hpD
      have hmpos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm; exact absurd hm D.pos.ne'
        · exact h
      set m' : ℕ+ := ⟨m, hmpos⟩ with hm'
      have hD : (D : ℕ) = p * (m' : ℕ) := hm
      have hm'm : (m' : ℕ) = m := rfl
      have hpm : ¬ p ∣ (m' : ℕ) := by
        intro hdvd
        obtain ⟨c, hc⟩ := hdvd
        have hpp : p * p ∣ (D : ℕ) := by
          refine ⟨c, ?_⟩
          rw [hD, hm'm] at *
          rw [hc]
          ring
        exact hp.not_isUnit (hsq p hpp)
      -- lower bound
      have hlow : p ^ 2 ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs :=
        sq_dvd_discr_of_dvd_discr ↥(cutOutField D chi) hdeg p hp
          (dvd_discr_cutOutField D chi p hp m' hD hpm hcond)
      -- upper bound
      have hup : ¬ p ^ 3 ∣ (NumberField.discr ↥(cutOutField D chi)).natAbs := by
        intro hc3
        refine not_pow_totient_dvd_discr D p hp m' hD hpm ?_
        refine dvd_trans ?_ hAq
        rw [← h3q, pow_mul]
        exact pow_dvd_pow_of_dvd hc3 _
      have hfp : (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p = 2 := by
        have h1 := (Nat.Prime.pow_dvd_iff_le_factorization hp hApos).mp hlow
        have h2 : ¬ (3 ≤ (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p) := by
          intro hc
          exact hup ((Nat.Prime.pow_dvd_iff_le_factorization hp hApos).mpr hc)
        omega
      have hD1 : (D : ℕ).factorization p = 1 := by
        have h1 : 1 ≤ (D : ℕ).factorization p :=
          (Nat.Prime.dvd_iff_one_le_factorization hp D.pos.ne').mp ⟨m, hm⟩
        have h2 := hsq.natFactorization_le_one p
        omega
      rw [hfp, Nat.factorization_pow]
      simp only [Finsupp.smul_apply, smul_eq_mul, hD1]
    · -- `p ∤ D`: unramified, so it divides neither side
      have h1 : (NumberField.discr ↥(cutOutField D chi)).natAbs.factorization p = 0 := by
        refine Nat.factorization_eq_zero_of_not_dvd ?_
        refine Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified
          ↥(cutOutField D chi) p hp ?_
        exact Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd D
          (cutOutField D chi) hFle p hp hpD
      have h2 : ((D : ℕ) ^ 2).factorization p = 0 := by
        rw [Nat.factorization_pow]
        simp only [Finsupp.smul_apply, smul_eq_mul]
        rw [Nat.factorization_eq_zero_of_not_dvd hpD]
      rw [h1, h2]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp,
      Nat.factorization_eq_zero_of_not_prime _ hp]

/-- **The discriminant of the cyclic cubic subfield of `ℚ(ζ_r)` is `r²`.** -/
theorem discr_cyclicCubicSubfield (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    [NumberField ↥(cyclicCubicSubfield r hr hr3)] :
    (NumberField.discr ↥(cyclicCubicSubfield r hr hr3)).natAbs = (r : ℕ) ^ 2 := by
  haveI : Fact ((r : ℕ).Prime) := ⟨hr⟩
  have hle : cyclicCubicSubfield r hr hr3 ≤ cyclotomicField' r := IntermediateField.lift_le _
  letI : Algebra ↥(cyclicCubicSubfield r hr hr3) ↥(cyclotomicField' r) :=
    (IntermediateField.inclusion hle).toAlgebra
  have hdeg : Module.finrank ℚ ↥(cyclicCubicSubfield r hr hr3) = 3 :=
    CyclicCubicSubfieldDegree r hr hr3
  have h := Workspace.ProofLemmas.TameDifferent.natAbs_discr_subfield (r : ℕ)
    ↥(cyclotomicField' r) ↥(cyclicCubicSubfield r hr hr3)
  rw [hdeg] at h
  simpa using h

end Workspace.ProofLemmas.CyclotomicTameDiscriminant

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Workspace.ProofLemmas.InertiaLocal
open Workspace.ProofLemmas.CyclotomicTameDiscriminant

set_option maxHeartbeats 1000000

/-!
# Ramification in a compositum of cyclic cubic fields

The inertia group at `r i` in `M = ⨆_j L_j` is disjoint from `Gal(M/L_i)` (because it fixes every
`L_j`, `j ≠ i`, all of which are unramified at `r i`), so it has at most `[L_i : ℚ] = 3` elements;
it is also a subgroup of the elementary abelian `Gal(M/ℚ)` of order `3^ℓ` and nontrivial because
`r i` divides `disc M`.  Hence `e(P / r i) = 3` — and therefore `M/F` is unramified at every finite
prime for any cubic subfield `F ⊆ M` of discriminant `D²`.
-/

namespace Workspace.ProofLemmas.CompositumRamification

section Ram

variable {ℓ : ℕ}

/-- Abstract version: an automorphism fixing every member of a family generating `N` is trivial. -/
theorem eq_one_of_fixes_family' {N : Type*} [Field N] [Algebra ℚ N]
    {ι : Type*} (E : ι → IntermediateField ℚ N) (hE : (⨆ i, E i) = ⊤)
    (σ : N ≃ₐ[ℚ] N) (hσ : ∀ i, σ ∈ (E i).fixingSubgroup) :
    σ = 1 := by
  have hle : (⨆ i, E i) ≤ IntermediateField.fixedField (Subgroup.closure ({σ} : Set (N ≃ₐ[ℚ] N))) := by
    refine iSup_le fun i => ?_
    intro x hx
    refine (IntermediateField.mem_fixedField_iff _ x).mpr ?_
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
        simp only [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mp (hσ i) x hx
    | one => rfl
    | mul a b _ _ ha hb => rw [AlgEquiv.mul_apply, hb, ha]
    | inv a _ ha =>
        have hinv : a⁻¹ (a x) = x := by simp
        rwa [ha] at hinv
  rw [hE] at hle
  ext x
  have hx : x ∈ IntermediateField.fixedField (Subgroup.closure ({σ} : Set (N ≃ₐ[ℚ] N))) :=
    hle (by trivial)
  simpa using
    (IntermediateField.mem_fixedField_iff _ x).mp hx σ (Subgroup.subset_closure rfl)

/-- **Ramification in a compositum of cubic fields** (abstract ambient field). -/
theorem ramificationIdx_eq_three (N : Type) [Field N] [NumberField N] [hgalN : IsGalois ℚ N]
    (E : Fin ℓ → IntermediateField ℚ N) (hE : (⨆ j, E j) = ⊤)
    (hdeg : ∀ j, Module.finrank ℚ ↥(E j) = 3)
    (hNdeg : Module.finrank ℚ N = 3 ^ ℓ)
    (i : Fin ℓ) (r : ℕ) (hr : r.Prime)
    (hother : ∀ j, j ≠ i →
      haveI : NumberField ↥(E j) := NumberField.of_module_finite ℚ ↥(E j)
      ¬ r ∣ (NumberField.discr ↥(E j)).natAbs)
    (hrN : r ∣ (NumberField.discr N).natAbs)
    (P : Ideal (𝓞 N)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {(r : ℤ)})]
    (hPne : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P = 3 := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  -- the inertia group is disjoint from the fixing subgroup of `E i`
  have hdisjoint : Disjoint (P.inertia (N ≃ₐ[ℚ] N)) ((E i).fixingSubgroup) := by
    rw [Subgroup.disjoint_def]
    intro σ hσI hσE
    refine eq_one_of_fixes_family' E hE σ ?_
    intro j
    by_cases hj : j = i
    · subst hj; exact hσE
    · exact inertia_le_fixingSubgroup_of_not_dvd_discr N (E j) r hr P hPne (hother j hj) hσI
  -- the index of that fixing subgroup is `3`
  have hindex : ((E i).fixingSubgroup).index = 3 := by
    have h1 := Subgroup.index_mul_card ((E i).fixingSubgroup)
    rw [IsGalois.card_fixingSubgroup_eq_finrank, IsGalois.card_aut_eq_finrank ℚ N] at h1
    have h2 : Module.finrank ℚ ↥(E i) * Module.finrank ↥(E i) N = Module.finrank ℚ N :=
      Module.finrank_mul_finrank ℚ _ N
    rw [hdeg i] at h2
    have h3 : 0 < Module.finrank ↥(E i) N := Module.finrank_pos
    rw [← h2] at h1
    exact Nat.eq_of_mul_eq_mul_right h3 h1
  -- hence `|I| ≤ 3`
  have hIle : Nat.card ↥(P.inertia (N ≃ₐ[ℚ] N)) ≤ 3 := by
    rw [← hindex]
    have hinj : Function.Injective
        (fun σ : ↥(P.inertia (N ≃ₐ[ℚ] N)) =>
          (QuotientGroup.mk (σ : N ≃ₐ[ℚ] N) : (N ≃ₐ[ℚ] N) ⧸ ((E i).fixingSubgroup))) := by
      rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ h
      have h1 : σ⁻¹ * τ ∈ (E i).fixingSubgroup := by
        simpa [QuotientGroup.eq] using h
      have h2 : σ⁻¹ * τ ∈ P.inertia (N ≃ₐ[ℚ] N) := mul_mem (inv_mem hσ) hτ
      have h3 : σ⁻¹ * τ = 1 := Subgroup.disjoint_def.mp hdisjoint h2 h1
      have h4 : σ = τ := by
        have h5 := congrArg (fun g => σ * g) h3
        simpa [← mul_assoc] using h5.symm
      exact Subtype.ext h4
    exact Nat.card_le_card_of_injective _ hinj
  have hcardI := card_inertia_eq_ramificationIdx_int N (Ideal.span {(r : ℤ)}) hrbot P hPne
  have hdvd : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ∣ 3 ^ ℓ := by
    rw [← hcardI, ← hNdeg, ← IsGalois.card_aut_eq_finrank ℚ N]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ≠ 1 := by
    intro hcon
    refine (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified N r hr
      ?_) hrN
    intro Q hQ
    obtain ⟨hQp, hQl⟩ := hQ
    haveI := hQp
    haveI := hQl
    have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hrbot Q
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) Q (N ≃ₐ[ℚ] N),
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) P (N ≃ₐ[ℚ] N)]
    exact hcon
  have hle3 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) P ≤ 3 := by
    rw [← hcardI]; exact hIle
  rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd with ⟨k, hk, hkeq⟩
  match k, hk, hkeq with
  | 0, _, hkeq => exact absurd (by simpa using hkeq) hne1
  | 1, _, hkeq => simpa using hkeq
  | (n + 2), _, hkeq =>
      exfalso
      rw [hkeq] at hle3
      have : (9 : ℕ) ≤ 3 ^ (n + 2) := by
        calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ (n + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega

end Ram

section Concrete

/-- The copies inside `M` of a family whose compositum is `M` generate `M`. -/
theorem iSup_comap_eq_top {ι : Type*} (E : ι → IntermediateField ℚ ℂ)
    (M : IntermediateField ℚ ℂ) (hM : M = ⨆ i, E i) :
    (⨆ i, (E i).comap M.val) = ⊤ := by
  refine eq_top_iff.mpr ?_
  intro x _
  have hle : ∀ i, E i ≤ M := fun i => by rw [hM]; exact le_iSup E i
  have hsub0 : (⨆ i, E i) ≤ IntermediateField.lift (⨆ i, (E i).comap M.val) := by
    refine iSup_le fun i => ?_
    intro y hy
    refine ⟨⟨y, hle i hy⟩, ?_, rfl⟩
    exact le_iSup (fun i => (E i).comap M.val) i (show (⟨y, hle i hy⟩ : ↥M) ∈ (E i).comap M.val
      from hy)
  have hsub : M ≤ IntermediateField.lift (⨆ i, (E i).comap M.val) := hM.le.trans hsub0
  obtain ⟨z, hz, hzx⟩ := hsub x.2
  have hzex : z = x := Subtype.ext hzx
  rwa [← hzex]

/-- **`e = 3` at each `r i` in the compositum of the cyclic cubic fields.** -/
theorem ramificationIdx_compositum_eq_three (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ j, cyclicCubicSubfield (r j) (hp j) (hm j)) [NumberField ↥M]
    (hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ)
    (i : Fin ℓ)
    (P : Ideal (𝓞 ↥M)) [hPp : P.IsPrime] [hPl : P.LiesOver (Ideal.span {((r i : ℕ) : ℤ)})]
    (hPne : P ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {((r i : ℕ) : ℤ)}) P = 3 := by
  haveI hfdL : ∀ j, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) :=
    fun j => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r j) (hp j) (hm j)]; norm_num)
  haveI hnfL : ∀ j, NumberField ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) := fun j => ⟨⟩
  haveI hgalL : ∀ j, IsGalois ℚ ↥(cyclicCubicSubfield (r j) (hp j) (hm j)) :=
    fun j => SublemmaCyclicCubicSubfieldNormal (r j) (hp j) (hm j)
  haveI hgalM : IsGalois ℚ ↥M := by
    rw [hM]; exact (SublemmaCompositumGalois _).1
  have hle : ∀ j, cyclicCubicSubfield (r j) (hp j) (hm j) ≤ M := fun j => by
    rw [hM]; exact le_iSup (fun j => cyclicCubicSubfield (r j) (hp j) (hm j)) j
  haveI hnfE : ∀ j, NumberField ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val) :=
    fun j => NumberField.of_module_finite ℚ _
  have hdiscE : ∀ j, (NumberField.discr
      ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)).natAbs = (r j : ℕ) ^ 2 := by
    intro j
    rw [discr_comap M (cyclicCubicSubfield (r j) (hp j) (hm j)) (hle j)]
    exact discr_cyclicCubicSubfield (r j) (hp j) (hm j)
  have hdegE : ∀ j, Module.finrank ℚ
      ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val) = 3 := by
    intro j
    rw [LinearEquiv.finrank_eq
      (comapEquiv M (cyclicCubicSubfield (r j) (hp j) (hm j)) (hle j)).toLinearEquiv]
    exact CyclicCubicSubfieldDegree (r j) (hp j) (hm j)
  refine ramificationIdx_eq_three ↥M (fun j => (cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)
    (iSup_comap_eq_top _ M hM) hdegE ?_ i (r i : ℕ) (hp i) ?_ ?_ P hPne
  · exact hMdeg
  · intro j hj
    show ¬ (r i : ℕ) ∣
      (NumberField.discr ↥((cyclicCubicSubfield (r j) (hp j) (hm j)).comap M.val)).natAbs
    rw [hdiscE j]
    intro hdvd
    have hprime := (Nat.prime_dvd_prime_iff_eq (hp i) (hp j)).mp ((hp i).dvd_of_dvd_pow hdvd)
    exact hj (hdist (by exact_mod_cast hprime.symm))
  · have h1 : (NumberField.discr ↥((cyclicCubicSubfield (r i) (hp i) (hm i)).comap M.val))
        ∣ NumberField.discr ↥M := NumberField.discr_dvd_discr _ _
    have h2 : (NumberField.discr
        ↥((cyclicCubicSubfield (r i) (hp i) (hm i)).comap M.val)).natAbs
        ∣ (NumberField.discr ↥M).natAbs := Int.natAbs_dvd_natAbs.mpr h1
    rw [hdiscE i] at h2
    exact dvd_trans (dvd_pow_self _ (by norm_num)) h2

end Concrete

/-- In a cubic Galois field, every prime dividing the discriminant is totally ramified. -/
theorem ramificationIdx_eq_three_of_dvd_discr (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (hdeg : Module.finrank ℚ F = 3) (r : ℕ) (hr : r.Prime)
    (hrA : r ∣ (NumberField.discr F).natAbs)
    (Q : Ideal (𝓞 F)) [hQp : Q.IsPrime] [hQl : Q.LiesOver (Ideal.span {(r : ℤ)})] (hQne : Q ≠ ⊥) :
    Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q = 3 := by
  have hrbot : (Ideal.span {(r : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hr.ne_zero
  haveI : (Ideal.span {(r : ℤ)}).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hr.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hr
  haveI : (Ideal.span {(r : ℤ)}).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hrbot
  have hcardI := card_inertia_eq_ramificationIdx_int F (Ideal.span {(r : ℤ)}) hrbot Q hQne
  have hdvd : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ∣ 3 := by
    rw [← hcardI, ← hdeg, ← IsGalois.card_aut_eq_finrank ℚ F]
    exact Subgroup.card_subgroup_dvd_card _
  have hne1 : Ideal.ramificationIdx (Ideal.span {(r : ℤ)}) Q ≠ 1 := by
    intro hcon
    refine (Workspace.ProofLemmas.UnramifiedOutsideLevel.not_dvd_discr_of_unramified F r hr
      ?_) hrA
    intro R hR
    obtain ⟨hRp, hRl⟩ := hR
    haveI := hRp
    haveI := hRl
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) R (F ≃ₐ[ℚ] F),
      Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(r : ℤ)}) Q (F ≃ₐ[ℚ] F)]
    exact hcon
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd h hne1
  · exact h

/-- Every nonzero prime of `ℤ` is `(r)` for a rational prime `r`. -/
theorem exists_prime_span (I : Ideal ℤ) (hIp : I.IsPrime) (hIne : I ≠ ⊥) :
    ∃ r : ℕ, r.Prime ∧ I = Ideal.span {(r : ℤ)} := by
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I)
  rw [ha] at hIp hIne ⊢
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hIne
    simp at hIne
  have hprime : Prime a := (Ideal.span_singleton_prime ha0).mp hIp
  refine ⟨a.natAbs, ?_, ?_⟩
  · rw [Int.prime_iff_natAbs_prime] at hprime
    exact hprime
  · rcases Int.natAbs_eq a with h | h
    · rw [← h]
    · rw [← neg_neg (a.natAbs : ℤ), ← h]
      exact (Ideal.span_singleton_neg a).symm

open Workspace.Types.SplittingRamification in
/-- **`M/F` is unramified at every finite prime**, for `F` a cubic Galois field of discriminant
`D²` inside the compositum `M`. -/
theorem unramified_compositum (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ) (hM : M = ⨆ j, cyclicCubicSubfield (r j) (hp j) (hm j))
    [NumberField ↥M] (hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ)
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F] [Algebra F ↥M] [IsScalarTower ℚ F ↥M]
    (hFdeg : Module.finrank ℚ F = 3)
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (hFdisc : (NumberField.discr F).natAbs = (D : ℕ) ^ 2)
    (hMD : M ≤ cyclotomicField' D) :
    UnramifiedAtFinitePrimes F ↥M := by
  intro p hpne hpprime P hP
  obtain ⟨hPp, hPl⟩ := hP
  haveI := hPp
  haveI := hPl
  haveI : FiniteDimensional F ↥M := Module.Finite.right ℚ F ↥M
  haveI : Module.Finite (𝓞 F) (𝓞 ↥M) := IsIntegralClosure.finite (𝓞 F) F ↥M (𝓞 ↥M)
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hpne P
  haveI hup : (p.under ℤ).IsPrime := Ideal.IsPrime.under _ p
  have hupne : p.under ℤ ≠ ⊥ := by
    intro hcon
    exact hpne (by simpa using Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (S := 𝓞 F) (I := p) hcon)
  obtain ⟨q, hq, hqspan⟩ := exists_prime_span (p.under ℤ) hup hupne
  haveI hpq : p.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hqspan.symm⟩
  haveI hPq : P.LiesOver (Ideal.span {(q : ℤ)}) := by
    constructor
    rw [← hqspan, ← Ideal.under_under (A := ℤ) (B := 𝓞 F) (C := 𝓞 ↥M)]
    exact congrArg (Ideal.under ℤ) hPl.over
  have hqbot : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  have hinjF : Function.Injective (algebraMap (𝓞 F) (𝓞 ↥M)) :=
    FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 ↥M)
  have hinjZ : Function.Injective (algebraMap ℤ (𝓞 ↥M)) :=
    FaithfulSMul.algebraMap_injective ℤ (𝓞 ↥M)
  have htower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p * Ideal.ramificationIdx p P := by
    refine Ideal.ramificationIdx_algebra_tower (R := ℤ) (S := 𝓞 F) (T := 𝓞 ↥M) ?_ ?_ ?_
    · exact (Ideal.map_eq_bot_iff_of_injective hinjF).not.mpr hpne
    · exact (Ideal.map_eq_bot_iff_of_injective hinjZ).not.mpr hqbot
    · exact Ideal.map_le_of_le_comap (le_of_eq hPl.over)
  by_cases hqD : q ∣ (D : ℕ)
  · -- `q` is one of the `r i`
    have hex : ∃ i, (r i : ℕ) = q := by
      rw [hD] at hqD
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hq.prime _).mp hqD
      exact ⟨i, ((Nat.prime_dvd_prime_iff_eq hq (hp i)).mp hi).symm⟩
    obtain ⟨i, hi⟩ := hex
    have hMram : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 3 := by
      subst hi
      exact ramificationIdx_compositum_eq_three ℓ hℓ r hp hm hdist M hM hMdeg i P hPne
    have hFram : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p = 3 := by
      refine ramificationIdx_eq_three_of_dvd_discr F hFdeg q hq ?_ p hpne
      rw [hFdisc]
      exact dvd_trans hqD (dvd_pow_self _ (by norm_num))
    rw [hMram, hFram] at htower
    omega
  · -- `q` is unramified in `M`
    have hun := Workspace.ProofLemmas.UnramifiedOutsideLevel.unramified_of_not_dvd D M hMD q hq hqD
    have h1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 :=
      hun P ⟨hPp, hPq⟩
    rw [h1] at htower
    have h2 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) p * Ideal.ramificationIdx p P = 1 :=
      htower.symm
    exact (Nat.eq_one_of_mul_eq_one_left h2)

end Workspace.ProofLemmas.CompositumRamification

set_option maxHeartbeats 1000000

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

theorem Prop32CyclotomicBase_totally_real (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M] :
    NumberField.IsTotallyReal ↥M := by
  subst hM
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  haveI hnf : ∀ i, NumberField ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := fun i => ⟨⟩
  haveI htr : ∀ i, NumberField.IsTotallyReal ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => CyclicCubicSubfieldTotallyReal (r i) (hp i) (hm i)
  exact SublemmaCompositumTotallyReal (fun i => cyclicCubicSubfield (r i) (hp i) (hm i))

theorem Prop32CyclotomicBase_degree (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :
    Module.finrank ℚ ↥M = 3 ^ ℓ := by
  subst hM
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  haveI hgi : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => SublemmaCyclicCubicSubfieldNormal (r i) (hp i) (hm i)
  obtain ⟨hindep, hdisj⟩ := SublemmaLinearDisjointFromDisjointRamification hℓ r hp hm hdist
  rw [SublemmaDegreeCompositumLinearlyDisjoint
    (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) hindep hdisj]
  simp only [CyclicCubicSubfieldDegree]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem Prop32CyclotomicBase_galois_elementary_abelian (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :
    (∀ σ τ : ↥M ≃ₐ[ℚ] ↥M, σ * τ = τ * σ) ∧ (∀ σ : ↥M ≃ₐ[ℚ] ↥M, σ ^ 3 = 1) := by
  subst hM
  haveI hgi : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => SublemmaCyclicCubicSubfieldNormal (r i) (hp i) (hm i)
  haveI hfd : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => FiniteDimensional.of_finrank_pos
      (by rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num)
  obtain ⟨hindep, hdisj⟩ := SublemmaLinearDisjointFromDisjointRamification hℓ r hp hm hdist
  letI algi : ∀ i, Algebra ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => (IntermediateField.inclusion
      (le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i)).toRingHom.toAlgebra
  haveI towi : ∀ i, IsScalarTower ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i))
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    fun i => IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion
        (le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i)).commutes x).symm)
  obtain ⟨e, -⟩ := SublemmaGaloisGroupCompositumProduct
    (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) hindep hdisj
  have hcard : ∀ i, Nat.card (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) = 3 := by
    intro i
    rw [IsGalois.card_aut_eq_finrank, CyclicCubicSubfieldDegree]
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI hcyc : ∀ i, IsCyclic (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
      ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) :=
    fun i => isCyclic_of_prime_card (hcard i)
  refine ⟨fun σ τ => ?_, fun σ => ?_⟩
  · apply e.injective
    rw [map_mul, map_mul]
    funext i
    simp only [Pi.mul_apply]
    letI : CommGroup (↥(cyclicCubicSubfield (r i) (hp i) (hm i)) ≃ₐ[ℚ]
        ↥(cyclicCubicSubfield (r i) (hp i) (hm i))) := IsCyclic.commGroup
    exact mul_comm _ _
  · apply e.injective
    rw [map_pow, map_one]
    funext i
    simp only [Pi.pow_apply, Pi.one_apply]
    rw [← hcard i]
    exact pow_card_eq_one'

theorem Prop32CyclotomicBase_relative_degree (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M)
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Module.finrank ↥F ↥M = 3 ^ (ℓ - 1) := by
  have hMdeg : Module.finrank ℚ ↥M = 3 ^ ℓ :=
    Prop32CyclotomicBase_degree ℓ hℓ r hp hm hdist M hM
  have hFdeg : Module.finrank ℚ ↥F = 3 := by
    rw [hFcut]; exact SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  haveI hfdM : FiniteDimensional ℚ ↥M :=
    FiniteDimensional.of_finrank_pos (by rw [hMdeg]; positivity)
  haveI hfdF : FiniteDimensional ℚ ↥F :=
    FiniteDimensional.of_finrank_pos (by rw [hFdeg]; norm_num)
  haveI : NumberField ↥F := ⟨⟩
  have htower := SublemmaTowerDegree F M hFM
  rw [hMdeg, hFdeg] at htower
  have h3 : (3 : ℕ) ^ (ℓ - 1) * 3 = 3 ^ ℓ := by rw [← pow_succ, Nat.sub_add_cancel hℓ]
  rw [← h3] at htower
  exact (Nat.eq_of_mul_eq_mul_right (by norm_num) htower).symm

theorem Prop32CyclotomicBase_discriminant (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (F : IntermediateField ℚ ℂ) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hchi_cond : DirichletCharacter.conductor chi = (D : ℕ))
    (hFcut : F = cutOutField D chi) :
    (NumberField.discr ↥F).natAbs = (∏ i, (r i : ℕ)) ^ 2 := by
  -- Proved from the tame conductor–discriminant computation in
  -- `Workspace.ProofLemmas.CyclotomicTameDiscriminant` (inertia + the conductor of `chi`).
  subst hFcut
  have hsq : Squarefree (D : ℕ) := by
    rw [hD]
    refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ (fun i _ => (hp i).squarefree)
    intro i _ j _ hij
    show IsRelPrime ((r i : ℕ)) ((r j : ℕ))
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hdist (by exact_mod_cast h)))
  have hdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3 :=
    SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  rw [Workspace.ProofLemmas.CyclotomicTameDiscriminant.natAbs_discr_cutOutField D chi hsq
    hchi_cond hdeg, hD]

theorem Prop32CyclotomicBase_unramified (ℓ : ℕ) (hℓ : 1 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M]
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hchi_cond : DirichletCharacter.conductor chi = (D : ℕ))
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    EverywhereUnramified ↥F ↥M := by
  subst hM
  subst hFcut
  -- `M/F` is unramified at the finite primes by the inertia computation of
  -- `Workspace.ProofLemmas.CompositumRamification` (`e = 3` at each `r i` both in `M` and in `F`).
  have hDF : (NumberField.discr ↥(cutOutField D chi)).natAbs = (D : ℕ) ^ 2 := by
    rw [Prop32CyclotomicBase_discriminant ℓ hℓ r hp hm hdist (cutOutField D chi) D hD chi
      hchi_ord hchi_cond rfl, hD]
  haveI hgalF : IsGalois ℚ ↥(cutOutField D chi) := SublemmaCutOutFieldGalois D chi
  have hFdeg : Module.finrank ℚ ↥(cutOutField D chi) = 3 :=
    SublemmaCutOutFieldDegreeThree D chi 3 hchi_ord
  have hMdeg : Module.finrank ℚ ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) = 3 ^ ℓ :=
    Prop32CyclotomicBase_degree ℓ hℓ r hp hm hdist _ rfl
  have hMD : (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) ≤ cyclotomicField' D := by
    refine iSup_le fun i => ?_
    refine (CyclicCubicSubfieldConductor (r i) (hp i) (hm i) D).mpr ?_
    rw [hD]
    exact Finset.dvd_prod_of_mem (fun i => (r i : ℕ)) (Finset.mem_univ i)
  have hfin : UnramifiedAtFinitePrimes ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Workspace.ProofLemmas.CompositumRamification.unramified_compositum ℓ hℓ r hp hm hdist
      _ rfl hMdeg ↥(cutOutField D chi) hFdeg D hD hDF hMD
  have hMtr : NumberField.IsTotallyReal ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Prop32CyclotomicBase_totally_real ℓ hℓ r hp hm hdist _ rfl
  have hFtr : NumberField.IsTotallyReal ↥(cutOutField D chi) :=
    SublemmaTotallyRealSubfield (cutOutField D chi)
      (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) hFM hMtr
  haveI : FiniteDimensional ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    Module.Finite.right ℚ ↥(cutOutField D chi) ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
  haveI := hFtr
  haveI := hMtr
  have hinf : IsUnramifiedAtInfinitePlaces ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) :=
    SublemmaInfinitePlacesUnramifiedTotallyReal ↥(cutOutField D chi)
      ↥(⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
  exact ⟨hfin, hinf⟩

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields

/-- Classification: a finite group `G` that is commutative and has exponent dividing `3`,
with `Nat.card G = 3 ^ n`, is isomorphic to `(Fin n → Multiplicative (ZMod 3))`.
This is fully proved (no `sorry`). -/
private theorem classify {G : Type*} [Group G] [Finite G] (n : ℕ)
    (hcomm : ∀ a b : G, a * b = b * a) (hexp : ∀ a : G, a ^ 3 = 1)
    (hcard : Nat.card G = 3 ^ n) :
    Nonempty (G ≃* (Fin n → Multiplicative (ZMod 3))) := by
  letI : CommGroup G := { mul_comm := hcomm }
  have h3 : ∀ x : Additive G, (3 : ℕ) • x = 0 := by
    intro x
    have hx : (Additive.toMul x) ^ 3 = 1 := hexp _
    have := congrArg Additive.ofMul hx
    simpa [ofMul_pow] using this
  letI : Module (ZMod 3) (Additive G) := AddCommGroup.zmodModule h3
  haveI : Finite (Additive G) := inferInstanceAs (Finite G)
  haveI : Module.Finite (ZMod 3) (Additive G) := Module.Finite.of_finite
  haveI : FiniteDimensional (ZMod 3) (Additive G) := inferInstance
  haveI : Fintype (Additive G) := Fintype.ofFinite _
  have hpow : Fintype.card (Additive G)
      = (Fintype.card (ZMod 3)) ^ Module.finrank (ZMod 3) (Additive G) :=
    Module.card_eq_pow_finrank
  have hcardA : Fintype.card (Additive G) = 3 ^ n := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  have hfr : Module.finrank (ZMod 3) (Additive G) = n := by
    have h33 : Fintype.card (ZMod 3) = 3 := by simp [ZMod.card]
    rw [h33, hcardA] at hpow
    exact Nat.pow_right_injective (by norm_num) hpow.symm
  let b := Module.finBasis (ZMod 3) (Additive G)
  let e : Additive G ≃ₗ[ZMod 3] (Fin (Module.finrank (ZMod 3) (Additive G)) → ZMod 3) :=
    b.equivFun
  let e2 : Additive G ≃ₗ[ZMod 3] (Fin n → ZMod 3) :=
    e.trans (LinearEquiv.funCongrLeft (ZMod 3) (ZMod 3) (finCongr hfr).symm)
  have eadd : Additive G ≃+ (Fin n → ZMod 3) := e2.toAddEquiv
  have emul : Multiplicative (Additive G) ≃* Multiplicative (Fin n → ZMod 3) :=
    AddEquiv.toMultiplicative eadd
  refine ⟨?_⟩
  refine (MulEquiv.multiplicativeAdditive G).symm.trans (emul.trans ?_)
  exact MulEquiv.funMultiplicative _ _

/-- **Prop 3.8, Step 1 — `Gal(M/F) ≅ (ℤ/3)^{ℓ-1}`.** -/
theorem SublemmaGalMFElementaryAbelianIso (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (r : Fin ℓ → ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1) (hdist : Function.Injective r)
    (M : IntermediateField ℚ ℂ)
    (hM : M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i)) [NumberField ↥M]
    (F : IntermediateField ℚ ℂ) (hFM : F ≤ M) [NumberField ↥F]
    (D : ℕ+) (hD : (D : ℕ) = ∏ i, (r i : ℕ))
    (chi : DirichletCharacter ℂ (D : ℕ)) (hchi_ord : orderOf chi = 3)
    (hFcut : F = cutOutField D chi)
    [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M] :
    Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) := by
  -- Relative degree [M:F] = 3^{ℓ-1}.
  have hdeg := Prop32CyclotomicBase_relative_degree ℓ (by omega) r hp hm hdist M hM F hFM D hD
    chi hchi_ord hFcut
  -- Gal(M/ℚ) elementary abelian: commutative and every element cubes to 1.
  have hea := Prop32CyclotomicBase_galois_elementary_abelian ℓ (by omega) r hp hm hdist M hM
  haveI hfin : FiniteDimensional ↥F ↥M := FiniteDimensional.right ℚ ↥F ↥M
  -- `Gal(M/F)` embeds into `Gal(M/ℚ)` via restriction of scalars; the embedding is
  -- multiplicative, so it transports commutativity and exponent 3 from `Gal(M/ℚ)`.
  have hcomm : ∀ σ τ : (↥M ≃ₐ[↥F] ↥M), σ * τ = τ * σ := by
    intro σ τ
    apply AlgEquiv.restrictScalars_injective ℚ
    have hmul : ∀ a b : (↥M ≃ₐ[↥F] ↥M),
        AlgEquiv.restrictScalars ℚ (a * b)
          = AlgEquiv.restrictScalars ℚ a * AlgEquiv.restrictScalars ℚ b := by
      intro a b; rfl
    rw [hmul, hmul]
    exact hea.1 _ _
  have hexp : ∀ σ : (↥M ≃ₐ[↥F] ↥M), σ ^ 3 = 1 := by
    intro σ
    apply AlgEquiv.restrictScalars_injective ℚ
    have hpw : AlgEquiv.restrictScalars ℚ (σ ^ 3)
        = (AlgEquiv.restrictScalars ℚ σ) ^ 3 := by rfl
    have hone : AlgEquiv.restrictScalars ℚ (1 : ↥M ≃ₐ[↥F] ↥M) = 1 := rfl
    rw [hpw, hone]
    exact hea.2 _
  -- The cardinality of the automorphism group equals the degree, PROVIDED M/F is Galois.
  -- `M/F` is Galois because `M/ℚ` is Galois (a compositum of the Galois cyclic cubic
  -- subfields `cyclicCubicSubfield (r i)`) and `F` is intermediate, so `IsGalois ℚ M`
  -- transfers to `IsGalois F M` via `tower_top`.
  haveI hGal : IsGalois ↥F ↥M := by
    -- Each `cyclicCubicSubfield (r i)` is Galois over `ℚ`: it is the fixed field of a
    -- normal subgroup (the comap of a subgroup of the *abelian* group `(ℤ/rℤ)ˣ`) of the
    -- Galois group of the cyclotomic field `ℚ(ζ_{r i})`.
    have hnormal : ∀ i, Normal ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
      intro i
      set H := (((powMonoidHom 3 : (ZMod (r i : ℕ))ˣ →* (ZMod (r i : ℕ))ˣ).range).comap
        (galToUnits (r i)).toMonoidHom) with hH
      haveI hg : IsGalois ℚ ↥(IntermediateField.fixedField H) :=
        IsGalois.of_fixedField_normal_subgroup _
      have e : ↥(IntermediateField.fixedField H) ≃ₐ[ℚ]
          ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) :=
        IntermediateField.liftAlgEquiv (IntermediateField.fixedField H)
      exact (IsGalois.of_algEquiv e).to_normal
    haveI hnormal' : ∀ i, Normal ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := hnormal
    have hnorm : Normal ℚ ↥M := by
      rw [hM]
      exact IntermediateField.normal_iSup ℚ ℂ
        (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) (h := hnormal')
    haveI : Normal ℚ ↥M := hnorm
    haveI hGalQM : IsGalois ℚ ↥M := isGalois_iff.mpr ⟨inferInstance, hnorm⟩
    exact IsGalois.tower_top_of_isGalois ℚ ↥F ↥M
  have hcard : Nat.card (↥M ≃ₐ[↥F] ↥M) = 3 ^ (ℓ - 1) := by
    rw [IsGalois.card_aut_eq_finrank ↥F ↥M, hdeg]
  exact classify (ℓ - 1) hcomm hexp hcard

open scoped NumberField

open Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000

namespace SublemmaUnramifiedTransportAux

variable {R S S₁ : Type*} [CommRing R] [CommRing S] [CommRing S₁] [Algebra R S] [Algebra R S₁]

/-- `Ideal.map φ` composed with `Ideal.map φ.symm` is the identity. -/
lemma map_symm_map (φ : S ≃ₐ[R] S₁) (Q : Ideal S₁) :
    Ideal.map φ (Ideal.map φ.symm Q) = Q := by
  show Ideal.map (φ : S →+* S₁) (Ideal.map (φ.symm : S₁ →+* S) Q) = Q
  rw [Ideal.map_map]
  have h : ((φ : S →+* S₁).comp (φ.symm : S₁ →+* S)) = RingHom.id S₁ := by ext x; simp
  rw [h, Ideal.map_id]

/-- The set of primes over `p` in `S₁` is the image under `Ideal.map φ` of those in `S`. -/
lemma primesOver_image (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    p.primesOver S₁ = Ideal.map φ '' p.primesOver S := by
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQp, hQl⟩
    refine ⟨Ideal.map φ.symm Q, ⟨?_, ?_⟩, map_symm_map φ Q⟩
    · haveI := hQp; exact Ideal.map_isPrime_of_equiv φ.symm
    · haveI := hQl; exact Ideal.map_equiv_liesOver Q p φ.symm
  · rintro ⟨P, ⟨hPp, hPl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · haveI := hPp; exact Ideal.map_isPrime_of_equiv φ
    · haveI := hPl; exact Ideal.map_equiv_liesOver P p φ

/-- Ramification index over `p` being `1` transfers along an algebra equivalence. -/
lemma ram_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ]
  exact h P hPmem

/-- Unramifiedness at infinite places transfers along an algebra equivalence over `F`. -/
lemma inf_transfer {F E Fj : Type*} [Field F] [Field E] [Field Fj]
    [Algebra F E] [Algebra F Fj] (e : E ≃ₐ[F] Fj)
    (hE : IsUnramifiedAtInfinitePlaces F E) : IsUnramifiedAtInfinitePlaces F Fj := by
  refine ⟨fun u => ?_⟩
  have hv := hE.isUnramified (u.comap (e : E →+* Fj))
  have h2 := hv.comap_algHom (e.symm : Fj →ₐ[F] E)
  have hcomp : (u.comap (e : E →+* Fj)).comap ((e.symm : Fj →ₐ[F] E) : Fj →+* E) = u := by
    rw [← NumberField.InfinitePlace.comap_comp]
    convert NumberField.InfinitePlace.comap_id u using 2
    ext x; simp
  rwa [hcomp] at h2

end SublemmaUnramifiedTransportAux

theorem SublemmaUnramifiedTransport
    {F : Type*} [Field F] [NumberField F]
    {A B : Type*} [Field A] [Field B] [NumberField A] [NumberField B]
    [Algebra F A] [Algebra F B]
    [IsScalarTower ℚ F A] [IsScalarTower ℚ F B]
    (g : A ≃ₐ[F] B) :
    EverywhereUnramified F A ↔ EverywhereUnramified F B := by
  set φ : 𝓞 A ≃ₐ[𝓞 F] 𝓞 B := NumberField.RingOfIntegers.mapAlgEquiv g with hφ
  constructor
  · rintro ⟨hfin, hinf⟩
    refine ⟨?_, ?_⟩
    · intro p hp hpp Q hQ
      exact SublemmaUnramifiedTransportAux.ram_transfer φ p (hfin p hp hpp) Q hQ
    · exact SublemmaUnramifiedTransportAux.inf_transfer g hinf
  · rintro ⟨hfin, hinf⟩
    refine ⟨?_, ?_⟩
    · intro p hp hpp P hP
      exact SublemmaUnramifiedTransportAux.ram_transfer φ.symm p (hfin p hp hpp) P hP
    · exact SublemmaUnramifiedTransportAux.inf_transfer g.symm hinf

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem SublemmaMPrimeRealization (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (F M : IntermediateField ℚ ℂ) [NumberField ↥F] [NumberField ↥M]
    (hFM : F ≤ M) [Algebra ↥F ↥M] [IsScalarTower ℚ ↥F ↥M]
    [FiniteDimensional ↥F ↥M] [IsGalois ↥F ↥M]
    (hunr : EverywhereUnramified ↥F ↥M)
    (hiso : Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3)))) :
    ∃ M' : IntermediateField ↥F (AlgebraicClosure ↥F),
      IsFiniteUnramifiedProPExt 3 ↥F M' ∧
      Nonempty ((M' ≃ₐ[↥F] M') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3)) := by
  haveI : Algebra.IsAlgebraic ↥F ↥M := inferInstance
  -- Embed M into AlgebraicClosure F
  let f : ↥M →ₐ[↥F] AlgebraicClosure ↥F := IsAlgClosed.lift
  have hf : Function.Injective f := f.toRingHom.injective
  let M' : IntermediateField ↥F (AlgebraicClosure ↥F) := f.fieldRange
  let e : ↥M ≃ₐ[↥F] ↥M' := AlgEquiv.ofInjective f hf
  -- Transport structure along e
  haveI hfd : FiniteDimensional ↥F ↥M' := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI hst : IsScalarTower ℚ ↥F ↥M' := inferInstance
  haveI hnf : NumberField ↥M' := NumberField.of_module_finite (K := ↥F) (L := ↥M')
  refine ⟨M', ⟨hfd, ?_, ?_, ?_⟩, ?_⟩
  · -- IsGalois
    exact (AlgEquiv.transfer_galois e).mp inferInstance
  · -- EverywhereUnramified, via SublemmaUnramifiedTransport
    exact (SublemmaUnramifiedTransport e).mp hunr
  · -- IsPGroup 3 of the Galois group of M'
    have hp : IsPGroup 3 (Fin (ℓ - 1) → Multiplicative (ZMod 3)) := by
      apply IsPGroup.of_card (n := ℓ - 1)
      simp [Nat.card_eq_fintype_card, Fintype.card_pi]
    have hpM : IsPGroup 3 (↥M ≃ₐ[↥F] ↥M) := hp.of_equiv hiso.some.symm
    exact hpM.of_equiv (AlgEquiv.autCongr e)
  · -- final MulEquiv onto Multiplicative (Fin (ℓ-1) → ZMod 3)
    exact ⟨((AlgEquiv.autCongr e).symm.trans hiso.some).trans
      (MulEquiv.funMultiplicative (Fin (ℓ - 1)) (ZMod 3)).symm⟩

open scoped NumberField
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000

theorem Prop38BaseFieldConstruction :
    ∀ (ℓ : ℕ), 2 ≤ ℓ →
      ∃ (r : Fin ℓ → ℕ+),
        StrictMono r ∧
        ∃ (hp : ∀ i, (r i : ℕ).Prime) (hm : ∀ i, (r i : ℕ) % 3 = 1),
          (∀ p : ℕ, p.Prime → p % 3 = 1 → (¬ ∃ i, (r i : ℕ) = p) → ∀ i, (r i : ℕ) < p) ∧
          ∃ (D : ℕ+), (D : ℕ) = ∏ i, (r i : ℕ) ∧
            ∃ (chi : DirichletCharacter ℂ (D : ℕ)),
              orderOf chi = 3 ∧
              DirichletCharacter.conductor chi = (D : ℕ) ∧
              ∃ (F M : IntermediateField ℚ ℂ),
                F = cutOutField D chi ∧
                M = ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) ∧
                F ≤ M ∧
                ∃ (nfF : NumberField ↥F) (nfM : NumberField ↥M) (algFM : Algebra ↥F ↥M),
                  letI := nfF
                  letI := nfM
                  letI := algFM
                  IsScalarTower ℚ ↥F ↥M ∧
                  NumberField.IsTotallyReal ↥F ∧
                  IsGalois ℚ ↥F ∧
                  Module.finrank ℚ ↥F = 3 ∧
                  (¬ ∃ x : ↥F, IsPrimitiveRoot x 3) ∧
                  EverywhereUnramified ↥F ↥M ∧
                  Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) ∧
                  (NumberField.discr ↥F).natAbs = (D : ℕ) ^ 2 ∧
                  ∃ (M' : IntermediateField ↥F (AlgebraicClosure ↥F)),
                    IsFiniteUnramifiedProPExt 3 ↥F M' ∧
                    Nonempty ((M' ≃ₐ[↥F] M') ≃*
                      Multiplicative (Fin (ℓ - 1) → ZMod 3)) := by
  intro ℓ hℓ
  -- Step 1: primes and modulus D
  obtain ⟨r, hmono, hp, hm, hmin⟩ := SublemmaFirstEllPrimes ℓ
  have hdist : Function.Injective r := hmono.injective
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (r i : ℕ) (r j : ℕ) := by
    intro i j hij
    have hne : (r i : ℕ) ≠ (r j : ℕ) := fun h => hij (hdist (PNat.coe_injective h))
    exact (Nat.coprime_primes (hp i) (hp j)).mpr hne
  set D : ℕ+ := ∏ i, r i with hDdef
  have hDcoe : (D : ℕ) = ∏ i, (r i : ℕ) := by rw [hDdef]; push_cast; rfl
  have hD1 : 1 < (D : ℕ) := by
    rw [hDcoe]
    have hi0 : (r (⟨0, by omega⟩ : Fin ℓ) : ℕ) ∣ ∏ i, (r i : ℕ) :=
      Finset.dvd_prod_of_mem (fun i => (r i : ℕ)) (Finset.mem_univ (⟨0, by omega⟩ : Fin ℓ))
    have hpos : 0 < ∏ i, (r i : ℕ) := Finset.prod_pos (fun i _ => (hp i).pos)
    have hle := Nat.le_of_dvd hpos hi0
    have := (hp (⟨0, by omega⟩ : Fin ℓ)).one_lt
    omega
  have hrd : ∀ i, (r i : ℕ) ∣ (D : ℕ) := by
    intro i; rw [hDcoe]; exact Finset.dvd_prod_of_mem (fun j => (r j : ℕ)) (Finset.mem_univ i)
  -- Step 2: characters
  have hψexists : ∀ i, ∃ ψ : DirichletCharacter ℂ (r i : ℕ),
      orderOf ψ = 3 ∧ DirichletCharacter.conductor ψ = (r i : ℕ) :=
    fun i => SublemmaCubicCharacterOfConductorR (r i) (hp i) (hm i)
  choose ψ hψord hψcond using hψexists
  set χ : Fin ℓ → DirichletCharacter ℂ (D : ℕ) :=
    fun i => DirichletCharacter.changeLevel (hrd i) (ψ i) with hχdef
  have hχcond : ∀ i, DirichletCharacter.conductor (χ i) = (r i : ℕ) := by
    intro i
    have h := (SublemmaChangeLevelPreservesConductorAndOrder (D := (D : ℕ)) (ψ i) (hrd i)).1
    rw [hχdef]
    exact h.trans (hψcond i)
  have hχord : ∀ i, orderOf (χ i) = 3 := by
    intro i
    have h := (SublemmaChangeLevelPreservesConductorAndOrder (D := (D : ℕ)) (ψ i) (hrd i)).2
    rw [hχdef]
    exact h.trans (hψord i)
  obtain ⟨hchicond, hchiord⟩ :=
    SublemmaCharacterProductOrderConductor ℓ (D : ℕ) r χ hcop hχcond hχord hDcoe hD1
  -- Step 3: fields and instances
  refine ⟨r, hmono, hp, hm, hmin, D, hDcoe, ∏ i, χ i, hchiord, hchicond, ?_⟩
  set M : IntermediateField ℚ ℂ := ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) with hMdef
  set F : IntermediateField ℚ ℂ := cutOutField D (∏ i, χ i) with hFdef
  -- NumberField ↥M
  haveI hFinEach : ∀ i, FiniteDimensional ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
    intro i
    apply FiniteDimensional.of_finrank_pos
    rw [CyclicCubicSubfieldDegree (r i) (hp i) (hm i)]; norm_num
  haveI hMfin : FiniteDimensional ℚ ↥M := by
    rw [hMdef]; exact IntermediateField.finiteDimensional_iSup_of_finite
  letI nfM : NumberField ↥M := NumberField.of_module_finite ℚ ↥M
  -- F ≤ M
  have hFM : F ≤ M := by
    rw [hFdef, hMdef]
    exact SublemmaFsubsetM ℓ r D hp hm hrd ψ hψord χ (fun i => by rw [hχdef]) (∏ i, χ i) rfl
  -- NumberField ↥F
  haveI hFfin : FiniteDimensional ℚ ↥F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hFM).toLinearMap
      (IntermediateField.inclusion_injective hFM)
  letI nfF : NumberField ↥F := NumberField.of_module_finite ℚ ↥F
  -- Algebra ↥F ↥M and scalar tower
  letI algFM : Algebra ↥F ↥M := (IntermediateField.inclusion hFM).toRingHom.toAlgebra
  haveI htower : IsScalarTower ℚ ↥F ↥M := by
    apply IsScalarTower.of_algebraMap_eq; intro x; apply Subtype.ext; rfl
  -- M/ℚ Galois (each summand Galois, finite compositum)
  have hLgal : ∀ i, IsGalois ℚ ↥(cyclicCubicSubfield (r i) (hp i) (hm i)) := by
    intro i
    rw [← SublemmaCutOutFieldCubicChar (r i) (hp i) (hm i) (ψ i) (hψord i)]
    exact SublemmaCutOutFieldGalois (r i) (ψ i)
  haveI hMgal : IsGalois ℚ ↥M := by
    rw [hMdef]
    have hgal_finset : ∀ s : Finset (Fin ℓ),
        IsGalois ℚ ↥(⨆ i ∈ s, cyclicCubicSubfield (r i) (hp i) (hm i)) := by
      intro s
      induction s using Finset.induction with
      | empty =>
          rw [show (⨆ i ∈ (∅ : Finset (Fin ℓ)), cyclicCubicSubfield (r i) (hp i) (hm i)) = ⊥
              from by simp]
          exact isGalois_bot
      | insert a s hnm ihg =>
          rw [Finset.iSup_insert]
          exact @FiniteGaloisIntermediateField.instIsGaloisSubtypeMemIntermediateFieldMax
            ℚ ℂ _ _ _
            (cyclicCubicSubfield (r a) (hp a) (hm a))
            (⨆ i ∈ s, cyclicCubicSubfield (r i) (hp i) (hm i))
            (hLgal a) ihg
    have heq : (⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i))
        = ⨆ i ∈ (Finset.univ : Finset (Fin ℓ)), cyclicCubicSubfield (r i) (hp i) (hm i) := by
      simp
    rw [heq]; exact hgal_finset Finset.univ
  -- Relative finite dimensionality and relative Galois
  haveI hFMfin : FiniteDimensional ↥F ↥M := FiniteDimensional.right ℚ ↥F ↥M
  haveI hFMgal : IsGalois ↥F ↥M := IsGalois.tower_top_of_isGalois ℚ ↥F ↥M
  -- Base-field properties
  have hMtr : NumberField.IsTotallyReal ↥M :=
    Prop32CyclotomicBase_totally_real ℓ (by omega) r hp hm hdist M hMdef
  have hFtr : NumberField.IsTotallyReal ↥F := SublemmaTotallyRealSubfield F M hFM hMtr
  have hFgal : IsGalois ℚ ↥F := by
    rw [hFdef]; exact SublemmaCutOutFieldGalois D (∏ i, χ i)
  have hFdeg : Module.finrank ℚ ↥F = 3 := by
    have hMdeg := Prop32CyclotomicBase_degree ℓ (by omega) r hp hm hdist M hMdef
    have hrel := Prop32CyclotomicBase_relative_degree ℓ (by omega) r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hFdef
    have hmul := Module.finrank_mul_finrank ℚ ↥F ↥M
    rw [hrel, hMdeg] at hmul
    have h3 : (3 : ℕ) ^ ℓ = 3 * 3 ^ (ℓ - 1) := by rw [← pow_succ']; congr 1; omega
    rw [h3] at hmul
    exact Nat.eq_of_mul_eq_mul_right (by positivity) hmul
  have hunr : EverywhereUnramified ↥F ↥M :=
    Prop32CyclotomicBase_unramified ℓ (by omega) r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hchicond hFdef
  have hiso : Nonempty ((↥M ≃ₐ[↥F] ↥M) ≃* (Fin (ℓ - 1) → Multiplicative (ZMod 3))) :=
    SublemmaGalMFElementaryAbelianIso ℓ hℓ r hp hm hdist M hMdef F hFM
      D hDcoe (∏ i, χ i) hchiord hFdef
  have hdisc : (NumberField.discr ↥F).natAbs = (D : ℕ) ^ 2 := by
    have h := Prop32CyclotomicBase_discriminant ℓ (by omega) r hp hm hdist F
      D hDcoe (∏ i, χ i) hchiord hchicond hFdef
    rw [hDcoe]; exact h
  have hmprime := SublemmaMPrimeRealization ℓ hℓ F M hFM hunr hiso
  exact ⟨F, M, rfl, rfl, hFM, nfF, nfM, algFM, htower, hFtr, hFgal, hFdeg,
    SublemmaNoZeta3 F hFtr, hunr, hiso, hdisc, hmprime⟩

-- Cited from: Ribes, L., Zalesskii, P. (2010). Profinite Groups, 2nd ed., Ergebnisse der Math. 40,
-- Springer. The existence of a descending chain of open normal subgroups of index tending to
-- infinity inside an infinite, topologically finitely generated pro-p group.
--
-- The chain does NOT require the pro-p Frattini/lower-central series:
-- for an INFINITE PROFINITE group `Gbar = G ⧸ N` (compact, Hausdorff, totally disconnected topological
-- group — all supplied by `IsProP 3`) the open normal subgroups form a neighbourhood basis of `1`
-- and hence separate points. Build the chain by iterated intersection: starting from `⊤`, given an
-- open normal subgroup `K` of finite index, `K` is INFINITE (finite index in the infinite `Gbar`), so it
-- contains some `g ≠ 1`; profiniteness gives an open normal `U` with `g ∉ U`, and `K ⊓ U` is again
-- open, normal, of finite index, and strictly smaller than `K` (it omits `g`). Strict descent forces
-- the indices to strictly increase (`Subgroup.index_strictAnti`), so they tend to `∞` for free
-- (`StrictMono.tendsto_atTop`). Pulling everything back along the (continuous, surjective) quotient
-- map `G ↠ Gbar` produces open normal subgroups of `G` above `N` with the same indices. Neither the
-- pro-p hypothesis nor topological finite generation is needed for the construction — only
-- infiniteness and the profinite structure carried by `IsProP 3`.
-- Paper label: [RZ10] Profinite Groups (descending open-normal chains in infinite f.g. pro-p groups)



set_option maxHeartbeats 800000

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

/-- A layer of the descending chain: an open, normal subgroup of finite index. -/
private structure DescChainLayer (Gbar : Type*) [Group Gbar] [TopologicalSpace Gbar] : Type _ where
  carrier : Subgroup Gbar
  hopen : IsOpen (carrier : Set Gbar)
  hnorm : carrier.Normal
  hfi : carrier.FiniteIndex

/-- In an infinite profinite group, any open-normal finite-index subgroup strictly contains a
smaller open-normal finite-index subgroup. -/
private lemma descChain_exists_smaller
    {Gbar : Type*} [Group Gbar] [TopologicalSpace Gbar] [IsTopologicalGroup Gbar]
    [CompactSpace Gbar] [T2Space Gbar] [TotallyDisconnectedSpace Gbar] [Infinite Gbar]
    (l : DescChainLayer Gbar) : ∃ l' : DescChainLayer Gbar, l'.carrier < l.carrier := by
  haveI := l.hnorm
  haveI := l.hfi
  -- `l.carrier` is infinite (finite index in the infinite `Gbar`)
  have hGbar0 : Nat.card Gbar = 0 := Nat.card_eq_zero_of_infinite
  have hcard0 : Nat.card l.carrier = 0 := by
    have h := Subgroup.card_mul_index l.carrier
    rw [hGbar0] at h
    exact (Nat.mul_eq_zero.mp h).resolve_right l.hfi.index_ne_zero
  haveI hInfK : Infinite l.carrier := by
    rcases Nat.card_eq_zero.mp hcard0 with h | h
    · exact absurd (⟨(1 : l.carrier)⟩ : Nonempty l.carrier) (not_nonempty_iff.mpr h)
    · exact h
  have hne : ∃ g : Gbar, g ∈ l.carrier ∧ g ≠ 1 := by
    obtain ⟨x, hx⟩ := exists_ne (1 : l.carrier)
    refine ⟨x, x.2, ?_⟩
    intro hc
    apply hx
    exact Subtype.ext hc
  obtain ⟨g, hgK, hg_ne⟩ := hne
  -- an open normal subgroup `U` avoiding `g`
  have hgc_open : IsOpen ({g}ᶜ : Set Gbar) := isOpen_compl_singleton
  have h1mem : (1 : Gbar) ∈ ({g}ᶜ : Set Gbar) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact fun hc => hg_ne hc.symm
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hgc_open h1mem
  haveI hUnorm : (U : Subgroup Gbar).Normal := U.isNormal'
  have hUopen : IsOpen ((U : Subgroup Gbar) : Set Gbar) := U.toOpenSubgroup.isOpen
  have hgU : g ∉ (U : Subgroup Gbar) := by
    intro hmem
    have hmem' : g ∈ (U : Set Gbar) := hmem
    exact (hU hmem') rfl
  -- the smaller layer `K ⊓ U`
  have hK'open : IsOpen ((l.carrier ⊓ (U : Subgroup Gbar) : Subgroup Gbar) : Set Gbar) := by
    rw [Subgroup.coe_inf]; exact l.hopen.inter hUopen
  refine ⟨⟨l.carrier ⊓ (U : Subgroup Gbar), hK'open, inferInstance, ?_⟩, ?_⟩
  · haveI : Finite (Gbar ⧸ (l.carrier ⊓ (U : Subgroup Gbar))) :=
      Subgroup.quotient_finite_of_isOpen _ hK'open
    exact Subgroup.finiteIndex_of_finite_quotient
  · apply lt_of_le_of_ne inf_le_left
    intro heq
    have hgK' : g ∈ l.carrier ⊓ (U : Subgroup Gbar) := by rw [heq]; exact hgK
    exact hgU (Subgroup.mem_inf.mp hgK').2

/-- **Descending open-normal chain in an infinite profinite group.** -/
private lemma descChain_main
    (Gbar : Type*) [Group Gbar] [TopologicalSpace Gbar] [IsTopologicalGroup Gbar]
    [CompactSpace Gbar] [T2Space Gbar] [TotallyDisconnectedSpace Gbar] [Infinite Gbar] :
    ∃ K : ℕ → Subgroup Gbar, (∀ j, (K j).Normal) ∧ (∀ j, IsOpen (K j : Set Gbar)) ∧
      K 0 = ⊤ ∧ StrictAnti K ∧ (∀ j, 0 < (K j).index) := by
  have Hstep : ∀ l : DescChainLayer Gbar, ∃ l' : DescChainLayer Gbar, l'.carrier < l.carrier :=
    fun l => descChain_exists_smaller l
  choose next hnext using Hstep
  let base : DescChainLayer Gbar :=
    { carrier := ⊤
      hopen := by rw [Subgroup.coe_top]; exact isOpen_univ
      hnorm := inferInstance
      hfi := ⟨by rw [Subgroup.index_top]; exact one_ne_zero⟩ }
  let chain : ℕ → DescChainLayer Gbar := fun n => Nat.rec base (fun _ l => next l) n
  refine ⟨fun n => (chain n).carrier, fun n => (chain n).hnorm, fun n => (chain n).hopen, rfl, ?_,
    fun n => Nat.pos_of_ne_zero (chain n).hfi.index_ne_zero⟩
  apply strictAnti_nat_of_succ_lt
  intro n
  exact hnext (chain n)

/-- **Descending open-normal chain in an infinite finitely generated pro-`3` quotient.**

For every number field `F`, writing `G := galUr 3 F`, whenever a quotient `Gbar = G ⧸ N` (for a closed
normal subgroup `N ≤ G`) is infinite, topologically finitely generated and pro-`3`, there is a chain
`H : ℕ → Subgroup G` of open normal subgroups above `N` with `H 0 = ⊤`, strictly decreasing, each of
finite index, whose indices tend to infinity.

Discharged from Mathlib alone: the profinite structure carried by `IsProP 3` makes the open normal
subgroups of `Gbar` separate points, so an iterated-intersection construction produces a strictly
descending chain of open normal finite-index subgroups; strict descent forces the indices to `→ ∞`,
and pulling back along `G ↠ Gbar` yields the chain in `G` above `N`. -/
theorem UnramifiedProPDescendingChain :
    ∀ (F : Type*) [Field F] [NumberField F],
      ∀ (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
          IsClosed (N : Set (galUr 3 F)) →
            letI := hNnorm
            Infinite (galUr 3 F ⧸ N) →
              TopFinitelyGenerated (galUr 3 F ⧸ N) →
                IsProP 3 (galUr 3 F ⧸ N) →
                  ∃ H : ℕ → Subgroup (galUr 3 F),
                    (∀ j, (H j).Normal) ∧
                      (∀ j, IsOpen ((H j : Set (galUr 3 F)))) ∧
                        (∀ j, N ≤ H j) ∧
                          H 0 = ⊤ ∧
                            StrictAnti H ∧
                              (∀ j, 0 < (H j).index) ∧
                                Filter.Tendsto (fun j => (H j).index)
                                  Filter.atTop Filter.atTop := by
  intro F instF instNF N hNnorm hNclosed
  letI := hNnorm
  intro hInf hFG hProP
  obtain ⟨hTG, hCompact, hT2, hTD, _hpow⟩ := hProP
  haveI := hTG
  haveI := hCompact
  haveI := hT2
  haveI := hTD
  haveI := hInf
  obtain ⟨K, hKnorm, hKopen, hK0, hKanti, hKidx⟩ := descChain_main (galUr 3 F ⧸ N)
  set q := QuotientGroup.mk' N with hq
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective N
  have hqcont : Continuous q := by rw [hq, QuotientGroup.coe_mk']; exact QuotientGroup.continuous_mk
  -- comap strict-mono on subgroups (via surjectivity)
  have hcs : ∀ {A B : Subgroup (galUr 3 F ⧸ N)}, A < B → A.comap q < B.comap q := by
    intro A B h
    apply lt_of_le_of_ne (Subgroup.comap_mono h.le)
    intro heq
    have hAB : A = B := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hqsurj A,
          ← Subgroup.map_comap_eq_self_of_surjective hqsurj B, heq]
    exact absurd hAB (ne_of_lt h)
  refine ⟨fun j => (K j).comap q, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j => (hKnorm j).comap q
  · intro j
    have hpre : (((K j).comap q) : Set (galUr 3 F)) = q ⁻¹' (K j : Set _) := rfl
    rw [hpre]; exact (hKopen j).preimage hqcont
  · intro j n hn
    rw [Subgroup.mem_comap]
    have : q n = 1 := by rw [hq, QuotientGroup.coe_mk', QuotientGroup.eq_one_iff]; exact hn
    rw [this]; exact one_mem _
  · show Subgroup.comap q (K 0) = ⊤
    rw [hK0]; exact Subgroup.comap_top q
  · intro a b hab
    exact hcs (hKanti hab)
  · intro j
    rw [Subgroup.index_comap_of_surjective _ hqsurj]
    exact hKidx j
  · have hmono : StrictMono (fun j => (K j).index) := by
      apply strictMono_nat_of_lt_succ
      intro n
      haveI : (K (n + 1)).FiniteIndex := ⟨(hKidx (n + 1)).ne'⟩
      exact Subgroup.index_strictAnti (hKanti (Nat.lt_succ_self n))
    have hfun : (fun j => ((K j).comap q).index) = (fun j => (K j).index) := by
      funext j; exact Subgroup.index_comap_of_surjective _ hqsurj
    rw [hfun]
    exact hmono.tendsto_atTop

-- Cited from: Ribes, L., Zalesskii, P. (2010). Profinite Groups, 2nd ed., Ergebnisse der Math. 40, Springer (infinite Galois correspondence for profinite groups; Frattini series and descending open-normal chains in infinite finitely generated pro-p groups). Combined with the maximal-unramified-pro-p setup of Definition A.3 (its finite quotients correspond to finite everywhere-unramified Galois p-group extensions of F).
-- Paper label: Definition A.3; [RZ10] Profinite Groups
-- This theorem has two parts. Part (a) [the infinite Galois correspondence for the open normal
-- subgroups of galUr 3 F: finite-Galois layers, finrank = index, Gal(layer) ≃ G⧸H, injectivity,
-- inclusion-reversing] is proved from Mathlib (see `UnramifiedProPTowerCorrespondence_partA`), using
-- Mathlib's infinite Galois (Krull) correspondence `FieldTheory/Galois/Infinite.lean` together with
-- the enabler `IsGalois F (maxUnramifiedProPExt 3 F)` (a compositum of Galois extensions is Galois).
-- Part (b) [the descending open-normal chain of index → ∞ in an infinite finitely generated
-- pro-3 quotient] is cited from prior published work, isolated as the
-- axiom `UnramifiedProPDescendingChain` (Ribes–Zalesskii, Profinite Groups), which this theorem
-- applies.
-- NL statement: For every number field F, letting G := galUr 3 F: (a) [infinite Galois correspondence] for every open normal subgroup H of G, the fixed field fixedFieldOf 3 F H is finite Galois over F with Module.finrank F (fixedFieldOf 3 F H) = H.index and a group isomorphism (fixedFieldOf 3 F H ≃ₐ[F] ·) ≃ (G ⧸ H), and the assignment H ↦ fixedFieldOf 3 F H is injective and inclusion-reversing on open normal subgroups; and (b) [descending chain] whenever a quotient Ḡ = G ⧸ N (for a closed normal N ≤ G) is infinite, topologically finitely generated and pro-3, there exists a family H : ℕ → Subgroup G of open normal subgroups with N ≤ H_j for all j, H_0 = ⊤, StrictAnti H, each (H_j).index finite, and Filter.Tendsto (fun j => (H_j).index) Filter.atTop Filter.atTop.




open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000

/-- **Part (a): the infinite Galois correspondence for `F^{ur,3}/F`, proved from Mathlib.**

For every number field `F`, writing `G := galUr 3 F` for the Galois group of the maximal everywhere-
unramified pro-`3` extension, for every open normal subgroup `H` of `G`:

* the fixed field `fixedFieldOf 3 F H` is finite-dimensional and Galois over `F`,
* `Module.finrank F (fixedFieldOf 3 F H) = H.index`,
* there is a group isomorphism `Gal(fixedFieldOf 3 F H / F) ≃* (G ⧸ H)`;

moreover `H ↦ fixedFieldOf 3 F H` is injective and inclusion-reversing on the open normal subgroups
of `G`. This is Mathlib's infinite fundamental theorem of Galois theory specialized to Definition
A.3; the enabler `IsGalois F (maxUnramifiedProPExt 3 F)` is the fact that a compositum of Galois
extensions is Galois. -/
theorem UnramifiedProPTowerCorrespondence_partA
    (F : Type*) [Field F] [NumberField F] :
    (∀ (H : Subgroup (galUr 3 F)) (hHnorm : H.Normal),
        IsOpen (H : Set (galUr 3 F)) →
          letI := hHnorm
          IsGalois F (fixedFieldOf 3 F H) ∧
            FiniteDimensional F (fixedFieldOf 3 F H) ∧
              Module.finrank F (fixedFieldOf 3 F H) = H.index ∧
                Nonempty
                  ((fixedFieldOf 3 F H ≃ₐ[F] fixedFieldOf 3 F H) ≃* (galUr 3 F ⧸ H))) ∧
      (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
          H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
            fixedFieldOf 3 F H₁ = fixedFieldOf 3 F H₂ → H₁ = H₂) ∧
      (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
          H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
            H₁ ≤ H₂ → fixedFieldOf 3 F H₂ ≤ fixedFieldOf 3 F H₁) := by
  -- Enabler: `F^{ur,3}/F` is Galois (compositum of finite Galois extensions).
  haveI hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  haveI hgal : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  refine ⟨?_, ?_, ?_⟩
  · -- (A1) fixed field of an open normal subgroup is a finite Galois layer with the right degree/iso
    intro H hHnorm hHopen
    haveI := hHnorm
    have hclosed : IsClosed (H : Set (galUr 3 F)) := H.isClosed_of_isOpen hHopen
    let Hc : ClosedSubgroup (galUr 3 F) := ⟨H, hclosed⟩
    have hff : (fixedFieldOf 3 F H).fixingSubgroup = H :=
      InfiniteGalois.fixingSubgroup_fixedField Hc
    -- finite-dimensionality + Galois of the layer, from the Krull correspondence
    have hfg : FiniteDimensional F (fixedFieldOf 3 F H) ∧ IsGalois F (fixedFieldOf 3 F H) := by
      rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (fixedFieldOf 3 F H), hff]
      exact ⟨hHopen, hHnorm⟩
    haveI hfdL := hfg.1
    haveI hgalL := hfg.2
    haveI hnormL : Normal F (fixedFieldOf 3 F H) := hgalL.to_normal
    -- restriction homomorphism G → Gal(layer/F)
    let φ : galUr 3 F →* ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H)) :=
      AlgEquiv.restrictNormalHom (F := F) (K₁ := maxUnramifiedProPExt 3 F) (fixedFieldOf 3 F H)
    have hker : φ.ker = H :=
      (IntermediateField.restrictNormalHom_ker (fixedFieldOf 3 F H)).trans hff
    have hsurj : Function.Surjective φ :=
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := (fixedFieldOf 3 F H))
        (maxUnramifiedProPExt 3 F)
    -- iso  G ⧸ H ≃* Gal(layer/F)
    let e : (galUr 3 F ⧸ H) ≃* ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H)) :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)
    refine ⟨hgalL, hfdL, ?_, ⟨e.symm⟩⟩
    -- finrank = index
    have hcard : Nat.card ((fixedFieldOf 3 F H) ≃ₐ[F] (fixedFieldOf 3 F H))
        = Nat.card (galUr 3 F ⧸ H) := (Nat.card_congr e.toEquiv).symm
    rw [← IsGalois.card_aut_eq_finrank F (fixedFieldOf 3 F H), hcard, ← Subgroup.index_eq_card]
  · -- (A2) injectivity of  H ↦ fixedFieldOf 3 F H  on open normal subgroups
    intro H₁ H₂ _ ho1 _ ho2 heq
    have hc1 : IsClosed (H₁ : Set (galUr 3 F)) := H₁.isClosed_of_isOpen ho1
    have hc2 : IsClosed (H₂ : Set (galUr 3 F)) := H₂.isClosed_of_isOpen ho2
    let Hc1 : ClosedSubgroup (galUr 3 F) := ⟨H₁, hc1⟩
    let Hc2 : ClosedSubgroup (galUr 3 F) := ⟨H₂, hc2⟩
    have hff1 : (fixedFieldOf 3 F H₁).fixingSubgroup = H₁ :=
      InfiniteGalois.fixingSubgroup_fixedField Hc1
    have hff2 : (fixedFieldOf 3 F H₂).fixingSubgroup = H₂ :=
      InfiniteGalois.fixingSubgroup_fixedField Hc2
    calc H₁ = (fixedFieldOf 3 F H₁).fixingSubgroup := hff1.symm
      _ = (fixedFieldOf 3 F H₂).fixingSubgroup := by rw [heq]
      _ = H₂ := hff2
  · -- (A3) inclusion-reversing (unconditional antitonicity of the fixed-field map)
    intro H₁ H₂ _ _ _ _ hle
    exact IntermediateField.fixedField_le hle

/-- **Infinite Galois correspondence for `F^{ur,3}/F` plus descending-chain existence.**

For every number field `F`, writing `G := galUr 3 F` for the Galois group of the maximal
everywhere-unramified pro-`3` extension:

* **(a)** *(infinite fundamental theorem of Galois theory, specialized to Definition A.3).* For every
  open normal subgroup `H` of `G`, the fixed field `fixedFieldOf 3 F H` is a finite Galois extension
  of `F` with `Module.finrank F (fixedFieldOf 3 F H) = H.index` and a group isomorphism
  `Gal(fixedFieldOf 3 F H / F) ≃* (G ⧸ H)`; moreover `H ↦ fixedFieldOf 3 F H` is injective and
  inclusion-reversing on the open normal subgroups of `G`. **This part is proved from Mathlib**
  (`UnramifiedProPTowerCorrespondence_partA`).

* **(b)** *(descending chain in an infinite finitely generated pro-`3` quotient).* Whenever a quotient
  `Ḡ = G ⧸ N` (for a closed normal subgroup `N ≤ G`) is infinite, topologically finitely generated
  and pro-`3`, there is a chain `H : ℕ → Subgroup G` of open normal subgroups above `N` with
  `H 0 = ⊤`, strictly decreasing, each of finite index, whose indices tend to infinity. **This part
  is admitted from prior published work** via `UnramifiedProPDescendingChain` (Ribes–Zalesskii,
  *Profinite Groups*); the corresponding pro-`p` Frattini / lower-central series theory is not
  currently in Mathlib. -/
theorem UnramifiedProPTowerCorrespondence :
    ∀ (F : Type*) [Field F] [NumberField F],
      -- (a) infinite Galois correspondence for the open normal subgroups of `galUr 3 F`
      (∀ (H : Subgroup (galUr 3 F)) (hHnorm : H.Normal),
          IsOpen (H : Set (galUr 3 F)) →
            letI := hHnorm
            IsGalois F (fixedFieldOf 3 F H) ∧
              FiniteDimensional F (fixedFieldOf 3 F H) ∧
                Module.finrank F (fixedFieldOf 3 F H) = H.index ∧
                  Nonempty
                    ((fixedFieldOf 3 F H ≃ₐ[F] fixedFieldOf 3 F H) ≃* (galUr 3 F ⧸ H))) ∧
        -- injectivity of `H ↦ fixedFieldOf 3 F H` on open normal subgroups
        (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
            H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
              fixedFieldOf 3 F H₁ = fixedFieldOf 3 F H₂ → H₁ = H₂) ∧
        -- inclusion-reversing on open normal subgroups
        (∀ (H₁ H₂ : Subgroup (galUr 3 F)), H₁.Normal → IsOpen (H₁ : Set (galUr 3 F)) →
            H₂.Normal → IsOpen (H₂ : Set (galUr 3 F)) →
              H₁ ≤ H₂ → fixedFieldOf 3 F H₂ ≤ fixedFieldOf 3 F H₁) ∧
        -- (b) descending open-normal chain of index → ∞ in an infinite f.g. pro-3 quotient
        (∀ (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
            IsClosed (N : Set (galUr 3 F)) →
              letI := hNnorm
              Infinite (galUr 3 F ⧸ N) →
                TopFinitelyGenerated (galUr 3 F ⧸ N) →
                  IsProP 3 (galUr 3 F ⧸ N) →
                    ∃ H : ℕ → Subgroup (galUr 3 F),
                      (∀ j, (H j).Normal) ∧
                        (∀ j, IsOpen ((H j : Set (galUr 3 F)))) ∧
                          (∀ j, N ≤ H j) ∧
                            H 0 = ⊤ ∧
                              StrictAnti H ∧
                                (∀ j, 0 < (H j).index) ∧
                                  Filter.Tendsto (fun j => (H j).index)
                                    Filter.atTop Filter.atTop) := by
  intro F _ _
  obtain ⟨ha1, ha2, ha3⟩ := UnramifiedProPTowerCorrespondence_partA F
  exact ⟨ha1, ha2, ha3, UnramifiedProPDescendingChain F⟩

-- Cited from: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008, Chapter X; standard infinite Galois theory of the maximal everywhere-unramified pro-p extension (Definition A.3 of the source paper).
-- Paper label: Definition A.3 (pro-3 property of Gal(F^{ur,3}/F))
-- Every open normal subgroup H of G = galUr 3 F has
-- index a power of 3. Proof: by the infinite Galois correspondence
-- `UnramifiedProPTowerCorrespondence_partA`, the fixed field E = fixedFieldOf 3 F H is a finite Galois
-- layer with finrank F E = H.index, so H.index = Nat.card (Gal(E/F)); it remains to show Gal(E/F) is a
-- 3-group. Lifting E into AlgebraicClosure F, E is a finite-dimensional (hence compact-element)
-- subextension of maxUnramifiedProPExt 3 F = sSup of the defining family of finite Galois everywhere-
-- unramified 3-group extensions, so E lies in a finite subcompositum W of family members. A finite
-- compositum of 3-group Galois extensions has 3-group Galois group (product-injection
-- Gal(A⊔B) ↪ Gal A × Gal B + Finset induction), and Gal(W/F) surjects onto Gal(E/F), so Gal(E/F) is a
-- 3-group.
-- NL statement: For every number field F, every open normal subgroup H of G = galUr 3 F (the Galois group of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F) has index a power of 3: there exists k with H.index = 3 ^ k. This is the arithmetic core of the pro-3 property of Gal(F^{ur,3}/F), which the paper's Definition A.3 states as background (the Galois group of the maximal unramified pro-p extension is a pro-p group).




open scoped NumberField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 800000

/-- The Galois group of the compositum of two finite Galois 3-group extensions inside a common
field is again a 3-group. -/
lemma pgroup_sup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    (A B : IntermediateField F K)
    [FiniteDimensional F A] [IsGalois F A] [FiniteDimensional F B] [IsGalois F B]
    (hA : IsPGroup 3 (A ≃ₐ[F] A)) (hB : IsPGroup 3 (B ≃ₐ[F] B)) :
    IsPGroup 3 (↥(A ⊔ B) ≃ₐ[F] ↥(A ⊔ B)) := by
  haveI hnA : Normal F A := IsGalois.to_normal
  haveI hnB : Normal F B := IsGalois.to_normal
  letI algA : Algebra ↥A ↥(A ⊔ B) :=
    (IntermediateField.inclusion (le_sup_left)).toRingHom.toAlgebra
  letI algB : Algebra ↥B ↥(A ⊔ B) :=
    (IntermediateField.inclusion (le_sup_right)).toRingHom.toAlgebra
  haveI towerA : IsScalarTower F ↥A ↥(A ⊔ B) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion (le_sup_left)).commutes x).symm)
  haveI towerB : IsScalarTower F ↥B ↥(A ⊔ B) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion (le_sup_right)).commutes x).symm)
  haveI halg : Algebra.IsAlgebraic F ↥(A ⊔ B) := Algebra.IsAlgebraic.of_finite F _
  -- the product-of-restrictions monoid hom
  let f := AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(A ⊔ B)) ↥A
  let g := AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(A ⊔ B)) ↥B
  let ρ := f.prod g
  -- injectivity
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hσA : σ.restrictNormal ↥A = 1 := congrArg Prod.fst hσ
    have hσB : σ.restrictNormal ↥B = 1 := congrArg Prod.snd hσ
    -- the two subfields, viewed as intermediate fields of A ⊔ B
    set A' : IntermediateField F ↥(A ⊔ B) := IntermediateField.restrict (le_sup_left : A ≤ A ⊔ B)
      with hA'def
    set B' : IntermediateField F ↥(A ⊔ B) := IntermediateField.restrict (le_sup_right : B ≤ A ⊔ B)
      with hB'def
    have hmapA : A'.map ((A ⊔ B).val) = A := IntermediateField.lift_restrict _
    have hmapB : B'.map ((A ⊔ B).val) = B := IntermediateField.lift_restrict _
    have hgen : A' ⊔ B' = (⊤ : IntermediateField F ↥(A ⊔ B)) := by
      apply IntermediateField.map_injective ((A ⊔ B).val)
      rw [IntermediateField.map_sup, hmapA, hmapB, ← AlgHom.fieldRange_eq_map,
        IntermediateField.fieldRange_val]
    -- σ fixes A' and B' pointwise
    have hfixA : ∀ x ∈ A', σ x = x := by
      intro x hx
      rw [hA'def, IntermediateField.mem_restrict] at hx
      have hxy : (algebraMap ↥A ↥(A ⊔ B)) ⟨x.1, hx⟩ = x := by
        apply Subtype.ext; rfl
      have hc := AlgEquiv.restrictNormal_commutes σ ↥A ⟨x.1, hx⟩
      rw [hσA, AlgEquiv.one_apply, hxy] at hc
      exact hc.symm
    have hfixB : ∀ x ∈ B', σ x = x := by
      intro x hx
      rw [hB'def, IntermediateField.mem_restrict] at hx
      have hxy : (algebraMap ↥B ↥(A ⊔ B)) ⟨x.1, hx⟩ = x := by
        apply Subtype.ext; rfl
      have hc := AlgEquiv.restrictNormal_commutes σ ↥B ⟨x.1, hx⟩
      rw [hσB, AlgEquiv.one_apply, hxy] at hc
      exact hc.symm
    -- hence σ is the identity
    have hadj : Algebra.adjoin F ((A' : Set ↥(A ⊔ B)) ∪ (B' : Set ↥(A ⊔ B))) = ⊤ := by
      rw [← IntermediateField.adjoin_eq_top_iff]
      apply le_antisymm le_top
      rw [← hgen]
      apply sup_le
      · exact fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_left hx)
      · exact fun x hx => IntermediateField.subset_adjoin F _ (Set.subset_union_right hx)
    have hEqOn : Set.EqOn (σ.toAlgHom) (AlgHom.id F ↥(A ⊔ B))
        ((A' : Set ↥(A ⊔ B)) ∪ (B' : Set ↥(A ⊔ B))) := by
      intro x hx
      rcases hx with hx | hx
      · show σ x = x; exact hfixA x hx
      · show σ x = x; exact hfixB x hx
    have hEq : σ.toAlgHom = AlgHom.id F ↥(A ⊔ B) := AlgHom.ext_of_adjoin_eq_top hadj hEqOn
    ext x
    simpa using AlgHom.ext_iff.mp hEq x
  -- the product of two 3-groups is a 3-group
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpgProd : IsPGroup 3 ((A ≃ₐ[F] A) × (B ≃ₐ[F] B)) := by
    obtain ⟨a, ha⟩ := (IsPGroup.iff_card).mp hA
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hB
    apply IsPGroup.of_card (n := a + b)
    rw [Nat.card_prod, ha, hb, pow_add]
  exact hpgProd.of_injective ρ hinj

/-- A finite union (compositum) of members of the defining pro-`3` family is a finite Galois
3-group extension of `F`. -/
lemma pgroup_finset_sup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    {ι : Type*} (fam : ι → IntermediateField F K)
    (hfd : ∀ i, FiniteDimensional F (fam i)) (hgal : ∀ i, IsGalois F (fam i))
    (hpg : ∀ i, IsPGroup 3 ((fam i) ≃ₐ[F] (fam i))) (t : Finset ι) :
    FiniteDimensional F ↥(⨆ i ∈ t, fam i) ∧ IsGalois F ↥(⨆ i ∈ t, fam i) ∧
      IsPGroup 3 (↥(⨆ i ∈ t, fam i) ≃ₐ[F] ↥(⨆ i ∈ t, fam i)) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  induction t using Finset.induction_on with
  | empty =>
    rw [show (⨆ i ∈ (∅ : Finset ι), fam i) = ⊥ by simp]
    refine ⟨inferInstance, inferInstance, ?_⟩
    apply IsPGroup.of_card (n := 0)
    rw [pow_zero, IsGalois.card_aut_eq_finrank F (⊥ : IntermediateField F K),
      IntermediateField.finrank_bot]
  | @insert a s ha ih =>
    obtain ⟨ihfd, ihgal, ihpg⟩ := ih
    rw [Finset.iSup_insert]
    haveI := hfd a; haveI := ihfd; haveI := hgal a; haveI := ihgal
    refine ⟨inferInstance, inferInstance, ?_⟩
    exact pgroup_sup (fam a) (⨆ i ∈ s, fam i) (hpg a) ihpg

/-- **Every open normal subgroup of `galUr 3 F` has 3-power index.** -/
theorem GalUrOpenNormalThreePowerIndex :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (galUr 3 F)),
      H.Normal → IsOpen (H : Set (galUr 3 F)) → ∃ k : ℕ, H.index = 3 ^ k := by
  intro F _ _ H hHnorm hHopen
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Part (a) of the Krull correspondence: the fixed field is a finite Galois layer.
  obtain ⟨hgalE, hfdE, hrank, _⟩ :=
    (UnramifiedProPTowerCorrespondence_partA F).1 H hHnorm hHopen
  haveI := hfdE
  haveI := hgalE
  -- STEP A: it suffices to show Gal(E/F) is a 3-group.
  suffices hpgE : IsPGroup 3 (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)) by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hpgE
    refine ⟨k, ?_⟩
    rw [← hrank, ← IsGalois.card_aut_eq_finrank F ↥(fixedFieldOf 3 F H), hk]
  -- STEP B: lift E into the algebraic closure and use the compositum structure of F^{ur,3}.
  set Ehat := IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
    (fixedFieldOf 3 F H) with hEhatdef
  have eEE : ↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥Ehat :=
    IntermediateField.equivMap (fixedFieldOf 3 F H)
      (IntermediateField.val (maxUnramifiedProPExt 3 F))
  haveI hfdEhat : FiniteDimensional F ↥Ehat := LinearEquiv.finiteDimensional eEE.toLinearEquiv
  haveI hgalEhat : IsGalois F ↥Ehat := (AlgEquiv.transfer_galois eEE).mp hgalE
  haveI hnormEhat : Normal F ↥Ehat := hgalEhat.to_normal
  -- The defining family and its per-member properties.
  set fam : ↥{E : IntermediateField F (AlgebraicClosure F) | IsFiniteUnramifiedProPExt 3 F E} →
      IntermediateField F (AlgebraicClosure F) := fun i => (i : IntermediateField F _) with hfamdef
  have hfamfd : ∀ i, FiniteDimensional F (fam i) := by
    intro i; obtain ⟨hfd, _⟩ := i.2; exact hfd
  have hfamgal : ∀ i, IsGalois F (fam i) := by
    intro i; obtain ⟨_, hgal, _, _⟩ := i.2; exact hgal
  have hfampg : ∀ i, IsPGroup 3 ((fam i) ≃ₐ[F] (fam i)) := by
    intro i; obtain ⟨_, _, _, hpg⟩ := i.2; exact hpg
  -- Kbig = ⨆ i, fam i
  have hKbigSup : maxUnramifiedProPExt 3 F = ⨆ i, fam i := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
  -- Ê ≤ Kbig ≤ ⨆ fam
  have hEhatKbig : Ehat ≤ maxUnramifiedProPExt 3 F := by
    rw [hEhatdef]
    calc IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
            (fixedFieldOf 3 F H)
        ≤ IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) ⊤ :=
          IntermediateField.map_mono _ le_top
      _ = maxUnramifiedProPExt 3 F := by
          rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
  have hEhatSup : Ehat ≤ ⨆ i, fam i := le_of_le_of_eq hEhatKbig hKbigSup
  -- Ê is compact (adjoin of a primitive element), so lies in a finite subcompositum.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F ↥Ehat
  set a := (IntermediateField.val Ehat) α with hadef
  have hEhatAdj : Ehat = IntermediateField.adjoin F {a} := by
    have h1 : IntermediateField.map (IntermediateField.val Ehat)
        (IntermediateField.adjoin F {α}) = IntermediateField.adjoin F {a} := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have h2 : IntermediateField.map (IntermediateField.val Ehat)
        (⊤ : IntermediateField F ↥Ehat) = Ehat := by
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val]
    calc Ehat = IntermediateField.map (IntermediateField.val Ehat) ⊤ := h2.symm
      _ = IntermediateField.map (IntermediateField.val Ehat) (IntermediateField.adjoin F {α}) := by
          rw [hα]
      _ = IntermediateField.adjoin F {a} := h1
  have hcompact : IsCompactElement Ehat := by
    rw [hEhatAdj]; exact IntermediateField.adjoin_simple_isCompactElement a
  obtain ⟨t, ht⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup (hk := hcompact) (f := fam)
      (h := hEhatSup)
  -- The finite subcompositum W is a finite Galois 3-group extension.
  obtain ⟨hWfd, hWgal, hWpg⟩ := pgroup_finset_sup fam hfamfd hfamgal hfampg t
  haveI := hWfd
  haveI := hWgal
  haveI hWnorm : Normal F ↥(⨆ i ∈ t, fam i) := hWgal.to_normal
  -- Ê is a subfield of W, so Gal(W/F) surjects onto Gal(Ê/F).
  letI algEW : Algebra ↥Ehat ↥(⨆ i ∈ t, fam i) :=
    (IntermediateField.inclusion ht).toRingHom.toAlgebra
  haveI towerEW : IsScalarTower F ↥Ehat ↥(⨆ i ∈ t, fam i) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion ht).commutes x).symm)
  have hsurj : Function.Surjective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(⨆ i ∈ t, fam i)) ↥Ehat) :=
    AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥Ehat) (↥(⨆ i ∈ t, fam i))
  have hpgEhat : IsPGroup 3 (↥Ehat ≃ₐ[F] ↥Ehat) := hWpg.of_surjective _ hsurj
  -- Transport back to Gal(E/F).
  exact hpgEhat.of_equiv (AlgEquiv.autCongr eEE).symm

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem GalUrIsProP :
    ∀ (F : Type) [Field F] [NumberField F], IsProP 3 (galUr 3 F) := by
  intro F _ _
  have hsep : Algebra.IsSeparable F (maxUnramifiedProPExt 3 F) := inferInstance
  have hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  have hgal : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  have halg : Algebra.IsAlgebraic F (maxUnramifiedProPExt 3 F) := inferInstance
  have hint : Algebra.IsIntegral F (maxUnramifiedProPExt 3 F) := halg.isIntegral
  unfold IsProP
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · exact InfiniteGalois.instCompactSpaceAlgEquivOfIsGalois F _
  · exact krullTopology_t2
  · exact inferInstance
  · exact GalUrOpenNormalThreePowerIndex F

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8;
-- H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10.
-- In a pro-p group G, every maximal proper OPEN subgroup H is normal of index p.
-- Proof: H is open in a compact group ⇒ finite index; its normal core N is
-- open normal, so by IsProP `N.index = p^k`, hence G/N is a finite p-group. The image of H in
-- G/N is a coatom (correspondence theorem + maximality among open subgroups, all of which
-- contain N hence correspond to subgroups of G/N). A finite p-group is nilpotent ⇒ satisfies the
-- normalizer condition ⇒ its coatoms are normal; the quotient by such a coatom has only the two
-- trivial subgroups and (p-group ⇒ nontrivial center ⇒ abelian) is simple of prime order p.
-- Transporting normality and index back through the quotient map gives the result.
-- (Topological finite generation `hfg` is not needed.)



set_option maxHeartbeats 800000
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
theorem ProPMaximalOpenNormalIndexP (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (H : Subgroup G) (hH : IsMaximalOpenSubgroup H) :
    H.Normal ∧ H.index = p := by
  obtain ⟨_, hcompact, _hT2, _hTD, hPindex⟩ := hpro
  haveI := hcompact
  obtain ⟨hHopen, hHne, hHmax⟩ := hH
  -- H has finite index (open subgroup of compact group)
  haveI hHfq : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI hHfi : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- normal core N of H
  have hNH : H.normalCore ≤ H := Subgroup.normalCore_le H
  have hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHopen
  have hNclosed : IsClosed (H.normalCore : Set G) := Subgroup.normalCore_isClosed H hHclosed
  have hNopen : IsOpen (H.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex H.normalCore hNclosed
  -- index of N is a power of p (from IsProP)
  obtain ⟨k, hk⟩ := hPindex H.normalCore inferInstance hNopen
  haveI hPfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hcardP : Nat.card (G ⧸ H.normalCore) = p ^ k := by
    rw [← Subgroup.index_eq_card]; exact hk
  haveI hPgroup : IsPGroup p (G ⧸ H.normalCore) := IsPGroup.of_card hcardP
  haveI hPnil : Group.IsNilpotent (G ⧸ H.normalCore) := hPgroup.isNilpotent
  have hNC : NormalizerCondition (G ⧸ H.normalCore) := normalizerCondition_of_isNilpotent
  -- quotient map and image of H
  set f := QuotientGroup.mk' H.normalCore with hfdef
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective H.normalCore
  have hker : f.ker = H.normalCore := QuotientGroup.ker_mk' H.normalCore
  set Hbar := Subgroup.map f H with hHbardef
  have hcomapHbar : Subgroup.comap f Hbar = H := by
    rw [hHbardef, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNH
  -- Hbar is a coatom of G/N
  have hcoatom : IsCoatom Hbar := by
    constructor
    · -- Hbar ≠ ⊤
      intro htop
      apply hHne
      have hc : Subgroup.comap f Hbar = Subgroup.comap f ⊤ := by rw [htop]
      rw [hcomapHbar, Subgroup.comap_top] at hc
      exact hc
    · intro Kbar hKbar
      have hNK : H.normalCore ≤ Subgroup.comap f Kbar := by
        have h1 : f.ker ≤ Subgroup.comap f Kbar := by
          rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
        rwa [hker] at h1
      have hKopen : IsOpen ((Subgroup.comap f Kbar) : Set G) := Subgroup.isOpen_mono hNK hNopen
      have hHK : H ≤ Subgroup.comap f Kbar :=
        Subgroup.map_le_iff_le_comap.mp (by rw [← hHbardef]; exact hKbar.le)
      have hmapK : Subgroup.map f (Subgroup.comap f Kbar) = Kbar :=
        Subgroup.map_comap_eq_self_of_surjective hfsurj Kbar
      rcases hHmax (Subgroup.comap f Kbar) hKopen hHK with hKH | hKtop
      · have hcontra : Kbar = Hbar := by rw [← hmapK, hKH, ← hHbardef]
        exact absurd hcontra.symm (ne_of_lt hKbar)
      · rw [← hmapK, hKtop]; exact Subgroup.map_top_of_surjective f hfsurj
  -- Hbar normal, hence H normal
  have hHbarNormal : Hbar.Normal := Subgroup.NormalizerCondition.normal_of_coatom Hbar hNC hcoatom
  haveI := hHbarNormal
  have hHnormal : H.Normal := by rw [← hcomapHbar]; exact hHbarNormal.comap f
  refine ⟨hHnormal, ?_⟩
  -- index transport: H.index = Hbar.index
  have hkerle : f.ker ≤ H := by rw [hker]; exact hNH
  have hmapidx : (Subgroup.map f H).index = H.index := H.index_map_eq hfsurj hkerle
  have hindexeq : H.index = Hbar.index := by rw [hHbardef]; exact hmapidx.symm
  rw [hindexeq]
  -- now show Hbar.index = p, i.e. Nat.card ((G/N)/Hbar) = p
  haveI hQnt : Nontrivial ((G ⧸ H.normalCore) ⧸ Hbar) :=
    QuotientGroup.nontrivial_iff.mpr hcoatom.1
  haveI hQpgroup : IsPGroup p ((G ⧸ H.normalCore) ⧸ Hbar) := hPgroup.to_quotient Hbar
  set g := QuotientGroup.mk' Hbar with hgdef
  have hgsurj : Function.Surjective g := QuotientGroup.mk'_surjective Hbar
  have hgker : g.ker = Hbar := QuotientGroup.ker_mk' Hbar
  -- every subgroup of the quotient Q is ⊥ or ⊤
  have hsimple : ∀ K : Subgroup ((G ⧸ H.normalCore) ⧸ Hbar), K = ⊥ ∨ K = ⊤ := by
    intro K
    have hHbarK' : Hbar ≤ Subgroup.comap g K := by
      have h1 : g.ker ≤ Subgroup.comap g K := by
        rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
      rwa [hgker] at h1
    have hmapK' : Subgroup.map g (Subgroup.comap g K) = K :=
      Subgroup.map_comap_eq_self_of_surjective hgsurj K
    rcases eq_or_lt_of_le hHbarK' with heq | hlt
    · left
      rw [← hmapK', ← heq, Subgroup.map_eq_bot_iff]
      exact le_of_eq hgker.symm
    · right
      rw [← hmapK', hcoatom.2 (Subgroup.comap g K) hlt]
      exact Subgroup.map_top_of_surjective g hgsurj
  -- Q is a nontrivial finite p-group with only trivial subgroups ⇒ |Q| = p
  haveI hcenterNt : Nontrivial (Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar)) :=
    hQpgroup.center_nontrivial
  have hcenterTop : Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar) = ⊤ := by
    rcases hsimple (Subgroup.center _) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hcenterNt)
    · exact h
  have hcomm : ∀ a b : ((G ⧸ H.normalCore) ⧸ Hbar), a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center _ := by rw [hcenterTop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  letI : CommGroup ((G ⧸ H.normalCore) ⧸ Hbar) := { mul_comm := hcomm }
  haveI hQsimple : IsSimpleGroup ((G ⧸ H.normalCore) ⧸ Hbar) :=
    ⟨fun K _ => hsimple K⟩
  have hprime : (Nat.card ((G ⧸ H.normalCore) ⧸ Hbar)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn0, hn⟩ := hQpgroup.nontrivial_iff_card.mp hQnt
  have hpdvd : p ∣ Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) := by
    rw [hn]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn0)
  have hpeq : p = Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) :=
    (Nat.prime_dvd_prime_iff_eq Fact.out hprime).mp hpdvd
  rw [Subgroup.index_eq_card]
  exact hpeq.symm

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8
-- (Burnside basis theorem / topological Nakayama lemma, Cor. 2.8.4); J. D. Dixon, M. P. F. du
-- Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
--
-- Paper label: Proposition 3.3 / Proposition A.8 (Burnside basis, upper bound).
--
-- The **topological Nakayama upper bound** of the topological Burnside basis theorem, proved from
-- Mathlib together with the sibling theorem `ProPMaximalOpenNormalIndexP`.
--
-- Proof structure:
--   * `gen_finset_of_module` / `exists_gen_finset`: a finite elementary abelian p-group Q = G/Φ(G)
--     of order p^d, viewed as a d-dimensional 𝔽_p-vector space (Additive Q), has an 𝔽_p-basis of
--     size d whose multiplicative image generates Q; hence a generating finset of card ≤ d.
--   * `exists_maximalOpen_ge` (the compactness step): a proper closed subgroup H of a profinite
--     group is contained in a maximal proper open subgroup. Proof: `closedSubgroup_eq_sInf_open`
--     yields a proper open N₀ ⊇ H; its normal core N is open normal, G/N is finite, and a coatom
--     M̄ of the finite subgroup lattice above the (proper) image of N₀ pulls back to a maximal open
--     M ⊇ H (via `IsCoatomic` on the finite group's subgroup lattice).
--   * The Frattini facts (`frattiniOpen_normal`, commutator/p-th-power in Φ(G), G/Φ(G) abelian of
--     exponent p) are re-derived locally from `ProPMaximalOpenNormalIndexP` (to avoid an import
--     cycle with `ProPGeneratorRankFrattini`, which imports this file).
--   * Nakayama assembly: lift an 𝔽_p-basis of G/Φ(G) to a finset S of size ≤ d. The closed subgroup
--     H := closure⟨S⟩ maps ONTO G/Φ(G); if H ≠ G it would sit inside a maximal open M ⊇ Φ(G), whose
--     image in G/Φ(G) is a proper subgroup containing the generators — contradiction. Hence S
--     topologically generates G.




set_option maxHeartbeats 800000
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace ProPTopologicalNakayamaAux

/-- If `Additive Q` is a finite `ZMod p`-module of dimension `d`, then `Q` has a generating
finset of cardinality `≤ d` (an `𝔽ₚ`-basis, mapped back multiplicatively). -/
theorem gen_finset_of_module (p : ℕ) [Fact p.Prime] (Q : Type*) [CommGroup Q] [Finite Q]
    [Module (ZMod p) (Additive Q)] (d : ℕ)
    (hd : Module.finrank (ZMod p) (Additive Q) = d) :
    ∃ T : Finset Q, T.card ≤ d ∧ Subgroup.closure (T : Set Q) = ⊤ := by
  classical
  haveI : Fintype (Additive Q) := Fintype.ofFinite _
  have hsmul : ∀ (c : ZMod p) (a : Additive Q), c • a = (c.val) • a := by
    intro c a; rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  haveI : Fintype ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) :=
    (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinite.fintype
  have hcardι : Fintype.card ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) = d := by
    rw [← Module.finrank_eq_card_basis (Module.Basis.ofVectorSpace (ZMod p) (Additive Q))]
    exact hd
  have hspan : Submodule.span (ZMod p)
      (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) = ⊤ := by
    have h := (Module.Basis.ofVectorSpace (ZMod p) (Additive Q)).span_eq
    rwa [Module.Basis.range_ofVectorSpace] at h
  refine ⟨(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image Additive.toMul,
    ?_, ?_⟩
  · calc ((Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image
              Additive.toMul).card
        ≤ (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.card :=
          Finset.card_image_le
      _ = Fintype.card ↥(Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)) :=
          Set.toFinset_card _
      _ = d := hcardι
  · rw [eq_top_iff]
    intro q _
    have key : ∀ a : Additive Q,
        a ∈ Submodule.span (ZMod p)
          (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) →
        Additive.toMul a ∈ Subgroup.closure
          (↑((Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q)).toFinset.image
            Additive.toMul) : Set Q) := by
      intro a ha'
      induction ha' using Submodule.span_induction with
      | mem x hx =>
          apply Subgroup.subset_closure
          rw [Finset.coe_image, Set.coe_toFinset]
          exact ⟨x, hx, rfl⟩
      | zero => simpa using Subgroup.one_mem _
      | add x y _ _ hx hy => rw [toMul_add]; exact Subgroup.mul_mem _ hx hy
      | smul c x _ hx => rw [hsmul c x, toMul_nsmul]; exact Subgroup.pow_mem _ hx _
    have hmem : (Additive.ofMul q) ∈ Submodule.span (ZMod p)
        (Module.Basis.ofVectorSpaceIndex (ZMod p) (Additive Q) : Set (Additive Q)) := by
      rw [hspan]; exact Submodule.mem_top
    have := key (Additive.ofMul q) hmem
    simpa using this

/-- A finite elementary abelian `p`-group `Q` of order `p^d` has a generating finset of
cardinality `≤ d`. -/
theorem exists_gen_finset (p : ℕ) [Fact p.Prime] (Q : Type*) [CommGroup Q] [Finite Q]
    (hexp : ∀ q : Q, q ^ p = 1) (d : ℕ) (hcard : Nat.card Q = p ^ d) :
    ∃ T : Finset Q, T.card ≤ d ∧ Subgroup.closure (T : Set Q) = ⊤ := by
  have hexpA : ∀ a : Additive Q, (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hexp (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hexpA
  haveI : Fintype (Additive Q) := Fintype.ofFinite _
  haveI : Module.Finite (ZMod p) (Additive Q) :=
    Module.Finite.of_finite (R := ZMod p) (M := Additive Q)
  have hfr : Module.finrank (ZMod p) (Additive Q) = d := by
    have hc := @Module.card_eq_pow_finrank (ZMod p) (Additive Q) _ _ _ _ _
    rw [ZMod.card, ← Nat.card_eq_fintype_card] at hc
    have hcA : Nat.card (Additive Q) = p ^ d := by
      rw [show Nat.card (Additive Q) = Nat.card Q from rfl]; exact hcard
    rw [hcA] at hc
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le hc.symm)
  exact gen_finset_of_module p Q d hfr

/-- **Compactness step.** A proper closed subgroup `H` of a profinite group is contained in a
maximal proper open subgroup. -/
theorem exists_maximalOpen_ge (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (H : Subgroup G) (hHcl : IsClosed (H : Set G)) (hHne : H ≠ ⊤) :
    ∃ M : Subgroup G, IsMaximalOpenSubgroup M ∧ H ≤ M := by
  obtain ⟨_, hcompact, hT2, hTD, _⟩ := hpro
  haveI := hcompact; haveI := hT2; haveI := hTD
  have hHeq : (H : Subgroup G) = sInf {N : Subgroup G | IsOpen (N : Set G) ∧ H ≤ N} :=
    ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨H, hHcl⟩
  obtain ⟨N0, hN0open, hHN0, hN0ne⟩ :
      ∃ N0 : Subgroup G, IsOpen (N0 : Set G) ∧ H ≤ N0 ∧ N0 ≠ ⊤ := by
    by_contra hcon
    push_neg at hcon
    apply hHne
    rw [hHeq, eq_top_iff]
    refine le_sInf ?_
    rintro N ⟨hNopen, hHN⟩
    exact le_of_eq (hcon N hNopen hHN).symm
  haveI : Finite (G ⧸ N0) := Subgroup.quotient_finite_of_isOpen N0 hN0open
  haveI : N0.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hN0closed : IsClosed (N0 : Set G) := Subgroup.isClosed_of_isOpen N0 hN0open
  have hNcl : IsClosed (N0.normalCore : Set G) := Subgroup.normalCore_isClosed N0 hN0closed
  have hNopen : IsOpen (N0.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex N0.normalCore hNcl
  set N := N0.normalCore with hNdef
  have hNle : N ≤ N0 := Subgroup.normalCore_le N0
  haveI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N hNopen
  set π := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hker : π.ker = N := QuotientGroup.ker_mk' N
  set N0bar := Subgroup.map π N0 with hN0bar
  have hcomapN0 : Subgroup.comap π N0bar = N0 := by
    rw [hN0bar, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNle
  have hN0barne : N0bar ≠ ⊤ := by
    intro htop
    apply hN0ne
    have hc : Subgroup.comap π N0bar = Subgroup.comap π ⊤ := by rw [htop]
    rwa [hcomapN0, Subgroup.comap_top] at hc
  obtain ⟨Mbar, hMcoatom, hN0Mbar⟩ :=
    (eq_top_or_exists_le_coatom N0bar).resolve_left hN0barne
  set M := Subgroup.comap π Mbar with hMdef
  have hNM : N ≤ M := by
    have h1 : π.ker ≤ Subgroup.comap π Mbar := by
      rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
    rw [hker] at h1; exact h1
  refine ⟨M, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Subgroup.isOpen_mono hNM hNopen
  · intro htop
    apply hMcoatom.1
    have hmap : Subgroup.map π M = Mbar := Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar
    rw [← hmap, htop]
    exact Subgroup.map_top_of_surjective π hπsurj
  · intro K hKopen hMK
    have hNK : N ≤ K := le_trans hNM hMK
    have hMbarle : Mbar ≤ Subgroup.map π K := by
      have h : Subgroup.map π M ≤ Subgroup.map π K := Subgroup.map_mono (f := π) hMK
      rwa [Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar] at h
    have hcomapK : Subgroup.comap π (Subgroup.map π K) = K := by
      rw [Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNK
    rcases eq_or_lt_of_le hMbarle with heq | hlt
    · left
      rw [← hcomapK, ← heq]
    · right
      rw [← hcomapK, hMcoatom.2 _ hlt, Subgroup.comap_top]
  · calc H ≤ N0 := hHN0
      _ = Subgroup.comap π N0bar := hcomapN0.symm
      _ ≤ Subgroup.comap π Mbar := Subgroup.comap_mono hN0Mbar
      _ = M := hMdef.symm

/-- `Φ(G)` is normal (re-derived locally from R1, to avoid an import cycle with
`ProPGeneratorRankFrattini`). -/
theorem frattiniOpen_normal (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) : (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)`. -/
theorem commutator_mem_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  haveI : IsMulCommutative (G ⧸ H) := IsCyclic.isMulCommutative
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mul_comm' (x : G ⧸ H) (y : G ⧸ H)]
  group

/-- Every `p`-th power lies in `Φ(G)`. -/
theorem pow_mem_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) (x : G) : x ^ p ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one'

/-- `G/Φ(G)` is abelian. -/
theorem frattiniQuotient_comm (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_mem_frattini p G hpro hfg y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattiniQuotient_expp (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfg : TopFinitelyGenerated G) [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_frattini p G hpro hfg x

end ProPTopologicalNakayamaAux

open ProPTopologicalNakayamaAux in
/-- **Topological Nakayama / Burnside basis, upper bound.** For a finitely generated pro-`p`
group `G` whose Frattini quotient has cardinality `p^d`, there is a topological generating
finset of `G` with at most `d` elements (obtained by lifting an `𝔽_p`-basis of `G/Φ(G)`). -/
theorem ProPTopologicalNakayama (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (d : ℕ) (hd : Nat.card (G ⧸ frattiniOpen G) = p ^ d) :
    ∃ S : Finset G, TopologicallyGenerates (↑S : Set G) ∧ S.card ≤ d := by
  classical
  haveI hN : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  haveI hQfin : Finite (G ⧸ frattiniOpen G) :=
    Nat.finite_of_card_ne_zero (by rw [hd]; exact pow_ne_zero d (Fact.out : p.Prime).pos.ne')
  letI : CommGroup (G ⧸ frattiniOpen G) :=
    { mul_comm := frattiniQuotient_comm p G hpro hfg }
  have hexp := frattiniQuotient_expp p G hpro hfg
  obtain ⟨T, hTcard, hTgen⟩ := exists_gen_finset p (G ⧸ frattiniOpen G) hexp d hd
  set π : G →* (G ⧸ frattiniOpen G) := QuotientGroup.mk' (frattiniOpen G) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set sec : (G ⧸ frattiniOpen G) → G := Function.surjInv hπsurj with hsec
  have hsecspec : ∀ t, π (sec t) = t := fun t => Function.surjInv_eq hπsurj t
  set S : Finset G := T.image sec with hS
  refine ⟨S, ?_, by rw [hS]; exact (Finset.card_image_le).trans hTcard⟩
  have hHtop : (Subgroup.closure (↑S : Set G)).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨M, hMmax, hHM⟩ := exists_maximalOpen_ge p G hpro
      ((Subgroup.closure (↑S : Set G)).topologicalClosure)
      (Subgroup.isClosed_topologicalClosure _) hne
    have hΦM : frattiniOpen G ≤ M := by rw [frattiniOpen]; exact sInf_le hMmax
    have hcomap : Subgroup.comap π (Subgroup.map π M) = M := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hΦM
    have hMbarne : Subgroup.map π M ≠ ⊤ := by
      intro htop
      apply hMmax.2.1
      have hc : Subgroup.comap π (Subgroup.map π M) = Subgroup.comap π ⊤ := by rw [htop]
      rwa [hcomap, Subgroup.comap_top] at hc
    have hTM : ∀ t ∈ T, t ∈ Subgroup.map π M := by
      intro t ht
      have hsecmem : sec t ∈ (Subgroup.closure (↑S : Set G)).topologicalClosure := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_closure
        rw [hS, Finset.coe_image]
        exact ⟨t, ht, rfl⟩
      have hmemM : sec t ∈ M := hHM hsecmem
      rw [← hsecspec t]
      exact Subgroup.mem_map_of_mem π hmemM
    have hle : (⊤ : Subgroup (G ⧸ frattiniOpen G)) ≤ Subgroup.map π M := by
      rw [← hTgen, Subgroup.closure_le]
      intro t ht
      exact hTM t (Finset.mem_coe.mp ht)
    exact hMbarne (top_le_iff.mp hle)
  show _root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G) = Set.univ
  rw [← Subgroup.topologicalClosure_coe, hHtop, Subgroup.coe_top]

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8
-- (Burnside basis / topological Nakayama); J. D. Dixon et al., Analytic Pro-p Groups, 2nd ed.,
-- CUP, 1999, Proposition 1.9(ii).
--
-- The only admitted input is the topological Nakayama upper bound `ProPTopologicalNakayama`
-- (∃ a topological generating set of size ≤ dim_{F_p} G/Φ(G)).
-- Everything else is proved from Mathlib and `ProPMaximalOpenNormalIndexP`:
--   * `frattiniOpen_isOpen` / `frattiniOpen_normal`: Φ(G) is open and normal, via the finiteness
--     of the set of maximal open subgroups (each is the kernel of a continuous hom G → 𝔽_p, and a
--     continuous hom into a finite discrete group is determined by its values on a topological
--     generating set, so there are only finitely many);
--   * `frattiniQuotient_card`: G/Φ(G) is a finite elementary abelian p-group of order p^d, d its
--     𝔽_p-dimension (commutators and p-th powers lie in Φ(G) by `ProPMaximalOpenNormalIndexP`, then
--     the ZMod p-module cardinality formula);
--   * LOWER bound d ≤ d(G) (`card_quot_le` + the assembly): the image of any topological
--     generating finset spans the 𝔽_p-vector space G/Φ(G), so any such finset has ≥ d elements.
-- The reverse inequality d(G) ≤ d (lifting an 𝔽_p-basis of G/Φ(G) to topological generators) is
-- the admitted input `ProPTopologicalNakayama`.





set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace ProPGeneratorRankFrattiniAux

/-- Continuous homs to a finite discrete group are determined by their values
on a topologically generating set. -/
theorem eq_of_eqOn_topgen {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [Group F] [TopologicalSpace F] [DiscreteTopology F] [T2Space F]
    (S : Set G) (hS : TopologicallyGenerates S)
    (φ ψ : G →* F) (hφ : Continuous φ) (hψ : Continuous ψ)
    (hagree : Set.EqOn φ ψ S) : φ = ψ := by
  have hgen : Set.EqOn φ ψ (Subgroup.closure S : Set G) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz => exact hagree hz
    | one => simp
    | mul a b _ _ ha hb => simp [map_mul, ha, hb]
    | inv a _ ha => simp [map_inv, ha]
  have hdense : Dense ((Subgroup.closure S : Subgroup G) : Set G) := by
    rw [dense_iff_closure_eq]; exact hS
  exact DFunLike.coe_injective (Continuous.ext_on hdense hφ hψ hgen)

/-- Cardinality bound from a spanning finset of a finite `ZMod p`-module. -/
theorem card_le_of_gen_span {M : Type*} [AddCommGroup M] [Finite M] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) M] (F : Finset M)
    (hgen : ∀ a : M, a ∈ Submodule.span (ZMod p) (↑F : Set M)) :
    Nat.card M ≤ p ^ F.card := by
  haveI : Fintype M := Fintype.ofFinite _
  have hspan : Submodule.span (ZMod p) (↑F : Set M) = ⊤ := Submodule.eq_top_iff'.mpr hgen
  have hcard := @Module.card_eq_pow_finrank (ZMod p) M _ _ _ _ _
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  apply Nat.pow_le_pow_right (Fact.out : p.Prime).pos
  have h := finrank_span_finset_le_card (R := ZMod p) F
  have heq : Set.finrank (ZMod p) (↑F : Set M) = Module.finrank (ZMod p) M := by
    unfold Set.finrank; rw [hspan, finrank_top]
  rwa [heq] at h

/-- The image of a multiplicative closure lands in the `ZMod p`-span of the image. -/
theorem mem_span_of_mem_closure {Q : Type*} [CommGroup Q] {p : ℕ} [Fact p.Prime]
    [Module (ZMod p) (Additive Q)] (F : Set Q) (q : Q)
    (hq : q ∈ Subgroup.closure F) :
    Additive.ofMul q ∈ Submodule.span (ZMod p) ((Additive.ofMul '' F) : Set (Additive Q)) := by
  induction hq using Subgroup.closure_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | one => simpa using Submodule.zero_mem _
  | mul x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | inv x _ hx => exact Submodule.neg_mem _ hx

/-- If a continuous surjection maps `G` onto a finite discrete elementary abelian `p`-group `Q`,
then any topologically generating finset `S` of `G` bounds `|Q| ≤ p ^ |S|`. -/
theorem card_quot_le {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {p : ℕ} [Fact p.Prime] [Finite Q]
    (hexp : ∀ q : Q, q ^ p = 1)
    (π : G →* Q) (hcont : Continuous π) (hsurj : Function.Surjective π)
    (S : Finset G) (hS : TopologicallyGenerates (↑S : Set G)) :
    Nat.card Q ≤ p ^ S.card := by
  classical
  have key : (Set.univ : Set Q) ⊆ (↑(Subgroup.closure (π '' (↑S : Set G))) : Set Q) := by
    have e1 : (Set.univ : Set Q)
        = π '' (_root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G)) := by
      rw [hS, Set.image_univ, hsurj.range_eq]
    rw [e1]
    calc π '' (_root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G))
        ⊆ _root_.closure (π '' ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G)) :=
          image_closure_subset_closure_image hcont
      _ = _root_.closure ((Subgroup.closure (π '' (↑S : Set G)) : Subgroup Q) : Set Q) := by
          rw [← Subgroup.coe_map, MonoidHom.map_closure]
      _ = ((Subgroup.closure (π '' (↑S : Set G)) : Subgroup Q) : Set Q) :=
          (isClosed_discrete _).closure_eq
  have hgen : Subgroup.closure (π '' (↑S : Set G)) = ⊤ := by
    rw [eq_top_iff]; intro x _; exact key (Set.mem_univ x)
  haveI : Fintype Q := Fintype.ofFinite _
  have hexpA : ∀ a : Additive Q, (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hexp (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive Q) := AddCommGroup.zmodModule hexpA
  haveI : Finite (Additive Q) := ‹Finite Q›
  set FA : Finset (Additive Q) := S.image (fun g => (Additive.ofMul (π g))) with hFA
  have hFAcoe : (↑FA : Set (Additive Q)) = Additive.ofMul '' (π '' (↑S : Set G)) := by
    rw [hFA, Finset.coe_image, Set.image_image]
  rw [show Nat.card Q = Nat.card (Additive Q) from rfl]
  refine (card_le_of_gen_span (M := Additive Q) (p := p) FA (fun a => ?_)).trans
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by rw [hFA]; exact Finset.card_image_le))
  have ha : Additive.toMul a ∈ Subgroup.closure (π '' (↑S : Set G)) := by
    rw [hgen]; exact Subgroup.mem_top _
  have hh := mem_span_of_mem_closure (p := p) (π '' (↑S : Set G)) (Additive.toMul a) ha
  rw [← hFAcoe] at hh
  simpa using hh

section
variable (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)

include hpro hfg

/-- Every maximal open subgroup is the kernel of a continuous hom onto `Multiplicative (ZMod p)`. -/
theorem exists_hom_ker (K : Subgroup G) (hK : IsMaximalOpenSubgroup K) :
    ∃ φ : G →* Multiplicative (ZMod p), Continuous φ ∧ φ.ker = K := by
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg K hK
  haveI := hnorm
  have hKopen : IsOpen (K : Set G) := hK.1
  haveI : DiscreteTopology (G ⧸ K) := QuotientGroup.discreteTopology hKopen
  have hcardK : Nat.card (G ⧸ K) = p := by rw [← Subgroup.index_eq_card]; exact hidx
  have hMult : Nat.card (Multiplicative (ZMod p)) = p := by
    simp [Nat.card_eq_fintype_card, ZMod.card]
  let e : (G ⧸ K) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcardK hMult
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' K), ?_, ?_⟩
  · exact (continuous_of_discreteTopology (f := e)).comp QuotientGroup.continuous_mk
  · ext x
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, QuotientGroup.coe_mk']
    rw [show (1 : Multiplicative (ZMod p)) = e 1 from (map_one e).symm, e.apply_eq_iff_eq,
      QuotientGroup.eq_one_iff]

/-- The set of maximal open subgroups is finite. -/
theorem finite_maximalOpen : {K : Subgroup G | IsMaximalOpenSubgroup K}.Finite := by
  obtain ⟨S, hS⟩ := id hfg
  haveI : Finite (↑(S : Set G)) := (S : Set G).toFinite.to_subtype
  rw [Set.finite_coe_iff.symm]
  have hchoose : ∀ K : {K : Subgroup G // IsMaximalOpenSubgroup K},
      ∃ φ : G →* Multiplicative (ZMod p), Continuous φ ∧ φ.ker = K.1 :=
    fun K => exists_hom_ker p G hpro hfg K.1 K.2
  choose φ hcont hker using hchoose
  have hinj : Function.Injective
      (fun K : {K : Subgroup G // IsMaximalOpenSubgroup K} =>
        (fun s : (↑(S : Set G)) => φ K s.1)) := by
    intro K₁ K₂ heq
    have hagree : Set.EqOn (φ K₁) (φ K₂) (S : Set G) := by
      intro s hs
      exact congrFun heq ⟨s, hs⟩
    have := eq_of_eqOn_topgen (S : Set G) hS (φ K₁) (φ K₂) (hcont K₁) (hcont K₂) hagree
    apply Subtype.ext
    rw [← hker K₁, ← hker K₂, this]
  exact Finite.of_injective _ hinj

/-- The topological Frattini subgroup is open. -/
theorem frattiniOpen_isOpen : IsOpen ((frattiniOpen G : Subgroup G) : Set G) := by
  have hfin := finite_maximalOpen p G hpro hfg
  rw [frattiniOpen, Subgroup.coe_sInf]
  exact hfin.isOpen_biInter (fun H hH => hH.1)

/-- The topological Frattini subgroup is normal. -/
theorem frattiniOpen_normal : (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)` (from R1: each maximal open `H` has index `p`, so `G/H`
is abelian). -/
theorem commutator_mem_frattini (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  haveI : IsMulCommutative (G ⧸ H) := IsCyclic.isMulCommutative
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mul_comm' (x : G ⧸ H) (y : G ⧸ H)]
  group

/-- Every `p`-th power lies in `Φ(G)`. -/
theorem pow_mem_frattini (x : G) : x ^ p ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one'

/-- `G/Φ(G)` is abelian. -/
theorem frattiniQuotient_comm [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_mem_frattini p G hpro hfg y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattiniQuotient_expp [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_mem_frattini p G hpro hfg x

/-- `G/Φ(G)` is a finite elementary abelian `p`-group: its cardinality is `p^d`. -/
theorem frattiniQuotient_card :
    ∃ d : ℕ, Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  have hcomm := frattiniQuotient_comm p G hpro hfg
  have hpow_all := frattiniQuotient_expp p G hpro hfg
  obtain ⟨_, hcompact, _, _, _⟩ := id hpro
  haveI := hcompact
  haveI : Finite (G ⧸ frattiniOpen G) :=
    Subgroup.quotient_finite_of_isOpen _ (frattiniOpen_isOpen p G hpro hfg)
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := hcomm }
  have hexp : ∀ a : Additive (G ⧸ frattiniOpen G), (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hpow_all (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive (G ⧸ frattiniOpen G)) := AddCommGroup.zmodModule hexp
  haveI : Fintype (G ⧸ frattiniOpen G) := Fintype.ofFinite _
  haveI : Fintype (Additive (G ⧸ frattiniOpen G)) := Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)), ?_⟩
  have hcard := @Module.card_eq_pow_finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)) _ _ _ _ _
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- Assembled Burnside rank formula (Nakayama upper bound cited). -/
theorem main :
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI hN : (frattiniOpen G).Normal := frattiniOpen_normal p G hpro hfg
  obtain ⟨_, hcompact, _, _, _⟩ := id hpro
  haveI := hcompact
  haveI hQfin : Finite (G ⧸ frattiniOpen G) :=
    Subgroup.quotient_finite_of_isOpen _ (frattiniOpen_isOpen p G hpro hfg)
  haveI hQdisc : DiscreteTopology (G ⧸ frattiniOpen G) :=
    QuotientGroup.discreteTopology (frattiniOpen_isOpen p G hpro hfg)
  have hexp := frattiniQuotient_expp p G hpro hfg
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := frattiniQuotient_comm p G hpro hfg }
  obtain ⟨d, hd⟩ := frattiniQuotient_card p G hpro hfg
  refine ⟨d, ?_, hd⟩
  apply le_antisymm
  · -- dRank G ≤ d  (topological Nakayama, residual)
    obtain ⟨S, hStop, hScard⟩ := ProPTopologicalNakayama p G hpro hfg d hd
    refine le_trans (sInf_le ⟨S, hStop, rfl⟩) ?_
    exact_mod_cast hScard
  · -- d ≤ dRank G  (lower bound, proved)
    apply le_sInf
    rintro n ⟨S, hStop, rfl⟩
    have hb := card_quot_le (Q := G ⧸ frattiniOpen G) hexp
      (QuotientGroup.mk' (frattiniOpen G)) QuotientGroup.continuous_mk
      (QuotientGroup.mk'_surjective _) S hStop
    rw [hd] at hb
    have hle : d ≤ S.card := (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hb
    exact_mod_cast hle

end
end ProPGeneratorRankFrattiniAux

/-- **Proposition 3.3 / A.8, Burnside basis (rank formula).** For a finitely generated pro-`p`
group `G`, the generator rank `d(G)` equals the `𝔽_p`-dimension of the Frattini quotient:
there is `d` with `dRank G = d` and `|G/Φ(G)| = p^d`.  Proved from Mathlib and
`ProPMaximalOpenNormalIndexP` except for the topological Nakayama upper bound, cited from
`ProPTopologicalNakayama`. -/
theorem ProPGeneratorRankFrattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) :
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d :=
  ProPGeneratorRankFrattiniAux.main p G hpro hfg

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8; H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10; J. D. Dixon, M. P. F. du Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
-- Paper label: Proposition 3.3 (first assertion) / Proposition A.8
-- NL statement: For a finitely generated pro-p group G, the Frattini subgroup satisfies Phi(G) = G^p [G,G]; hence every commutator x y x^{-1} y^{-1} and every p-th power x^p lies in Phi(G), the quotient G/Phi(G) is an elementary abelian p-group (an F_p-vector space), and Burnside's basis theorem gives d(G) = dim_{F_p} G/Phi(G): there is a natural number d with d(G) = d and |G/Phi(G)| = p^d.
--
-- This theorem is factored into two cited inputs:
--   * ProPMaximalOpenNormalIndexP: every maximal proper open subgroup is normal of index p;
--   * ProPGeneratorRankFrattini:   d(G) equals the F_p-dimension of the Frattini quotient.
-- Conjuncts (a) [commutators lie in Φ(G)] and (b) [p-th powers lie in Φ(G)] are proved here from
-- ProPMaximalOpenNormalIndexP (each maximal open subgroup H has index p, hence G/H is cyclic of
-- order p, hence abelian of exponent p, so every commutator and every p-th power maps to 1 in G/H;
-- Φ(G) is the intersection of all such H). Conjunct (c) [the rank/cardinality equality] is cited
-- from ProPGeneratorRankFrattini.





set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.3, Burnside basis.** For a finitely generated pro-`p` group `G`, the
quotient `G/Φ(G)` is an elementary abelian `p`-group (all commutators and `p`-th powers lie
in `Φ(G)`), i.e. an `𝔽_p`-vector space, and the generator rank `d(G)` equals its
`𝔽_p`-dimension: there is `d` with `d(G) = d` and `|G/Φ(G)| = p^d`.

Conjuncts (a) and (b) are proved from `ProPMaximalOpenNormalIndexP`; conjunct (c) is
cited from `ProPGeneratorRankFrattini`. -/
theorem ProPBurnsideBasis (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) :
    (∀ x y : G, x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G) ∧
    (∀ x : G, x ^ p ∈ frattiniOpen G) ∧
    ∃ d : ℕ, dRank G = (d : ℕ∞) ∧ Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  refine ⟨?_, ?_, ProPGeneratorRankFrattini p G hpro hfg⟩
  · -- (a) commutators lie in Φ(G)
    intro x y
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro H hH
    obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
    haveI := hnorm
    have hcard : Nat.card (G ⧸ H) = p := hidx
    haveI : Finite (G ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
    haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
    haveI : IsMulCommutative (G ⧸ H) := IsCyclic.isMulCommutative
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [mul_comm' (x : G ⧸ H) (y : G ⧸ H)]
    group
  · -- (b) p-th powers lie in Φ(G)
    intro x
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro H hH
    obtain ⟨hnorm, hidx⟩ := ProPMaximalOpenNormalIndexP p G hpro hfg H hH
    haveI := hnorm
    have hcard : Nat.card (G ⧸ H) = p := hidx
    haveI : Finite (G ⧸ H) :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
    rw [← QuotientGroup.eq_one_iff]
    rw [QuotientGroup.mk_pow]
    rw [← hcard]
    exact pow_card_eq_one'

open scoped NumberField Classical

open Workspace.Types.UnramifiedProPExtension Workspace.Types.ProPGroup

/-- A finite set generating the elementary abelian group `(ℤ/3)^n` (written multiplicatively)
has at least `n` elements: its `𝔽₃`-dimension is a lower bound for the number of generators. -/
private theorem elem_abelian_rank (n : ℕ) (T : Finset (Multiplicative (Fin n → ZMod 3)))
    (hT : Subgroup.closure (↑T : Set (Multiplicative (Fin n → ZMod 3))) = ⊤) :
    n ≤ T.card := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set T' : Finset (Fin n → ZMod 3) := T.image Multiplicative.toAdd with hT'
  have hcard : T'.card = T.card := by
    rw [hT']
    exact Finset.card_image_of_injective _ Multiplicative.toAdd.injective
  have hclos : AddSubgroup.closure (↑T' : Set (Fin n → ZMod 3)) = ⊤ := by
    have h2 := Subgroup.toAddSubgroup'_closure (↑T : Set (Multiplicative (Fin n → ZMod 3)))
    rw [hT] at h2
    have hset : (Multiplicative.ofAdd ⁻¹' (↑T : Set (Multiplicative (Fin n → ZMod 3))) :
        Set (Fin n → ZMod 3)) = (↑T' : Set (Fin n → ZMod 3)) := by
      rw [hT']; ext x; simp
    rw [hset] at h2
    simpa using h2.symm
  have hspan : Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ AddSubgroup.closure (↑T' : Set (Fin n → ZMod 3)) := by
      rw [hclos]; exact AddSubgroup.mem_top x
    exact (AddSubgroup.closure_le
      (Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3))).toAddSubgroup).mpr
      Submodule.subset_span hx
  have hfin : Module.finrank (ZMod 3) (Fin n → ZMod 3) = n := by simp
  calc n = Module.finrank (ZMod 3) (Fin n → ZMod 3) := hfin.symm
    _ = Module.finrank (ZMod 3) ↥(Submodule.span (ZMod 3) (↑T' : Set (Fin n → ZMod 3))) := by
          rw [hspan, finrank_top]
    _ ≤ (↑T' : Set (Fin n → ZMod 3)).toFinset.card := finrank_span_le_card _
    _ = T'.card := by simp
    _ = T.card := hcard

/-- **Proposition 3.8, eqn (5).** Let `F` be a totally real cyclic cubic number field and
`ℓ ≥ 2` an integer. Suppose there is a finite everywhere-unramified Galois extension `M/F`
that is a member of the defining family (`IsFiniteUnramifiedProPExt 3 F M'` for `M'` the image
of `M` as an `IntermediateField F (AlgebraicClosure F)`) whose Galois group is elementary abelian
of rank `ℓ-1` (a group isomorphism `(M' ≃ₐ[F] M') ≃* Multiplicative (Fin (ℓ-1) → ZMod 3)`).
Then the generator rank of `G := galUr 3 F` satisfies `(ℓ - 1 : ℕ∞) ≤ dRank G`. -/
theorem GalUrGeneratorLowerBound
    (F : Type*) [Field F] [NumberField F]
    (hTR : NumberField.IsTotallyReal F) (hGal : IsGalois ℚ F)
    (hdeg : Module.finrank ℚ F = 3)
    (ℓ : ℕ) (hℓ : 2 ≤ ℓ)
    (M' : IntermediateField F (AlgebraicClosure F))
    (hM : IsFiniteUnramifiedProPExt 3 F M')
    (φ : (M' ≃ₐ[F] M') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3)) :
    ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 F) := by
  set L := maxUnramifiedProPExt 3 F with hLdef
  have hle : M' ≤ L := le_sSup hM
  have hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  -- realise `M'` as an intermediate field `M''` of `L = F^{ur,3}`
  set valL := IntermediateField.val (maxUnramifiedProPExt 3 F) with hvalL
  set M'' := IntermediateField.comap valL M' with hM''
  have hmapeq : IntermediateField.map valL M'' = M' := by
    apply IntermediateField.map_comap_eq_self
    rw [hvalL, IntermediateField.fieldRange_val]; exact hle
  -- instances on `M'`
  obtain ⟨hfd, hgalM, _, _⟩ := hM
  haveI := hfd
  letI : NumberField (M' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (M' : Type _))
  haveI : IsGalois F (↥M') := hgalM
  haveI : Normal F (↥M') := inferInstance
  -- field isomorphism `M'' ≃ₐ[F] M'`
  let g : ↥M'' ≃ₐ[F] ↥M' := (M''.equivMap valL).trans (IntermediateField.equivOfEq hmapeq)
  haveI : Normal F (↥M'') := Normal.of_algEquiv g.symm
  haveI : FiniteDimensional F (↥M'') := LinearEquiv.finiteDimensional g.symm.toLinearEquiv
  haveI : Normal F (↥L) := hnorm
  haveI : DiscreteTopology (↥M'' ≃ₐ[F] ↥M'') :=
    krullTopology_discreteTopology_of_finiteDimensional F ↥M''
  -- restriction homomorphism `Gal(L/F) ↠ Gal(M''/F)`, continuous and surjective
  let ρ₁ : (↥L ≃ₐ[F] ↥L) →* (↥M'' ≃ₐ[F] ↥M'') := AlgEquiv.restrictNormalHom ↥M''
  have hρ₁surj : Function.Surjective ρ₁ :=
    AlgEquiv.restrictNormalHom_surjective (K₁ := ↥M'') ↥L
  have hρ₁cont : Continuous ⇑ρ₁ := InfiniteGalois.restrictNormalHom_continuous M''
  -- group isomorphism `Gal(M''/F) ≃* (ℤ/3)^{ℓ-1}`
  let e : (↥M'' ≃ₐ[F] ↥M'') ≃* Multiplicative (Fin (ℓ - 1) → ZMod 3) :=
    (AlgEquiv.autCongr g).trans φ
  -- reduce `dRank` to a lower bound on the cardinality of any topological generating set
  show ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (↥L ≃ₐ[F] ↥L)
  rw [dRank]
  apply le_sInf
  rintro m ⟨S, hgen, rfl⟩
  rw [Nat.cast_le]
  have hgen' : _root_.closure (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) :
      Set (↥L ≃ₐ[F] ↥L)) = Set.univ := hgen
  -- the image of `S` topologically (hence, by discreteness, algebraically) generates `Gal(M''/F)`
  have hgenT1 : Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M'')) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨x, rfl⟩ := hρ₁surj y
    have hxA : x ∈ _root_.closure
        (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L)) := by
      rw [hgen']; exact Set.mem_univ x
    have h1 : ρ₁ x ∈ _root_.closure
        (ρ₁ '' (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L))) :=
      image_closure_subset_closure_image hρ₁cont (Set.mem_image_of_mem ρ₁ hxA)
    have h2 : (ρ₁ '' (↑(Subgroup.closure (↑S : Set (↥L ≃ₐ[F] ↥L))) : Set (↥L ≃ₐ[F] ↥L)))
        = (↑(Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M''))) :
          Set (↥M'' ≃ₐ[F] ↥M'')) := by
      rw [← Subgroup.coe_map, MonoidHom.map_closure]
      congr 1
      rw [Finset.coe_image]
    rw [h2, (isClosed_discrete _).closure_eq] at h1
    exact h1
  -- transport the generating set through the group isomorphism `e`
  have hgenT0 : Subgroup.closure
      (↑((S.image ρ₁).image e) : Set (Multiplicative (Fin (ℓ - 1) → ZMod 3))) = ⊤ := by
    have hmap : Subgroup.map e.toMonoidHom
        (Subgroup.closure (↑(S.image ρ₁) : Set (↥M'' ≃ₐ[F] ↥M''))) =
        Subgroup.closure (↑((S.image ρ₁).image e) :
          Set (Multiplicative (Fin (ℓ - 1) → ZMod 3))) := by
      rw [MonoidHom.map_closure]; congr 1; simp [Finset.coe_image]
    rw [hgenT1, Subgroup.map_top_of_surjective _ e.surjective] at hmap
    exact hmap.symm
  -- the elementary abelian rank bound closes the goal
  have hEA : (ℓ - 1) ≤ ((S.image ρ₁).image e).card := elem_abelian_rank (ℓ - 1) _ hgenT0
  have hc1 : ((S.image ρ₁).image e).card ≤ (S.image ρ₁).card := Finset.card_image_le
  have hc2 : (S.image ρ₁).card ≤ S.card := Finset.card_image_le
  omega

/-!
# From a polynomial bound on the `i`-th prime `≡ 1 (mod 3)` to the `O(ℓ log ℓ)` log-sum

Reduction of the `PrimesOneModThreeLogSum` estimate (PNT in arithmetic progressions) to the
much smaller quantitative bound `Workspace.ProofLemmas.PrimesOneModThreePolyBound`
("the `i`-th prime `≡ 1 (mod 3)` is at most `(i+2)^A` for some absolute `A`").

Given that bound, `∑_{i < ℓ} log pᵢ ≤ ℓ · A · log(ℓ+1) ≤ 2A · ℓ log ℓ` for `ℓ ≥ 2`, using
`ℓ + 1 ≤ ℓ²`.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PrimesOneModThreeReduction

/-- The predicate "prime and `≡ 1 (mod 3)`". -/
abbrev POne : ℕ → Prop := fun n => n.Prime ∧ n % 3 = 1

/-- **Reduction.**  A polynomial bound on the `i`-th prime `≡ 1 (mod 3)` gives the
`O(ℓ log ℓ)` bound on the sum of the logarithms of the first `ℓ` of them. -/
theorem logSum_le_of_poly_bound
    (A : ℕ) (hA : 0 < A) (hbd : ∀ i : ℕ, Nat.nth POne i ≤ (i + 2) ^ A) :
    ∀ ℓ : ℕ, 2 ≤ ℓ →
      (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth POne i : ℝ)))
        ≤ (2 * A : ℝ) * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  intro ℓ hℓ
  have hℓR : (2 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ
  have hlogℓ : (0 : ℝ) < Real.log (ℓ : ℝ) := Real.log_pos (by linarith)
  -- each term is at most `A * log (ℓ + 1)`
  have hterm : ∀ i ∈ Finset.range ℓ,
      Real.log ((Nat.nth POne i : ℝ)) ≤ (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : ((Nat.nth POne i : ℕ) : ℝ) ≤ (((i + 2) ^ A : ℕ) : ℝ) := by
      exact_mod_cast hbd i
    have h2 : (((i + 2) ^ A : ℕ) : ℝ) ≤ (((ℓ : ℝ) + 1)) ^ A := by
      push_cast
      have : ((i : ℝ) + 2) ≤ (ℓ : ℝ) + 1 := by
        have : (i : ℝ) + 1 ≤ (ℓ : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hi
        linarith
      gcongr
    have h3 : ((Nat.nth POne i : ℕ) : ℝ) ≤ ((ℓ : ℝ) + 1) ^ A := le_trans h1 h2
    calc Real.log ((Nat.nth POne i : ℝ))
        ≤ Real.log (((ℓ : ℝ) + 1) ^ A) := by
          rcases eq_or_lt_of_le (Nat.cast_nonneg (Nat.nth POne i) : (0:ℝ) ≤ _) with h0 | h0
          · rw [← h0, Real.log_zero]
            have : (0 : ℝ) ≤ Real.log (((ℓ : ℝ) + 1) ^ A) := by
              apply Real.log_nonneg
              have : (1 : ℝ) ≤ (ℓ : ℝ) + 1 := by linarith
              exact one_le_pow₀ this
            exact this
          · exact Real.log_le_log h0 h3
      _ = (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := by
          rw [Real.log_pow]
  -- and `log (ℓ + 1) ≤ 2 log ℓ` for `ℓ ≥ 2`
  have hlog2 : Real.log ((ℓ : ℝ) + 1) ≤ 2 * Real.log (ℓ : ℝ) := by
    have h1 : (ℓ : ℝ) + 1 ≤ (ℓ : ℝ) ^ 2 := by nlinarith
    calc Real.log ((ℓ : ℝ) + 1) ≤ Real.log ((ℓ : ℝ) ^ 2) := Real.log_le_log (by linarith) h1
      _ = 2 * Real.log (ℓ : ℝ) := by rw [Real.log_pow]; push_cast; ring
  calc (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth POne i : ℝ)))
      ≤ ∑ _i ∈ Finset.range ℓ, (A : ℝ) * Real.log ((ℓ : ℝ) + 1) := Finset.sum_le_sum hterm
    _ = (ℓ : ℝ) * ((A : ℝ) * Real.log ((ℓ : ℝ) + 1)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ (ℓ : ℝ) * ((A : ℝ) * (2 * Real.log (ℓ : ℝ))) := by
        have hA0 : (0 : ℝ) ≤ (A : ℝ) := Nat.cast_nonneg _
        have hl0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
        gcongr
    _ = (2 * A : ℝ) * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by ring

end Workspace.ProofLemmas.PrimesOneModThreeReduction

/-!
# An elementary Mertens theorem for primes `≡ 1 (mod 3)`

Development toward the polynomial bound `PrimesOneModThreePolyBound` (the `i`-th prime `≡ 1 (mod 3)`
is polynomially bounded).  Everything here is elementary arithmetic over `ℕ`; no algebraic number
theory is used, although the underlying object is the ideal-counting function of `ℚ(√-3)`:

* `chi` — the nontrivial character mod `3`;
* `r = 1 * chi` — `r n` is the number of ideals of `𝓞_{ℚ(√-3)}` of norm `n`;
* `A N = ∑_{n ≤ N} r n`, with `N/2 ≤ A N ≤ N` (`A_ge`, `A_le`) proved by summation by parts,
  using only that the partial sums of `chi` lie in `{0, 1}`.  This is where the positivity of
  `L(1, χ)` enters, in completely elementary form;
* `swap`, `hyp_symm` — the Dirichlet divisor-sum swap and the symmetry of the hyperbola region;
* `T_eq` — `∑_{n ≤ N} r(n) log n = ∑_{k ≤ N} Λ(k)(1 + χ(k)) A(⌊N/k⌋)`, the summatory form of
  `ζ_K'/ζ_K`, obtained by triple-sum rearrangement (no multiplicativity needed);
* `T_le`, `T_ge` — `(N/2) log N − N ≤ ∑_{n≤N} r(n) log n ≤ N log N`;
* `mertens_lower` — hence `∑_{k ≤ N} Λ(k)(1+χ(k))/k ≥ (1/2) log N − 1`.
-/

open Finset

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.MertensThreeMod

/-- The nontrivial character mod `3`, as an integer-valued function. -/
def chi (n : ℕ) : ℤ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

@[simp] theorem chi_one : chi 1 = 1 := by decide

/-- `chi` is completely multiplicative. -/
theorem chi_mul (m n : ℕ) : chi (m * n) = chi m * chi n := by
  have h : (m * n) % 3 = (m % 3) * (n % 3) % 3 := Nat.mul_mod m n 3
  have hm : m % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hn : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases hm' : (m % 3) <;> interval_cases hn' : (n % 3) <;>
    simp [chi, h, hm', hn']

/-- The ideal-counting function of `ℚ(√-3)`: `r n = ∑_{d ∣ n} χ(d)`. -/
def r (n : ℕ) : ℤ := ∑ d ∈ n.divisors, chi d

/-- The summatory function `A N = ∑_{n ≤ N} r n`. -/
def A (N : ℕ) : ℤ := ∑ n ∈ Finset.Icc 1 N, r n

/-- For `1 ≤ n ≤ N`, the divisors of `n` are exactly the `d ∈ [1, N]` dividing `n`. -/
theorem divisors_eq_filter {n N : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ N) :
    n.divisors = (Finset.Icc 1 N).filter (fun d => d ∣ n) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨hd, hn0⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun h => by simp [h] at hd; omega),
      le_trans (Nat.le_of_dvd (by omega) hd) h2⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, by omega⟩

/-- The number of multiples of `d` in `[1, N]` is `⌊N/d⌋`. -/
theorem card_multiples_Icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  classical
  rw [← Nat.card_multiples' N d]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hd⟩; exact ⟨by omega, by omega, hd⟩
  · rintro ⟨h1, h2, hd⟩; exact ⟨⟨by omega, by omega⟩, hd⟩

/-- `A N = ∑_{d ≤ N} χ(d) ⌊N/d⌋`. -/
theorem A_eq (N : ℕ) : A N = ∑ d ∈ Finset.Icc 1 N, chi d * (N / d : ℕ) := by
  classical
  unfold A r
  have hinner : ∀ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, chi d
      = ∑ d ∈ Finset.Icc 1 N, (if d ∣ n then chi d else 0) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    rw [divisors_eq_filter hn.1 hn.2, Finset.sum_filter]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_multiples_Icc, nsmul_eq_mul, mul_comm]

/-! ### Partial sums of `chi` and summation by parts -/

/-- Partial sums of `chi`. -/
def X (k : ℕ) : ℤ := ∑ d ∈ Finset.Icc 1 k, chi d

@[simp] theorem X_zero : X 0 = 0 := by simp [X]

theorem X_succ (k : ℕ) : X (k + 1) = X k + chi (k + 1) := by
  rw [X, X, Finset.sum_Icc_succ_top (by omega)]

/-- `X k = 1` if `k ≡ 1 (mod 3)` and `0` otherwise. -/
theorem X_eq (k : ℕ) : X k = if k % 3 = 1 then 1 else 0 := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [X_succ, ih, chi]
      have h : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
      have h2 : (n + 1) % 3 = (n % 3 + 1) % 3 := by omega
      interval_cases hn : (n % 3) <;> simp [h2, hn]

theorem X_nonneg (k : ℕ) : 0 ≤ X k := by rw [X_eq]; split <;> norm_num

theorem X_le_one (k : ℕ) : X k ≤ 1 := by rw [X_eq]; split <;> norm_num

@[simp] theorem X_one : X 1 = 1 := by rw [X_eq]; norm_num

/-- **Summation by parts.** -/
theorem abel (g : ℕ → ℤ) : ∀ N : ℕ,
    ∑ d ∈ Finset.Icc 1 (N + 1), chi d * g d
      = X (N + 1) * g (N + 1) + ∑ d ∈ Finset.Icc 1 N, X d * (g d - g (d + 1)) := by
  intro N
  induction N with
  | zero => simp [X_eq]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), ih,
        Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), X_succ (n + 1)]
      ring

/-- Telescoping. -/
theorem telescope (g : ℕ → ℤ) : ∀ M : ℕ,
    ∑ d ∈ Finset.Icc 1 M, (g d - g (d + 1)) = g 1 - g (M + 1) := by
  intro M
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
      ring

/-! ### `A N ≍ N` -/

theorem A_le (N : ℕ) : A N ≤ N := by
  rcases N with _ | M
  · simp [A]
  set g : ℕ → ℤ := fun d => ((M + 1) / d : ℕ) with hg
  have hganti : ∀ d, 1 ≤ d → g (d + 1) ≤ g d := by
    intro d hd
    simp only [hg]
    exact_mod_cast Nat.div_le_div_left (by omega) (by omega)
  have hg0 : ∀ d, 0 ≤ g d := fun d => by positivity
  have hkey : A (M + 1) = ∑ d ∈ Finset.Icc 1 (M + 1), chi d * g d := A_eq (M + 1)
  rw [hkey, abel g M]
  have h1 : X (M + 1) * g (M + 1) ≤ g (M + 1) := by
    nlinarith [X_le_one (M + 1), X_nonneg (M + 1), hg0 (M + 1)]
  have h2 : ∑ d ∈ Finset.Icc 1 M, X d * (g d - g (d + 1))
      ≤ ∑ d ∈ Finset.Icc 1 M, (g d - g (d + 1)) := by
    refine Finset.sum_le_sum fun d hd => ?_
    rw [Finset.mem_Icc] at hd
    have := hganti d hd.1
    nlinarith [X_le_one d, X_nonneg d]
  rw [telescope g M] at h2
  have hg1 : g 1 = ((M + 1 : ℕ) : ℤ) := by simp [hg]
  linarith [h1, h2, hg1.le, hg1.ge]

theorem A_ge (N : ℕ) : (N : ℤ) ≤ 2 * A N := by
  rcases N with _ | M
  · simp [A]
  set g : ℕ → ℤ := fun d => ((M + 1) / d : ℕ) with hg
  have hganti : ∀ d, 1 ≤ d → g (d + 1) ≤ g d := by
    intro d hd
    simp only [hg]
    exact_mod_cast Nat.div_le_div_left (by omega) (by omega)
  have hg0 : ∀ d, 0 ≤ g d := fun d => by positivity
  have hkey : A (M + 1) = ∑ d ∈ Finset.Icc 1 (M + 1), chi d * g d := A_eq (M + 1)
  rw [hkey, abel g M]
  -- every term is nonnegative, and the `d = 1` term is `g 1 - g 2`
  have hterms : ∀ d ∈ Finset.Icc 1 M, 0 ≤ X d * (g d - g (d + 1)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have := hganti d hd.1
    nlinarith [X_nonneg d]
  have hfirst : X (M + 1) * g (M + 1) ≥ 0 := by nlinarith [X_nonneg (M + 1), hg0 (M + 1)]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · -- `N = 1`
    simp [hg, X_eq]
  · have h1mem : (1 : ℕ) ∈ Finset.Icc 1 M := by simp only [Finset.mem_Icc]; omega
    have hsum : X 1 * (g 1 - g 2) ≤ ∑ d ∈ Finset.Icc 1 M, X d * (g d - g (d + 1)) :=
      Finset.single_le_sum hterms h1mem
    have hg1 : g 1 = ((M + 1 : ℕ) : ℤ) := by simp [hg]
    have hg2 : g 2 = (((M + 1) / 2 : ℕ) : ℤ) := by simp [hg]
    have hdiv2 : (M + 1) ≤ 2 * ((M + 1) - (M + 1) / 2) := by omega
    rw [X_one, one_mul] at hsum
    have : ((M + 1 : ℕ) : ℤ) - (((M + 1) / 2 : ℕ) : ℤ) ≤ ∑ d ∈ Finset.Icc 1 M,
        X d * (g d - g (d + 1)) := by rw [← hg1, ← hg2]; exact hsum
    have hcast : ((M + 1 : ℕ) : ℤ) ≤ 2 * (((M + 1 : ℕ) : ℤ) - (((M + 1) / 2 : ℕ) : ℤ)) := by
      push_cast
      omega
    linarith

/-! ### The Dirichlet swap -/

/-- Sums over `n ≤ N` and divisors `d ∣ n` are sums over pairs `(d, e)` with `d·e ≤ N`. -/
theorem swap {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℕ → ℕ → M) :
    ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors, F d (n / d)
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), F d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1 / x.2⟩) (fun y => ⟨y.1 * y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨h1, h2⟩, hd, _⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    refine ⟨⟨hd0, le_trans (Nat.le_of_dvd (by omega) hd) h2⟩, ?_, ?_⟩
    · exact Nat.one_le_div_iff hd0 |>.mpr (Nat.le_of_dvd (by omega) hd)
    · exact Nat.div_le_div_right h2 |>.trans (le_refl _)
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hy ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hy
    refine ⟨⟨Nat.mul_pos hd1 he1, ?_⟩, ⟨e, rfl⟩, by positivity⟩
    rw [mul_comm]
    exact (Nat.le_div_iff_mul_le (by omega)).mp heN
  · rintro ⟨n, d⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hx
    obtain ⟨⟨h1, h2⟩, hd, _⟩ := hx
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
    simp [Nat.mul_div_cancel' hd]
  · rintro ⟨d, e⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hy
    have hd0 : 0 < d := hy.1.1
    simp [Nat.mul_div_cancel_left e hd0]
  · rintro ⟨n, d⟩ _
    rfl

/-- The hyperbola region is symmetric. -/
theorem hyp_symm {M : Type*} [AddCommMonoid M] (N : ℕ) (G : ℕ → ℕ → M) :
    ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), G d e
      = ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 (N / e), G d e := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun x => ⟨x.2, x.1⟩) (fun y => ⟨y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨d, e⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx ⊢
    obtain ⟨⟨hd1, hdN⟩, he1, heN⟩ := hx
    have hde : d * e ≤ N := by
      rw [mul_comm]; exact (Nat.le_div_iff_mul_le (by omega)).mp heN
    have hle : e ≤ N := le_trans (Nat.le_mul_of_pos_left e (by omega)) hde
    exact ⟨⟨he1, hle⟩, hd1, (Nat.le_div_iff_mul_le (by omega)).mpr hde⟩
  · rintro ⟨e, d⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hy ⊢
    obtain ⟨⟨he1, heN⟩, hd1, hdN⟩ := hy
    have hde : d * e ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hdN
    have hle : d ≤ N := le_trans (Nat.le_mul_of_pos_right d (by omega)) hde
    refine ⟨⟨hd1, hle⟩, he1, (Nat.le_div_iff_mul_le (by omega)).mpr ?_⟩
    rw [mul_comm]; exact hde
  · rintro ⟨d, e⟩ _; rfl
  · rintro ⟨e, d⟩ _; rfl
  · rintro ⟨d, e⟩ _; rfl

/-! ### The main identity -/

open ArithmeticFunction in
/-- `∑_{e ≤ M} log e = ∑_{k ≤ M} Λ(k)⌊M/k⌋`. -/
theorem sumLog_eq (M : ℕ) :
    ∑ e ∈ Finset.Icc 1 M, Real.log e = ∑ k ∈ Finset.Icc 1 M, Λ k * ((M / k : ℕ) : ℝ) := by
  have h1 : ∑ e ∈ Finset.Icc 1 M, Real.log e
      = ∑ e ∈ Finset.Icc 1 M, ∑ k ∈ e.divisors, Λ k :=
    Finset.sum_congr rfl fun e _ => vonMangoldt_sum.symm
  rw [h1, swap M (fun a _ => Λ a)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
  simp [mul_comm]

open ArithmeticFunction in
/-- The Dirichlet-series identity in summatory form:
`∑_{n ≤ N} r(n) log n = ∑_{k ≤ N} Λ(k)(1 + χ(k)) A(⌊N/k⌋)`. -/
theorem T_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n
      = ∑ k ∈ Finset.Icc 1 N, (Λ k * (1 + (chi k : ℝ))) * ((A (N / k) : ℤ) : ℝ) := by
  classical
  -- unfold `r` and reindex as a sum over pairs
  have step1 : ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n
      = ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
          ((chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e) := by
    rw [← swap N (fun d e => (chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_Icc] at hn
    rw [r, Int.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [Nat.mem_divisors] at hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd.1 (by omega)
    have hnd : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hd.1) hd0
    have hd0' : ((d : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr hd0).ne'
    have hnd' : (((n / d : ℕ) : ℕ) : ℝ) ≠ 0 := (Nat.cast_pos.mpr hnd).ne'
    have hlog : Real.log (n : ℝ) = Real.log (d : ℝ) + Real.log ((n / d : ℕ) : ℝ) := by
      rw [← Real.log_mul hd0' hnd']
      congr 1
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hd.1]
    rw [hlog]
    ring
  have hsplit : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d),
        ((chi d : ℝ) * Real.log d + (chi d : ℝ) * Real.log e)
      = (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
        + (∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_add_distrib
  -- the two halves
  have hT1 : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d
      = ∑ k ∈ Finset.Icc 1 N, (Λ k * (chi k : ℝ)) * ((A (N / k) : ℤ) : ℝ) := by
    have hcol : ∀ d ∈ Finset.Icc 1 N,
        (∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
          = ∑ k ∈ d.divisors,
              ((chi (k * (d / k)) : ℝ) * Λ k * (((N / (k * (d / k))) : ℕ) : ℝ)) := by
      intro d hd
      rw [Finset.mem_Icc] at hd
      have hinner : ∀ k ∈ d.divisors,
          ((chi (k * (d / k)) : ℝ) * Λ k * (((N / (k * (d / k))) : ℕ) : ℝ))
            = (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Λ k := by
        intro k hk
        rw [Nat.mem_divisors] at hk
        rw [Nat.mul_div_cancel' hk.1]
        ring
      have hL : (∑ _e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log d)
          = ((N / d : ℕ) : ℝ) * ((chi d : ℝ) * Real.log d) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        ring
      have hR : (∑ k ∈ d.divisors, (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Λ k)
          = (chi d : ℝ) * ((N / d : ℕ) : ℝ) * Real.log d := by
        rw [← Finset.mul_sum, vonMangoldt_sum]
      rw [Finset.sum_congr rfl hinner, hR, hL]
      ring
    rw [Finset.sum_congr rfl hcol,
      swap N (fun k m => (chi (k * m) : ℝ) * Λ k * (((N / (k * m)) : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [A_eq, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [chi_mul, ← Nat.div_div_eq_div_mul]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  have hT2 : ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e
      = ∑ k ∈ Finset.Icc 1 N, Λ k * ((A (N / k) : ℤ) : ℝ) := by
    have hcol : ∀ d ∈ Finset.Icc 1 N,
        (∑ e ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Real.log e)
          = ∑ k ∈ Finset.Icc 1 (N / d), (chi d : ℝ) * Λ k * (((N / (d * k)) : ℕ) : ℝ) := by
      intro d hd
      rw [← Finset.mul_sum, sumLog_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Nat.div_div_eq_div_mul]
      ring
    rw [Finset.sum_congr rfl hcol,
      hyp_symm N (fun d k => (chi d : ℝ) * Λ k * (((N / (d * k)) : ℕ) : ℝ))]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [A_eq, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [mul_comm d k, ← Nat.div_div_eq_div_mul]
    simp only [Int.cast_mul, Int.cast_natCast]
    ring
  rw [step1, hsplit, hT1, hT2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ### Bounds on `T` -/

/-- General summation by parts. -/
theorem abel_gen (a g : ℕ → ℝ) : ∀ N : ℕ,
    ∑ d ∈ Finset.Icc 1 (N + 1), a d * g d
      = (∑ d ∈ Finset.Icc 1 (N + 1), a d) * g (N + 1)
        + ∑ d ∈ Finset.Icc 1 N, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) := by
  intro N
  induction N with
  | zero => simp
  | succ n ih =>
      have e1 : ∑ x ∈ Finset.Icc 1 (n + 1), a x = (∑ x ∈ Finset.Icc 1 n, a x) + a (n + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e2 : ∑ x ∈ Finset.Icc 1 (n + 1 + 1), a x
          = (∑ x ∈ Finset.Icc 1 (n + 1), a x) + a (n + 1 + 1) :=
        Finset.sum_Icc_succ_top (by omega) _
      have e3 : ∑ d ∈ Finset.Icc 1 (n + 1), (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1))
          = (∑ d ∈ Finset.Icc 1 n, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)))
            + (∑ e ∈ Finset.Icc 1 (n + 1), a e) * (g (n + 1) - g (n + 1 + 1)) :=
        Finset.sum_Icc_succ_top (by omega) _
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1 + 1), ih, e3, e2, e1]
      ring

theorem log_succ_sub_le (d : ℕ) (hd : 1 ≤ d) :
    Real.log ((d : ℝ) + 1) - Real.log d ≤ 1 / d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : Real.log ((d : ℝ) + 1) - Real.log d = Real.log (((d : ℝ) + 1) / d) := by
    rw [Real.log_div (by linarith) (by linarith)]
  rw [h1]
  have h2 : Real.log (((d : ℝ) + 1) / d) ≤ ((d : ℝ) + 1) / d - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : ((d : ℝ) + 1) / d - 1 = 1 / d := by
    field_simp
    ring
  linarith

/-- `T N ≥ (N/2) log N - N`. -/
theorem T_ge (N : ℕ) :
    ((N : ℝ) / 2) * Real.log N - N ≤ ∑ n ∈ Finset.Icc 1 N, (r n : ℝ) * Real.log n := by
  rcases N with _ | M
  · simp
  rw [abel_gen (fun n => (r n : ℝ)) (fun n => Real.log n) M]
  have hAN : (∑ d ∈ Finset.Icc 1 (M + 1), (r d : ℝ)) = ((A (M + 1) : ℤ) : ℝ) := by
    rw [A, Int.cast_sum]
  rw [hAN]
  have hlog0 : (0 : ℝ) ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
  have hAge : ((M + 1 : ℕ) : ℝ) ≤ 2 * ((A (M + 1) : ℤ) : ℝ) := by exact_mod_cast A_ge (M + 1)
  have hterm : ∀ d ∈ Finset.Icc 1 M,
      (-1 : ℝ) ≤ (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) * (Real.log d - Real.log ((d : ℕ) + 1 : ℕ)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hcast : (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) = ((A d : ℤ) : ℝ) := by rw [A, Int.cast_sum]
    rw [hcast]
    have hAd : ((A d : ℤ) : ℝ) ≤ (d : ℝ) := by exact_mod_cast A_le d
    have hAd0 : (0 : ℝ) ≤ ((A d : ℤ) : ℝ) := by
      have h1 : (0 : ℤ) ≤ (d : ℤ) := by positivity
      have h2 : (0 : ℤ) ≤ 2 * A d := le_trans h1 (A_ge d)
      exact_mod_cast (by omega : (0 : ℤ) ≤ A d)
    have hlogd : Real.log (((d : ℕ) + 1 : ℕ) : ℝ) - Real.log d ≤ 1 / d := by
      have := log_succ_sub_le d hd.1
      push_cast
      exact this
    have hmono : Real.log d ≤ Real.log (((d : ℕ) + 1 : ℕ) : ℝ) := by
      apply Real.log_le_log hd0
      push_cast
      linarith
    have hkey : (d : ℝ) * (Real.log (((d : ℕ) + 1 : ℕ) : ℝ) - Real.log d) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hlogd (le_of_lt hd0)
      rwa [mul_one_div, div_self (ne_of_gt hd0)] at h
    nlinarith [hkey]
  have hsum : (-(M : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 M,
      (∑ e ∈ Finset.Icc 1 d, (r e : ℝ)) * (Real.log d - Real.log ((d : ℕ) + 1 : ℕ)) := by
    have := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Nat.card_Icc] at this
    simpa using this
  have hAge' : ((M + 1 : ℕ) : ℝ) / 2 ≤ ((A (M + 1) : ℤ) : ℝ) := by linarith
  have hmul : (((M + 1 : ℕ) : ℝ) / 2) * Real.log ((M + 1 : ℕ) : ℝ)
      ≤ ((A (M + 1) : ℤ) : ℝ) * Real.log ((M + 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_right hAge' hlog0
  have hM : (0 : ℝ) ≤ (M : ℝ) := by positivity
  push_cast at hmul hsum ⊢
  linarith

/-! ### Mertens-type lower bound -/

open ArithmeticFunction in
/-- The twisted von Mangoldt function of `ℚ(√-3)`. -/
noncomputable def LK (k : ℕ) : ℝ := Λ k * (1 + (chi k : ℝ))

theorem LK_nonneg (k : ℕ) : 0 ≤ LK k := by
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (0 : ℝ) ≤ 1 + (chi k : ℝ) := by
    rw [chi]
    split
    · norm_num
    · split <;> norm_num
  exact mul_nonneg h1 h2

theorem LK_le_two_vonMangoldt (k : ℕ) : LK k ≤ 2 * ArithmeticFunction.vonMangoldt k := by
  have h1 : 0 ≤ ArithmeticFunction.vonMangoldt k := ArithmeticFunction.vonMangoldt_nonneg
  have h2 : (1 : ℝ) + (chi k : ℝ) ≤ 2 := by
    rw [chi]
    split
    · norm_num
    · split <;> norm_num
  rw [LK]
  nlinarith

/-- `∑_{k ≤ N} Λ_K(k)/k ≥ (1/2) log N - 1`. -/
theorem mertens_lower (N : ℕ) :
    (1 / 2 : ℝ) * Real.log N - 1 ≤ ∑ k ∈ Finset.Icc 1 N, LK k / k := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hT := T_ge N
  rw [T_eq N] at hT
  have hb : ∀ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k * (1 + (chi k : ℝ)))
        * ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) * (LK k / k) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hA : ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) / k := by
      have h1 : ((A (N / k) : ℤ) : ℝ) ≤ ((N / k : ℕ) : ℝ) := by
        have h := (Int.cast_le (R := ℝ)).mpr (A_le (N / k))
        rwa [Int.cast_natCast] at h
      have h2 : ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / k := Nat.cast_div_le
      linarith
    have hLK := LK_nonneg k
    have : (N : ℝ) * (LK k / k) = LK k * ((N : ℝ) / k) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hA hLK
  have hstep : ∑ k ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt k * (1 + (chi k : ℝ)))
      * ((A (N / k) : ℤ) : ℝ) ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, LK k / k := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hb
  have hfin := le_trans hT hstep
  have hS : (N : ℝ) * ((1 / 2 : ℝ) * Real.log N - 1)
      ≤ (N : ℝ) * ∑ k ∈ Finset.Icc 1 N, LK k / k := by nlinarith [hfin]
  exact le_of_mul_le_mul_left hS hN0

/-! ### Mertens upper bound (all primes), from Chebyshev -/

open ArithmeticFunction Chebyshev in
theorem psi_eq_sum (N : ℕ) : ψ (N : ℝ) = ∑ k ∈ Finset.Icc 1 N, Λ k := by
  rw [Chebyshev.psi, Nat.floor_natCast]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

open ArithmeticFunction in
/-- `∑_{k ≤ N} Λ(k)/k ≤ log N + (log 4 + 4)`. -/
theorem mertens_upper (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, Λ k / k ≤ Real.log N + (Real.log 4 + 4) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- lower bound for the divisor sum
  have hlow : (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k) - (∑ k ∈ Finset.Icc 1 N, Λ k)
      ≤ ∑ k ∈ Finset.Icc 1 N, Λ k * ((N / k : ℕ) : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk.1
    have hfl : (N : ℝ) / k - 1 ≤ ((N / k : ℕ) : ℝ) := by
      have hk' : 0 < k := by omega
      have hnat : N < k * (N / k) + k := by
        have hdm := Nat.div_add_mod N k
        have hmod := Nat.mod_lt N hk'
        omega
      have h2 : (N : ℝ) < (k : ℝ) * ((N / k : ℕ) : ℝ) + (k : ℝ) := by exact_mod_cast hnat
      rw [sub_le_iff_le_add, div_le_iff₀ hk0]
      linarith
    have hLam : 0 ≤ Λ k := vonMangoldt_nonneg
    have : (N : ℝ) * (Λ k / k) - Λ k = Λ k * ((N : ℝ) / k - 1) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hfl hLam
  -- upper bound for the log sum
  have hup : ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ (N : ℝ) * Real.log N := by
    have : ∀ n ∈ Finset.Icc 1 N, Real.log n ≤ Real.log N := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      exact Real.log_le_log (by exact_mod_cast hn.1) (by exact_mod_cast hn.2)
    calc ∑ n ∈ Finset.Icc 1 N, Real.log n ≤ ∑ _n ∈ Finset.Icc 1 N, Real.log N :=
          Finset.sum_le_sum this
      _ = (N : ℝ) * Real.log N := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
          push_cast
          ring
  have hpsi : (∑ k ∈ Finset.Icc 1 N, Λ k) ≤ (Real.log 4 + 4) * N := by
    rw [← psi_eq_sum N]
    exact Chebyshev.psi_le_const_mul_self (by positivity)
  rw [sumLog_eq N] at hup
  have hkey : (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k)
      ≤ (N : ℝ) * Real.log N + (Real.log 4 + 4) * N := by linarith
  have := le_of_mul_le_mul_left (by nlinarith [hkey] :
    (N : ℝ) * (∑ k ∈ Finset.Icc 1 N, Λ k / k) ≤ (N : ℝ) * (Real.log N + (Real.log 4 + 4))) hN0
  exact this

/-! ### `∑_{p ≤ N} log p / p² = O(1)` -/

open Chebyshev in
theorem theta_eq_sum (N : ℕ) :
    θ (N : ℝ) = ∑ k ∈ Finset.Icc 1 N, (if k.Prime then Real.log k else 0) := by
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [Chebyshev.theta, Nat.floor_natCast, hIoc, Finset.sum_filter]

/-- Telescoping. -/
theorem telescope_inv (M : ℕ) :
    ∑ d ∈ Finset.Icc 1 M, ((1 : ℝ) / d - 1 / (d + 1)) ≤ 1 := by
  have h : ∀ M : ℕ, ∑ d ∈ Finset.Icc 1 M, ((1 : ℝ) / d - 1 / (d + 1))
      = 1 - 1 / ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), ih]
        push_cast
        ring
  rw [h M]
  have h1 : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  linarith

/-- `∑_{p ≤ N} log p / p² ≤ 4 (log 4 + 4)`. -/
theorem sum_log_div_sq_le (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (if k.Prime then Real.log k else 0) / (k : ℝ) ^ 2
      ≤ 4 * (Real.log 4 + 4) := by
  set c : ℝ := Real.log 4 + 4 with hc
  have hc0 : (0 : ℝ) < c := by
    have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    simp only [hc]; linarith
  rcases N with _ | M
  · simp
    positivity
  set a : ℕ → ℝ := fun k => (if k.Prime then Real.log k else 0) with ha
  set g : ℕ → ℝ := fun k => 1 / (k : ℝ) ^ 2 with hg
  have hkey : ∑ k ∈ Finset.Icc 1 (M + 1), a k * g k
      = (∑ k ∈ Finset.Icc 1 (M + 1), a k) * g (M + 1)
        + ∑ d ∈ Finset.Icc 1 M, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) :=
    abel_gen a g M
  have hpartial : ∀ d : ℕ, (∑ e ∈ Finset.Icc 1 d, a e) ≤ c * d := by
    intro d
    have h1 : Chebyshev.theta (d : ℝ) ≤ Real.log 4 * d :=
      Chebyshev.theta_le_log4_mul_x (by positivity)
    rw [ha, ← theta_eq_sum d]
    have hd0 : (0 : ℝ) ≤ d := by positivity
    simp only [hc]
    nlinarith [h1, hd0]
  have hfirst : (∑ k ∈ Finset.Icc 1 (M + 1), a k) * g (M + 1) ≤ c := by
    have h1 := hpartial (M + 1)
    have hMpos : (0 : ℝ) < ((M : ℝ) + 1) := by positivity
    have hg0 : g (M + 1) = 1 / ((M : ℝ) + 1) ^ 2 := by rw [hg]; push_cast; ring
    rw [hg0]
    push_cast at h1
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    have hsq : ((M : ℝ) + 1) ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [h1, hMpos, hc0, hsq]
  have hterm : ∀ d ∈ Finset.Icc 1 M,
      (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ 3 * c * ((1 : ℝ) / d - 1 / (d + 1)) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd.1
    have hgd : g d - g (d + 1) = (2 * (d : ℝ) + 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by
      rw [hg]
      push_cast
      field_simp
      ring
    have hgd0 : 0 ≤ g d - g (d + 1) := by rw [hgd]; positivity
    have hbnd : (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ (c * d) * (g d - g (d + 1)) :=
      mul_le_mul_of_nonneg_right (hpartial d) hgd0
    refine le_trans hbnd ?_
    rw [hgd]
    have hdne : (d : ℝ) ≠ 0 := ne_of_gt hd0
    have hd1ne : (d : ℝ) + 1 ≠ 0 := by positivity
    have hrhs : (1 : ℝ) / d - 1 / ((d : ℝ) + 1) = 1 / ((d : ℝ) * ((d : ℝ) + 1)) := by
      field_simp
      ring
    have hL : (c * (d : ℝ)) * ((2 * (d : ℝ) + 1) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2))
        = (c * (d : ℝ) * (2 * (d : ℝ) + 1)) / ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2) := by ring
    have hR : 3 * c * ((1 : ℝ) / ((d : ℝ) * ((d : ℝ) + 1)))
        = (3 * c) / ((d : ℝ) * ((d : ℝ) + 1)) := by ring
    rw [hrhs, hL, hR, div_le_div_iff₀ (by positivity) (by positivity)]
    have key : 3 * c * ((d : ℝ) ^ 2 * ((d : ℝ) + 1) ^ 2)
        - c * (d : ℝ) * (2 * (d : ℝ) + 1) * ((d : ℝ) * ((d : ℝ) + 1))
        = c * (d : ℝ) ^ 2 * ((d : ℝ) + 1) * ((d : ℝ) + 2) := by ring
    have hpos : 0 ≤ c * (d : ℝ) ^ 2 * ((d : ℝ) + 1) * ((d : ℝ) + 2) := by positivity
    linarith [key, hpos]
  have hsum : ∑ d ∈ Finset.Icc 1 M, (∑ e ∈ Finset.Icc 1 d, a e) * (g d - g (d + 1)) ≤ 3 * c := by
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    have h := telescope_inv M
    nlinarith [hc0]
  have hrewrite : ∑ k ∈ Finset.Icc 1 (M + 1),
      (if k.Prime then Real.log k else 0) / (k : ℝ) ^ 2
      = ∑ k ∈ Finset.Icc 1 (M + 1), a k * g k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ha, hg]
    ring
  rw [hrewrite, hkey]
  linarith [hfirst, hsum]

/-! ### The prime-power (non-prime) tail of `∑ Λ(k)/k` -/

/-- For `j ≥ 2`, `∑_{p ≤ M} log p / p^j ≤ (1/2)^{j-2} · 4(log 4 + 4)`. -/
theorem sum_log_div_pow_le (M j : ℕ) (hj : 2 ≤ j) :
    ∑ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p), Real.log p / (p : ℝ) ^ j
      ≤ ((1 : ℝ) / 2) ^ (j - 2) * (4 * (Real.log 4 + 4)) := by
  have hpow2 : (0 : ℝ) ≤ ((1 : ℝ) / 2) ^ (j - 2) := by positivity
  have key : ∀ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p),
      Real.log p / (p : ℝ) ^ j
        ≤ ((1 : ℝ) / 2) ^ (j - 2) * ((if p.Prime then Real.log p else 0) / (p : ℝ) ^ 2) := by
    intro p hp
    rw [Finset.mem_filter] at hp
    have hpp := hp.2
    rw [if_pos hpp]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    have hpow : (p : ℝ) ^ j = (p : ℝ) ^ 2 * (p : ℝ) ^ (j - 2) := by
      rw [← pow_add]; congr 1; omega
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hR : ((1 : ℝ) / 2) ^ (j - 2) * (Real.log p / (p : ℝ) ^ 2)
        = Real.log p / ((p : ℝ) ^ 2 * 2 ^ (j - 2)) := by
      rw [div_pow, one_pow]
      field_simp
    rw [hpow, hR]
    have h2p : (2 : ℝ) ^ (j - 2) ≤ (p : ℝ) ^ (j - 2) :=
      pow_le_pow_left₀ (by norm_num) hp2 _
    have hd : (0 : ℝ) < (p : ℝ) ^ 2 * 2 ^ (j - 2) := by
      have : (0 : ℝ) < (p : ℝ) := by linarith
      positivity
    exact div_le_div_of_nonneg_left hlog hd (by nlinarith [sq_nonneg ((p:ℝ))])
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hpow2
  refine le_trans ?_ (sum_log_div_sq_le M)
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  positivity

/-- Geometric bookkeeping for the outer sum over exponents. -/
theorem sum_geom_shift (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (if 2 ≤ j then ((1 : ℝ) / 2) ^ (j - 2) else 0) ≤ 4 := by
  rw [show Finset.Icc 1 J = Finset.Ico 1 (J + 1) by
      ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine le_trans (Finset.sum_le_sum (g := fun i => 2 * ((1 : ℝ) / 2) ^ i) (fun i _ => ?_)) ?_
  · show (if 2 ≤ 1 + i then ((1 : ℝ) / 2) ^ (1 + i - 2) else 0) ≤ 2 * ((1 : ℝ) / 2) ^ i
    rcases i with _ | i
    · norm_num
    · rw [if_pos (by omega), show 1 + (i + 1) - 2 = i by omega]
      rw [div_pow, one_pow, div_pow, one_pow]
      rw [pow_succ]
      rw [mul_comm (2:ℝ)]
      rw [div_le_iff₀ (by positivity)]
      field_simp
      norm_num
  · rw [← Finset.mul_sum]
    have := sum_geometric_two_le J
    linarith

open ArithmeticFunction in
/-- The whole non-prime part of `∑_{k ≤ N} Λ(k)/k` is bounded by an absolute constant. -/
theorem tail_le (N : ℕ) :
    ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k.Prime), Λ k / (k : ℝ)
      ≤ 16 * (Real.log 4 + 4) := by
  have hlog4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set f : ℕ → ℝ := fun n => if n.Prime then 0 else Λ n / n with hf
  have h1 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ k.Prime), Λ k / (k : ℝ)
      = ∑ n ∈ (Finset.Ioc 0 N).filter (fun n => IsPrimePow n), f n := by
    rw [Finset.sum_filter, Finset.sum_filter]
    have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rw [hIoc]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [hf, hp, hp.isPrimePow]
    · by_cases hpp : IsPrimePow n
      · simp [hf, hp, hpp]
      · simp [hf, hp, hpp, ArithmeticFunction.vonMangoldt_apply]
  have h2 := Chebyshev.sum_PrimePow_eq_sum_sum f (x := (N : ℝ)) (by positivity)
  rw [Nat.floor_natCast] at h2
  rw [h1, h2]
  set J : ℕ := ⌊Real.log (N : ℝ) / Real.log 2⌋₊ with hJ
  have hinner : ∀ j ∈ Finset.Icc 1 J,
      ∑ p ∈ (Finset.Ioc 0 ⌊(N : ℝ) ^ ((1 : ℝ) / j)⌋₊).filter (fun p => Nat.Prime p), f (p ^ j)
        ≤ (if 2 ≤ j then ((1 : ℝ) / 2) ^ (j - 2) else 0) * (4 * (Real.log 4 + 4)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    set M : ℕ := ⌊(N : ℝ) ^ ((1 : ℝ) / j)⌋₊ with hM
    have hIoc : Finset.Ioc 0 M = Finset.Icc 1 M := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    rcases eq_or_lt_of_le hj.1 with h1j | h2j
    · -- j = 1 : every term vanishes because `p ^ 1 = p` is prime
      rw [if_neg (by omega)]
      rw [zero_mul]
      refine le_of_eq ?_
      refine Finset.sum_eq_zero fun p hp => ?_
      rw [Finset.mem_filter] at hp
      simp [hf, ← h1j, hp.2]
    · -- j ≥ 2
      have hj2 : 2 ≤ j := h2j
      rw [if_pos hj2, hIoc]
      refine le_trans (le_of_eq ?_) (sum_log_div_pow_le M j hj2)
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.mem_filter] at hp
      have hpp := hp.2
      have hnp : ¬ (p ^ j).Prime := by
        intro hc
        rcases hc.eq_one_or_self_of_dvd p (dvd_pow_self p (by omega : j ≠ 0)) with h | h
        · exact hpp.ne_one h
        · have hlt : p ^ 1 < p ^ j := Nat.pow_lt_pow_right hpp.one_lt (by omega)
          rw [pow_one] at hlt
          omega
      have hΛ : Λ (p ^ j) = Real.log p := by
        rw [ArithmeticFunction.vonMangoldt_apply, if_pos (hpp.isPrimePow.pow (by omega)),
          Nat.Prime.pow_minFac hpp (by omega)]
      simp only [hf, if_neg hnp, hΛ, Nat.cast_pow]
  refine le_trans (Finset.sum_le_sum hinner) ?_
  rw [← Finset.sum_mul]
  have hg := sum_geom_shift J
  nlinarith [hg, hlog4]

/-! ### Extracting the primes `≡ 1 (mod 3)` -/

/-- `∑_{p ≤ N, p prime, p ≡ 1 (3)} log p / p`. -/
noncomputable def S1 (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % 3 = 1), Real.log p / (p : ℝ)

open ArithmeticFunction in
theorem S1_lower (N : ℕ) :
    (1 / 4 : ℝ) * Real.log N - (1 / 2 + Real.log 3 / 6 + 16 * (Real.log 4 + 4)) ≤ S1 N := by
  have hlog3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hml := mertens_lower N
  -- split into primes / non-primes
  have hsplit :
      ∑ k ∈ Finset.Icc 1 N, LK k / (k : ℝ)
        = ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k), LK k / (k : ℝ)
          + ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k), LK k / (k : ℝ) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  -- non-prime part
  have hnp : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k), LK k / (k : ℝ)
      ≤ 32 * (Real.log 4 + 4) := by
    have hstep : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => ¬ Nat.Prime k),
        LK k / (k : ℝ) ≤ 2 * (Λ k / (k : ℝ)) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1.1
      have := LK_le_two_vonMangoldt k
      rw [div_le_iff₀ hk0]
      have h2 : 2 * (Λ k / (k : ℝ)) * k = 2 * Λ k := by field_simp
      rw [h2]
      exact this
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    have := tail_le N
    linarith
  -- prime part
  have hp : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k), LK k / (k : ℝ)
      ≤ 2 * S1 N + Real.log 3 / 3 := by
    have hstep : ∀ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        LK k / (k : ℝ)
          ≤ 2 * (if k % 3 = 1 then Real.log k / (k : ℝ) else 0)
            + (if k = 3 then Real.log 3 / 3 else 0) := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hkp := hk.2
      have hΛ : Λ k = Real.log k := ArithmeticFunction.vonMangoldt_apply_prime hkp
      have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkp.pos
      have hlogk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hkp.one_le)
      have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
      rcases h3 with h | h | h
      · -- 3 ∣ k, k prime ⇒ k = 3
        have hk3 : k = 3 := by
          have hdvd : (3 : ℕ) ∣ k := Nat.dvd_of_mod_eq_zero h
          rcases (Nat.Prime.eq_one_or_self_of_dvd hkp 3 hdvd) with h' | h'
          · omega
          · omega
        subst hk3
        simp only [LK, chi, hΛ]
        norm_num
      · rw [if_pos h, if_neg (by omega)]
        simp only [LK, chi, hΛ, if_pos h]
        push_cast
        rw [add_zero]
        have : Real.log k * (1 + 1) / (k : ℝ) = 2 * (Real.log k / k) := by ring
        rw [this]
      · rw [if_neg (by omega), if_neg (by omega)]
        simp only [LK, chi, hΛ, if_neg (by omega : ¬ k % 3 = 1), if_pos h]
        push_cast
        norm_num
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        (if k % 3 = 1 then Real.log k / (k : ℝ) else 0) = S1 N := by
      rw [S1, Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h1 : Nat.Prime k <;> by_cases h2 : k % 3 = 1 <;> simp [h1, h2]
    have h2 : ∑ k ∈ (Finset.Icc 1 N).filter (fun k => Nat.Prime k),
        (if k = 3 then Real.log 3 / 3 else 0) ≤ Real.log 3 / 3 := by
      rw [Finset.sum_ite_eq' ((Finset.Icc 1 N).filter (fun k => Nat.Prime k)) 3
        (fun _ => Real.log 3 / 3)]
      split
      · exact le_rfl
      · positivity
    rw [h1]
    linarith
  linarith [hml, hsplit ▸ hml]

open ArithmeticFunction in
theorem S1_upper (M : ℕ) : S1 M ≤ Real.log M + (Real.log 4 + 4) := by
  refine le_trans ?_ (mertens_upper M)
  have h : S1 M
      = ∑ p ∈ (Finset.Icc 1 M).filter (fun p => Nat.Prime p ∧ p % 3 = 1), Λ p / (p : ℝ) := by
    rw [S1]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.mem_filter] at hp
    rw [ArithmeticFunction.vonMangoldt_apply_prime hp.2.1]
  rw [h]
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
  intro i _ _
  have h1 : (0 : ℝ) ≤ Λ i := ArithmeticFunction.vonMangoldt_nonneg
  positivity

/-- The absolute constant governing where the Chebyshev-type lower bound kicks in. -/
noncomputable def C4 : ℝ :=
  (1 / 2 + Real.log 3 / 6 + 16 * (Real.log 4 + 4)) + (Real.log 4 + 4)

theorem C4_pos : 0 < C4 := by
  have h3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have h4 : (0 : ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [C4]; linarith

/-- The threshold `m₀`. -/
noncomputable def m0 : ℕ := ⌈Real.exp (2 * C4)⌉₊

theorem log_ge_of_m0_le {m : ℕ} (hm : m0 ≤ m) : 2 * C4 ≤ Real.log m := by
  have h1 : Real.exp (2 * C4) ≤ (m0 : ℝ) := Nat.le_ceil _
  have h2 : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h3 : Real.exp (2 * C4) ≤ (m : ℝ) := le_trans h1 h2
  have := Real.log_le_log (Real.exp_pos _) h3
  rwa [Real.log_exp] at this

theorem two_le_m0 : 2 ≤ m0 := by
  have hC := C4_pos
  have h1 : (1 : ℝ) < Real.exp (2 * C4) := by
    rw [show (1 : ℝ) = Real.exp 0 by simp]
    exact Real.exp_lt_exp.mpr (by linarith)
  have : (1 : ℝ) < (m0 : ℝ) := lt_of_lt_of_le h1 (Nat.le_ceil _)
  have : 1 < m0 := by exact_mod_cast this
  omega

/-- Chebyshev-type lower bound for primes `≡ 1 (mod 3)` along `N = m^8`. -/
theorem count_lower (m : ℕ) (hm : m0 ≤ m) :
    (m : ℝ) / 16
      ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) := by
  have hm2 : 2 ≤ m := le_trans two_le_m0 hm
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
  have hlogm : 2 * C4 ≤ Real.log m := log_ge_of_m0_le hm
  have hC := C4_pos
  have hlogm0 : 0 < Real.log m := by linarith
  set F : Finset ℕ := (Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1) with hF
  set G : Finset ℕ := (Finset.Icc 1 m).filter (fun p => Nat.Prime p ∧ p % 3 = 1) with hG
  have hGF : G ⊆ F := by
    refine Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right ?_)
    calc m = m ^ 1 := (pow_one m).symm
    _ ≤ m ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  -- the difference of the two partial sums
  have hdiff : S1 (m ^ 8) - S1 m = ∑ p ∈ F \ G, Real.log p / (p : ℝ) := by
    rw [Finset.sum_sdiff_eq_sub hGF, S1, S1]
  -- lower bound for the difference
  have hlow : Real.log m - C4 ≤ S1 (m ^ 8) - S1 m := by
    have h1 := S1_lower (m ^ 8)
    have h2 := S1_upper m
    have hcast : ((m ^ 8 : ℕ) : ℝ) = (m : ℝ) ^ 8 := by push_cast; ring
    rw [hcast, Real.log_pow] at h1
    rw [C4]
    push_cast at h1
    linarith
  -- upper bound for the difference
  have hup : ∑ p ∈ F \ G, Real.log p / (p : ℝ)
      ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by
    have hstep : ∀ p ∈ F \ G, Real.log p / (p : ℝ) ≤ 8 * Real.log m / (m : ℝ) := by
      intro p hp
      rw [Finset.mem_sdiff, hF, hG, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hp
      obtain ⟨⟨⟨hp1, hp2⟩, hpP⟩, hpG⟩ := hp
      have hpm : m < p := by
        by_contra hc
        exact hpG ⟨Finset.mem_Icc.mpr ⟨hp1, by omega⟩, hpP⟩
      have hpR : (m : ℝ) < (p : ℝ) := by exact_mod_cast hpm
      have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
      have hlogp : Real.log p ≤ 8 * Real.log m := by
        have h1 : ((p : ℝ)) ≤ (m : ℝ) ^ 8 := by
          have : (p : ℝ) ≤ ((m ^ 8 : ℕ) : ℝ) := by exact_mod_cast hp2
          rwa [show ((m ^ 8 : ℕ) : ℝ) = (m : ℝ) ^ 8 by push_cast; ring] at this
        have := Real.log_le_log hp0 h1
        rwa [Real.log_pow] at this
        <;> norm_num
      have hlogp0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
      calc Real.log p / (p : ℝ) ≤ (8 * Real.log m) / (p : ℝ) := by gcongr
        _ ≤ (8 * Real.log m) / (m : ℝ) := by
            refine div_le_div_of_nonneg_left (by linarith) (by linarith) (le_of_lt hpR)
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((F \ G).card : ℝ) ≤ (F.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset)
    have hpos : (0 : ℝ) ≤ 8 * Real.log m / (m : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_right hcard hpos
  -- combine
  have hkey : Real.log m - C4 ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by
    rw [hdiff] at hlow
    linarith
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hhalf : Real.log m / 2 ≤ (F.card : ℝ) * (8 * Real.log m / (m : ℝ)) := by linarith
  have h8 : (F.card : ℝ) * (8 * Real.log m / (m : ℝ))
      = 16 * (F.card : ℝ) * Real.log m / (m : ℝ) / 2 := by
    field_simp
    ring
  rw [h8, div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2),
    le_div_iff₀ hm0] at hhalf
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 16)]
  nlinarith [hhalf, hlogm0, hm0]

/-! ### The polynomial bound on the `i`-th prime `≡ 1 (mod 3)` -/

theorem card_eq_count (N : ℕ) :
    ((Finset.Icc 1 N).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card
      = Nat.count (fun n => Nat.Prime n ∧ n % 3 = 1) (N + 1) := by
  rw [Nat.count_eq_card_filter_range]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨_, h2⟩, hP⟩
    exact ⟨by omega, hP⟩
  · rintro ⟨h1, hP⟩
    refine ⟨⟨?_, by omega⟩, hP⟩
    exact hP.1.one_lt.le.trans' (by norm_num)

/-- **The i-th prime `≡ 1 (mod 3)` is polynomially bounded.** -/
theorem primes_one_mod_three_poly_bound :
    ∃ A : ℕ, 0 < A ∧ ∀ i : ℕ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i ≤ (i + 2) ^ A := by
  refine ⟨max 40 (m0 ^ 8), lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun i => ?_⟩
  set A : ℕ := max 40 (m0 ^ 8) with hA
  set m : ℕ := max (16 * (i + 2)) m0 with hm
  have hmm0 : m0 ≤ m := le_max_right _ _
  have hmi : 16 * (i + 2) ≤ m := le_max_left _ _
  -- there are at least `i + 2` primes `≡ 1 (mod 3)` below `m ^ 8`
  have hcl := count_lower m hmm0
  have hcard : i + 2 ≤ ((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card := by
    have h1 : ((i : ℝ) + 2) ≤ (m : ℝ) / 16 := by
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 16)]
      have : ((16 * (i + 2) : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmi
      push_cast at this
      linarith
    have h2 : ((i : ℝ) + 2)
        ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) :=
      le_trans h1 hcl
    have h3 : (((i + 2 : ℕ)) : ℝ)
        ≤ (((Finset.Icc 1 (m ^ 8)).filter (fun p => Nat.Prime p ∧ p % 3 = 1)).card : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h3
  -- turn it into a bound on `Nat.nth`
  have hlt : i < Nat.count (fun n => Nat.Prime n ∧ n % 3 = 1) (m ^ 8 + 1) := by
    rw [← card_eq_count]
    omega
  have hnth := Nat.nth_lt_of_lt_count hlt
  have hle : Nat.nth (fun n => Nat.Prime n ∧ n % 3 = 1) i ≤ m ^ 8 := by omega
  refine hle.trans ?_
  -- `m ^ 8 ≤ (i + 2) ^ A`
  have hi2 : 2 ≤ i + 2 := by omega
  rcases le_total (m0 : ℕ) (16 * (i + 2)) with h | h
  · have hmv : m = 16 * (i + 2) := max_eq_left h
    rw [hmv]
    have h1 : (16 * (i + 2)) ^ 8 = 2 ^ 32 * (i + 2) ^ 8 := by ring
    have h2 : (2 : ℕ) ^ 32 ≤ (i + 2) ^ 32 := Nat.pow_le_pow_left hi2 32
    calc (16 * (i + 2)) ^ 8 = 2 ^ 32 * (i + 2) ^ 8 := h1
      _ ≤ (i + 2) ^ 32 * (i + 2) ^ 8 := Nat.mul_le_mul_right _ h2
      _ = (i + 2) ^ 40 := by rw [← pow_add]
      _ ≤ (i + 2) ^ A := Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  · have hmv : m = m0 := max_eq_right h
    rw [hmv]
    calc m0 ^ 8 ≤ 2 ^ (m0 ^ 8) := Nat.le_of_lt (Nat.lt_two_pow_self)
      _ ≤ (i + 2) ^ (m0 ^ 8) := Nat.pow_le_pow_left hi2 _
      _ ≤ (i + 2) ^ A := Nat.pow_le_pow_right (by omega) (le_max_right _ _)

end Workspace.ProofLemmas.MertensThreeMod

-- Cited from: H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer, 2000 — prime
-- number theorem in arithmetic progressions (or already Linnik/Chebyshev-type lower bounds for
-- π(x; 3, 1), which suffice).
-- Paper label: Fact 3.10 (quantitative core)
--
-- Proved from Mathlib alone in `Workspace.ProofLemmas.MertensThreeMod` by an elementary
-- (Chebyshev/Mertens-style) argument in the field `ℚ(√-3)`:
--   * `r = 1 ∗ χ` for the quadratic character `χ` mod 3 has `A(N) = ∑_{n≤N} r n ∈ [N/2, N]`
--     (a hyperbola/partial-summation count, no L-functions);
--   * `∑_{n≤N} r n log n = ∑_k Λ(k)(1+χ(k)) A(N/k)` (Dirichlet convolution `log = Λ ∗ 1`),
--     and this double-counted sum is squeezed between `(N/2)log N − N` and `N log N`,
--     giving the Mertens-type lower bound `∑_{k≤N} Λ(k)(1+χ(k))/k ≥ (1/2)log N − 1`;
--   * Chebyshev's `ψ(x) ≤ (log 4 + 4)x` (Mathlib) gives the matching upper bound
--     `∑_{k≤N} Λ(k)/k ≤ log N + (log 4 + 4)`, and the prime-power tail
--     `∑_{k≤N, k not prime} Λ(k)/k` is bounded by an absolute constant via
--     `Chebyshev.sum_PrimePow_eq_sum_sum` + `θ(x) ≤ log 4 · x`;
--   * hence `S₁(N) = ∑_{p≤N, p≡1(3)} log p/p ≥ (1/4)log N − C`; comparing `S₁(m^8)` with
--     `S₁(m)` and using `log p ≤ 8 log m`, `1/p ≤ 1/m` on the range `m < p ≤ m^8` gives
--     `π(m^8; 3, 1) ≥ m/16` for `m ≥ m₀`, i.e. the polynomial bound below with `A = 40`
--     (enlarged to `max 40 m₀^8` to absorb the finitely many small indices).
--
-- This quantitative prime-counting bound (equivalently `π(y; 3, 1) ≫ y^{1/A}`) is the input to
-- `PrimesOneModThreeLogSum`: from a polynomial bound `pᵢ ≤ (i+2)^A` one gets
-- `∑_{i<ℓ} log pᵢ ≤ ℓ·A·log(ℓ+1) ≤ 2A·ℓ log ℓ` for `ℓ ≥ 2`
-- (`Workspace.ProofLemmas.PrimesOneModThreeReduction.logSum_le_of_poly_bound`).  Mathlib has
-- Dirichlet's theorem (qualitative infinitude) but no quantitative counting in arithmetic
-- progressions; the quantitative input is developed in `Workspace/ProofLemmas/MertensThreeMod.lean`.
--
-- NL statement: There is a positive integer A such that for every i, the i-th prime congruent to
-- 1 modulo 3 (in increasing order, 0-indexed by Nat.nth) is at most (i + 2)^A.


/-- **Quantitative prime counting.**  The `i`-th prime `≡ 1 (mod 3)` is polynomially bounded. -/
theorem PrimesOneModThreePolyBound :
    ∃ A : ℕ, 0 < A ∧ ∀ i : ℕ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i ≤ (i + 2) ^ A :=
  Workspace.ProofLemmas.MertensThreeMod.primes_one_mod_three_poly_bound

-- Cited from: H. Davenport, Multiplicative Number Theory, 3rd ed., GTM 74, Springer, 2000 (revised by H. L. Montgomery) — prime number theorem in arithmetic progressions.
-- Paper label: Fact 3.10 (the O(l log l) bound used in equation (6) of Proposition 3.8, Step 1)
-- NL statement: There is a constant C > 0 such that for every l >= 2, the sum of the logarithms of the first l rational primes congruent to 1 modulo 3 is at most C * l * log l. (Consequence of the prime number theorem in arithmetic progressions.)
--
-- The passage from the polynomial bound `Workspace.ProofLemmas.PrimesOneModThreePolyBound` (the `i`-th
-- prime `≡ 1 (mod 3)` is at most `(i+2)^A`, equivalently `π(y;3,1) ≫ y^{1/A}`) to the `O(ℓ log ℓ)`
-- log-sum is proved from Mathlib in `Workspace.ProofLemmas.PrimesOneModThreeReduction`.



/-- **Fact 3.10.** There is `C > 0` such that the sum of `log` of the first `ℓ` primes
`≡ 1 (mod 3)` is `≤ C·ℓ·log ℓ`.  The first `ℓ` such primes are enumerated by `Nat.nth`. -/
theorem PrimesOneModThreeLogSum :
    ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 2 ≤ ℓ →
      (∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i : ℝ)))
        ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  obtain ⟨A, hA, hbd⟩ := PrimesOneModThreePolyBound
  refine ⟨2 * A, by positivity, ?_⟩
  exact Workspace.ProofLemmas.PrimesOneModThreeReduction.logSum_le_of_poly_bound A hA hbd

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

theorem BaseRootDiscriminantBound :
    ∃ C : ℝ, 0 < C ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      ∀ (F : Type) [Field F] [NumberField F],
        NumberField.IsTotallyReal F →
        Module.finrank ℚ F = 3 →
        (NumberField.discr F).natAbs =
            (∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i) ^ 2 →
        Real.log (rootDiscriminant F) =
              (2 / 3) * ∑ i ∈ Finset.range ℓ,
                Real.log ((Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i : ℝ)) ∧
            Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := PrimesOneModThreeLogSum
  refine ⟨(2 / 3) * A, by positivity, 2, ?_⟩
  intro ℓ hℓ F _ _ _ hfin hdisc
  set pred := fun n => n.Prime ∧ n % 3 = 1 with hpred
  set P := ∏ i ∈ Finset.range ℓ, Nat.nth pred i with hP
  -- discriminant is nonzero, so P ≠ 0
  have hdne : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero (K := F)
  have hPsq : (NumberField.discr F).natAbs = P ^ 2 := hdisc
  have hPne : P ≠ 0 := by
    have h2 : P ^ 2 ≠ 0 := by
      rw [← hPsq]; exact Int.natAbs_ne_zero.mpr hdne
    intro h0; exact h2 (by simp [h0])
  have hrne : ∀ i ∈ Finset.range ℓ, Nat.nth pred i ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (hP ▸ hPne)
  have hPposR : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hPne)
  have hPpos : (0 : ℝ) < (P : ℝ) ^ 2 := pow_pos hPposR 2
  -- finrank cast
  have hfinr : (Module.finrank ℚ F : ℝ) = 3 := by rw [hfin]; norm_num
  -- |discr| as (P:ℝ)^2
  have habs : |(NumberField.discr F : ℝ)| = (P : ℝ) ^ 2 := by
    have h1 : |(NumberField.discr F : ℝ)| = ((NumberField.discr F).natAbs : ℝ) := by
      rw [Int.cast_natAbs, Int.cast_abs]
    rw [h1, hPsq]; push_cast; ring
  -- rootDiscriminant explicit
  have hrd : rootDiscriminant F = ((P : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
    rw [rootDiscriminant, habs, hfinr]
  -- log of product = sum of logs
  have hsum : Real.log ((P : ℝ)) =
      ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ)) := by
    rw [hP]; push_cast
    rw [Real.log_prod (fun i hi => Nat.cast_ne_zero.mpr (hrne i hi))]
  -- the log identity
  have hlog : Real.log (rootDiscriminant F) =
      (2 / 3) * ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ)) := by
    rw [hrd, Real.log_rpow hPpos, Real.log_pow, ← hsum]
    push_cast; ring
  refine ⟨hlog, ?_⟩
  rw [hlog]
  have hb := hbound ℓ hℓ
  calc (2 / 3) * ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ))
      ≤ (2 / 3) * (A * (ℓ : ℝ) * Real.log (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (2 / 3) * A * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by ring

-- Cited from: I. R. Shafarevich, Extensions with given points of ramification, Publ. Math. IHES 18:71-92, 1963 (English transl. AMS Transl. (2) 59 (1966), 128-149); J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008, Chapter X, Section 10.
-- Paper label: Proposition 3.5 (Shafarevich relation-rank estimate) / Proposition A.10
-- NL statement: There is an absolute constant C_0, independent of the field, such that for every totally real cubic number field F (so [F:Q] = 3 and zeta_3 is not in F), the Galois group G = Gal(F^{ur,3}/F) of its maximal everywhere-unramified pro-3 extension satisfies r(G) <= d(G) + C_0.




open scoped NumberField
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
open Workspace.Types.UnramifiedProPExtension

/-- **Proposition 3.5 (Shafarevich relation-rank estimate).** There is an absolute constant
`C₀` (independent of `F`) such that for every totally real cubic number field `F`
(`[F : ℚ] = 3`, `F` totally real — so `ζ₃ ∉ F`), the Galois group `G = Gal(F^{ur,3}/F)`
of its maximal everywhere-unramified pro-`3` extension satisfies `r(G) ≤ d(G) + C₀`. -/
axiom ShafarevichRelationRank :
    ∃ C₀ : ℕ, ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → Module.finrank ℚ F = 3 →
        relRank 3 (galUr 3 F) ≤ dRank (galUr 3 F) + (C₀ : ℕ∞)

-- Cited from: Standard profinite group theory: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010 (quotients of pro-p groups by closed normal subgroups are pro-p).
-- Paper label: standard profinite fact (implicit in paper Step 2, tex 747-781)
-- NL statement: For a prime p, a pro-p group G (a compact Hausdorff totally-disconnected topological group in which every open normal subgroup has p-power index), and a closed normal subgroup N ≤ G, the quotient topological group G/N is again pro-p.
-- Proof outline. G/N inherits IsTopologicalGroup, CompactSpace, and (since N is closed and
-- normal) T3 hence T2 as Mathlib instances. The p-power-index condition transfers along the
-- surjective quotient map QuotientGroup.mk' N via Subgroup.index_comap_of_surjective: an open
-- normal H ≤ G/N pulls back to an open normal H.comap (mk' N) ≤ G of equal index, which is a
-- p-power by hypothesis. The key point is TotallyDisconnectedSpace (G/N): by
-- totallyDisconnectedSpace_iff_connectedComponent_one it suffices to show the connected
-- component of 1 is {1}, and in the compact Hausdorff quotient this component equals the
-- intersection of all clopen neighbourhoods of 1 (connectedComponent_eq_iInter_isClopen). Given
-- g ∉ N, ProfiniteGrp.closedSubgroup_eq_sInf_open expresses the closed subgroup N as the
-- infimum of the open subgroups containing it, so some open K ⊇ N has g ∉ K; its image K.map
-- (mk' N) is an open — hence clopen (OpenSubgroup.isClopen) — subgroup of G/N containing 1 but
-- not the class of g, separating that class from 1. Hence only 1 survives the intersection.


open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000 in
theorem SublemmaProPQuotientClosed :
    ∀ (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G]
      (N : Subgroup G) [N.Normal],
      IsClosed (N : Set G) → IsProP p G → IsProP p (G ⧸ N) := by
  intro p _ G _ _ N _ hNclosed hG
  obtain ⟨hTop, hCompact, hT2, hTD, hIndex⟩ := hG
  haveI : IsTopologicalGroup G := hTop
  haveI : CompactSpace G := hCompact
  haveI : T2Space G := hT2
  haveI : TotallyDisconnectedSpace G := hTD
  haveI : IsClosed (N : Set G) := hNclosed
  -- Quotient instances
  haveI hqTop : IsTopologicalGroup (G ⧸ N) := inferInstance
  haveI hqCompact : CompactSpace (G ⧸ N) := inferInstance
  haveI hqT3 : T3Space (G ⧸ N) := inferInstance
  haveI hqT2 : T2Space (G ⧸ N) := inferInstance
  refine ⟨hqTop, hqCompact, hqT2, ?_, ?_⟩
  · -- TotallyDisconnectedSpace (G ⧸ N)
    rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    rw [connectedComponent_eq_iInter_isClopen]
    -- goal: ⋂ s : {s // IsClopen s ∧ (1:G⧸N) ∈ s}, s = {1}
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · -- 1 ∈ ⋂
      rw [Set.mem_iInter]
      intro s
      exact s.2.2
    · -- uniqueness: any y in the intersection equals 1
      intro y hy
      by_contra hne
      -- y ≠ 1. Lift y to g ∈ G with mk g = y, g ∉ N
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      -- g ∉ N since mk g ≠ 1
      have hgN : g ∉ N := by
        intro hgin
        exact hne ((QuotientGroup.eq_one_iff g).mpr hgin)
      -- N as closed subgroup; use closedSubgroup_eq_sInf_open
      have hNeq : (N : Subgroup G) = sInf {K : Subgroup G | IsOpen (K : Set G) ∧ (⟨N, hNclosed⟩ : ClosedSubgroup G) ≤ K} :=
        ProfiniteGrp.closedSubgroup_eq_sInf_open ⟨N, hNclosed⟩
      -- since g ∉ N = sInf, there is open K ⊇ N with g ∉ K
      have hg_not_sInf : g ∉ sInf {K : Subgroup G | IsOpen (K : Set G) ∧ (⟨N, hNclosed⟩ : ClosedSubgroup G) ≤ K} := by
        rw [← hNeq]; exact hgN
      rw [Subgroup.mem_sInf] at hg_not_sInf
      push Not at hg_not_sInf
      obtain ⟨K, ⟨hKopen, hNK⟩, hgK⟩ := hg_not_sInf
      -- image π '' K is a clopen subgroup of G/N containing 1, not containing mk g
      set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
      have hNleK : N ≤ K := hNK
      -- π K = K.map π is open
      have hmapopen : IsOpen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [Subgroup.coe_map]
        exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hKopen
      -- clopen
      have hmapclopen : IsClopen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
        (OpenSubgroup.isClopen ⟨K.map π, hmapopen⟩)
      -- 1 ∈ K.map π
      have h1mem : (1 : G ⧸ N) ∈ (K.map π : Subgroup (G ⧸ N)) := one_mem _
      -- mk g ∉ K.map π
      have hgmap : (π g) ∉ (K.map π : Subgroup (G ⧸ N)) := by
        rw [Subgroup.mem_map]
        rintro ⟨x, hxK, hx⟩
        -- hx : π x = π g, so x⁻¹ * g ∈ N ≤ K, and x ∈ K ⟹ g ∈ K, contradiction
        rw [hπ] at hx
        have hxgN : x⁻¹ * g ∈ N := by
          rw [← QuotientGroup.eq]
          exact hx
        have hxgK : x⁻¹ * g ∈ K := hNleK hxgN
        have : g ∈ K := by
          have := mul_mem hxK hxgK
          simpa using this
        exact hgK this
      -- (π g) lies in the intersection (it is y), hence in this clopen set containing 1
      have : (π g) ∈ ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
        rw [Set.mem_iInter] at hy
        exact hy ⟨((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)), hmapclopen, h1mem⟩
      exact hgmap this
  · -- index condition: every open normal subgroup of G/N has p-power index
    intro H hHnorm hHopen
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
    have hcont : Continuous π := QuotientGroup.continuous_mk
    set K : Subgroup G := H.comap π with hK
    have hKnorm : K.Normal := hHnorm.comap π
    have hKopen : IsOpen (K : Set G) := by
      rw [hK, Subgroup.coe_comap]
      exact hcont.isOpen_preimage _ hHopen
    obtain ⟨k, hk⟩ := hIndex K hKnorm hKopen
    refine ⟨k, ?_⟩
    rw [← hk, hK]
    exact (Subgroup.index_comap_of_surjective H hsurj).symm

-- Cited from: Standard: the continuous image of a topologically finitely generated group is topologically finitely generated; L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010.
-- Paper label: standard profinite fact (implicit in paper Step 2, tex 747-781)
-- NL statement: A quotient G/N of a topologically finitely generated topological group G by a closed normal subgroup N is again topologically finitely generated (the images of the generators topologically generate the quotient).
-- Proof: the quotient map QuotientGroup.mk' N is surjective and
-- continuous; push the finite topological generators through it via MonoidHom.map_closure
-- and image_closure_subset_closure_image.


open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000 in
theorem SublemmaTopFinGenQuotientClosed :
    ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (N : Subgroup G) [N.Normal],
      TopFinitelyGenerated G → TopFinitelyGenerated (G ⧸ N) := by
  intro G _ _ _ N _ hG
  classical
  obtain ⟨S, hS⟩ := hG
  refine ⟨S.image (QuotientGroup.mk' N), ?_⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcont : Continuous π := QuotientGroup.continuous_mk
  unfold TopologicallyGenerates at hS ⊢
  -- rewrite the generated subgroup of the image of S as the image of the generated subgroup of S
  have hcoe : ((Subgroup.closure ((S.image π : Finset (G ⧸ N)) : Set (G ⧸ N)) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = π '' ((Subgroup.closure (S : Set G) : Subgroup G) : Set G) := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, Subgroup.coe_map]
  rw [hcoe]
  -- now: closure (π '' ↑(Subgroup.closure ↑S)) = univ
  apply Set.eq_univ_of_univ_subset
  have himg : π '' (Set.univ : Set G) = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ]; exact hsurj
  calc (Set.univ : Set (G ⧸ N))
      = π '' (Set.univ : Set G) := himg.symm
    _ = π '' (_root_.closure ((Subgroup.closure (S : Set G) : Subgroup G) : Set G)) := by rw [hS]
    _ ⊆ _root_.closure (π '' ((Subgroup.closure (S : Set G) : Subgroup G) : Set G)) :=
        image_closure_subset_closure_image hcont

/-!
# Generator rank of a pro-`p` group modulo a closed normal subgroup of the Frattini subgroup

`d(G/N) = d(G)` when `N` is the closed normal closure of finitely many elements of `Φ(G)`.
Extracted from `ProPFrattiniQuotientRanks` into its own file so that the *relation*-rank half
(`ProPRelationRankFrattiniQuotient`) can use it without an import cycle.
-/

set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace Workspace.ProofLemmas.ProPGeneratorRankQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]

/-- The comap of a maximal open subgroup of `G/N` (along `G ↠ G/N`) is a maximal open subgroup
of `G`. -/
theorem comap_maximalOpen (Mbar : Subgroup (G ⧸ N))
    (hMbar : IsMaximalOpenSubgroup Mbar) :
    IsMaximalOpenSubgroup (Mbar.comap (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπcont : Continuous π := QuotientGroup.continuous_mk
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_comap]; exact hπcont.isOpen_preimage _ hMbar.1
  · intro htop
    apply hMbar.2.1
    have h := Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar
    rw [htop, Subgroup.map_top_of_surjective π hπsurj] at h
    exact h.symm
  · intro K hKopen hMK
    have hNcomap : N ≤ Mbar.comap π := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx1 : π x = 1 := by
        rw [hπ, QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]; exact one_mem _
    have hNK : N ≤ K := le_trans hNcomap hMK
    have hcomapmapK : (K.map π).comap π = K := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNK
    have hmapKopen : IsOpen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [Subgroup.coe_map]
      exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hKopen
    have hMbarle : Mbar ≤ K.map π := by
      have h := Subgroup.map_mono (f := π) hMK
      rwa [Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar] at h
    rcases hMbar.2.2 (K.map π) hmapKopen hMbarle with h | h
    · left; rw [← hcomapmapK, h]
    · right; rw [← hcomapmapK, h, Subgroup.comap_top]

/-- For a maximal open subgroup `M` of `G` containing `N`, its image `M.map (G ↠ G/N)` is a maximal
open subgroup of `G/N`. -/
theorem map_maximalOpen (M : Subgroup G) (hM : IsMaximalOpenSubgroup M) (hNM : N ≤ M) :
    IsMaximalOpenSubgroup (M.map (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcm : (M.map π).comap π = M := by
    rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
    exact sup_eq_left.mpr hNM
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hM.1
  · intro htop
    apply hM.2.1
    rw [← hcm, htop, Subgroup.comap_top]
  · intro Kbar hKbaropen hMKbar
    have hcomapKbaropen : IsOpen ((Kbar.comap π : Subgroup G) : Set G) := by
      rw [Subgroup.coe_comap]
      exact (QuotientGroup.continuous_mk).isOpen_preimage _ hKbaropen
    have hMcomap : M ≤ Kbar.comap π := by
      rw [← hcm]; exact Subgroup.comap_mono hMKbar
    rcases hM.2.2 (Kbar.comap π) hcomapKbaropen hMcomap with h | h
    · left
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h]
    · right
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h, Subgroup.map_top_of_surjective π hπsurj]

/-- **Correspondence step.** If `N ⊆ Φ(G)`, the topological Frattini subgroup of `G` is the
preimage of the topological Frattini subgroup of `G/N` along `G ↠ G/N`. -/
theorem frattini_comap_eq (hNsub : N ≤ frattiniOpen G) :
    (frattiniOpen (G ⧸ N)).comap (QuotientGroup.mk' N) = frattiniOpen G := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro M hM
    have hNM : N ≤ M := le_trans hNsub (by rw [frattiniOpen]; exact sInf_le hM)
    have hmapM : IsMaximalOpenSubgroup (M.map π) := map_maximalOpen M hM hNM
    have hcm : (M.map π).comap π = M := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNM
    have hπxM : π x ∈ M.map π := by
      have hle : frattiniOpen (G ⧸ N) ≤ M.map π := by rw [frattiniOpen]; exact sInf_le hmapM
      exact hle hx
    have hxcomap : x ∈ (M.map π).comap π := by rw [Subgroup.mem_comap]; exact hπxM
    rwa [hcm] at hxcomap
  · intro x hx
    rw [Subgroup.mem_comap, frattiniOpen, Subgroup.mem_sInf]
    intro Mbar hMbar
    have hcomapMax : IsMaximalOpenSubgroup (Mbar.comap π) := comap_maximalOpen Mbar hMbar
    have hxin : x ∈ Mbar.comap π := by
      have hle : frattiniOpen G ≤ Mbar.comap π := by rw [frattiniOpen]; exact sInf_le hcomapMax
      exact hle hx
    rwa [Subgroup.mem_comap] at hxin

/-- The generator-rank half of Proposition 3.3: `d(G/N) = d(G)`. -/
theorem main (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    dRank (G ⧸ N) = dRank G := by
  -- N ⊆ Φ(G)
  haveI hΦnorm : (frattiniOpen G).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p G hpro hfg
  have hΦopen : IsOpen ((frattiniOpen G : Subgroup G) : Set G) :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_isOpen p G hpro hfg
  have hΦclosed : IsClosed ((frattiniOpen G : Subgroup G) : Set G) :=
    Subgroup.isClosed_of_isOpen _ hΦopen
  have hrange : Set.range g ⊆ (frattiniOpen G : Set G) := by
    rintro _ ⟨i, rfl⟩; exact hg i
  have hnc : Subgroup.normalClosure (Set.range g) ≤ frattiniOpen G :=
    Subgroup.normalClosure_le_normal hrange
  have hNsub : N ≤ frattiniOpen G := by
    rw [hN]; exact Subgroup.topologicalClosure_minimal _ hnc hΦclosed
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN]; exact Subgroup.isClosed_topologicalClosure _
  -- quotient is pro-p and top. finitely generated
  have hproQ : IsProP p (G ⧸ N) := SublemmaProPQuotientClosed p G N hNclosed hpro
  have hfgQ : TopFinitelyGenerated (G ⧸ N) := SublemmaTopFinGenQuotientClosed G N hfg
  haveI hNormQ : (frattiniOpen (G ⧸ N)).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p (G ⧸ N) hproQ hfgQ
  -- Burnside rank formula for both groups
  obtain ⟨d, hdrank, hdcard⟩ := ProPGeneratorRankFrattini p G hpro hfg
  obtain ⟨d', hd'rank, hd'card⟩ := ProPGeneratorRankFrattini p (G ⧸ N) hproQ hfgQ
  -- Frattini quotients have equal cardinality via  G/Φ(G) ≅ (G/N)/Φ(G/N)
  have hcardeq : Nat.card (G ⧸ frattiniOpen G)
      = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := by
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    set σ : G →* ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) :=
      (QuotientGroup.mk' (frattiniOpen (G ⧸ N))).comp π with hσ
    have hσsurj : Function.Surjective σ := by
      rw [hσ, MonoidHom.coe_comp]
      exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hkerσ : σ.ker = frattiniOpen G := by
      have h1 : σ.ker = (frattiniOpen (G ⧸ N)).comap π := by
        rw [hσ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rw [h1]; exact frattini_comap_eq hNsub
    have e := QuotientGroup.quotientKerEquivOfSurjective σ hσsurj
    have hc : Nat.card (G ⧸ σ.ker)
        = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := Nat.card_congr e.toEquiv
    rwa [hkerσ] at hc
  -- conclude d = d', hence dRank equal
  rw [hdcard, hd'card] at hcardeq
  have hdd : d = d' := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcardeq
  rw [hd'rank, hdrank, hdd]


end Workspace.ProofLemmas.ProPGeneratorRankQuotient

/-!
# The relation-rank half of the pro-`p` Frattini-quotient proposition

`r(G/N) ≤ r(G) + k` when `N` is the closed normal closure of `g_1, …, g_k ∈ Φ(G)`.

Given a minimal pro-`p` presentation `π : freeProP p d ↠ G` with `m = r(G)` relations, lift each
`g_i` to `ĝ_i ∈ freeProP p d` and adjoin the `ĝ_i` as `k` further relations.  The resulting
`π' = (G ↠ G/N) ∘ π` is surjective, and its kernel `π⁻¹(N)` is exactly the closed normal closure
`M` of the enlarged relation family:

* `M ≤ π⁻¹(N)` because `π⁻¹(N)` is a closed normal subgroup containing all the new relations;
* `π⁻¹(N) ≤ M` because `M` is closed in the compact group `freeProP p d`, so `π(M)` is a closed
  normal subgroup of `G` containing every `g_i`, hence containing `N`; combined with
  `ker π ≤ M` this gives `π⁻¹(N) ⊆ M`.

Finally `d(G/N) = d(G)` (the generator-rank half, `ProPGeneratorRankQuotient.main`) makes the new
presentation a *minimal-generator* presentation of `G/N`, so it witnesses `r(G/N) ≤ m + k`.
The passage from "for every presentation of `G`" to the infima uses `tsub_le_iff_right` in `ℕ∞`.
-/

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.ProPRelationRank


/-- `freeProP p n` is compact (a closed subgroup of a product of finite discrete groups). -/
theorem compactSpace_freeProP (p n : ℕ) : CompactSpace (freeProP p n) := by
  have hclosed : IsClosed ((freeProPSubgroup p n : Set (ProdQuot p n))) :=
    Subgroup.isClosed_topologicalClosure _
  exact isCompact_iff_compactSpace.mp hclosed.isCompact

/-- The quotient map as a continuous monoid hom. -/
def quotHom {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (N : Subgroup G)
    [N.Normal] : G →ₜ* (G ⧸ N) where
  toFun := QuotientGroup.mk' N
  map_one' := map_one _
  map_mul' := map_mul _
  continuous_toFun := continuous_quot_mk

@[simp] theorem quotHom_apply {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (N : Subgroup G) [N.Normal] (x : G) : quotHom N x = QuotientGroup.mk' N x := rfl



/-- **Relation-rank half of Proposition 3.3 / A.8.**  If `g_1, …, g_k ∈ Φ(G)` and `N` is the closed
normal subgroup they generate, then `r(G/N) ≤ r(G) + k`. -/
theorem proPRelationRankFrattiniQuotient (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    relRank p (G ⧸ N) ≤ relRank p G + (k : ℕ∞) := by
  classical
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN]; exact Subgroup.isClosed_topologicalClosure _
  have hdrank : dRank (G ⧸ N) = dRank G :=
    Workspace.ProofLemmas.ProPGeneratorRankQuotient.main p G hpro hfg k g hg N hN
  obtain ⟨_, hcomp, hT2, _, _⟩ := hpro
  haveI := hT2
  haveI := hcomp
  rw [← tsub_le_iff_right, relRank]
  apply le_sInf
  rintro c ⟨d, m, π, rels, hdr, hpres, rfl⟩
  rw [tsub_le_iff_right]
  haveI : CompactSpace (freeProP p d) := compactSpace_freeProP p d
  obtain ⟨hsurj, hker⟩ := hpres
  -- lifts of the `g i`
  choose ĝ hĝ using fun i => hsurj (g i)
  set rels' : Fin (m + k) → freeProP p d := Fin.append rels ĝ with hrels'
  set M : Subgroup (freeProP p d) :=
    (Subgroup.normalClosure (Set.range rels')).topologicalClosure with hM
  -- basic facts about the ranges
  have hrelsub : Set.range rels ⊆ Set.range rels' := by
    rintro _ ⟨j, rfl⟩
    exact ⟨Fin.castAdd k j, by simp [hrels']⟩
  have hgsub : Set.range ĝ ⊆ Set.range rels' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨Fin.natAdd m i, by simp [hrels']⟩
  have hrangesub : Set.range rels' ⊆ Set.range rels ∪ Set.range ĝ := by
    rintro _ ⟨j, rfl⟩
    refine Fin.addCases (fun j₁ => ?_) (fun j₂ => ?_) j
    · exact Or.inl ⟨j₁, by simp [hrels']⟩
    · exact Or.inr ⟨j₂, by simp [hrels']⟩
  haveI : (Subgroup.normalClosure (Set.range rels')).Normal := Subgroup.normalClosure_normal
  haveI hMnormal : M.Normal := Subgroup.is_normal_topologicalClosure _
  have hMclosed : IsClosed (M : Set (freeProP p d)) := Subgroup.isClosed_topologicalClosure _
  -- `ker π ≤ M`
  have hkerM : MonoidHom.ker π.toMonoidHom ≤ M := by
    rw [← hker, hM]
    exact Subgroup.topologicalClosure_mono (Subgroup.normalClosure_le_normal
      (le_trans hrelsub Subgroup.subset_normalClosure))
  -- the quotient presentation
  set π' : freeProP p d →ₜ* (G ⧸ N) := (quotHom N).comp π with hπ'
  have hsurj' : Function.Surjective π' := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨z, rfl⟩ := hsurj y
    exact ⟨z, rfl⟩
  have hkerπ' : MonoidHom.ker π'.toMonoidHom = N.comap π.toMonoidHom := by
    ext x
    simp [hπ', MonoidHom.mem_ker, Subgroup.mem_comap, QuotientGroup.eq_one_iff]
  -- `M = ker π'`
  have hMker : M = MonoidHom.ker π'.toMonoidHom := by
    rw [hkerπ']
    apply le_antisymm
    · -- `M ≤ π⁻¹ N`
      haveI : (N.comap π.toMonoidHom).Normal := Subgroup.Normal.comap ‹N.Normal› π.toMonoidHom
      have hclosed : IsClosed ((N.comap π.toMonoidHom : Subgroup (freeProP p d)) :
          Set (freeProP p d)) := hNclosed.preimage π.continuous_toFun
      refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
      refine Subgroup.normalClosure_le_normal ?_
      intro x hx
      rcases hrangesub hx with hx | hx
      · obtain ⟨j, rfl⟩ := hx
        have : rels j ∈ MonoidHom.ker π.toMonoidHom := by
          rw [← hker]
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨j, rfl⟩)
        show rels j ∈ (N.comap π.toMonoidHom : Subgroup (freeProP p d))
        rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp this]
        exact N.one_mem
      · obtain ⟨i, rfl⟩ := hx
        have hgi : g i ∈ N := by
          rw [hN]
          exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)
        show ĝ i ∈ (N.comap π.toMonoidHom : Subgroup (freeProP p d))
        rw [Subgroup.mem_comap]
        show π (ĝ i) ∈ N
        rw [hĝ i]
        exact hgi
    · -- `π⁻¹ N ≤ M`
      have hMcpt : IsCompact (M : Set (freeProP p d)) := hMclosed.isCompact
      have himgclosed : IsClosed ((Subgroup.map π.toMonoidHom M : Subgroup G) : Set G) := by
        have : ((Subgroup.map π.toMonoidHom M : Subgroup G) : Set G) = π '' (M : Set _) := rfl
        rw [this]
        exact (hMcpt.image π.continuous_toFun).isClosed
      haveI : (Subgroup.map π.toMonoidHom M).Normal := hMnormal.map _ hsurj
      have hNle : N ≤ Subgroup.map π.toMonoidHom M := by
        rw [hN]
        refine Subgroup.topologicalClosure_minimal _ ?_ himgclosed
        refine Subgroup.normalClosure_le_normal ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨ĝ i, Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (hgsub ⟨i, rfl⟩)),
          hĝ i⟩
      intro x hx
      rw [Subgroup.mem_comap] at hx
      obtain ⟨y, hyM, hy⟩ := hNle hx
      have hxy : x * y⁻¹ ∈ MonoidHom.ker π.toMonoidHom := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hy, mul_inv_cancel]
      have : x * y⁻¹ ∈ M := hkerM hxy
      simpa using M.mul_mem this hyM
  -- conclude
  have hmem : ((m + k : ℕ) : ℕ∞) ∈ {c : ℕ∞ | ∃ (d' : ℕ) (m' : ℕ) (π'' : freeProP p d' →ₜ* (G ⧸ N))
      (rels'' : Fin m' → freeProP p d'),
      (d' : ℕ∞) = dRank (G ⧸ N) ∧ IsProPPresentation p d' π'' rels'' ∧ (m' : ℕ∞) = c} :=
    ⟨d, m + k, π', rels', hdr.trans hdrank.symm, ⟨hsurj', hMker⟩, rfl⟩
  calc relRank p (G ⧸ N) ≤ ((m + k : ℕ) : ℕ∞) := sInf_le hmem
    _ = (m : ℕ∞) + (k : ℕ∞) := by push_cast; ring

end Workspace.ProofLemmas.ProPRelationRank

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8;
-- H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10; J. D. Dixon, M. P. F. du
-- Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
-- Paper label: Proposition 3.3 (second assertion) / Proposition A.8, relation-rank half.
--
-- This is the relation-rank half of `ProPFrattiniQuotientRanks`: if `g_1,…,g_k ∈ Φ(G)` and `N` is
-- the closed normal subgroup they generate, then `r(G/N) ≤ r(G) + k`.  (The generator-rank half
-- `d(G/N) = d(G)` is proved separately in `ProPFrattiniQuotientRanks.lean`.)
--
-- The presentation-lifting argument is carried out in `Workspace.ProofLemmas.ProPRelationRank`:
-- take a minimal pro-p presentation `π : freeProP p d(G) ↠ G` realising `r(G)` relations, lift each
-- `g_i` to `ĝ_i` and adjoin the `ĝ_i` as `k` new relations.  The composite `π' = (G ↠ G/N) ∘ π` is
-- surjective and its kernel `π⁻¹(N)` equals the closed normal closure `M` of the enlarged family:
--   * `M ≤ π⁻¹(N)`: the latter is a closed normal subgroup containing every new relation;
--   * `π⁻¹(N) ≤ M`: `M` is closed in the COMPACT group `freeProP p d`, so `π(M)` is a closed normal
--     subgroup of `G` containing every `g_i`, hence `N ≤ π(M)`; with `ker π ≤ M` this gives the
--     reverse inclusion.
-- Together with the generator-rank half `d(G/N) = d(G)` this presentation witnesses
-- `r(G/N) ≤ r(G) + k`.




open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.3 / A.8, relation-rank half.** If `g_1, …, g_k ∈ Φ(G)` and `N` is
the closed normal subgroup they generate, then `r(G/N) ≤ r(G) + k`.  This is the relation-rank
half of `ProPFrattiniQuotientRanks`; the generator-rank half is proved separately. -/
theorem ProPRelationRankFrattiniQuotient (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    relRank p (G ⧸ N) ≤ relRank p G + (k : ℕ∞) :=
  Workspace.ProofLemmas.ProPRelationRank.proPRelationRankFrattiniQuotient
    p G hpro hfg k g hg N hN

-- Cited from: L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010, Section 2.8; H. Koch, Galois Theory of p-Extensions, Springer, 2002, Theorem 4.10; J. D. Dixon, M. P. F. du Sautoy, A. Mann, D. Segal, Analytic Pro-p Groups, 2nd ed., CUP, 1999, Proposition 1.9(ii).
-- Paper label: Proposition 3.3 (second assertion) / Proposition A.8
-- NL statement: Let G be a finitely generated pro-p group, let g_1, ..., g_k be elements of the Frattini subgroup Phi(G), and let N be the closed normal subgroup they generate (their closed normal closure). Then d(G/N) = d(G) and r(G/N) <= r(G) + k.
--
-- This theorem splits into two independent halves:
--   * the generator-rank half  d(G/N) = d(G)  is proved here from Mathlib together with the
--     Burnside/Frattini siblings `ProPGeneratorRankFrattini` (d(G) = dim_{F_p} G/Φ(G)),
--     `SublemmaProPQuotientClosed` (G/N is pro-p for N closed normal), and
--     `SublemmaTopFinGenQuotientClosed` (G/N is top. finitely generated).  The key step
--     (`frattini_comap_eq`) is the correspondence of maximal open subgroups: since N ⊆ Φ(G), every
--     maximal open subgroup of G contains N, so the maximal-open subgroups of G/N pull back
--     bijectively to those of G, giving Φ(G) = (Φ(G/N)).comap (G ↠ G/N); the induced
--     G/Φ(G) ≅ (G/N)/Φ(G/N) equates the two Frattini quotients' cardinalities, hence d(G)=d(G/N)
--     via the Burnside rank formula applied to both groups.
--   * the relation-rank half  r(G/N) ≤ r(G) + k  is a free-pro-p presentation-lifting statement,
--     cited as `ProPRelationRankFrattiniQuotient`.







set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

namespace ProPFrattiniQuotientRanksAux

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {N : Subgroup G} [N.Normal]

/-- The comap of a maximal open subgroup of `G/N` (along `G ↠ G/N`) is a maximal open subgroup
of `G`. -/
theorem comap_maximalOpen (Mbar : Subgroup (G ⧸ N))
    (hMbar : IsMaximalOpenSubgroup Mbar) :
    IsMaximalOpenSubgroup (Mbar.comap (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hπcont : Continuous π := QuotientGroup.continuous_mk
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_comap]; exact hπcont.isOpen_preimage _ hMbar.1
  · intro htop
    apply hMbar.2.1
    have h := Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar
    rw [htop, Subgroup.map_top_of_surjective π hπsurj] at h
    exact h.symm
  · intro K hKopen hMK
    have hNcomap : N ≤ Mbar.comap π := by
      intro x hx
      rw [Subgroup.mem_comap]
      have hx1 : π x = 1 := by
        rw [hπ, QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [hx1]; exact one_mem _
    have hNK : N ≤ K := le_trans hNcomap hMK
    have hcomapmapK : (K.map π).comap π = K := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNK
    have hmapKopen : IsOpen ((K.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
      rw [Subgroup.coe_map]
      exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hKopen
    have hMbarle : Mbar ≤ K.map π := by
      have h := Subgroup.map_mono (f := π) hMK
      rwa [Subgroup.map_comap_eq_self_of_surjective hπsurj Mbar] at h
    rcases hMbar.2.2 (K.map π) hmapKopen hMbarle with h | h
    · left; rw [← hcomapmapK, h]
    · right; rw [← hcomapmapK, h, Subgroup.comap_top]

/-- For a maximal open subgroup `M` of `G` containing `N`, its image `M.map (G ↠ G/N)` is a maximal
open subgroup of `G/N`. -/
theorem map_maximalOpen (M : Subgroup G) (hM : IsMaximalOpenSubgroup M) (hNM : N ≤ M) :
    IsMaximalOpenSubgroup (M.map (QuotientGroup.mk' N)) := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcm : (M.map π).comap π = M := by
    rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
    exact sup_eq_left.mpr hNM
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact (QuotientGroup.isOpenQuotientMap_mk).isOpenMap _ hM.1
  · intro htop
    apply hM.2.1
    rw [← hcm, htop, Subgroup.comap_top]
  · intro Kbar hKbaropen hMKbar
    have hcomapKbaropen : IsOpen ((Kbar.comap π : Subgroup G) : Set G) := by
      rw [Subgroup.coe_comap]
      exact (QuotientGroup.continuous_mk).isOpen_preimage _ hKbaropen
    have hMcomap : M ≤ Kbar.comap π := by
      rw [← hcm]; exact Subgroup.comap_mono hMKbar
    rcases hM.2.2 (Kbar.comap π) hcomapKbaropen hMcomap with h | h
    · left
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h]
    · right
      have hkk := Subgroup.map_comap_eq_self_of_surjective hπsurj Kbar
      rw [← hkk, h, Subgroup.map_top_of_surjective π hπsurj]

/-- **Correspondence step.** If `N ⊆ Φ(G)`, the topological Frattini subgroup of `G` is the
preimage of the topological Frattini subgroup of `G/N` along `G ↠ G/N`. -/
theorem frattini_comap_eq (hNsub : N ≤ frattiniOpen G) :
    (frattiniOpen (G ⧸ N)).comap (QuotientGroup.mk' N) = frattiniOpen G := by
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    rw [frattiniOpen, Subgroup.mem_sInf]
    intro M hM
    have hNM : N ≤ M := le_trans hNsub (by rw [frattiniOpen]; exact sInf_le hM)
    have hmapM : IsMaximalOpenSubgroup (M.map π) := map_maximalOpen M hM hNM
    have hcm : (M.map π).comap π = M := by
      rw [Subgroup.comap_map_eq, show π.ker = N from QuotientGroup.ker_mk' N]
      exact sup_eq_left.mpr hNM
    have hπxM : π x ∈ M.map π := by
      have hle : frattiniOpen (G ⧸ N) ≤ M.map π := by rw [frattiniOpen]; exact sInf_le hmapM
      exact hle hx
    have hxcomap : x ∈ (M.map π).comap π := by rw [Subgroup.mem_comap]; exact hπxM
    rwa [hcm] at hxcomap
  · intro x hx
    rw [Subgroup.mem_comap, frattiniOpen, Subgroup.mem_sInf]
    intro Mbar hMbar
    have hcomapMax : IsMaximalOpenSubgroup (Mbar.comap π) := comap_maximalOpen Mbar hMbar
    have hxin : x ∈ Mbar.comap π := by
      have hle : frattiniOpen G ≤ Mbar.comap π := by rw [frattiniOpen]; exact sInf_le hcomapMax
      exact hle hx
    rwa [Subgroup.mem_comap] at hxin

/-- The generator-rank half of Proposition 3.3: `d(G/N) = d(G)`. -/
theorem main (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    dRank (G ⧸ N) = dRank G := by
  -- N ⊆ Φ(G)
  haveI hΦnorm : (frattiniOpen G).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p G hpro hfg
  have hΦopen : IsOpen ((frattiniOpen G : Subgroup G) : Set G) :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_isOpen p G hpro hfg
  have hΦclosed : IsClosed ((frattiniOpen G : Subgroup G) : Set G) :=
    Subgroup.isClosed_of_isOpen _ hΦopen
  have hrange : Set.range g ⊆ (frattiniOpen G : Set G) := by
    rintro _ ⟨i, rfl⟩; exact hg i
  have hnc : Subgroup.normalClosure (Set.range g) ≤ frattiniOpen G :=
    Subgroup.normalClosure_le_normal hrange
  have hNsub : N ≤ frattiniOpen G := by
    rw [hN]; exact Subgroup.topologicalClosure_minimal _ hnc hΦclosed
  have hNclosed : IsClosed (N : Set G) := by
    rw [hN]; exact Subgroup.isClosed_topologicalClosure _
  -- quotient is pro-p and top. finitely generated
  have hproQ : IsProP p (G ⧸ N) := SublemmaProPQuotientClosed p G N hNclosed hpro
  have hfgQ : TopFinitelyGenerated (G ⧸ N) := SublemmaTopFinGenQuotientClosed G N hfg
  haveI hNormQ : (frattiniOpen (G ⧸ N)).Normal :=
    ProPGeneratorRankFrattiniAux.frattiniOpen_normal p (G ⧸ N) hproQ hfgQ
  -- Burnside rank formula for both groups
  obtain ⟨d, hdrank, hdcard⟩ := ProPGeneratorRankFrattini p G hpro hfg
  obtain ⟨d', hd'rank, hd'card⟩ := ProPGeneratorRankFrattini p (G ⧸ N) hproQ hfgQ
  -- Frattini quotients have equal cardinality via  G/Φ(G) ≅ (G/N)/Φ(G/N)
  have hcardeq : Nat.card (G ⧸ frattiniOpen G)
      = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := by
    set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
    set σ : G →* ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) :=
      (QuotientGroup.mk' (frattiniOpen (G ⧸ N))).comp π with hσ
    have hσsurj : Function.Surjective σ := by
      rw [hσ, MonoidHom.coe_comp]
      exact (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
    have hkerσ : σ.ker = frattiniOpen G := by
      have h1 : σ.ker = (frattiniOpen (G ⧸ N)).comap π := by
        rw [hσ, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rw [h1]; exact frattini_comap_eq hNsub
    have e := QuotientGroup.quotientKerEquivOfSurjective σ hσsurj
    have hc : Nat.card (G ⧸ σ.ker)
        = Nat.card ((G ⧸ N) ⧸ frattiniOpen (G ⧸ N)) := Nat.card_congr e.toEquiv
    rwa [hkerσ] at hc
  -- conclude d = d', hence dRank equal
  rw [hdcard, hd'card] at hcardeq
  have hdd : d = d' := Nat.pow_right_injective (Fact.out : p.Prime).two_le hcardeq
  rw [hd'rank, hdrank, hdd]

end ProPFrattiniQuotientRanksAux

/-- **Proposition 3.3, Frattini quotient.** If `g_1, …, g_k ∈ Φ(G)` and `N` is the closed
normal subgroup they generate, then `d(G/N) = d(G)` and `r(G/N) ≤ r(G) + k`.  The generator-rank
half is proved from Mathlib and the Burnside/Frattini siblings; the relation-rank half is cited
from `ProPRelationRankFrattiniQuotient`. -/
theorem ProPFrattiniQuotientRanks (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G)
    (k : ℕ) (g : Fin k → G) (hg : ∀ i, g i ∈ frattiniOpen G)
    (N : Subgroup G) [N.Normal]
    (hN : N = (Subgroup.normalClosure (Set.range g)).topologicalClosure) :
    dRank (G ⧸ N) = dRank G ∧ relRank p (G ⧸ N) ≤ relRank p G + (k : ℕ∞) :=
  ⟨ProPFrattiniQuotientRanksAux.main p G hpro hfg k g hg N hN,
   ProPRelationRankFrattiniQuotient p G hpro hfg k g hg N hN⟩

/-!
# The Golod–Shafarevich generating-function argument

`gs_core`: if a sequence `c : ℕ → ℕ` satisfies `c 0 = 1`, `c 1 = d`, the *filtration inequality*
`d · c (n+1) ≤ c (n+2) + r · c n`, and vanishes eventually, then `1 ≤ d` forces `d² < 4r`.

Proof.  If `r = 0` the recursion gives `c (n+2) ≥ d · c (n+1) ≥ c (n+1)`, so `c` never vanishes —
contradiction.  So `r ≥ 1`; if `d² ≥ 4r`, the polynomial `r t² − d t + 1` has the positive root
`t₀ = (d − √(d²−4r))/(2r)`.  Summing the filtration inequality against `t₀ⁿ⁺²` and telescoping,
`0 ≤ A·(1 − d t₀ + r t₀²) − 1 = −1` where `A = ∑ₙ cₙ t₀ⁿ` — contradiction.

`one_le_dRank`: a nontrivial Hausdorff topological group has generator rank at least `1`
(the empty set topologically generates only the trivial group).
-/

open Finset
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.GolodShafarevichCore

/-- **The Golod–Shafarevich generating-function argument.**
If a sequence `c` of naturals satisfies `c 0 = 1`, `c 1 = d`, the filtration inequality
`d · c (n+1) ≤ c (n+2) + r · c n`, and vanishes eventually, then `d ≥ 1` forces `d² < 4r`. -/
theorem gs_core (d r : ℕ) (hd1 : 1 ≤ d) (c : ℕ → ℕ)
    (hc0 : c 0 = 1) (hc1 : c 1 = d)
    (hrec : ∀ n, d * c (n + 1) ≤ c (n + 2) + r * c n)
    (N : ℕ) (hN : ∀ n, N ≤ n → c n = 0) :
    d ^ 2 < 4 * r := by
  by_contra hcon
  push_neg at hcon
  -- `r = 0` is impossible: the recursion would force `c` to grow
  have hr1 : 1 ≤ r := by
    by_contra hr0
    push_neg at hr0
    interval_cases r
    · -- `c (n+2) ≥ d * c (n+1) ≥ c (n+1)`, so `c n ≥ 1` for all `n ≥ 1`
      have hgrow : ∀ n, 1 ≤ c (n + 1) := by
        intro n
        induction n with
        | zero => rw [hc1]; exact hd1
        | succ k ih =>
            have := hrec k
            simp only [Nat.zero_mul, Nat.add_zero] at this
            calc 1 ≤ c (k + 1) := ih
              _ ≤ d * c (k + 1) := Nat.le_mul_of_pos_left _ hd1
              _ ≤ c (k + 2) := this
      have := hgrow N
      rw [hN (N + 1) (by omega)] at this
      omega
  -- the smaller root `t₀ > 0` of `r t² - d t + 1`
  set D : ℝ := Real.sqrt ((d : ℝ) ^ 2 - 4 * r) with hD
  have hdisc : (0 : ℝ) ≤ (d : ℝ) ^ 2 - 4 * r := by
    have : (4 : ℝ) * r ≤ (d : ℝ) ^ 2 := by exact_mod_cast hcon
    linarith
  have hDsq : D ^ 2 = (d : ℝ) ^ 2 - 4 * r := Real.sq_sqrt hdisc
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hDlt : D < (d : ℝ) := by
    nlinarith [hDsq, hD0, hrR]
  set t : ℝ := ((d : ℝ) - D) / (2 * r) with ht
  have ht0 : 0 < t := by
    rw [ht]
    apply div_pos (by linarith) (by linarith)
  have hroot : 1 - (d : ℝ) * t + (r : ℝ) * t ^ 2 = 0 := by
    rw [ht]
    field_simp
    nlinarith [hDsq]
  -- the partial sums of the generating function
  have hSstab : ∀ M, N ≤ M → ∑ n ∈ Finset.range M, (c n : ℝ) * t ^ n
      = ∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n := by
    intro M hM
    refine (Finset.sum_subset (Finset.range_mono hM) ?_).symm
    intro n _ hnN
    rw [Finset.mem_range] at hnN
    push_neg at hnN
    rw [hN n hnN]
    simp
  -- shift identities
  have hshift1 : ∀ M : ℕ, ∑ n ∈ Finset.range M, (c (n + 1) : ℝ) * t ^ (n + 1)
      = (∑ n ∈ Finset.range (M + 1), (c n : ℝ) * t ^ n) - (c 0 : ℝ) := by
    intro M
    have h := Finset.sum_range_succ' (fun n => (c n : ℝ) * t ^ n) M
    simp only [pow_zero, mul_one] at h
    rw [h]
    ring
  have hshift2 : ∀ M : ℕ, ∑ n ∈ Finset.range M, (c (n + 2) : ℝ) * t ^ (n + 2)
      = (∑ n ∈ Finset.range (M + 2), (c n : ℝ) * t ^ n) - (c 0 : ℝ) - (c 1 : ℝ) * t := by
    intro M
    have h1 := hshift1 (M + 1)
    have h2 : ∑ n ∈ Finset.range (M + 1), (c (n + 1) : ℝ) * t ^ (n + 1)
        = (c 1 : ℝ) * t + ∑ n ∈ Finset.range M, (c (n + 2) : ℝ) * t ^ (n + 2) := by
      have h := Finset.sum_range_succ' (fun n => (c (n + 1) : ℝ) * t ^ (n + 1)) M
      simp only [pow_one] at h
      rw [h]
      ring
    rw [h2] at h1
    linarith
  -- sum the filtration inequality
  have hnonneg : (0 : ℝ) ≤
      ∑ n ∈ Finset.range N,
        (((c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ)) - (d : ℝ) * (c (n + 1) : ℝ)) * t ^ (n + 2) := by
    refine Finset.sum_nonneg ?_
    intro n _
    have h := hrec n
    have h' : (d : ℝ) * (c (n + 1) : ℝ) ≤ (c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ) := by
      exact_mod_cast h
    have hpow : (0 : ℝ) ≤ t ^ (n + 2) := le_of_lt (pow_pos ht0 _)
    nlinarith
  -- expand the sum
  have hexpand :
      ∑ n ∈ Finset.range N,
        (((c (n + 2) : ℝ) + (r : ℝ) * (c n : ℝ)) - (d : ℝ) * (c (n + 1) : ℝ)) * t ^ (n + 2)
      = (∑ n ∈ Finset.range N, (c (n + 2) : ℝ) * t ^ (n + 2))
        + (r : ℝ) * t ^ 2 * (∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n)
        - (d : ℝ) * t * (∑ n ∈ Finset.range N, (c (n + 1) : ℝ) * t ^ (n + 1)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [hexpand, hshift1 N, hshift2 N, hSstab (N + 2) (by omega), hSstab (N + 1) (by omega),
    hc0, hc1] at hnonneg
  set A : ℝ := ∑ n ∈ Finset.range N, (c n : ℝ) * t ^ n with hA
  push_cast at hnonneg
  have key : A - 1 - (d : ℝ) * t + (r : ℝ) * t ^ 2 * A - (d : ℝ) * t * (A - 1)
      = A * (1 - (d : ℝ) * t + (r : ℝ) * t ^ 2) - 1 := by ring
  rw [key, hroot, mul_zero] at hnonneg
  linarith




/-- A nontrivial (Hausdorff) topological group has generator rank at least `1`. -/
theorem one_le_dRank (G : Type*) [Group G] [TopologicalSpace G] [T2Space G]
    (hnt : Nontrivial G) : 1 ≤ dRank G := by
  by_contra h
  push_neg at h
  have h0 : dRank G = 0 := by
    rcases eq_or_ne (dRank G) 0 with h' | h'
    · exact h'
    · exact absurd h (not_lt.mpr (Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h')))
  -- `0` is then a member of the defining set
  have hmem : (0 : ℕ∞) ∈ {n : ℕ∞ | ∃ S : Finset G, TopologicallyGenerates (S : Set G) ∧
      (S.card : ℕ∞) = n} := by
    by_contra hcon
    have : (1 : ℕ∞) ≤ dRank G := by
      rw [dRank]
      refine le_sInf ?_
      intro b hb
      rcases eq_or_ne b 0 with rfl | hb0
      · exact absurd hb hcon
      · exact Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr hb0)
    rw [h0] at this
    simp at this
  obtain ⟨S, hgen, hcard⟩ := hmem
  have hS : S = ∅ := by
    have : S.card = 0 := by exact_mod_cast hcard
    exact Finset.card_eq_zero.mp this
  subst hS
  rw [TopologicallyGenerates] at hgen
  simp only [Finset.coe_empty, Subgroup.closure_empty] at hgen
  have h1 : ((⊥ : Subgroup G) : Set G) = {(1 : G)} := by simp
  rw [h1, closure_singleton] at hgen
  obtain ⟨x, y, hxy⟩ := hnt
  have hx : x ∈ ({(1 : G)} : Set G) := by rw [hgen]; trivial
  have hy : y ∈ ({(1 : G)} : Set G) := by rw [hgen]; trivial
  simp only [Set.mem_singleton_iff] at hx hy
  exact hxy (hx.trans hy.symm)



end Workspace.ProofLemmas.GolodShafarevichCore

-- Cited from: E. S. Golod and I. R. Shafarevich, On the class field tower, Izv. Akad. Nauk SSSR
-- Ser. Mat. 28(2):261-272, 1964; H. Koch, Galois Theory of p-Extensions, Springer, 2002, Ch. 11
-- (the filtration inequality for the augmentation ideal of the completed group algebra).
-- Paper label: Proposition 3.4 / Proposition A.9 (technical core)
--
-- The cited result was
--   d(G)² < 4·r(G)   for a finite nontrivial finitely generated pro-p group G.
-- The generating-function deduction is proved from Mathlib in
-- `Workspace.ProofLemmas.GolodShafarevichCore.gs_core`: from `c 0 = 1`, `c 1 = d`, the inequality
-- `d·c(n+1) ≤ c(n+2) + r·c n` and eventual vanishing of `c`, one gets `d² < 4r` by summing against
-- `t₀ⁿ⁺²` at the positive root `t₀` of `r t² − d t + 1`.
--
-- What remains admitted is exactly the module-theoretic input: the Hilbert function
--   c n  =  dim_{𝔽_p} (Iⁿ / Iⁿ⁺¹)
-- of the augmentation ideal `I` of `𝔽_p[G]` satisfies `c 0 = 1`, `c 1 = d(G)`, the filtration
-- inequality with `r = r(G)` (this comes from the minimal free presentation
-- `Ω^r → Ω^d → Ω → 𝔽_p → 0` of the completed group algebra), and vanishes eventually because `I` is
-- nilpotent for finite `G`.  Mathlib has neither the completed group algebra of a pro-p group nor
-- this filtration estimate.
--
-- NL statement: For a finite nontrivial topologically finitely generated pro-p group G with
-- generator rank d and relation rank r, there is a sequence c : ℕ → ℕ (the dimensions of the
-- successive quotients of the augmentation filtration of 𝔽_p[G]) with c 0 = 1, c 1 = d,
-- d * c (n+1) ≤ c (n+2) + r * c n for all n, and c n = 0 for all large n.



open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Golod–Shafarevich filtration inequality.**  The Hilbert function of the
augmentation filtration of `𝔽_p[G]` exists with the stated properties. -/
axiom GolodShafarevichFiltration (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hfin : Finite G) (hnt : Nontrivial G)
    (d r : ℕ) (hd : (d : ℕ∞) = dRank G) (hr : (r : ℕ∞) = relRank p G) :
    ∃ c : ℕ → ℕ, c 0 = 1 ∧ c 1 = d ∧
      (∀ n, d * c (n + 1) ≤ c (n + 2) + r * c n) ∧
      (∃ N, ∀ n, N ≤ n → c n = 0)

-- Cited from: E. S. Golod and I. R. Shafarevich, On the class field tower, Izv. Akad. Nauk SSSR Ser. Mat. 28(2):261-272, 1964 (English transl. AMS Transl. (2) 48 (1965), 91-102); H. Koch, Galois Theory of p-Extensions, Springer, 2002, Chapter 11.
-- Paper label: Proposition 3.4 (Golod-Shafarevich inequality) / Proposition A.9
-- NL statement: If a finite nontrivial finitely generated pro-p group G has generator rank d(G) and relation rank r(G), then r(G) > d(G)^2 / 4 (division-free: d(G)^2 < 4 r(G)).
--
-- The generating-function argument — the "clever" half of Golod–Shafarevich — is proved from
-- Mathlib in `Workspace.ProofLemmas.GolodShafarevichCore.gs_core`, as is the fact that a nontrivial
-- pro-p group has generator rank ≥ 1 and that d(G) is finite for a topologically finitely generated
-- G.  The only admitted input is `Workspace.PriorWork.GolodShafarevichFiltration` (the Hilbert
-- function of the augmentation filtration of 𝔽_p[G]).





open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.4 (Golod–Shafarevich).** A finite nontrivial (finitely generated) pro-`p`
group has `r(G) > d(G)^2 / 4` (division-free: `d(G)^2 < 4·r(G)`). -/
theorem GolodShafarevichInequality (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hfin : Finite G) (hnt : Nontrivial G) :
    (dRank G) ^ 2 < 4 * relRank p G := by
  obtain ⟨_, _, hT2, _, _⟩ := hpro
  haveI := hT2
  -- `dRank G` is finite
  obtain ⟨S₀, hS₀⟩ := hfg
  have hdle : dRank G ≤ (S₀.card : ℕ∞) := sInf_le ⟨S₀, hS₀, rfl⟩
  have hdne : dRank G ≠ ⊤ := by
    intro h
    rw [h] at hdle
    exact (ENat.coe_ne_top S₀.card) (top_le_iff.mp hdle)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hdne
  have hd1 : 1 ≤ d := by
    have := Workspace.ProofLemmas.GolodShafarevichCore.one_le_dRank G hnt
    rw [← hd] at this
    exact_mod_cast this
  by_cases hr : relRank p G = ⊤
  · rw [hr, ← hd]
    have h4 : (4 : ℕ∞) * ⊤ = ⊤ := by
      simp
    rw [h4]
    refine lt_of_le_of_ne le_top ?_
    have : ((d : ℕ∞)) ^ 2 = ((d ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
    rw [this]
    exact ENat.coe_ne_top _
  · obtain ⟨r, hrr⟩ := ENat.ne_top_iff_exists.mp hr
    obtain ⟨c, hc0, hc1, hrec, N, hN⟩ :=
      GolodShafarevichFiltration p G ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩ ⟨S₀, hS₀⟩ hfin hnt d r hd hrr
    have hcore := Workspace.ProofLemmas.GolodShafarevichCore.gs_core d r hd1 c hc0 hc1 hrec N hN
    rw [← hd, ← hrr]
    exact_mod_cast hcore

-- Proposition 3.4 (contrapositive form) / Proposition A.9.
-- Derived as the pure contrapositive of the Golod-Shafarevich inequality
-- (`Workspace.ProofLemmas.GolodShafarevichInequality`): a nontrivial finitely
-- generated pro-p group with 4 r(G) <= d(G)^2 is infinite.




open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 800000

/-- **Proposition 3.4 (Golod–Shafarevich, contrapositive).** A nontrivial finitely generated
pro-`p` group with `4·r(G) ≤ d(G)^2` is infinite. -/
theorem GolodShafarevichInfinite (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hnt : Nontrivial G)
    (hgs : 4 * relRank p G ≤ (dRank G) ^ 2) : Infinite G := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have h := GolodShafarevichInequality p G hpro hfg hfin hnt
  exact lt_irrefl _ (lt_of_lt_of_le h hgs)

open scoped NumberField

open Workspace.Types.SplittingRamification
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

set_option maxHeartbeats 1000000

theorem FrobeniusKillingInfiniteQuotient :
    ∃ L₀ : ℕ, ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → IsGalois ℚ F →
      Module.finrank ℚ F = 3 →
      (¬ ∃ x : F, IsPrimitiveRoot x 3) →
      IsProP 3 (galUr 3 F) →
      TopFinitelyGenerated (galUr 3 F) →
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 F) →
        ∀ (q : Fin ((ℓ - 1) ^ 2 / 100) → ℕ),
          Function.Injective q →
          (∀ b, SplitsCompletelyRat (q b) F) →
          ∀ (σ : (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
                    {v : Ideal (𝓞 F) //
                      v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) →
                  galUr 3 F),
            (∀ w, IsFrobeniusRepAt 3 F (σ w) (w.2 : Ideal (𝓞 F))) →
            (∀ w, σ w ∈ frattiniOpen (galUr 3 F)) →
            ∀ (N : Subgroup (galUr 3 F)) [N.Normal],
              N = (Subgroup.normalClosure (Set.range σ)).topologicalClosure →
                Nontrivial (galUr 3 F ⧸ N) ∧
                  Infinite (galUr 3 F ⧸ N) ∧
                  TopFinitelyGenerated (galUr 3 F ⧸ N) ∧
                  IsProP 3 (galUr 3 F ⧸ N) ∧
                  dRank (galUr 3 F ⧸ N) = dRank (galUr 3 F) ∧
                  4 * relRank 3 (galUr 3 F ⧸ N) ≤ (dRank (galUr 3 F ⧸ N)) ^ 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Step 0.1: extract the absolute Shafarevich constant `C₀`.
  obtain ⟨C₀, hC₀⟩ := ShafarevichRelationRank
  -- Step 0.3: the threshold `L₀ = max 2 (d₀ + 1)` with `d₀ = 8·C₀ + 6`, uniform in `F`.
  refine ⟨max 2 (8 * C₀ + 6 + 1), ?_⟩
  -- Step 1: introduce all binders.
  intro F _ _ hTR hGal hdeg hnoζ hpro hfg ℓ hℓ hgen q hqinj hqsplit σ hσfrob hσfrat N _ hN
  -- topological-group instance on `G = galUr 3 F` (first conjunct of `IsProP`).
  haveI hTG : IsTopologicalGroup (galUr 3 F) := hpro.1
  -- Step 2: Burnside basis — `d(G)` is the finite natural `d`.
  obtain ⟨hcomm, hpow, d, hdG, hcard⟩ := ProPBurnsideBasis 3 (galUr 3 F) hpro hfg
  -- Step 3: `ℓ - 1 ≤ d`.
  rw [hdG] at hgen
  have hd_ge_l : ℓ - 1 ≤ d := by exact_mod_cast hgen
  -- threshold consequences.
  have h2 : 2 ≤ max 2 (8 * C₀ + 6 + 1) := le_max_left _ _
  have hd0 : 8 * C₀ + 6 + 1 ≤ max 2 (8 * C₀ + 6 + 1) := le_max_right _ _
  -- Step 4: `d ≥ d₀` and `d ≥ 1`.
  have hd_ge_d0 : 8 * C₀ + 6 ≤ d := by omega
  have hd_ge_1 : 1 ≤ d := by omega
  -- Step 5: the index type is `σ`'s domain; establish finiteness and cardinality `3·t`.
  -- each fibre is finite of cardinality 3.
  have hfib : ∀ b : Fin ((ℓ - 1) ^ 2 / 100),
      Nat.card {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)} = 3 := by
    intro b
    have h := (hqsplit b).2.1
    rw [hdeg] at h
    rw [Nat.card_coe_set_eq]; exact h
  have hfin : ∀ b : Fin ((ℓ - 1) ^ 2 / 100),
      Finite {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)} := by
    intro b
    have h := (hqsplit b).2.1
    rw [hdeg] at h
    exact (Set.finite_of_ncard_ne_zero (by rw [h]; norm_num)).to_subtype
  -- `Finite` instance on `σ`'s domain.
  haveI hSfin : Finite (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) := inferInstance
  have hcardS : Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})
      = 3 * ((ℓ - 1) ^ 2 / 100) := by
    rw [Nat.card_sigma]
    simp only [hfib]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  -- Step 5.3 + Step 6: reindex `σ` by `Fin (Nat.card S)` and restate `N`, keeping the
  -- ORIGINAL `σ` (no `set`, which would introduce a fresh, unrelated `σ`).
  have hrange : Set.range (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) = Set.range σ := by
    rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have hN' : N = (Subgroup.normalClosure
      (Set.range (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm))).topologicalClosure := by
    rw [hrange]; exact hN
  have hg : ∀ i, (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) i ∈
      frattiniOpen (galUr 3 F) :=
    fun i => hσfrat ((Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
      {v : Ideal (𝓞 F) //
        v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm i)
  -- Step 7: generator and relation ranks of `Ḡ = G ⧸ N`.
  obtain ⟨hdbar, hrbar⟩ :=
    ProPFrattiniQuotientRanks 3 (galUr 3 F) hpro hfg
      (Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}))
      (σ ∘ (Finite.equivFin (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 F) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)})).symm) hg N hN'
  have hdbar' : dRank (galUr 3 F ⧸ N) = (d : ℕ∞) := hdbar.trans hdG
  -- Step 8a: Shafarevich bound `r(G) ≤ d + C₀`.
  have hrG : relRank 3 (galUr 3 F) ≤ dRank (galUr 3 F) + (C₀ : ℕ∞) := hC₀ F hTR hdeg
  rw [hdG] at hrG
  -- Step 8b: the count bound `100 · t ≤ d²`.
  have htk : 100 * ((ℓ - 1) ^ 2 / 100) ≤ d ^ 2 := by
    have h1 : 100 * ((ℓ - 1) ^ 2 / 100) ≤ (ℓ - 1) ^ 2 := Nat.mul_div_le _ _
    have h2' : (ℓ - 1) ^ 2 ≤ d ^ 2 := Nat.pow_le_pow_left hd_ge_l 2
    omega
  -- Step 8c: relation-rank chain `r(Ḡ) ≤ d + C₀ + 3t`.
  have hr_bound : relRank 3 (galUr 3 F ⧸ N) ≤
      ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) := by
    calc relRank 3 (galUr 3 F ⧸ N)
        ≤ (relRank 3 (galUr 3 F)) + ((Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
            {v : Ideal (𝓞 F) //
              v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) : ℕ) : ℕ∞) := hrbar
      _ ≤ ((d : ℕ∞) + (C₀ : ℕ∞)) + ((Nat.card (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
            {v : Ideal (𝓞 F) //
              v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F)}) : ℕ) : ℕ∞) := by gcongr
      _ = ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) := by
          rw [hcardS]; push_cast; ring
  -- Step 8d: the ℕ arithmetic core.
  have hquad : 400 * d + 400 * C₀ ≤ 88 * d ^ 2 := by nlinarith [hd_ge_d0]
  have harith : 4 * (d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100)) ≤ d ^ 2 := by
    nlinarith [htk, hquad]
  -- Step 8e: lift the margin to `ℕ∞`.
  have hGS : 4 * relRank 3 (galUr 3 F ⧸ N) ≤ (dRank (galUr 3 F ⧸ N)) ^ 2 := by
    have h4 : 4 * relRank 3 (galUr 3 F ⧸ N) ≤
        4 * ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) :=
      mul_le_mul_left' hr_bound 4
    refine le_trans h4 ?_
    rw [hdbar']
    have e1 : (4 : ℕ∞) * ((d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100) : ℕ) : ℕ∞) =
        ((4 * (d + C₀ + 3 * ((ℓ - 1) ^ 2 / 100)) : ℕ) : ℕ∞) := by
      push_cast; ring
    have e2 : ((d : ℕ∞)) ^ 2 = ((d ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
    rw [e1, e2]
    exact_mod_cast harith
  -- Step 9.1: `N` is closed.
  have hNclosed : IsClosed (N : Set (galUr 3 F)) := by
    rw [hN']; exact Subgroup.isClosed_topologicalClosure _
  -- Step 9.2: `Ḡ` is pro-`3`.
  have hproBar : IsProP 3 (galUr 3 F ⧸ N) :=
    SublemmaProPQuotientClosed 3 (galUr 3 F) N hNclosed hpro
  -- Step 9.3: `Ḡ` is topologically finitely generated.
  have hfgBar : TopFinitelyGenerated (galUr 3 F ⧸ N) :=
    SublemmaTopFinGenQuotientClosed (galUr 3 F) N hfg
  -- Step 10: `Ḡ` is nontrivial.
  obtain ⟨_, _, d', hd'bar, hcard'⟩ := ProPBurnsideBasis 3 (galUr 3 F ⧸ N) hproBar hfgBar
  have hdd' : d' = d := by
    have : (d' : ℕ∞) = (d : ℕ∞) := hd'bar.symm.trans hdbar'
    exact_mod_cast this
  have hd'ge1 : 1 ≤ d' := by omega
  have hfrat_fin :
      Finite ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard']; positivity)
  have hgt : 1 < Nat.card ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) := by
    rw [hcard']
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ d' := Nat.pow_le_pow_right (by norm_num) hd'ge1
  haveI : Finite ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) := hfrat_fin
  haveI hntFrat : Nontrivial ((galUr 3 F ⧸ N) ⧸ frattiniOpen (galUr 3 F ⧸ N)) :=
    Finite.one_lt_card_iff_nontrivial.mp hgt
  -- Derive nontriviality of `Ḡ` from the coset projection (no `Normal` instance needed).
  have hntBar : Nontrivial (galUr 3 F ⧸ N) :=
    (QuotientGroup.mk_surjective (s := frattiniOpen (galUr 3 F ⧸ N))).nontrivial
  -- Step 11: `Ḡ` is infinite.
  have hinfBar : Infinite (galUr 3 F ⧸ N) :=
    GolodShafarevichInfinite 3 (galUr 3 F ⧸ N) hproBar hfgBar hntBar hGS
  -- Step 12: assemble.
  exact ⟨hntBar, hinfBar, hfgBar, hproBar, hdbar, hGS⟩

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem UnramifiedProPTowerFields :
    ∀ (F : Type*) [Field F] [NumberField F]
      (N : Subgroup (galUr 3 F)) (hNnorm : N.Normal),
      IsClosed (N : Set (galUr 3 F)) →
        letI := hNnorm
        Infinite (galUr 3 F ⧸ N) →
          TopFinitelyGenerated (galUr 3 F ⧸ N) →
            IsProP 3 (galUr 3 F ⧸ N) →
              ∀ (H : ℕ → Subgroup (galUr 3 F)),
                (∀ j, (H j).Normal) →
                  (∀ j, IsOpen ((H j : Set (galUr 3 F)))) →
                    (∀ j, N ≤ H j) →
                      H 0 = ⊤ →
                        StrictAnti H →
                          (∀ j, 0 < (H j).index) →
                            Filter.Tendsto (fun j => (H j).index)
                                Filter.atTop Filter.atTop →
                              ∃ Fj : ℕ → IntermediateField F (AlgebraicClosure F),
                                (∀ j, Fj j =
                                    IntermediateField.map
                                      (IntermediateField.val (maxUnramifiedProPExt 3 F))
                                      (fixedFieldOf 3 F (H j))) ∧
                                  Fj 0 = ⊥ ∧ StrictMono Fj ∧
                                    Filter.Tendsto (fun j => Module.finrank ℚ ↥(Fj j))
                                      Filter.atTop Filter.atTop := by
  intro F _ _ N hNnorm hNclosed hNinf hNtfg hNprop H hHnorm hHopen hHN hH0 hSA hHpos hHtend
  -- Unpack the correspondence axiom, part (a): degree formula, injectivity, inclusion-reversal.
  obtain ⟨hGal, hInj, hRev, _hChain⟩ := UnramifiedProPTowerCorrespondence F
  -- The ambient embedding `ι : F^{ur,3} ↪ AlgebraicClosure F`.
  set ι := IntermediateField.val (maxUnramifiedProPExt 3 F) with hι
  -- The tower of fields.
  refine ⟨fun j => IntermediateField.map ι (fixedFieldOf 3 F (H j)), fun j => rfl, ?_, ?_, ?_⟩
  · -- Base layer: Fj 0 = ⊥.
    show IntermediateField.map ι (fixedFieldOf 3 F (H 0)) = ⊥
    have hbot : fixedFieldOf 3 F (H 0) = ⊥ := by
      rw [← IntermediateField.finrank_eq_one_iff]
      rw [(hGal (H 0) (hHnorm 0) (hHopen 0)).2.2.1, hH0, Subgroup.index_top]
    rw [hbot, IntermediateField.map_bot]
  · -- Strict monotonicity.
    refine strictMono_nat_of_lt_succ (fun j => ?_)
    have hlt : H (j + 1) < H j := hSA (Nat.lt_succ_self j)
    have hfle : fixedFieldOf 3 F (H j) ≤ fixedFieldOf 3 F (H (j + 1)) :=
      hRev (H (j + 1)) (H j) (hHnorm _) (hHopen _) (hHnorm _) (hHopen _) hlt.le
    have hfne : fixedFieldOf 3 F (H j) ≠ fixedFieldOf 3 F (H (j + 1)) := by
      intro heq
      exact hlt.ne' (hInj (H j) (H (j + 1)) (hHnorm _) (hHopen _) (hHnorm _) (hHopen _) heq)
    have hflt : fixedFieldOf 3 F (H j) < fixedFieldOf 3 F (H (j + 1)) :=
      lt_of_le_of_ne hfle hfne
    show IntermediateField.map ι (fixedFieldOf 3 F (H j)) <
        IntermediateField.map ι (fixedFieldOf 3 F (H (j + 1)))
    refine lt_of_le_of_ne (IntermediateField.map_mono ι hflt.le) ?_
    intro heq
    exact hfne (IntermediateField.map_injective ι heq)
  · -- Degrees diverge.
    have hdeg : ∀ j, Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
        = Module.finrank ℚ F * (H j).index := by
      intro j
      haveI hfd : FiniteDimensional F ↥(fixedFieldOf 3 F (H j)) :=
        (hGal (H j) (hHnorm j) (hHopen j)).2.1
      have hidx : Module.finrank F ↥(fixedFieldOf 3 F (H j)) = (H j).index :=
        (hGal (H j) (hHnorm j) (hHopen j)).2.2.1
      have hmapeq : Module.finrank F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
          = Module.finrank F ↥(fixedFieldOf 3 F (H j)) :=
        ((fixedFieldOf 3 F (H j)).equivMap ι).toLinearEquiv.finrank_eq.symm
      haveI : FiniteDimensional F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))) :=
        ((fixedFieldOf 3 F (H j)).equivMap ι).toLinearEquiv.finiteDimensional
      have htower : Module.finrank ℚ F
          * Module.finrank F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
          = Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))) :=
        Module.finrank_mul_finrank ℚ F ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j)))
      rw [← htower, hmapeq, hidx]
    have hkey : (fun j => Module.finrank ℚ ↥(IntermediateField.map ι (fixedFieldOf 3 F (H j))))
        = (fun j => Module.finrank ℚ F * (H j).index) := funext hdeg
    rw [hkey]
    have hc : 0 < Module.finrank ℚ F := Module.finrank_pos
    exact Filter.tendsto_atTop_mono (fun j => Nat.le_mul_of_pos_left _ hc) hHtend

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 1000000

namespace SublemmaLayerIsoAux

variable {R S S₁ : Type*} [CommRing R] [CommRing S] [CommRing S₁] [Algebra R S] [Algebra R S₁]

/-- `Ideal.map φ` composed with `Ideal.map φ.symm` is the identity. -/
lemma map_symm_map (φ : S ≃ₐ[R] S₁) (Q : Ideal S₁) :
    Ideal.map φ (Ideal.map φ.symm Q) = Q := by
  show Ideal.map (φ : S →+* S₁) (Ideal.map (φ.symm : S₁ →+* S) Q) = Q
  rw [Ideal.map_map]
  have h : ((φ : S →+* S₁).comp (φ.symm : S₁ →+* S)) = RingHom.id S₁ := by ext x; simp
  rw [h, Ideal.map_id]

/-- `Ideal.map φ` is injective for an algebra equivalence `φ`. -/
lemma map_injective (φ : S ≃ₐ[R] S₁) : Function.Injective (Ideal.map φ) := by
  have hleft : Function.LeftInverse (Ideal.comap φ) (Ideal.map φ) :=
    fun I => Ideal.comap_map_of_bijective φ φ.bijective
  exact hleft.injective

/-- The set of primes over `p` in `S₁` is the image under `Ideal.map φ` of those in `S`. -/
lemma primesOver_image (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    p.primesOver S₁ = Ideal.map φ '' p.primesOver S := by
  ext Q
  simp only [Ideal.primesOver, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hQp, hQl⟩
    refine ⟨Ideal.map φ.symm Q, ⟨?_, ?_⟩, map_symm_map φ Q⟩
    · haveI := hQp; exact Ideal.map_isPrime_of_equiv φ.symm
    · haveI := hQl; exact Ideal.map_equiv_liesOver Q p φ.symm
  · rintro ⟨P, ⟨hPp, hPl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · haveI := hPp; exact Ideal.map_isPrime_of_equiv φ
    · haveI := hPl; exact Ideal.map_equiv_liesOver P p φ

/-- The number of primes over `p` is preserved by an algebra equivalence. -/
lemma primesOver_ncard (φ : S ≃ₐ[R] S₁) (p : Ideal R) :
    (p.primesOver S₁).ncard = (p.primesOver S).ncard := by
  rw [primesOver_image φ p, Set.ncard_image_of_injective _ (map_injective φ)]

/-- Ramification index over `p` being `1` transfers along an algebra equivalence. -/
lemma ram_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ]
  exact h P hPmem

/-- Ramification index and inertia degree both being `1` transfers along an algebra equivalence. -/
lemma raminertia_transfer (φ : S ≃ₐ[R] S₁) (p : Ideal R)
    (h : ∀ P ∈ p.primesOver S, p.ramificationIdx P = 1 ∧ p.inertiaDeg P = 1) :
    ∀ Q ∈ p.primesOver S₁, p.ramificationIdx Q = 1 ∧ p.inertiaDeg Q = 1 := by
  intro Q hQ
  rw [primesOver_image φ p] at hQ
  obtain ⟨P, hPmem, rfl⟩ := hQ
  rw [Ideal.ramificationIdx_map_eq p P φ, Ideal.inertiaDeg_map_eq p P φ]
  exact h P hPmem

/-- Unramifiedness at infinite places transfers along an algebra equivalence over `F`. -/
lemma inf_transfer {F E Fj : Type*} [Field F] [Field E] [Field Fj]
    [Algebra F E] [Algebra F Fj] (e : E ≃ₐ[F] Fj)
    (hE : IsUnramifiedAtInfinitePlaces F E) : IsUnramifiedAtInfinitePlaces F Fj := by
  refine ⟨fun u => ?_⟩
  have hv := hE.isUnramified (u.comap (e : E →+* Fj))
  have h2 := hv.comap_algHom (e.symm : Fj →ₐ[F] E)
  have hcomp : (u.comap (e : E →+* Fj)).comap ((e.symm : Fj →ₐ[F] E) : Fj →+* E) = u := by
    rw [← NumberField.InfinitePlace.comap_comp]
    convert NumberField.InfinitePlace.comap_id u using 2
    ext x; simp
  rwa [hcomp] at h2

end SublemmaLayerIsoAux

theorem SublemmaLayerIso (F : Type*) [Field F] [NumberField F]
    (H : Subgroup (galUr 3 F))
    [FiniteDimensional F (fixedFieldOf 3 F H : Type _)] :
    haveI : NumberField (fixedFieldOf 3 F H : Type _) :=
      NumberField.of_module_finite F (fixedFieldOf 3 F H : Type _)
    ∃ _e : (fixedFieldOf 3 F H : Type _) ≃ₐ[F]
        (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
          (fixedFieldOf 3 F H) : Type _),
      ∃ _hfd : FiniteDimensional F
          (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
            (fixedFieldOf 3 F H) : Type _),
        haveI := _hfd
        haveI : NumberField
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _) :=
          NumberField.of_module_finite F
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _)
        (FiniteDimensional F (fixedFieldOf 3 F H : Type _) ↔
            FiniteDimensional F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (NumberField (fixedFieldOf 3 F H : Type _) ↔
            NumberField
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (IsGalois F (fixedFieldOf 3 F H : Type _) ↔
            IsGalois F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (EverywhereUnramified F (fixedFieldOf 3 F H : Type _) ↔
            EverywhereUnramified F
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (IsPGroup 3 ((fixedFieldOf 3 F H : Type _) ≃ₐ[F] (fixedFieldOf 3 F H : Type _)) →
            IsPGroup 3
              ((IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                  (fixedFieldOf 3 F H) : Type _) ≃ₐ[F]
                (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                  (fixedFieldOf 3 F H) : Type _))) ∧
        (NumberField.IsTotallyReal (fixedFieldOf 3 F H : Type _) ↔
            NumberField.IsTotallyReal
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) ∧
        (rootDiscriminant
            (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
              (fixedFieldOf 3 F H) : Type _) =
          rootDiscriminant (fixedFieldOf 3 F H : Type _)) ∧
        (∀ q : ℕ, SplitsCompletelyRat q (fixedFieldOf 3 F H : Type _) ↔
            SplitsCompletelyRat q
              (IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
                (fixedFieldOf 3 F H) : Type _)) := by
  -- The algebra iso E ≃ₐ[F] Fj
  set val := IntermediateField.val (maxUnramifiedProPExt 3 F) with hval
  set E := (fixedFieldOf 3 F H : Type _) with hE
  set Fj := (IntermediateField.map val (fixedFieldOf 3 F H) : Type _) with hFj
  set e : E ≃ₐ[F] Fj := IntermediateField.equivMap (fixedFieldOf 3 F H) val with he
  have hfd : FiniteDimensional F Fj := LinearEquiv.finiteDimensional e.toLinearEquiv
  refine ⟨e, hfd, ?_⟩
  haveI nfE : NumberField E := NumberField.of_module_finite F E
  haveI nfFj : NumberField Fj := NumberField.of_module_finite F Fj
  have hrank : Module.finrank ℚ E = Module.finrank ℚ Fj :=
    LinearEquiv.finrank_eq (e.restrictScalars ℚ).toLinearEquiv
  -- Ring-of-integers algebra equivalences transporting the arithmetic
  set φ : 𝓞 E ≃ₐ[𝓞 F] 𝓞 Fj := NumberField.RingOfIntegers.mapAlgEquiv e with hφ
  set φℤ : 𝓞 E ≃ₐ[ℤ] 𝓞 Fj := φ.restrictScalars ℤ with hφℤ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- FiniteDimensional iff
    exact ⟨fun _ => hfd, fun _ => ‹FiniteDimensional F E›⟩
  · -- NumberField iff
    exact ⟨fun _ => nfFj, fun _ => nfE⟩
  · -- IsGalois iff
    exact AlgEquiv.transfer_galois e
  · -- EverywhereUnramified iff
    constructor
    · rintro ⟨hfin, hinf⟩
      refine ⟨?_, ?_⟩
      · intro p hp hpp Q hQ
        exact SublemmaLayerIsoAux.ram_transfer φ p (hfin p hp hpp) Q hQ
      · exact SublemmaLayerIsoAux.inf_transfer e hinf
    · rintro ⟨hfin, hinf⟩
      refine ⟨?_, ?_⟩
      · intro p hp hpp P hP
        exact SublemmaLayerIsoAux.ram_transfer φ.symm p (hfin p hp hpp) P hP
      · exact SublemmaLayerIsoAux.inf_transfer e.symm hinf
  · -- IsPGroup forward
    exact fun h => IsPGroup.of_equiv h (AlgEquiv.autCongr e)
  · -- IsTotallyReal iff
    exact NumberField.isTotallyReal_iff_ofRingEquiv e.toRingEquiv
  · -- rootDiscriminant equal
    have hdiscr : NumberField.discr E = NumberField.discr Fj :=
      NumberField.discr_eq_discr_of_ringEquiv E e.toRingEquiv
    unfold rootDiscriminant
    rw [hdiscr, hrank]
  · -- SplitsCompletelyRat iff
    intro q
    constructor
    · rintro ⟨hq, hncard, hrest⟩
      refine ⟨hq, ?_, ?_⟩
      · rw [SublemmaLayerIsoAux.primesOver_ncard φℤ (Ideal.span {(q : ℤ)}), hncard, hrank]
      · exact SublemmaLayerIsoAux.raminertia_transfer φℤ (Ideal.span {(q : ℤ)}) hrest
    · rintro ⟨hq, hncard, hrest⟩
      refine ⟨hq, ?_, ?_⟩
      · rw [SublemmaLayerIsoAux.primesOver_ncard φℤ.symm (Ideal.span {(q : ℤ)}), hncard, ← hrank]
      · exact SublemmaLayerIsoAux.raminertia_transfer φℤ.symm (Ideal.span {(q : ℤ)}) hrest

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension

/-- **SublemmaFixedFieldKernel** (infinite Galois correspondence, kernel form).

Let `G = galUr 3 F` be the Galois group of the maximal everywhere-unramified pro-`3`
extension of the number field `F`, and let `H : Subgroup G` be open and normal.  Put
`E := fixedFieldOf 3 F H`.  Then the kernel of the restriction homomorphism
`AlgEquiv.restrictNormalHom ↥E : G →* (↥E ≃ₐ[F] ↥E)` is exactly `H`.

Equivalently, for every `σ : G`, `σ ∈ H ↔ restrictNormalHom ↥E σ = 1`; in particular
`σ ∈ H → restrictNormalHom ↥E σ = 1`.

The `[Normal F ↥E]` instance is what makes `restrictNormalHom ↥E` available; it is the
Lean-level manifestation of `H` being normal (the fixed field of a normal subgroup is a
normal subextension). -/
theorem SublemmaFixedFieldKernel
    (F : Type*) [Field F] [NumberField F]
    (H : Subgroup (galUr 3 F))
    (hopen : IsOpen (H : Set (galUr 3 F)))
    (hnormal : H.Normal)
    [Normal F (fixedFieldOf 3 F H : Type _)] :
    MonoidHom.ker (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F H : Type _)) = H := by
  -- The ambient extension `F^{ur,3}/F` is Galois: it is the supremum of finite Galois
  -- (everywhere-unramified `3`-group) subextensions, hence normal; separability is
  -- automatic in characteristic zero.
  haveI hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    have hn : ∀ i : {E // E ∈ {E | IsFiniteUnramifiedProPExt 3 F E}},
        Normal F ↥(i : IntermediateField F (AlgebraicClosure F)) := by
      rintro ⟨E, hE⟩
      obtain ⟨hfd, hgal, _, _⟩ := hE
      letI := hfd
      letI : NumberField (E : Type _) :=
        NumberField.of_module_finite (K := F) (L := (E : Type _))
      exact hgal.to_normal
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    exact IntermediateField.normal_iSup F (AlgebraicClosure F) (h := hn)
  haveI : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  -- Fundamental theorem of infinite Galois theory, kernel form:
  -- `(restrictNormalHom E).ker = E.fixingSubgroup`.
  rw [IntermediateField.restrictNormalHom_ker]
  -- `H` is open, hence closed; the Krull-topology Galois correspondence gives
  -- `fixingSubgroup (fixedField H) = H` for the closed subgroup `H`.
  let H' : ClosedSubgroup (galUr 3 F) := ⟨H, Subgroup.isClosed_of_isOpen H hopen⟩
  have hcorr := InfiniteGalois.fixingSubgroup_fixedField H'
  simpa [fixedFieldOf, H'] using hcorr

open scoped NumberField

open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

theorem SublemmaKrullLayerFinite3Group
    (F : Type) [Field F] [NumberField F]
    (hpro : IsProP 3 (galUr 3 F))
    (H : Subgroup (galUr 3 F))
    (hHopen : IsOpen (H : Set (galUr 3 F)))
    (hHnormal : H.Normal) :
    ∃ (_ : FiniteDimensional F ↥(fixedFieldOf 3 F H))
      (_ : IsGalois F ↥(fixedFieldOf 3 F H))
      (hn : Normal F ↥(fixedFieldOf 3 F H)),
      (letI := hn
       Function.Surjective
         (AlgEquiv.restrictNormalHom (F := F)
           (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))) ∧
      (letI := hn
       MonoidHom.ker
         (AlgEquiv.restrictNormalHom (F := F)
           (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) = H) ∧
      IsPGroup 3 (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)) := by
  -- Galois structure on the ambient field K = F^{ur,3}.
  have hnorm : Normal F (maxUnramifiedProPExt 3 F) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
    apply IntermediateField.normal_iSup (h := ?_)
    rintro ⟨E, hE⟩
    obtain ⟨hfd, hg, _, _⟩ := hE
    haveI := hfd
    letI : NumberField (E : Type _) :=
      NumberField.of_module_finite (K := F) (L := (E : Type _))
    haveI := hg
    infer_instance
  haveI : Normal F (maxUnramifiedProPExt 3 F) := hnorm
  haveI hgalK : IsGalois F (maxUnramifiedProPExt 3 F) := ⟨⟩
  -- H is closed, being an open subgroup of a topological group.
  have hclosed : IsClosed (H : Set (galUr 3 F)) := H.isClosed_of_isOpen hHopen
  let Hc : ClosedSubgroup (galUr 3 F) := ⟨H, hclosed⟩
  -- Krull correspondence: the fixing subgroup of the fixed field of (closed) H is H.
  have hff : (fixedFieldOf 3 F H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField
      (k := F) (K := ↥(maxUnramifiedProPExt 3 F)) Hc
  -- FiniteDimensional and IsGalois of the finite layer E = fixedField H.
  have hfin_gal :
      FiniteDimensional F ↥(fixedFieldOf 3 F H) ∧ IsGalois F ↥(fixedFieldOf 3 F H) := by
    rw [← InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois (fixedFieldOf 3 F H), hff]
    exact ⟨hHopen, hHnormal⟩
  obtain ⟨hfd, hgal⟩ := hfin_gal
  haveI := hfd
  haveI := hgal
  haveI hn : Normal F ↥(fixedFieldOf 3 F H) := inferInstance
  -- Surjectivity of the restriction homomorphism to the normal layer.
  have hsurj :
      Function.Surjective
        (AlgEquiv.restrictNormalHom (F := F)
          (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) :=
    AlgEquiv.restrictNormalHom_surjective
      (F := F) (K₁ := ↥(fixedFieldOf 3 F H)) (↥(maxUnramifiedProPExt 3 F))
  -- Kernel of the restriction homomorphism is exactly H (cited sublemma).
  have hker :
      MonoidHom.ker
        (AlgEquiv.restrictNormalHom (F := F)
          (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)) = H :=
    SublemmaFixedFieldKernel F H hHopen hHnormal
  refine ⟨hfd, hgal, hn, hsurj, hker, ?_⟩
  -- |Gal(E/F)| = |range restrictNormalHom| = |G/ker| = H.index = 3^k, hence a 3-group.
  obtain ⟨k, hk⟩ := GalUrOpenNormalThreePowerIndex F H hHnormal hHopen
  refine IsPGroup.of_card (n := k) ?_
  -- Forward chain, rewriting ONLY the `H` inside `H.index` (never inside `fixedFieldOf`).
  have step1 :
      Nat.card (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))
        = Nat.card ↥(⊤ : Subgroup (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))) :=
    (Nat.card_congr
      (Subgroup.topEquiv
        (G := ↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H))).toEquiv).symm
  have step2 :
      Nat.card ↥(⊤ : Subgroup (↥(fixedFieldOf 3 F H) ≃ₐ[F] ↥(fixedFieldOf 3 F H)))
        = Nat.card ↥(MonoidHom.range
            (AlgEquiv.restrictNormalHom (F := F)
              (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))) := by
    rw [MonoidHom.range_eq_top.mpr hsurj]
  have step3 :
      Nat.card ↥(MonoidHom.range
          (AlgEquiv.restrictNormalHom (F := F)
            (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H)))
        = (MonoidHom.ker
            (AlgEquiv.restrictNormalHom (F := F)
              (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))).index :=
    (Subgroup.index_ker _).symm
  have step4 :
      (MonoidHom.ker
          (AlgEquiv.restrictNormalHom (F := F)
            (K₁ := ↥(maxUnramifiedProPExt 3 F)) ↥(fixedFieldOf 3 F H))).index = H.index := by
    rw [hker]
  rw [step1, step2, step3, step4, hk]

open scoped NumberField
open NumberField NumberField.InfinitePlace

theorem SublemmaTotallyRealDescends
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    [NumberField.IsTotallyReal F]
    (hodd : Odd (Module.finrank F E)) :
    NumberField.IsTotallyReal E := by
  have hunr : IsUnramifiedAtInfinitePlaces F E :=
    IsUnramifiedAtInfinitePlaces_of_odd_finrank hodd
  rw [NumberField.isTotallyReal_iff]
  intro w
  have hw : w.IsUnramified F := hunr.isUnramified w
  rcases (NumberField.InfinitePlace.isUnramified_iff.1 hw) with h | h
  · exact h
  · exfalso
    have hre : (w.comap (algebraMap F E)).IsReal := NumberField.IsTotallyReal.isReal _
    exact (NumberField.InfinitePlace.not_isReal_iff_isComplex.2 h) hre

open scoped NumberField

open Workspace.Types.SplittingRamification Workspace.Types.DiscriminantsClassNumber

/-- **Proposition 3.8 Step 3 (P3): root discriminant is preserved under a finite
everywhere-unramified extension.** -/
theorem SublemmaRdPreserved
    (F : Type*) [Field F] [NumberField F]
    (E : Type*) [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hur : UnramifiedAtFinitePrimes F E) :
    rootDiscriminant E = rootDiscriminant F := by
  -- Step 1: every nonzero prime of `𝓞 E` is unramified over `𝓞 F`.
  have key : ∀ (P : Ideal (𝓞 E)) [hP : P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 F) P := by
    intro P hP hPne
    have hpne : Ideal.under (𝓞 F) P ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hPne
    haveI hpprime : (Ideal.under (𝓞 F) P).IsPrime := inferInstance
    have hmem : P ∈ Ideal.primesOver (Ideal.under (𝓞 F) P) (𝓞 E) := ⟨hP, ⟨rfl⟩⟩
    have hram : Ideal.ramificationIdx (Ideal.under (𝓞 F) P) P = 1 :=
      hur (Ideal.under (𝓞 F) P) hpne hpprime P hmem
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPne]
    exact hram
  -- Step 2: the relative different ideal is the whole ring.
  have hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    haveI : M.IsPrime := hM.isPrime
    have hbot : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
    have hM_ne : M ≠ ⊥ := by
      rintro rfl; exact hbot (le_bot_iff.mp hle)
    have hdvd : M ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
    rw [dvd_differentIdeal_iff] at hdvd
    exact hdvd (key M hM_ne)
  -- Step 3: discriminant tower formula.
  have htower :
      (NumberField.discr E).natAbs
        = Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E))
          * (NumberField.discr F).natAbs ^ Module.finrank F E :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hdiff, Ideal.absNorm_top, one_mul] at htower
  -- Step 4: rpow arithmetic.
  have cast_eq : ∀ (n : ℤ), ((n.natAbs : ℝ)) = |(n : ℝ)| :=
    fun n => by rw [Int.cast_natAbs, Int.cast_abs]
  have haEF : |(NumberField.discr E : ℝ)|
      = |(NumberField.discr F : ℝ)| ^ Module.finrank F E := by
    rw [← cast_eq, ← cast_eq, htower]; push_cast; ring
  have haF_nonneg : (0 : ℝ) ≤ |(NumberField.discr F : ℝ)| := abs_nonneg _
  have hmpos : 0 < Module.finrank F E := Module.finrank_pos
  have hnFpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : (Module.finrank F E : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hnF : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast hnFpos.ne'
  have hn : (Module.finrank ℚ E : ℝ)
      = (Module.finrank ℚ F : ℝ) * (Module.finrank F E : ℝ) := by
    rw [← Module.finrank_mul_finrank ℚ F E]; push_cast; ring
  simp only [rootDiscriminant]
  rw [haEF, ← Real.rpow_natCast |(NumberField.discr F : ℝ)| (Module.finrank F E),
      ← Real.rpow_mul haF_nonneg]
  congr 1
  rw [hn]
  field_simp

/-!
# Compositum of everywhere-unramified extensions is everywhere unramified (finite primes)

A compositum of finitely many everywhere-unramified (at the finite primes) extensions is again
everywhere unramified at the finite primes.

The argument is Hilbert's inertia-group argument.  For a prime `P` of `𝓞 M` over `p` of `𝓞 F`, with
`M/F` finite Galois, Mathlib's `Ideal.card_inertia_eq_ramificationIdxIn` says the inertia group
`I(P) ≤ Gal(M/F)` has order `e(P/p)`.  If `E` is an intermediate field with `E/F` unramified, then
`e(P/p) = e(P/P∩E)` by tower multiplicativity, and `I_{M/E}(P) = I_{M/F}(P) ∩ Gal(M/E)` is defined by
the *same* condition on `𝓞 M`; equality of the (finite) cardinalities forces `I_{M/F}(P) ≤ Gal(M/E)`.
Applying this to `A` and `B` with `A ⊔ B = ⊤` gives `I(P) ≤ Gal(M/A) ⊓ Gal(M/B) = Gal(M/⊤) = 1`,
i.e. `e(P/p) = 1`.  A `Finset` induction then covers the whole family.

Transport of unramifiedness along field isomorphisms is free here because
`Workspace.ProofLemmas.UnramifiedDiscriminant.unramified_iff_natAbs_discr` re-expresses it as an
identity between absolute discriminants.
-/

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.UnramifiedProPExtension
open Workspace.ProofLemmas.UnramifiedDiscriminant

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.CompositumUnramified

/-- Compositum of finitely many finite Galois subextensions is Galois (local copy of the helper in
`SublemmaSubextUnramified`, duplicated here to keep the import graph acyclic). -/
theorem isGalois_biSup {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K) (s : Finset ι)
    (hg : ∀ i, IsGalois F ↥(t i)) :
    IsGalois F ↥(⨆ i ∈ s, t i) := by
  haveI : ∀ i, Normal F ↥(t i) := fun i => (hg i).to_normal
  haveI : ∀ i, Algebra.IsSeparable F ↥(t i) := fun i => (hg i).to_isSeparable
  haveI : Normal F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.normal_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  haveI : Algebra.IsSeparable F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.isSeparable_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  exact { }

/-- **Compositum of two everywhere-unramified Galois subextensions.**  If `M/F` is a finite Galois
extension of number fields and `A ⊔ B = ⊤` for two intermediate fields that are unramified over `F`
at all finite primes, then `M/F` is unramified at all finite primes.

The proof is Hilbert's: the inertia group of a prime `P` of `𝓞 M` has order `e(P/p)`; because
`e(P/p) = e(P/P∩A)` (as `A/F` is unramified) and the inertia group for `M/A` is the intersection of
the inertia group for `M/F` with `Gal(M/A)`, that intersection has the same (finite) cardinality as
the whole inertia group, so the inertia group is contained in `Gal(M/A)`; likewise for `B`.  Hence
the inertia group lies in `Gal(M/A) ⊓ Gal(M/B) = Gal(M/(A ⊔ B)) = Gal(M/M) = 1`, i.e. `e(P/p) = 1`. -/
theorem unramified_of_sup_eq_top {F M : Type*} [Field F] [NumberField F] [Field M] [NumberField M]
    [Algebra F M] [IsGalois F M] (A B : IntermediateField F M) (hAB : A ⊔ B = ⊤)
    (hA : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 ↥A),
        haveI : NumberField ↥A := NumberField.of_module_finite (K := F) (L := ↥A)
        Ideal.ramificationIdx q Q = 1)
    (hB : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 ↥B),
        haveI : NumberField ↥B := NumberField.of_module_finite (K := F) (L := ↥B)
        Ideal.ramificationIdx q Q = 1) :
    ∀ (p : Ideal (𝓞 F)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 M), Ideal.ramificationIdx p P = 1 := by
  haveI : IsScalarTower ℚ F M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional F M := Module.Finite.right ℚ F M
  intro p hp hpp P hP
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver p := hPlies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  haveI : P.IsMaximal := hPprime.isMaximal hPne
  -- the action of `Gal(M/F)` on `𝓞 M`
  letI actF : MulSemiringAction (M ≃ₐ[F] M) (𝓞 M) :=
    IsIntegralClosure.MulSemiringAction (𝓞 F) F M (𝓞 M)
  haveI : IsGaloisGroup (M ≃ₐ[F] M) (𝓞 F) (𝓞 M) := IsGaloisGroup.of_isFractionRing _ _ _ F M
  haveI := residue_isSeparable p hp P hPne
  have hcardF : Nat.card (P.inertia (M ≃ₐ[F] M)) = Ideal.ramificationIdx p P := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[F] M) p hp P,
      Ideal.ramificationIdxIn_eq_ramificationIdx p P (M ≃ₐ[F] M)]
  -- KEY: the inertia group lies inside the fixing subgroup of any unramified intermediate field
  have key : ∀ (E : IntermediateField F M),
      (∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
        ∀ Q ∈ Ideal.primesOver q (𝓞 ↥E),
          haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
          Ideal.ramificationIdx q Q = 1) →
      P.inertia (M ≃ₐ[F] M) ≤ E.fixingSubgroup := by
    intro E hE σ hσ
    haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
    haveI : IsGalois ↥E M := IsGalois.tower_top_of_isGalois F ↥E M
    haveI tower : IsScalarTower (𝓞 F) (𝓞 ↥E) (𝓞 M) :=
      NumberField.RingOfIntegers.inst_isScalarTower F ↥E M
    letI actE : MulSemiringAction (M ≃ₐ[↥E] M) (𝓞 M) :=
      IsIntegralClosure.MulSemiringAction (𝓞 ↥E) (↥E) M (𝓞 M)
    haveI : IsGaloisGroup (M ≃ₐ[↥E] M) (𝓞 ↥E) (𝓞 M) :=
      IsGaloisGroup.of_isFractionRing _ _ _ (↥E) M
    set pE : Ideal (𝓞 ↥E) := P.under (𝓞 ↥E) with hpE
    haveI : P.LiesOver pE := ⟨rfl⟩
    haveI : pE.IsPrime := Ideal.IsPrime.under _ P
    have hpEover : pE.under (𝓞 F) = p := by
      rw [hpE, Ideal.under_under]
      exact (Ideal.over_def P p).symm
    haveI : pE.LiesOver p := ⟨hpEover.symm⟩
    have hpEne : pE ≠ ⊥ := by
      intro hcon
      exact hp (by rw [← hpEover, hcon, Ideal.under_bot])
    haveI := residue_isSeparable pE hpEne P hPne
    have hcardE : Nat.card (P.inertia (M ≃ₐ[↥E] M)) = Ideal.ramificationIdx pE P := by
      rw [Ideal.card_inertia_eq_ramificationIdxIn (G := M ≃ₐ[↥E] M) pE hpEne P,
        Ideal.ramificationIdxIn_eq_ramificationIdx pE P (M ≃ₐ[↥E] M)]
    -- ramification tower: e(P/p) = e(pE/p) * e(P/pE) = e(P/pE)
    have htower : Ideal.ramificationIdx p P
        = Ideal.ramificationIdx p pE * Ideal.ramificationIdx pE P :=
      Ideal.ramificationIdx_algebra_tower' (R := 𝓞 F) (S := 𝓞 ↥E) (T := 𝓞 M) p pE P
    have hone : Ideal.ramificationIdx p pE = 1 :=
      hE p hp hpp pE ⟨inferInstance, inferInstance⟩
    rw [hone, one_mul] at htower
    -- the restriction map on inertia groups
    have hsmul : ∀ (τ : M ≃ₐ[↥E] M) (x : 𝓞 M), (τ.restrictScalars F) • x = τ • x := by
      intro τ x
      show galRestrict (𝓞 F) F M (𝓞 M) (τ.restrictScalars F) x
        = galRestrict (𝓞 ↥E) (↥E) M (𝓞 M) τ x
      apply FaithfulSMul.algebraMap_injective (𝓞 M) M
      rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
      rfl
    have hmaps : ∀ τ : M ≃ₐ[↥E] M, τ ∈ P.inertia (M ≃ₐ[↥E] M) →
        τ.restrictScalars F ∈ P.inertia (M ≃ₐ[F] M) := by
      intro τ hτ x
      rw [hsmul]
      exact hτ x
    set g : (P.inertia (M ≃ₐ[↥E] M)) → (P.inertia (M ≃ₐ[F] M)) :=
      fun τ => ⟨(τ : M ≃ₐ[↥E] M).restrictScalars F, hmaps _ τ.2⟩ with hg
    have hginj : Function.Injective g := by
      rintro ⟨τ₁, h₁⟩ ⟨τ₂, h₂⟩ h
      have h' : (τ₁.restrictScalars F) = (τ₂.restrictScalars F) := congrArg Subtype.val h
      ext x
      exact DFunLike.congr_fun h' x
    haveI : Finite (M ≃ₐ[F] M) := inferInstance
    haveI : Finite (M ≃ₐ[↥E] M) := inferInstance
    haveI : Fintype (P.inertia (M ≃ₐ[↥E] M)) := Fintype.ofFinite _
    haveI : Fintype (P.inertia (M ≃ₐ[F] M)) := Fintype.ofFinite _
    have hcards : Fintype.card (P.inertia (M ≃ₐ[↥E] M))
        = Fintype.card (P.inertia (M ≃ₐ[F] M)) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardE, hcardF, htower]
    have hbij : Function.Bijective g :=
      (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcards⟩
    obtain ⟨τ, hτ⟩ := hbij.2 ⟨σ, hσ⟩
    have hστ : σ = (τ : M ≃ₐ[↥E] M).restrictScalars F := (congrArg Subtype.val hτ).symm
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hστ]
    exact (τ : M ≃ₐ[↥E] M).commutes (⟨x, hx⟩ : ↥E)
  -- combine: the inertia group is trivial
  have hbot : P.inertia (M ≃ₐ[F] M) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro σ hσ
    have h1 := key A hA hσ
    have h2 := key B hB hσ
    have h3 : σ ∈ (A ⊔ B).fixingSubgroup := by
      rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨h1, h2⟩
    rwa [hAB, IntermediateField.fixingSubgroup_top] at h3
  rw [← hcardF, hbot]
  simp




/-- Unramifiedness at all finite primes, as a predicate on intermediate fields (instance-free, so
that it can be rewritten along equalities of intermediate fields). -/
def Unram (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra F K]
    (E : IntermediateField F K) : Prop :=
  ∀ hfd : FiniteDimensional F ↥E,
    haveI := hfd
    haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
    ∀ (p : Ideal (𝓞 F)), p ≠ ⊥ → p.IsPrime →
      ∀ P ∈ Ideal.primesOver p (𝓞 ↥E), Ideal.ramificationIdx p P = 1

/-- Unramifiedness at finite primes transports along an `F`-algebra equivalence. -/
theorem unramified_transport {F : Type*} [Field F] [NumberField F]
    {A B : Type*} [Field A] [NumberField A] [Field B] [NumberField B]
    [Algebra F A] [Algebra F B] (e : A ≃ₐ[F] B)
    (h : ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 A), Ideal.ramificationIdx q Q = 1) :
    ∀ (q : Ideal (𝓞 F)), q ≠ ⊥ → q.IsPrime →
      ∀ Q ∈ Ideal.primesOver q (𝓞 B), Ideal.ramificationIdx q Q = 1 := by
  rw [unramified_iff_natAbs_discr] at h ⊢
  rw [← NumberField.discr_eq_discr_of_ringEquiv _ e.toRingEquiv, ← e.toLinearEquiv.finrank_eq]
  exact h

/-- `⊥` is unramified. -/
theorem unram_bot (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra F K] :
    Unram F (⊥ : IntermediateField F K) := by
  intro hfd
  haveI := hfd
  haveI : NumberField ↥(⊥ : IntermediateField F K) :=
    NumberField.of_module_finite (K := F) (L := ↥(⊥ : IntermediateField F K))
  refine unramified_transport (IntermediateField.botEquiv F K).symm ?_
  rw [unramified_iff_natAbs_discr]
  simp

/-- **Compositum of two unramified finite Galois subextensions is unramified.** -/
theorem unram_sup {F K : Type*} [Field F] [NumberField F] [Field K] [Algebra F K]
    (A B : IntermediateField F K) [FiniteDimensional F ↥A] [FiniteDimensional F ↥B]
    [IsGalois F ↥A] [IsGalois F ↥B] (hA : Unram F A) (hB : Unram F B) :
    Unram F (A ⊔ B) := by
  intro hfd
  haveI := hfd
  haveI : NumberField ↥(A ⊔ B) := NumberField.of_module_finite (K := F) (L := ↥(A ⊔ B))
  haveI : IsGalois F ↥(A ⊔ B) := by
    haveI : Normal F ↥(A ⊔ B) := inferInstance
    haveI : Algebra.IsSeparable F ↥(A ⊔ B) := inferInstance
    exact { }
  set M : IntermediateField F K := A ⊔ B with hM
  let A' : IntermediateField F ↥M := IntermediateField.restrict (le_sup_left : A ≤ M)
  let B' : IntermediateField F ↥M := IntermediateField.restrict (le_sup_right : B ≤ M)
  let eA : ↥A ≃ₐ[F] ↥A' := IntermediateField.restrict_algEquiv (le_sup_left : A ≤ M)
  let eB : ↥B ≃ₐ[F] ↥B' := IntermediateField.restrict_algEquiv (le_sup_right : B ≤ M)
  haveI : FiniteDimensional F ↥A' := eA.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥B' := eB.toLinearEquiv.finiteDimensional
  haveI : NumberField ↥A := NumberField.of_module_finite (K := F) (L := ↥A)
  haveI : NumberField ↥B := NumberField.of_module_finite (K := F) (L := ↥B)
  haveI : NumberField ↥A' := NumberField.of_module_finite (K := F) (L := ↥A')
  haveI : NumberField ↥B' := NumberField.of_module_finite (K := F) (L := ↥B')
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← IntermediateField.lift_inj, IntermediateField.lift_top, IntermediateField.lift_sup,
      IntermediateField.lift_restrict (le_sup_left : A ≤ M),
      IntermediateField.lift_restrict (le_sup_right : B ≤ M)]
  exact unramified_of_sup_eq_top (F := F) (M := ↥M) A' B' hsup
    (unramified_transport eA (hA inferInstance)) (unramified_transport eB (hB inferInstance))

/-- **The compositum of a finite family of unramified finite Galois subextensions is
unramified at all finite primes.** -/
theorem unram_biSup {F K : Type*} [Field F] [NumberField F] [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K)
    (hfd : ∀ i, FiniteDimensional F ↥(t i)) (hgal : ∀ i, IsGalois F ↥(t i))
    (hunr : ∀ i, Unram F (t i)) (s : Finset ι) :
    Unram F (⨆ i ∈ s, t i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using unram_bot F (K := K)
  | insert a s ha ih =>
      have hins : (⨆ i ∈ insert a s, t i) = t a ⊔ (⨆ i ∈ s, t i) := by
        simp only [Finset.mem_insert, iSup_or, iSup_sup_eq, iSup_iSup_eq_left]
      rw [hins]
      haveI := hfd a
      haveI := hgal a
      haveI : FiniteDimensional F ↥(⨆ i ∈ s, t i) :=
        IntermediateField.finiteDimensional_iSup_of_finset' (fun i _ => hfd i)
      haveI : IsGalois F ↥(⨆ i ∈ s, t i) := isGalois_biSup t s hgal
      exact unram_sup (t a) (⨆ i ∈ s, t i) (hunr a) ih


/-- For a finite set `s` of members of the defining family of
finite Galois everywhere-unramified pro-3 subextensions of `AlgebraicClosure F`, their compositum
`⨆ i ∈ s, i` is unramified at every finite prime of `F`. -/
theorem compositumFamilyUnramifiedAtFinitePrimes :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
        NumberField.of_module_finite (K := F)
          (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
      UnramifiedAtFinitePrimes F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) := by
  intro F _ _ s hfdM
  exact unram_biSup (F := F) (K := AlgebraicClosure F)
    (t := fun i : ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E} => (i : IntermediateField F (AlgebraicClosure F)))
    (fun i => i.2.choose)
    (fun i => i.2.choose_spec.1)
    (fun i _ => (i.2.choose_spec.2.1).1)
    s hfdM

end Workspace.ProofLemmas.CompositumUnramified

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

-- Cited from: J. Neukirch, Algebraic Number Theory, Springer, 1999 (Neu99).
-- Each member `Eᵢ` of the defining family is a finite Galois pro-3 extension, so `[Eᵢ : F]` equals
-- `|Gal(Eᵢ/F)|`, a power of `3` (hence odd).  For a compositum of two finite Galois extensions
-- `A, B ≤ AlgebraicClosure F`, the restriction map `Gal(A ⊔ B / F) ↪ Gal(A/F) × Gal(B/F)` is
-- injective (an automorphism fixing both `A` and `B` fixes their compositum `A ⊔ B = ⊤`), so by
-- Lagrange `[A ⊔ B : F] = |Gal(A ⊔ B / F)|` divides `|Gal(A/F)| · |Gal(B/F)| = [A:F]·[B:F]`.  A
-- divisor of an odd number is odd, so by induction over the finite family the compositum
-- `⨆ i ∈ s, Eᵢ` has odd degree over `F`.
-- Paper label: Definitions A.2/A.3 (odd-degree half).
--
-- NL statement: For a finite set `s` of members of the defining family (finite Galois everywhere-
-- unramified pro-3 subextensions of `AlgebraicClosure F`), the degree `[⨆ i ∈ s, Eᵢ : F]` is odd.
--
-- This feeds the infinite-places half of everywhere-unramifiedness: given this odd degree and the
-- Mathlib-derived `IsGalois F (⨆ i ∈ s, Eᵢ)`, `IsUnramifiedAtInfinitePlaces F (⨆ i ∈ s, Eᵢ)` is
-- proved from Mathlib via `IsUnramifiedAtInfinitePlaces_of_odd_finrank` in the consuming file.



open scoped NumberField
open Module IntermediateField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

/-- For finite Galois intermediate fields `A, B` of `E / F`, the degree of the compositum
`[A ⊔ B : F]` divides `[A : F] · [B : F]`, via the injective restriction embedding
`Gal(A ⊔ B / F) ↪ Gal(A/F) × Gal(B/F)`. -/
private theorem finrank_sup_dvd {F E : Type*} [Field F] [Field E] [Algebra F E]
    (A B : IntermediateField F E) [FiniteDimensional F A] [FiniteDimensional F B]
    [IsGalois F A] [IsGalois F B] :
    finrank F ↥(A ⊔ B) ∣ finrank F A * finrank F B := by
  set C : IntermediateField F E := A ⊔ B with hC
  let A' : IntermediateField F C := IntermediateField.restrict (le_sup_left : A ≤ C)
  let B' : IntermediateField F C := IntermediateField.restrict (le_sup_right : B ≤ C)
  let eA : ↥A ≃ₐ[F] ↥A' := IntermediateField.restrict_algEquiv (le_sup_left : A ≤ C)
  let eB : ↥B ≃ₐ[F] ↥B' := IntermediateField.restrict_algEquiv (le_sup_right : B ≤ C)
  haveI : FiniteDimensional F ↥A' := eA.toLinearEquiv.finiteDimensional
  haveI : FiniteDimensional F ↥B' := eB.toLinearEquiv.finiteDimensional
  haveI : IsGalois F ↥A' := IsGalois.of_algEquiv eA
  haveI : IsGalois F ↥B' := IsGalois.of_algEquiv eB
  have hsup : A' ⊔ B' = ⊤ := by
    rw [← lift_inj, lift_top, lift_sup, lift_restrict (le_sup_left : A ≤ C),
      lift_restrict (le_sup_right : B ≤ C)]
  let Φ := (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥C) (↥A')).prod
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥C) (↥B'))
  have hker : Φ.ker = ⊥ := by
    rw [MonoidHom.ker_prod, IntermediateField.restrictNormalHom_ker,
      IntermediateField.restrictNormalHom_ker, ← IntermediateField.fixingSubgroup_sup, hsup,
      IntermediateField.fixingSubgroup_top]
  have hinj : Function.Injective Φ := (MonoidHom.ker_eq_bot_iff Φ).mp hker
  have hdvd : Nat.card (↥C ≃ₐ[F] ↥C) ∣ Nat.card (↥A' ≃ₐ[F] ↥A') * Nat.card (↥B' ≃ₐ[F] ↥B') := by
    have := Subgroup.card_dvd_of_injective Φ hinj
    rwa [Nat.card_prod] at this
  rw [IsGalois.card_aut_eq_finrank F ↥C, IsGalois.card_aut_eq_finrank F ↥A',
    IsGalois.card_aut_eq_finrank F ↥B'] at hdvd
  have hA : finrank F ↥A' = finrank F A := (eA.toLinearEquiv.finrank_eq).symm
  have hB : finrank F ↥B' = finrank F B := (eB.toLinearEquiv.finrank_eq).symm
  rw [hA, hB] at hdvd
  exact hdvd

/-- A member `E` of the defining family is finite Galois over `F` with odd degree (its degree is a
power of `3`, coming from `Gal(E/F)` being a finite `3`-group). -/
private theorem member_odd {F : Type} [Field F] [NumberField F]
    (E : IntermediateField F (AlgebraicClosure F))
    (h : IsFiniteUnramifiedProPExt 3 F E) :
    FiniteDimensional F E ∧ IsGalois F E ∧ Odd (finrank F E) := by
  obtain ⟨hfd, hgal, _, hpg⟩ := h
  haveI := hfd
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  refine ⟨hfd, hgal, ?_⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := E ≃ₐ[F] E)).mp hpg
  rw [IsGalois.card_aut_eq_finrank F E] at hn
  rw [hn]
  exact (by norm_num : Odd 3).pow

/-- The compositum `⨆ i ∈ s, Eᵢ` of a finite family of members is finite-dimensional and Galois over
`F` with odd degree, proved by induction on `s` using `finrank_sup_dvd`. -/
private theorem family_props {F : Type} [Field F] [NumberField F]
    (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E}) :
    FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) ∧
      IsGalois F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) ∧
      Odd (finrank F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hbot : (⨆ i ∈ (∅ : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E}), (i : IntermediateField F (AlgebraicClosure F)))
        = ⊥ :=
      iSup_eq_bot.mpr (fun i => iSup_eq_bot.mpr (fun hi => absurd hi (Finset.notMem_empty i)))
    rw [hbot]
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IntermediateField.finrank_bot]
    exact odd_one
  | @insert a t ha ih =>
    obtain ⟨ihfd, ihgal, ihodd⟩ := ih
    obtain ⟨afd, agal, aodd⟩ := member_odd (F := F) (↑a) a.2
    haveI := ihfd; haveI := ihgal; haveI := afd; haveI := agal
    rw [Finset.iSup_insert]
    refine ⟨inferInstance, inferInstance, ?_⟩
    have hd := finrank_sup_dvd (F := F) (E := AlgebraicClosure F) (↑a)
      (⨆ i ∈ t, (i : IntermediateField F (AlgebraicClosure F)))
    exact (aodd.mul ihodd).of_dvd_nat hd

/-- **Compositum of family members has odd degree over `F`.**
For a finite set `s` of members of the defining family of finite Galois everywhere-unramified
pro-3 subextensions of `AlgebraicClosure F`, the degree `[⨆ i ∈ s, i : F]` is odd (it is a power
of `3`). Feeds the infinite-places half of everywhere-unramifiedness,
which is otherwise derived from Mathlib's `IsUnramifiedAtInfinitePlaces_of_odd_finrank`. -/
theorem CompositumFamilyOddFinrank :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      Odd (Module.finrank F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))) := by
  intro F _ _ s _
  exact (family_props s).2.2

-- Cited from: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd ed., Springer, 2008 (NSW08), and J. Neukirch, Algebraic Number Theory, Springer, 1999 (Neu99): a compositum of finitely many finite Galois everywhere-unramified extensions is everywhere unramified.
-- Paper label: Definitions A.2/A.3
--
-- `CompositumFamilyEverywhereUnramified`'s everywhere-unramifiedness conclusion
-- `EverywhereUnramified F (⨆ i ∈ s, i)` splits as:
--   * finite-primes half `UnramifiedAtFinitePrimes F (⨆ i ∈ s, i)` — cited as the arithmetic input
--     `Workspace.ProofLemmas.CompositumFamilyUnramifiedAtFinitePrimes` (the
--     Neukirch input; the closure of the finite-prime ramification index under compositum is not
--     currently in Mathlib);
--   * infinite-places half `IsUnramifiedAtInfinitePlaces F (⨆ i ∈ s, i)` — derived from Mathlib
--     via `IsUnramifiedAtInfinitePlaces_of_odd_finrank`, using the Mathlib-proved
--     `IsGalois F (⨆ i ∈ s, i)` (compositum of finite Galois extensions is Galois, `isGalois_biSup_of_finset`
--     below) together with the residual degree fact
--     `Workspace.ProofLemmas.CompositumFamilyOddFinrank` (the degree is a 3-power, hence odd).
-- The descent of everywhere-unramifiedness to an arbitrary finite subextension `E'` of the maximal
-- pro-3 extension is proved below from Mathlib (tower multiplicativity of ramification indices at
-- finite primes, and `IsUnramifiedAtInfinitePlaces.bot` at infinite places), together with a
-- finite-capture (compactness) argument realizing `E'` inside a finite sub-compositum.






open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 800000

/-- **Compositum of finite Galois extensions from the family is Galois over `F`.**
Generic helper with abstract index/field data so the elaborator never needs to whnf the heavy
`setOf`/coercion of the defining family; the compositum of finitely many finite Galois
subextensions is again Galois (normality via `IntermediateField.normal_iSup`, separability via
`IntermediateField.isSeparable_iSup`, collapsing the finite biSup with `iSup_subtype''`). -/
theorem isGalois_biSup_of_finset {F : Type*} [Field F] {K : Type*} [Field K] [Algebra F K]
    {ι : Type*} (t : ι → IntermediateField F K) (s : Finset ι)
    (hg : ∀ i, IsGalois F ↥(t i)) :
    IsGalois F ↥(⨆ i ∈ s, t i) := by
  haveI : ∀ i, Normal F ↥(t i) := fun i => (hg i).to_normal
  haveI : ∀ i, Algebra.IsSeparable F ↥(t i) := fun i => (hg i).to_isSeparable
  haveI : Normal F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.normal_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  haveI : Algebra.IsSeparable F ↥(⨆ i ∈ s, t i) :=
    iSup_subtype'' (s : Set ι) t ▸
      IntermediateField.isSeparable_iSup (t := fun i : ↥(s : Set ι) => t i.1)
  exact { }

/-- **The compositum of finitely many family members is everywhere unramified over `F`.**
Its everywhere-unramifiedness is split into (1) the finite-primes arithmetic input
`CompositumFamilyUnramifiedAtFinitePrimes` and (2) the infinite-places half derived from Mathlib's
`IsUnramifiedAtInfinitePlaces_of_odd_finrank`, using the Mathlib-proved `IsGalois F (⨆ i ∈ s, i)`
and the residual degree fact `CompositumFamilyOddFinrank`. -/
theorem CompositumFamilyEverywhereUnramified :
    ∀ (F : Type) [Field F] [NumberField F]
      (s : Finset ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E})
      [FiniteDimensional F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)))],
      haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
        NumberField.of_module_finite (K := F)
          (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
      EverywhereUnramified F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) := by
  intro F _ _ s _
  haveI : NumberField ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
    NumberField.of_module_finite (K := F)
      (L := ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))))
  haveI hgalM : IsGalois F ↥(⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F))) :=
    isGalois_biSup_of_finset
      (t := fun i : ↥{E : IntermediateField F (AlgebraicClosure F) | IsFiniteUnramifiedProPExt 3 F E} =>
        (i : IntermediateField F (AlgebraicClosure F))) s
      (by intro i; have h := i.2; rw [Set.mem_setOf_eq] at h; exact h.choose_spec.1)
  refine ⟨CompositumFamilyUnramifiedAtFinitePrimes F s, ?_⟩
  exact IsUnramifiedAtInfinitePlaces_of_odd_finrank (CompositumFamilyOddFinrank F s)

namespace SublemmaSubextUnramifiedAux

open Workspace.Types.SplittingRamification

/-- Descent of unramifiedness at finite primes to a subfield `E'' ≤ M`. -/
lemma descent_finite (F : Type) [Field F] [NumberField F]
    (E'' M : IntermediateField F (AlgebraicClosure F)) (hle : E'' ≤ M)
    [NumberField ↥E''] [NumberField ↥M]
    (hM : UnramifiedAtFinitePrimes F ↥M) :
    UnramifiedAtFinitePrimes F ↥E'' := by
  letI : Algebra ↥E'' ↥M := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥E'' ↥M :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  intro p hp hpp P hP
  obtain ⟨hP_prime, hP_lo⟩ := hP
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver p := hP_lo
  -- a prime `Q` of `𝓞 M` lying over `P`
  obtain ⟨⟨Q, hQprime, hQlo⟩⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver P (𝓞 ↥M)))
  haveI : Q.IsPrime := hQprime
  haveI : Q.LiesOver P := hQlo
  haveI : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have hQmem : Q ∈ Ideal.primesOver p (𝓞 ↥M) := ⟨hQprime, inferInstance⟩
  have hram1 : Ideal.ramificationIdx p Q = 1 := hM p hp hpp Q hQmem
  have htower :
      Ideal.ramificationIdx p Q =
        Ideal.ramificationIdx p P * Ideal.ramificationIdx P Q :=
    Ideal.ramificationIdx_algebra_tower' (R := 𝓞 F) (S := 𝓞 ↥E'') (T := 𝓞 ↥M) p P Q
  rw [hram1] at htower
  exact Nat.eq_one_of_mul_eq_one_right htower.symm

/-- Descent of unramifiedness at infinite places to a subfield `E'' ≤ M`. -/
lemma descent_inf (F : Type) [Field F] [NumberField F]
    (E'' M : IntermediateField F (AlgebraicClosure F)) (hle : E'' ≤ M)
    [NumberField ↥E''] [NumberField ↥M] [FiniteDimensional F ↥M]
    (hM : IsUnramifiedAtInfinitePlaces F ↥M) :
    IsUnramifiedAtInfinitePlaces F ↥E'' := by
  letI : Algebra ↥E'' ↥M := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower F ↥E'' ↥M :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IntermediateField.inclusion hle).commutes x).symm)
  haveI : Module.Finite ↥E'' ↥M := Module.Finite.right F ↥E'' ↥M
  haveI : Algebra.IsAlgebraic ↥E'' ↥M := inferInstance
  exact IsUnramifiedAtInfinitePlaces.bot (k := F) (K := ↥E'') (F := ↥M)

end SublemmaSubextUnramifiedAux

/-- **Every finite subextension of the maximal everywhere-unramified pro-3 extension is
everywhere unramified over `F`.**  Proved from the residual compositum axiom by descent. -/
theorem SublemmaSubextUnramified :
    ∀ (F : Type) [Field F] [NumberField F]
      (E' : IntermediateField F (maxUnramifiedProPExt 3 F))
      [FiniteDimensional F E'],
      haveI : NumberField (E' : Type _) :=
        NumberField.of_module_finite (K := F) (L := (E' : Type _))
      Workspace.Types.SplittingRamification.EverywhereUnramified F (E' : Type _) := by
  intro F _ _ E' _
  haveI : NumberField (E' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (E' : Type _))
  show EverywhereUnramified F (E' : Type _)
  -- realize `E'` as an intermediate field `E''` of `AlgebraicClosure F` via `ι = val`
  set E'' : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) E' with hE''
  have e : E' ≃ₐ[F] ↥E'' :=
    IntermediateField.equivMap E' (IntermediateField.val (maxUnramifiedProPExt 3 F))
  haveI : FiniteDimensional F ↥E'' := LinearEquiv.finiteDimensional e.toLinearEquiv
  haveI : NumberField (↥E'' : Type _) :=
    NumberField.of_module_finite (K := F) (L := (↥E'' : Type _))
  -- `E'' ≤ maxUnramifiedProPExt 3 F`
  have hE''_le : E'' ≤ maxUnramifiedProPExt 3 F := by
    rw [hE'']
    calc IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) E'
          ≤ IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F)) ⊤ :=
          IntermediateField.map_mono _ le_top
      _ = (IntermediateField.val (maxUnramifiedProPExt 3 F)).fieldRange :=
          (AlgHom.fieldRange_eq_map _).symm
      _ = maxUnramifiedProPExt 3 F := IntermediateField.fieldRange_val _
  -- FINITE CAPTURE: `E''` sits inside a finite sub-compositum of the defining family.
  have hFG : E''.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨t, ht_fin, ht_eq⟩ := IntermediateField.fg_def.mp hFG
  have hcompact : IsCompactElement E'' :=
    ht_eq ▸ IntermediateField.adjoin_finite_isCompactElement (F := F) ht_fin
  -- `maxUnramifiedProPExt 3 F = ⨆ i : S, i`
  have hle_isup :
      E'' ≤ ⨆ i : ↥{E : IntermediateField F (AlgebraicClosure F) |
          IsFiniteUnramifiedProPExt 3 F E}, (i : IntermediateField F (AlgebraicClosure F)) := by
    have hKe : maxUnramifiedProPExt 3 F =
        ⨆ i : ↥{E : IntermediateField F (AlgebraicClosure F) |
          IsFiniteUnramifiedProPExt 3 F E}, (i : IntermediateField F (AlgebraicClosure F)) := by
      rw [maxUnramifiedProPExt, sSup_eq_iSup']
    rw [← hKe]; exact hE''_le
  obtain ⟨s, hs_le⟩ :=
    CompleteLattice.IsCompactElement.exists_finset_of_le_iSup _ hcompact
      (fun i : ↥{E : IntermediateField F (AlgebraicClosure F) |
        IsFiniteUnramifiedProPExt 3 F E} => (i : IntermediateField F (AlgebraicClosure F)))
      hle_isup
  -- the finite compositum `M`
  set M : IntermediateField F (AlgebraicClosure F) :=
    ⨆ i ∈ s, (i : IntermediateField F (AlgebraicClosure F)) with hM_def
  have hE''_le_M : E'' ≤ M := hs_le
  haveI : FiniteDimensional F ↥M := by
    rw [hM_def]
    apply IntermediateField.finiteDimensional_iSup_of_finset'
    intro i _
    exact i.2.choose
  haveI : NumberField (↥M : Type _) :=
    NumberField.of_module_finite (K := F) (L := (↥M : Type _))
  -- `M` is everywhere unramified (residual axiom)
  have hEU_M : EverywhereUnramified F (↥M : Type _) :=
    CompositumFamilyEverywhereUnramified F s
  -- descend to `E''`
  have hEU_E'' : EverywhereUnramified F (↥E'' : Type _) :=
    ⟨SublemmaSubextUnramifiedAux.descent_finite F E'' M hE''_le_M hEU_M.1,
     SublemmaSubextUnramifiedAux.descent_inf F E'' M hE''_le_M hEU_M.2⟩
  -- transport back to `E'`
  exact (SublemmaUnramifiedTransport e).mpr hEU_E''

-- Cited from: Neukirch, Algebraic Number Theory (Neu99), Ch. VII §13 (paper Definition A.7):
-- at a prime unramified in a finite Galois extension, the Frobenius class is trivial iff the prime
-- splits completely. This file proves the direction (trivial Frobenius ⟹ complete splitting): the
-- trivial Frobenius forces `y = y^q` on the residue field `κ(P)`, a finite-field root-count gives
-- inertia degree `1`, unramifiedness gives ramification index `1`, and the fundamental identity
-- `∑ e·f = [M:F]` gives the prime count.
-- Paper label: Definition A.7 [Neu99, Ch. VII §13]
-- NL statement: Let F, M be number fields with [Algebra F M], IsGalois F M and FiniteDimensional F M,
-- and let v : Ideal(𝒪_F) be a nonzero prime unramified in M (every P ∈ Ideal.primesOver v (𝒪_M) has
-- ramificationIdx v P = 1; supplied by UnramifiedAtFinitePrimes F M). Suppose some Frobenius element of
-- v is trivial: there is σ : M ≃ₐ[F] M with IsFrobeniusAt σ v and σ = 1. Then v splits completely in
-- M/F: SplitsCompletely (F := F) (M := M) v.



open scoped NumberField

open Workspace.Types.FrobeniusSplitting Workspace.Types.SplittingRamification

attribute [local instance] Ideal.Quotient.field

set_option maxHeartbeats 1600000

/-- In a finite integral domain `L` (a finite field), if every element satisfies `y ^ q = y` and
`2 ≤ q`, then `Nat.card L ≤ q` (the polynomial `X^q - X` has at most `q` roots). -/
theorem card_le_of_forall_pow_eq_self (L : Type*) [CommRing L] [IsDomain L] [Finite L]
    (q : ℕ) (hq : 2 ≤ q) (h : ∀ y : L, y ^ q = y) : Nat.card L ≤ q := by
  classical
  haveI : Fintype L := Fintype.ofFinite L
  rw [Nat.card_eq_fintype_card]
  set p : Polynomial L := Polynomial.X ^ q - Polynomial.X with hp
  have hcoeff : p.coeff q = 1 := by
    have h1 : (Polynomial.X ^ q : Polynomial L).coeff q = 1 := by
      rw [Polynomial.coeff_X_pow]; simp
    have h2 : (Polynomial.X : Polynomial L).coeff q = 0 := by
      rw [Polynomial.coeff_X]; simp [Nat.ne_of_lt (by omega : 1 < q)]
    rw [hp, Polynomial.coeff_sub, h1, h2, sub_zero]
  have hpne : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff
    exact one_ne_zero hcoeff.symm
  have hdeg : p.natDegree ≤ q := by
    calc p.natDegree ≤ max (Polynomial.X ^ q : Polynomial L).natDegree
              (Polynomial.X : Polynomial L).natDegree := Polynomial.natDegree_sub_le _ _
      _ = max q 1 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X]
      _ = q := by omega
  have hsub : (Finset.univ : Finset L) ⊆ p.roots.toFinset := by
    intro y _
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hpne]
    show p.eval y = 0
    rw [hp]; simp [h y]
  calc Fintype.card L = (Finset.univ : Finset L).card := (Finset.card_univ).symm
    _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
    _ ≤ p.natDegree := Polynomial.card_roots' p
    _ ≤ q := hdeg

/-- **Definition A.7 [Neu99, Ch. VII §13] — trivial Frobenius ⟹ complete splitting.**

For a finite Galois extension `M/F` of number fields and a nonzero prime `v` of `𝓞 F` that is
unramified in `M`, if some Frobenius element of `v` is the identity automorphism, then `v` splits
completely in `M/F`. This is the converse direction of Def A.7 (at an unramified prime, the
Frobenius class is trivial iff the prime splits completely). -/
theorem SublemmaTrivialFrobSplits :
    ∀ (F M : Type*) [Field F] [NumberField F] [Field M] [NumberField M]
      [Algebra F M] [IsGalois F M] [FiniteDimensional F M]
      (v : Ideal (𝓞 F)), v ≠ ⊥ → v.IsPrime →
      UnramifiedAtFinitePrimes F M →
      (∃ σ : M ≃ₐ[F] M, IsFrobeniusAt σ v ∧ σ = 1) →
      SplitsCompletely (F := F) (M := M) v := by
  intro F M _ _ _ _ _ _ _ v hv hvp hunram hfrob
  classical
  haveI : v.IsMaximal := hvp.isMaximal hv
  obtain ⟨σ, hFrob, hσ1⟩ := hfrob
  subst hσ1
  obtain ⟨P, hP_prime, hP_lies, hFrobP⟩ := hFrob
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver v := hP_lies
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hv P
  haveI : P.IsMaximal := hP_prime.isMaximal hPne
  have hPunder : P.under (𝓞 F) = v := (Ideal.over_def P v).symm
  -- q = size of residue field of v
  set q : ℕ := Nat.card (𝓞 F ⧸ v) with hq_def
  -- φ = 1 acts as identity on 𝓞 M
  have hφx : ∀ x : 𝓞 M,
      (galRestrict (𝓞 F) F M (𝓞 M) (1 : M ≃ₐ[F] M)).toAlgHom x = x := by
    intro x
    rw [map_one]
    rfl
  -- trivial Frobenius ⇒ every residue class satisfies y^q = y
  have hmk : ∀ x : 𝓞 M, (Ideal.Quotient.mk P x) ^ q = Ideal.Quotient.mk P x := by
    intro x
    have key := hFrobP.mk_apply x
    rw [hφx x, hPunder] at key
    exact key.symm
  -- residue fields are finite fields
  have h2q : 2 ≤ q := by
    have : 1 < Nat.card (𝓞 F ⧸ v) := Finite.one_lt_card
    omega
  -- every element of κ(P) satisfies y^q = y
  have hpow : ∀ y : 𝓞 M ⧸ P, y ^ q = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hmk x
  have hcardP : Nat.card (𝓞 M ⧸ P) ≤ q :=
    card_le_of_forall_pow_eq_self (𝓞 M ⧸ P) q h2q hpow
  -- inertia degree of P is 1
  have hf1 : Ideal.inertiaDeg v P = 1 := by
    haveI : Module.Finite (𝓞 F ⧸ v) (𝓞 M ⧸ P) := Module.Finite.of_finite
    have hcardpow : Nat.card (𝓞 M ⧸ P)
        = Nat.card (𝓞 F ⧸ v) ^ Module.finrank (𝓞 F ⧸ v) (𝓞 M ⧸ P) :=
      Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v) (V := 𝓞 M ⧸ P)
    rw [← hq_def, ← Ideal.inertiaDeg_algebraMap v P] at hcardpow
    set f := Ideal.inertiaDeg v P with hf_def
    -- hcardpow : Nat.card (𝓞 M ⧸ P) = q ^ f
    have hgt : 1 < Nat.card (𝓞 M ⧸ P) := Finite.one_lt_card
    have hfpos : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with h0 | h
      · rw [h0, pow_zero] at hcardpow; omega
      · omega
    have hle : q ^ f ≤ q ^ 1 := by rw [pow_one, ← hcardpow]; exact hcardP
    have hfle := (Nat.pow_le_pow_iff_right (by omega : 1 < q)).mp hle
    omega
  -- extend e = 1, f = 1 to all primes over v
  have hall : ∀ P' ∈ Ideal.primesOver v (𝓞 M),
      Ideal.ramificationIdx v P' = 1 ∧ Ideal.inertiaDeg v P' = 1 := by
    intro P' hP'
    obtain ⟨hP'_prime, hP'_lies⟩ := hP'
    haveI : P'.IsPrime := hP'_prime
    haveI : P'.LiesOver v := hP'_lies
    refine ⟨hunram v hv hvp P' ⟨hP'_prime, hP'_lies⟩, ?_⟩
    rw [Ideal.inertiaDeg_eq_of_isGaloisGroup v P' P (M ≃ₐ[F] M), hf1]
  -- count: ncard = finrank F M via the fundamental identity
  have hcount : (Ideal.primesOver v (𝓞 M)).ncard = Module.finrank F M := by
    rw [← IsDedekindDomain.coe_primesOverFinset hv (𝓞 M), Set.ncard_coe_finset,
      ← Ideal.sum_ramification_inertia (𝓞 M) F M hv, Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P' hP'
    rw [← Finset.mem_coe, IsDedekindDomain.coe_primesOverFinset hv (𝓞 M)] at hP'
    obtain ⟨he, hfe⟩ := hall P' hP'
    rw [he, hfe, mul_one]
  exact ⟨hcount, hall⟩

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

theorem SublemmaSplitDescendsEFOne
    (N Lp : Type*) [Field N] [NumberField N] [Field Lp] [NumberField Lp]
    [Algebra ℚ Lp] [Algebra Lp N] [Algebra ℚ N] [IsScalarTower ℚ Lp N]
    [FiniteDimensional Lp N] (q : ℕ) (hsplitN : SplitsCompletelyRat q N)
    (𝔭 : Ideal (𝓞 Lp))
    (h𝔭 : 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)) :
    Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
      Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 := by
  obtain ⟨hqP, hncardN, hefN⟩ := hsplitN
  obtain ⟨h𝔭p, h𝔭lo⟩ := h𝔭
  haveI : 𝔭.IsPrime := h𝔭p
  haveI : 𝔭.LiesOver (Ideal.span {(q : ℤ)}) := h𝔭lo
  -- (q) ≠ ⊥, 𝔭 ≠ ⊥, 𝔭 maximal
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hqP
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hqP.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  have h𝔭_ne : 𝔭 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔭
  haveI h𝔭max : 𝔭.IsMaximal := h𝔭p.isMaximal h𝔭_ne
  -- relative integral-extension instances 𝓞 Lp ⊆ 𝓞 N
  haveI : Module.Finite (𝓞 Lp) (𝓞 N) := IsIntegralClosure.finite (𝓞 Lp) Lp N (𝓞 N)
  haveI : Algebra.IsIntegral (𝓞 Lp) (𝓞 N) := IsIntegralClosure.isIntegral_algebra (𝓞 Lp) N
  -- going up: a maximal prime 𝔓 of 𝓞 N over 𝔭
  obtain ⟨𝔓, h𝔓max, h𝔓lo⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 N) 𝔭
  haveI : 𝔓.IsMaximal := h𝔓max
  haveI : 𝔓.LiesOver 𝔭 := h𝔓lo
  -- 𝔓 lies over (q)
  haveI h𝔓loq : 𝔓.LiesOver (Ideal.span {(q : ℤ)}) := Ideal.LiesOver.trans 𝔓 𝔭 (Ideal.span {(q : ℤ)})
  have h𝔓mem : 𝔓 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 N) := ⟨h𝔓max.isPrime, h𝔓loq⟩
  obtain ⟨heN, hfN⟩ := hefN 𝔓 h𝔓mem
  -- tower multiplicativity for inertia degree
  have hftower : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔓
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 * Ideal.inertiaDeg 𝔭 𝔓 :=
    Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) 𝔭 𝔓
  rw [hfN] at hftower
  have hf1 : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    Nat.eq_one_of_mul_eq_one_right hftower.symm
  -- tower multiplicativity for ramification index
  have hmap𝔭_ne : Ideal.map (algebraMap (𝓞 Lp) (𝓞 N)) 𝔭 ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 Lp) (𝓞 N))]
    exact h𝔭_ne
  have hmapq_ne : Ideal.map (algebraMap ℤ (𝓞 N)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 N))]
    exact hqb_ne
  have hle : Ideal.map (algebraMap (𝓞 Lp) (𝓞 N)) 𝔭 ≤ 𝔓 :=
    Ideal.map_le_iff_le_comap.mpr h𝔓lo.over.le
  have hetower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔓
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 * Ideal.ramificationIdx 𝔭 𝔓 :=
    Ideal.ramificationIdx_algebra_tower hmap𝔭_ne hmapq_ne hle
  rw [heN] at hetower
  have he1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    Nat.eq_one_of_mul_eq_one_right hetower.symm
  exact ⟨he1, hf1⟩

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaSplitDescendsCount
    (Lp : Type*) [Field Lp] [NumberField Lp] (q : ℕ) (hq : q.Prime)
    (hef : ∀ 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp),
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1) :
    (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)).ncard = Module.finrank ℚ Lp := by
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  -- fundamental identity ∑ e·f = [Lp : ℚ]
  have hsum := Ideal.sum_ramification_inertia (𝓞 Lp) ℚ Lp hqb_ne
  -- bridge primesOverFinset ↔ primesOver
  set F := IsDedekindDomain.primesOverFinset (Ideal.span {(q : ℤ)}) (𝓞 Lp) with hF
  have hcoe : (↑F : Set (Ideal (𝓞 Lp))) = (Ideal.span {(q : ℤ)}).primesOver (𝓞 Lp) :=
    IsDedekindDomain.coe_primesOverFinset hqb_ne (𝓞 Lp)
  have hmem : ∀ P, P ∈ F ↔ P ∈ (Ideal.span {(q : ℤ)}).primesOver (𝓞 Lp) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  -- each e·f = 1, so the sum equals the cardinality
  have hsumcard : ∑ P ∈ F,
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P * Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
        = F.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P ((hmem P).mp hP)
    rw [he, hf, one_mul]
  -- so F.card = finrank ℚ Lp
  have hFcard : (F.card : ℕ) = Module.finrank ℚ Lp := by rw [← hsumcard, hsum]
  -- ncard = F.card
  have hncardeq : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp)).ncard = F.card := by
    rw [← hcoe, Set.ncard_coe_finset]
  rw [hncardeq, hFcard]

open scoped NumberField
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000

theorem SublemmaCompleteSplittingDescends
    (N Lp : Type*) [Field N] [NumberField N] [Field Lp] [NumberField Lp]
    [Algebra ℚ Lp] [Algebra Lp N] [Algebra ℚ N] [IsScalarTower ℚ Lp N]
    [FiniteDimensional Lp N] (q : ℕ) :
    SplitsCompletelyRat q N → SplitsCompletelyRat q Lp := by
  intro hsplitN
  have hqP : q.Prime := hsplitN.1
  have hef : ∀ 𝔭 ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Lp),
      Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔭 = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔭 = 1 :=
    fun 𝔭 h𝔭 => SublemmaSplitDescendsEFOne N Lp q hsplitN 𝔭 h𝔭
  exact ⟨hqP, SublemmaSplitDescendsCount Lp q hqP hef, hef⟩

-- Cited from: Neukirch, Algebraic Number Theory (Neu99), Ch. I §8-9: multiplicativity of the ramification index e and residue degree f in a tower of extensions; consequently complete splitting is transitive in a tower ℚ ⊆ F ⊆ E.
-- Paper label: standard ANT (tower e,f multiplicativity)
-- NL statement: Let F, E be number fields with [Algebra F E], [Algebra ℚ F], [Algebra ℚ E], [IsScalarTower ℚ F E], with E/F and F/ℚ separable and FiniteDimensional F E. For a rational prime q : ℕ: SplitsCompletelyRat q E ↔ (SplitsCompletelyRat q F ∧ ∀ v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F), SplitsCompletely (F := F) (M := E) v). In particular the ⇐ direction yields SplitsCompletelyRat q E from complete splitting ℚ → F together with complete splitting of every intermediate prime F → E.
--
-- PROOF: The fundamental identity ∑_P e(P)·f(P) = [E:K] (Ideal.sum_ramification_inertia) turns
-- each `ncard = finrank` count into a consequence of `e = f = 1`. Tower multiplicativity of e
-- (Ideal.ramificationIdx_algebra_tower) and f (Ideal.inertiaDeg_algebra_tower) along
-- ℤ → 𝓞 F → 𝓞 E then relates the three levels. The descent direction reuses the
-- ProofLemmas SublemmaCompleteSplittingDescends / SublemmaSplitDescendsCount.





open scoped NumberField

open Workspace.Types.SplittingRamification

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

/-- Relative fundamental-identity count: if every prime over `v` in `𝓞 E` has `e = f = 1`,
then the number of such primes is `[E : F]`. -/
theorem SublemmaSplittingTransitive_relCount
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E] (v : Ideal (𝓞 F)) (hv_ne : v ≠ ⊥) [v.IsMaximal]
    (hef : ∀ P ∈ Ideal.primesOver v (𝓞 E),
      Ideal.ramificationIdx v P = 1 ∧ Ideal.inertiaDeg v P = 1) :
    (Ideal.primesOver v (𝓞 E)).ncard = Module.finrank F E := by
  have hsum := Ideal.sum_ramification_inertia (𝓞 E) F E hv_ne
  set S := IsDedekindDomain.primesOverFinset v (𝓞 E) with hS
  have hcoe : (↑S : Set (Ideal (𝓞 E))) = v.primesOver (𝓞 E) :=
    IsDedekindDomain.coe_primesOverFinset hv_ne (𝓞 E)
  have hmem : ∀ P, P ∈ S ↔ P ∈ v.primesOver (𝓞 E) := fun P => by
    rw [← Finset.mem_coe, hcoe]
  have hsumcard : ∑ P ∈ S, Ideal.ramificationIdx v P * Ideal.inertiaDeg v P = S.card := by
    rw [Finset.card_eq_sum_ones]
    apply Finset.sum_congr rfl
    intro P hP
    obtain ⟨he, hf⟩ := hef P ((hmem P).mp hP)
    rw [he, hf, one_mul]
  have hScard : (S.card : ℕ) = Module.finrank F E := by rw [← hsumcard, hsum]
  have hncardeq : (Ideal.primesOver v (𝓞 E)).ncard = S.card := by
    rw [← hcoe, Set.ncard_coe_finset]
  rw [hncardeq, hScard]

/-- Tower multiplicativity of `e` and `f` along `ℤ → 𝓞 F → 𝓞 E`, for a prime `P` of `𝓞 E`
lying over a prime `v` of `𝓞 F` which lies over `(q)`. -/
theorem SublemmaSplittingTransitive_towerEF
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra ℚ F] [Algebra ℚ E] [IsScalarTower ℚ F E]
    [FiniteDimensional F E] (q : ℕ) (hq : q.Prime)
    (v : Ideal (𝓞 F)) [hvp : v.IsPrime] [v.LiesOver (Ideal.span {(q : ℤ)})]
    (P : Ideal (𝓞 E)) [hPp : P.IsPrime] [P.LiesOver v] :
    Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) v * Ideal.ramificationIdx v P ∧
    Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) v * Ideal.inertiaDeg v P := by
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hq.ne_zero
  have hprime_int : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  haveI hpP : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hq.ne_zero)).mpr hprime_int
  haveI hpM : (Ideal.span {(q : ℤ)}).IsMaximal := hpP.isMaximal hqb_ne
  have hv_ne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne v
  haveI hvmax : v.IsMaximal := hvp.isMaximal hv_ne
  haveI hPloq : P.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans P v (Ideal.span {(q : ℤ)})
  have hftower : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P
      = Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) v * Ideal.inertiaDeg v P :=
    Ideal.inertiaDeg_algebra_tower (Ideal.span {(q : ℤ)}) v P
  have hmapv_ne : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
    exact hv_ne
  have hmapq_ne : Ideal.map (algebraMap ℤ (𝓞 E)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective ℤ (𝓞 E))]
    exact hqb_ne
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v ≤ P :=
    Ideal.map_le_iff_le_comap.mpr (‹P.LiesOver v›).over.le
  have hetower : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P
      = Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) v * Ideal.ramificationIdx v P :=
    Ideal.ramificationIdx_algebra_tower hmapv_ne hmapq_ne hle
  exact ⟨hetower, hftower⟩

theorem SublemmaSplittingTransitive
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Algebra ℚ F] [Algebra ℚ E] [IsScalarTower ℚ F E]
    [Algebra.IsSeparable F E] [Algebra.IsSeparable ℚ F]
    [FiniteDimensional F E] (q : ℕ) :
    SplitsCompletelyRat q E ↔
      (SplitsCompletelyRat q F ∧
        ∀ v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F),
          SplitsCompletely (F := F) (M := E) v) := by
  constructor
  · -- (⇒)
    intro hE
    obtain ⟨hqP, hncardE, hefE⟩ := hE
    refine ⟨SublemmaCompleteSplittingDescends E F q ⟨hqP, hncardE, hefE⟩, ?_⟩
    intro v hv
    obtain ⟨hvp, hvlo⟩ := hv
    haveI : v.IsPrime := hvp
    haveI : v.LiesOver (Ideal.span {(q : ℤ)}) := hvlo
    have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
    have hv_ne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne v
    haveI hvmax : v.IsMaximal := hvp.isMaximal hv_ne
    have hef : ∀ P ∈ Ideal.primesOver v (𝓞 E),
        Ideal.ramificationIdx v P = 1 ∧ Ideal.inertiaDeg v P = 1 := by
      intro P hP
      obtain ⟨hPp, hPlo⟩ := hP
      haveI : P.IsPrime := hPp
      haveI : P.LiesOver v := hPlo
      haveI : P.LiesOver (Ideal.span {(q : ℤ)}) :=
        Ideal.LiesOver.trans P v (Ideal.span {(q : ℤ)})
      have hPmem : P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 E) := ⟨hPp, inferInstance⟩
      obtain ⟨heP, hfP⟩ := hefE P hPmem
      obtain ⟨het, hft⟩ := SublemmaSplittingTransitive_towerEF F E q hqP v P
      rw [heP] at het
      rw [hfP] at hft
      exact ⟨Nat.eq_one_of_mul_eq_one_left het.symm, Nat.eq_one_of_mul_eq_one_left hft.symm⟩
    exact ⟨SublemmaSplittingTransitive_relCount F E v hv_ne hef, hef⟩
  · -- (⇐)
    rintro ⟨hF, hvsplit⟩
    obtain ⟨hqP, hncardF, hefF⟩ := hF
    have hefE : ∀ P ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 E),
        Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) P = 1 := by
      intro P hP
      obtain ⟨hPp, hPlo⟩ := hP
      haveI : P.IsPrime := hPp
      haveI : P.LiesOver (Ideal.span {(q : ℤ)}) := hPlo
      set v := P.under (𝓞 F) with hvdef
      haveI hvp : v.IsPrime := inferInstance
      haveI hPlov : P.LiesOver v := ⟨rfl⟩
      haveI hvlo : v.LiesOver (Ideal.span {(q : ℤ)}) := by
        refine ⟨?_⟩
        show Ideal.span {(q : ℤ)} = v.under ℤ
        rw [hvdef, Ideal.under_under]
        exact hPlo.over
      have hvmem : v ∈ Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 F) := ⟨hvp, hvlo⟩
      obtain ⟨hev, hfv⟩ := hefF v hvmem
      have hPmemv : P ∈ Ideal.primesOver v (𝓞 E) := ⟨hPp, hPlov⟩
      obtain ⟨_, hefvP⟩ := hvsplit v hvmem
      obtain ⟨hevP, hfvP⟩ := hefvP P hPmemv
      obtain ⟨het, hft⟩ := SublemmaSplittingTransitive_towerEF F E q hqP v P
      rw [hev, hevP, one_mul] at het
      rw [hfv, hfvP, one_mul] at hft
      exact ⟨het, hft⟩
    exact ⟨hqP, SublemmaSplitDescendsCount E q hqP hefE, hefE⟩

open scoped NumberField
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.ProPGroup
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 1000000

theorem TowerLayerProperties
    (F : Type) [Field F] [NumberField F]
    (hTR : NumberField.IsTotallyReal F)
    (hGal : IsGalois ℚ F)
    (hdeg : Module.finrank ℚ F = 3)
    (N : Subgroup (galUr 3 F)) [N.Normal]
    (H : ℕ → Subgroup (galUr 3 F))
    (hHopen : ∀ j, IsOpen (H j : Set (galUr 3 F)))
    (hHnormal : ∀ j, (H j).Normal)
    (hNH : ∀ j, N ≤ H j)
    (Fj : ℕ → IntermediateField F (AlgebraicClosure F))
    (hFj : ∀ j, Fj j =
      IntermediateField.map (IntermediateField.val (maxUnramifiedProPExt 3 F))
        (fixedFieldOf 3 F (H j)))
    (t : ℕ) (q : Fin t → ℕ)
    (hq : ∀ b, (q b).Prime ∧ q b % 4 = 1 ∧ SplitsCompletelyRat (q b) F ∧
      ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
        ∃ σ : galUr 3 F,
          Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 F σ v ∧ σ ∈ N) :
    ∀ j, ∃ (_ : FiniteDimensional F ↥(Fj j)) (_ : NumberField ↥(Fj j)),
      IsGalois F ↥(Fj j) ∧
      EverywhereUnramified F ↥(Fj j) ∧
      IsPGroup 3 (↥(Fj j) ≃ₐ[F] ↥(Fj j)) ∧
      NumberField.IsTotallyReal ↥(Fj j) ∧
      rootDiscriminant ↥(Fj j) = rootDiscriminant F ∧
      (∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) ↥(Fj j)) := by
  intro j
  haveI := hTR
  -- Step 1: `G = galUr 3 F` is pro-3.
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  -- Step 2a: Krull correspondence package for the finite layer `E = fixedFieldOf 3 F (H j)`.
  obtain ⟨hfd, hgal, hn, hsurj, hker, hpg⟩ :=
    SublemmaKrullLayerFinite3Group F hpro (H j) (hHopen j) (hHnormal j)
  haveI := hfd
  haveI := hgal
  haveI := hn
  letI nfE : NumberField (fixedFieldOf 3 F (H j) : Type _) :=
    NumberField.of_module_finite F (fixedFieldOf 3 F (H j) : Type _)
  -- Step 2b: everywhere unramified for `E`.
  have hEU : EverywhereUnramified F (fixedFieldOf 3 F (H j) : Type _) :=
    SublemmaSubextUnramified F (fixedFieldOf 3 F (H j))
  -- Odd degree of `E/F` from the 3-group Galois group.
  have hodd : Odd (Module.finrank F (fixedFieldOf 3 F (H j) : Type _)) := by
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨n, hcard⟩ := hpg.exists_card_eq
    rw [← IsGalois.card_aut_eq_finrank F (fixedFieldOf 3 F (H j) : Type _), hcard]
    exact Odd.pow (by norm_num)
  -- Step 4a: total reality descends to `E`.
  have hTRE : NumberField.IsTotallyReal (fixedFieldOf 3 F (H j) : Type _) :=
    SublemmaTotallyRealDescends F (fixedFieldOf 3 F (H j) : Type _) hodd
  -- Step 4b: root discriminant preserved.
  have hRD : rootDiscriminant (fixedFieldOf 3 F (H j) : Type _) = rootDiscriminant F :=
    SublemmaRdPreserved F (fixedFieldOf 3 F (H j) : Type _) hEU.1
  -- Step 3: each `q b` splits completely in `E`.
  have hsplitE : ∀ b, q b % 4 = 1 ∧
      SplitsCompletelyRat (q b) (fixedFieldOf 3 F (H j) : Type _) := by
    intro b
    obtain ⟨hprime, hmod, hsplitF, hfrob⟩ := hq b
    refine ⟨hmod, ?_⟩
    have hqZ : (q b : ℤ) ≠ 0 := by exact_mod_cast hprime.ne_zero
    have hspan_ne : Ideal.span {(q b : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZ
    -- complete splitting of each prime of `𝓞 F` above `q b` in `E/F`
    have hSC : ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
        SplitsCompletely (F := F) (M := (fixedFieldOf 3 F (H j) : Type _)) v := by
      intro v hv
      obtain ⟨σ, hσfrob, hσN⟩ := hfrob v hv
      -- v ≠ ⊥
      have hv_ne : v ≠ ⊥ := by
        rintro rfl
        have hover := hv.2.over
        rw [Ideal.under_bot ℤ (𝓞 F)] at hover
        exact hspan_ne hover
      -- Frobenius representative restricts to a Frobenius on the finite layer `E`.
      have hfrobE : Workspace.Types.FrobeniusSplitting.IsFrobeniusAt
          (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ) v :=
        hσfrob (fixedFieldOf 3 F (H j))
      -- σ ∈ N ≤ H j, so its restriction is trivial in Gal(E/F).
      have hmemH : σ ∈ H j := hNH j hσN
      have hσE1 : AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ = 1 := by
        have hk := SublemmaFixedFieldKernel F (H j) (hHopen j) (hHnormal j)
        have hmem : σ ∈ MonoidHom.ker
            (AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _)) := by
          rw [hk]; exact hmemH
        simpa [MonoidHom.mem_ker] using hmem
      exact SublemmaTrivialFrobSplits F (fixedFieldOf 3 F (H j) : Type _) v hv_ne hv.1 hEU.1
        ⟨AlgEquiv.restrictNormalHom (fixedFieldOf 3 F (H j) : Type _) σ, hfrobE, hσE1⟩
    -- assemble complete splitting of the rational prime `q b` in `E` via the tower.
    exact (SublemmaSplittingTransitive F (fixedFieldOf 3 F (H j) : Type _) (q b)).mpr
      ⟨hsplitF, hSC⟩
  -- Step 0/5: transport the whole package from `E` to `Fj j` and assemble.
  obtain ⟨_e, hfdFj, hiffFD, hiffNF, hiffGal, hiffEU, himpPG, hiffTR, heqRD, hiffSC⟩ :=
    SublemmaLayerIso F (H j)
  rw [hFj j]
  haveI := hfdFj
  refine ⟨hfdFj, NumberField.of_module_finite F _, hiffGal.mp hgal, hiffEU.mp hEU,
    himpPG hpg, hiffTR.mp hTRE, heqRD.trans hRD, ?_⟩
  intro b
  exact ⟨(hsplitE b).1, (hiffSC (q b)).mp (hsplitE b).2⟩

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

/--
`ClassNumberLeIdealCount`:  the class number of a number field `K` is bounded above
by the number of *nonzero integral ideals of `𝓞 K` whose absolute norm is at most the
Minkowski bound* `MB K`, where
`MB K = (4/π)^{r₂} · (n! / nⁿ) · √|D_K|`,   `n = [K:ℚ]`,  `r₂ = nrComplexPlaces K`.

This is the Minkowski ideal-class reduction, proved purely from Mathlib:
every ideal class of `𝓞 K` contains an integral representative of absolute norm `≤ MB K`
(`NumberField.exists_ideal_in_class_of_norm_le`), so the map sending each class to such a
representative injects `ClassGroup (𝓞 K)` into the (finite, by
`Ideal.finite_setOf_absNorm_le`) set of bounded-norm ideals.
-/
theorem ClassNumberLeIdealCount (K : Type) [Field K] [NumberField K] :
    (classNumber K : ℝ) ≤
      (Nat.card {I : Ideal (𝓞 K) //
        I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤
          (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
            ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(NumberField.discr K : ℝ)|)} : ℝ) := by
  classical
  set MB : ℝ := (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
        Real.sqrt |(NumberField.discr K : ℝ)|) with hMBdef
  have hMBnonneg : 0 ≤ MB := by rw [hMBdef]; positivity
  -- The counting set is finite: it embeds into ideals of absNorm ≤ ⌊MB⌋₊.
  have hfin : {I : Ideal (𝓞 K) | I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB}.Finite := by
    apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le (Nat.floor MB))
    intro I hI
    simp only [Set.mem_setOf_eq]
    exact Nat.le_floor hI.2
  haveI : Finite {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB} :=
    hfin.to_subtype
  -- The class-to-representative map injects into the counting set.
  have hcard : classNumber K ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB} := by
    show Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB}
    have hinj : Function.Injective
        (fun C : ClassGroup (𝓞 K) =>
          (⟨((NumberField.exists_ideal_in_class_of_norm_le C).choose : Ideal (𝓞 K)),
            ⟨mem_nonZeroDivisors_iff_ne_zero.mp (NumberField.exists_ideal_in_class_of_norm_le C).choose.2,
             (NumberField.exists_ideal_in_class_of_norm_le C).choose_spec.2⟩⟩ :
            {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB})) := by
      intro C₁ C₂ hC
      have hval := congrArg Subtype.val hC
      simp only at hval
      have h1 := (NumberField.exists_ideal_in_class_of_norm_le C₁).choose_spec.1
      have h2 := (NumberField.exists_ideal_in_class_of_norm_le C₂).choose_spec.1
      have heq : (NumberField.exists_ideal_in_class_of_norm_le C₁).choose
               = (NumberField.exists_ideal_in_class_of_norm_le C₂).choose := Subtype.ext hval
      rw [← h1, ← h2, heq]
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card] at hle
  exact_mod_cast hcard

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



open scoped NumberField

/-- **Ideal count ≤ divisor-tuple count.**  The number of nonzero integral ideals of `𝓞 K` of norm
at most `m` is at most the number of `[K:ℚ]`-tuples of positive integers with product at most `m`. -/
theorem IdealCountDivisorTuple :
    ∀ (K : Type) [Field K] [NumberField K] (m : ℕ),
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ Ideal.absNorm I ≤ m}
        ≤ (Workspace.ProofLemmas.IdealNormCount.DivisorCount.D (Module.finrank ℚ K) m).card :=
  fun K _ _ m => Workspace.ProofLemmas.IdealCountInjection.idealCount_le_D (K := K) m

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

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

/--
`ClassNumberRootDiscriminantBound` (Proposition 3.7 / A.13):  there is an absolute
constant `C > 0` such that every number field `K` satisfies
`h(K) ≤ max{2, rd(K)}^{C · [K:ℚ]}`,  where `rd(K) = |D_K|^{1/[K:ℚ]}`.

Proved by composing the Minkowski reduction `ClassNumberLeIdealCount` (class number ≤ count of
nonzero ideals up to the Minkowski bound) with `IdealCountByNormBound` (that ideal count is
≤ `max{2, rd(K)}^{C·[K:ℚ]}`, the divisor-sum ideal-counting core).
-/
theorem ClassNumberRootDiscriminantBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ)
        ≤ (max 2 (rootDiscriminant K)) ^ (C * (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := IdealCountByNormBound
  refine ⟨C, hC, ?_⟩
  intro K _ _
  exact le_trans (ClassNumberLeIdealCount K) (hbound K)

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI

open Polynomial
open scoped ComplexConjugate

theorem CMLayerAdjoinIRootDiscriminantBound (L : Type) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (K : Type) [Field K] [NumberField K] [Algebra L K] (hadj : IsAdjoinI L K) :
    rootDiscriminant K ≤ 2 * rootDiscriminant L := by
  classical
  obtain ⟨iota, hsq, hadjeq⟩ := hadj
  -- `iota` is integral over `L`.
  have hint : IsIntegral L iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  -- `iota ∉ L`, since `L` is totally real.
  have hne : iota ∉ (algebraMap L K).range := by
    rintro ⟨a, ha⟩
    have ha2 : a ^ 2 = -1 := by
      apply (algebraMap L K).injective
      rw [map_pow, ha, hsq, map_neg, map_one]
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- The minimal polynomial of `iota` over `L` is `X ^ 2 + 1`.
  have hmin : minpoly L iota = X ^ 2 + 1 := by
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd; simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdeg : (X ^ 2 + 1 : L[X]).natDegree ≤ (minpoly L iota).natDegree := by
      have h2 : 2 ≤ (minpoly L iota).natDegree :=
        (minpoly.two_le_natDegree_iff hint).mpr hne
      have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
      omega
    exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hmonic hdvd hdeg).symm
  -- `[K : L] = 2`.
  have hrank2 : Module.finrank L K = 2 := by
    have h1 := IntermediateField.adjoin.finrank hint
    rw [hmin] at h1
    have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    rw [hnd] at h1
    have e : (IntermediateField.adjoin L {iota}) ≃ₐ[L] K :=
      (IntermediateField.equivOfEq hadjeq).trans IntermediateField.topEquiv
    have h3 : Module.finrank L (IntermediateField.adjoin L {iota}) = Module.finrank L K :=
      e.toLinearEquiv.finrank_eq
    rw [h3] at h1; exact h1
  haveI hfd : FiniteDimensional L K := by
    apply FiniteDimensional.of_finrank_pos; rw [hrank2]; norm_num
  haveI hmodfin : Module.Finite (𝓞 L) (𝓞 K) := IsIntegralClosure.finite (𝓞 L) L K (𝓞 K)
  -- `iota` is integral over `ℤ`, hence an algebraic integer.
  have hintZ : IsIntegral ℤ iota := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsq]
  set xI : 𝓞 K := ⟨iota, hintZ⟩ with hxI
  have hxI_map : (algebraMap (𝓞 K) K) xI = iota := rfl
  -- `xI ^ 2 = -1` in `𝓞 K`.
  have hsqOK : (xI : 𝓞 K) ^ 2 = -1 := by
    apply IsFractionRing.injective (𝓞 K) K
    simp only [map_pow, hxI_map, hsq, map_neg, map_one]
  -- `xI` is integral over `𝓞 L`.
  have hintOL : IsIntegral (𝓞 L) xI := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · monicity!
    · simp [hsqOK]
  -- Minimal polynomial of `xI` over `𝓞 L` is `X ^ 2 + 1`.
  have hminOL : minpoly (𝓞 L) xI = X ^ 2 + 1 := by
    have htr := minpoly.isIntegrallyClosed_eq_field_fractions L K hintOL
    rw [hxI_map, hmin] at htr
    have hinj : Function.Injective (Polynomial.map (algebraMap (𝓞 L) L)) :=
      Polynomial.map_injective _ (IsFractionRing.injective (𝓞 L) L)
    apply hinj
    rw [← htr]; simp
  -- `xI` generates `K` over `L`.
  have hx : Algebra.adjoin L {(algebraMap (𝓞 K) K) xI} = ⊤ := by
    rw [hxI_map, ← IntermediateField.adjoin_simple_toSubalgebra_of_integral hint, hadjeq,
      IntermediateField.top_toSubalgebra]
  -- Conductor / different identity: `conductor · 𝔡 = span {2 · xI}`.
  have hcond := conductor_mul_differentIdeal (𝓞 L) L K xI hx
  rw [hminOL] at hcond
  have haeval : (aeval xI) (derivative (X ^ 2 + 1 : (𝓞 L)[X])) = 2 * xI := by
    simp [derivative_pow, map_ofNat]
  rw [haeval] at hcond
  -- Absolute norms.
  have hnorm : Ideal.absNorm (conductor (𝓞 L) xI) *
      Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) =
      Ideal.absNorm (Ideal.span {(2 * xI : 𝓞 K)}) := by
    rw [← map_mul, hcond]
  have hspan : Ideal.absNorm (Ideal.span {(2 * xI : 𝓞 K)}) =
      (Algebra.norm ℤ (2 * xI)).natAbs := Ideal.absNorm_span_singleton _
  -- `xI` is a unit (`xI · (-xI) = 1`).
  have hxIunit : IsUnit (xI : 𝓞 K) := by
    refine isUnit_of_mul_eq_one (-xI) ?_
    have h : xI * (-xI) = -(xI ^ 2) := by ring
    rw [h, hsqOK]; ring
  have hnormval : (Algebra.norm ℤ (2 * xI : 𝓞 K)).natAbs = 2 ^ (Module.finrank ℚ K) := by
    have h2 : Algebra.norm ℤ (2 : 𝓞 K) = 2 ^ Module.finrank ℤ (𝓞 K) := by
      rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 by simp]
      rw [Algebra.norm_algebraMap_of_basis (NumberField.RingOfIntegers.basis K) 2,
        Module.finrank_eq_card_chooseBasisIndex]
    have hunit : IsUnit (Algebra.norm ℤ xI) := IsUnit.map (Algebra.norm ℤ) hxIunit
    have hu : (Algebra.norm ℤ xI).natAbs = 1 := by
      rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> rfl
    rw [map_mul, h2, Int.natAbs_mul, hu, mul_one, Int.natAbs_pow]
    rw [NumberField.RingOfIntegers.rank K]
    norm_num
  -- `𝔡`'s norm divides `2 ^ [K:ℚ]`, hence is `≤`.
  have hDdvd : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) ∣ 2 ^ Module.finrank ℚ K := by
    have h := dvd_mul_left (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)))
      (Ideal.absNorm (conductor (𝓞 L) xI))
    rw [hnorm, hspan, hnormval] at h
    exact h
  have hD : Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) ≤ 2 ^ Module.finrank ℚ K :=
    Nat.le_of_dvd (by positivity) hDdvd
  -- Tower formula for discriminants.
  have htower := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    L (𝓞 L) K (𝓞 K)
  rw [hrank2] at htower
  -- Degrees.
  have hnm : Module.finrank ℚ L * 2 = Module.finrank ℚ K := by
    rw [← hrank2]; exact Module.finrank_mul_finrank ℚ L K
  have hm_pos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hn_pos : 0 < Module.finrank ℚ K := by omega
  -- Real abbreviations.
  set n := Module.finrank ℚ K with hn
  set m := Module.finrank ℚ L with hm
  have haL : (0 : ℝ) ≤ ((NumberField.discr L).natAbs : ℝ) := by positivity
  have hdiscK : |(NumberField.discr K : ℝ)| = ((NumberField.discr K).natAbs : ℝ) := by
    rw [Int.cast_natAbs, Int.cast_abs]
  have hdiscL : |(NumberField.discr L : ℝ)| = ((NumberField.discr L).natAbs : ℝ) := by
    rw [Int.cast_natAbs, Int.cast_abs]
  -- Relate `|D_K|` to `D · |D_L|²`.
  have htowerR : |(NumberField.discr K : ℝ)| =
      (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) : ℝ) * |(NumberField.discr L : ℝ)| ^ 2 := by
    rw [hdiscK, hdiscL]
    have := htower
    rw [this]
    push_cast
    ring
  -- Unfold root discriminants.
  simp only [rootDiscriminant, ← hn, ← hm]
  rw [htowerR, hdiscL]
  -- Now: `(D * aL²) ^ (1/n) ≤ 2 * aL ^ (1/m)`.
  set D : ℝ := (Ideal.absNorm (differentIdeal (𝓞 L) (𝓞 K)) : ℝ) with hDdef
  set aL : ℝ := ((NumberField.discr L).natAbs : ℝ) with haLdef
  have hDnn : (0 : ℝ) ≤ D := by positivity
  have hDle : D ≤ (2 : ℝ) ^ n := by
    rw [hDdef]; exact_mod_cast hD
  have hbase_nn : (0 : ℝ) ≤ D * aL ^ 2 := by positivity
  have hexp_nn : (0 : ℝ) ≤ (1 : ℝ) / n := by positivity
  -- Step 1: monotonicity.
  have step1 : (D * aL ^ 2) ^ ((1 : ℝ) / n) ≤ ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) := by
    apply Real.rpow_le_rpow hbase_nn _ hexp_nn
    exact mul_le_mul_of_nonneg_right hDle (by positivity)
  -- Step 2: split the product.
  have step2 : ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) =
      ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) * (aL ^ 2) ^ ((1 : ℝ) / n) := by
    apply Real.mul_rpow (by positivity) (by positivity)
  -- Step 3: `(2^n)^(1/n) = 2`.
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn_pos.ne'
  have step3 : ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) = 2 := by
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num)]
    rw [mul_one_div, div_self hnR, Real.rpow_one]
  -- Step 4: `(aL²)^(1/n) = aL^(1/m)`.
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm_pos.ne'
  have hnm_R : (n : ℝ) = (m : ℝ) * 2 := by exact_mod_cast hnm.symm
  have step4 : (aL ^ 2) ^ ((1 : ℝ) / n) = aL ^ ((1 : ℝ) / m) := by
    rw [← Real.rpow_natCast aL 2, ← Real.rpow_mul haL]
    congr 1
    push_cast
    rw [hnm_R]
    field_simp
  -- Combine.
  calc (D * aL ^ 2) ^ ((1 : ℝ) / n)
      ≤ ((2 : ℝ) ^ n * aL ^ 2) ^ ((1 : ℝ) / n) := step1
    _ = ((2 : ℝ) ^ n) ^ ((1 : ℝ) / n) * (aL ^ 2) ^ ((1 : ℝ) / n) := step2
    _ = 2 * aL ^ ((1 : ℝ) / m) := by rw [step3, step4]

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Polynomial

theorem CMModelDiscriminantClassNumberBounds
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (L : Type) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (hrd : rootDiscriminant L = rootDiscriminant F)
    (C_class : ℝ) (hCpos : 0 < C_class)
    (hCbound : ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ)
        ≤ (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ)))
    (H : ℝ) (hH : H = (2 * rootDiscriminant F) ^ (2 * C_class)) :
    0 < H ∧
      ∀ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K),
        IsAdjoinI L K →
          rootDiscriminant K ≤ 2 * rootDiscriminant F ∧
          (classNumber K : ℝ) ≤ H ^ (Module.finrank ℚ L) := by
  -- Root discriminant of `F` is at least `1` (since `|D_F| ≥ 1`).
  have hrdF_ge_one : (1 : ℝ) ≤ rootDiscriminant F := by
    have hDF : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero (K := F)
    have h1 : (1 : ℝ) ≤ |(NumberField.discr F : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hDF
    have hexp : (0 : ℝ) ≤ 1 / (Module.finrank ℚ F : ℝ) := by positivity
    unfold rootDiscriminant
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) := by rw [Real.one_rpow]
      _ ≤ |(NumberField.discr F : ℝ)| ^ (1 / (Module.finrank ℚ F : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) h1 hexp
  have hrdF_pos : (0 : ℝ) < rootDiscriminant F := by linarith
  have h2rdF_pos : (0 : ℝ) < 2 * rootDiscriminant F := by linarith
  have h2rdF_ge_two : (2 : ℝ) ≤ 2 * rootDiscriminant F := by linarith
  refine ⟨?_, ?_⟩
  · -- `0 < H`
    rw [hH]
    exact Real.rpow_pos_of_pos h2rdF_pos _
  · intro K fK nfK algLK hadj
    letI := fK
    letI := nfK
    letI := algLK
    -- Scalar tower `ℚ → L → K`.
    haveI hstL : IsScalarTower ℚ L K := by
      apply IsScalarTower.of_algebraMap_eq'
      exact Subsingleton.elim _ _
    haveI hfdLK : FiniteDimensional L K := by
      have : FiniteDimensional ℚ K := inferInstance
      exact FiniteDimensional.right ℚ L K
    -- Extract the generator `iota`.
    obtain ⟨iota, hsq, hadjT⟩ := hadj
    have hint : IsIntegral L iota := by
      refine ⟨X ^ 2 + 1, ?_, ?_⟩
      · monicity!
      · simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    -- `[K : L] ≤ 2`.
    have hfL : Module.finrank L K ≤ 2 := by
      have hadjfin := IntermediateField.adjoin.finrank hint
      rw [hadjT] at hadjfin
      rw [IntermediateField.topEquiv.toLinearEquiv.finrank_eq] at hadjfin
      have hle := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
      rw [hnd] at hle
      rw [hadjfin]; exact hle
    -- `[K : ℚ] ≤ 2 [L : ℚ]`.
    have htower : Module.finrank ℚ L * Module.finrank L K = Module.finrank ℚ K :=
      Module.finrank_mul_finrank ℚ L K
    have hdeg_le : Module.finrank ℚ K ≤ 2 * Module.finrank ℚ L := by
      rw [← htower]
      calc Module.finrank ℚ L * Module.finrank L K
            ≤ Module.finrank ℚ L * 2 := by
              apply Nat.mul_le_mul_left; exact hfL
        _ = 2 * Module.finrank ℚ L := by ring
    -- The relative-discriminant bound (paper tex 806–818).
    have hdisc : rootDiscriminant K ≤ 2 * rootDiscriminant F := by
      rw [← hrd]
      exact CMLayerAdjoinIRootDiscriminantBound L K ⟨iota, hsq, hadjT⟩
    refine ⟨hdisc, ?_⟩
    -- Class-number bound.
    have hcn := hCbound K
    have hmax : max 2 (rootDiscriminant K) ≤ 2 * rootDiscriminant F :=
      max_le h2rdF_ge_two hdisc
    have hmax_nonneg : (0 : ℝ) ≤ max 2 (rootDiscriminant K) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hexp_nonneg : (0 : ℝ) ≤ C_class * (Module.finrank ℚ K : ℝ) := by positivity
    have step2 : (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ))
        ≤ (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ)) :=
      Real.rpow_le_rpow hmax_nonneg hmax hexp_nonneg
    have hbase_ge_one : (1 : ℝ) ≤ 2 * rootDiscriminant F := by linarith
    have hexp_le : C_class * (Module.finrank ℚ K : ℝ)
        ≤ C_class * (2 * (Module.finrank ℚ L : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
      have : (Module.finrank ℚ K : ℝ) ≤ 2 * (Module.finrank ℚ L : ℝ) := by
        exact_mod_cast hdeg_le
      linarith
    have step3 : (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ))
        ≤ (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
    have hrhs : (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ)))
        = H ^ (Module.finrank ℚ L) := by
      rw [hH]
      rw [← Real.rpow_natCast ((2 * rootDiscriminant F) ^ (2 * C_class)) (Module.finrank ℚ L)]
      rw [← Real.rpow_mul (le_of_lt h2rdF_pos)]
      congr 1
      ring
    calc (classNumber K : ℝ)
          ≤ (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ)) := hcn
      _ ≤ (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ)) := step2
      _ ≤ (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ))) := step3
      _ = H ^ (Module.finrank ℚ L) := hrhs

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

set_option maxHeartbeats 2000000 in
/-- **Proposition 3.8, Step 4 / P6 (numeric closers).** -/
theorem FieldConstructionNumericBounds :
    ∀ (C_class : ℝ), 0 < C_class →
    ∀ (C : ℝ), 0 < C →
    ∃ C' : ℝ, 0 < C' ∧ ∃ L₀ : ℕ, 0 < L₀ ∧
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ∀ (F : Type) [Field F] [NumberField F],
          NumberField.IsTotallyReal F →
          Module.finrank ℚ F = 3 →
          Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) →
          0 < (2 * rootDiscriminant F) ^ (2 * C_class) ∧
          Real.log ((2 * rootDiscriminant F) ^ (2 * C_class)) ≤
              C' * (ℓ : ℝ) * Real.log (ℓ : ℝ) ∧
          0 < (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) * Real.log 2 -
                Real.log ((2 * rootDiscriminant F) ^ (2 * C_class)) := by
  intro C_class hC_class C hC
  -- constants
  have hL2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L2 := Real.log 2 with hL2def
  set K := 2 * C_class * C with hKdef
  have hK : 0 < K := by rw [hKdef]; positivity
  set a := 400 * K / L2 with hadef
  have ha : 0 < a := by rw [hadef]; positivity
  set D := 2 * C_class * L2 with hDdef
  have hD : 0 < D := by rw [hDdef]; positivity
  -- the threshold L₀
  refine ⟨K + 1, by positivity,
    max 4 (max ⌈D⌉₊ (max ⌈800 * K * a / L2⌉₊ ⌈800 * (D + L2 + 1) / L2⌉₊)),
    lt_of_lt_of_le (by norm_num : (0:ℕ) < 4) (le_max_left _ _), ?_⟩
  intro ℓ hℓ F _ _ _hTR _hrank hlogrd
  -- unpack the threshold
  simp only [max_le_iff] at hℓ
  obtain ⟨h4, hnD, hnA, hnB⟩ := hℓ
  have hℓ4 : (4:ℝ) ≤ (ℓ:ℝ) := by exact_mod_cast h4
  have hℓpos : (0:ℝ) < (ℓ:ℝ) := by linarith
  have h1le : 1 ≤ ℓ := by omega
  have hD_le : D ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil D) (by exact_mod_cast hnD)
  have hA_le : 800 * K * a / L2 ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnA)
  have hB_le : 800 * (D + L2 + 1) / L2 ≤ (ℓ:ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hnB)
  -- root discriminant positivity
  have hrd : 0 < rootDiscriminant F := by
    unfold rootDiscriminant
    apply Real.rpow_pos_of_pos
    have h : ((NumberField.discr F : ℝ)) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero F
    positivity
  set rd := rootDiscriminant F with hrddef
  have h2rd : (0:ℝ) < 2 * rd := by linarith
  -- log ℓ facts
  have hlogℓ_nonneg : 0 ≤ Real.log (ℓ:ℝ) := Real.log_nonneg (by linarith)
  have hlogℓ_ge1 : 1 ≤ Real.log (ℓ:ℝ) := by
    rw [Real.le_log_iff_exp_le hℓpos]
    have := Real.exp_one_lt_d9
    linarith
  -- log H equation
  set logH := Real.log ((2 * rd) ^ (2 * C_class)) with hlogHdef
  have hlogH_eq : logH = 2 * C_class * (L2 + Real.log rd) := by
    rw [hlogHdef, Real.log_rpow h2rd, Real.log_mul (by norm_num) (ne_of_gt hrd)]
  -- upper bound in ℓ·log ℓ form
  have hlogH_le1 : logH ≤ D + K * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by
    rw [hlogH_eq, hDdef]
    have h2c : (0:ℝ) < 2 * C_class := by positivity
    have hstep : 2 * C_class * (L2 + Real.log rd) ≤ 2 * C_class * (L2 + C * (ℓ:ℝ) * Real.log (ℓ:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith [hlogrd]) (le_of_lt h2c)
    have hexp : 2 * C_class * (L2 + C * (ℓ:ℝ) * Real.log (ℓ:ℝ))
        = 2 * C_class * L2 + K * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by rw [hKdef]; ring
    linarith [hstep, hexp.le, hexp.ge]
  -- goal 2 : logH ≤ (K+1)·ℓ·log ℓ
  have hgoal2 : logH ≤ (K + 1) * (ℓ:ℝ) * Real.log (ℓ:ℝ) := by
    have hDlll : D ≤ (ℓ:ℝ) * Real.log (ℓ:ℝ) := by nlinarith [hlogℓ_ge1, hℓpos, hD_le]
    nlinarith [hlogH_le1, hDlll]
  -- tangent bound for log ℓ
  have hlogℓ_tan : Real.log (ℓ:ℝ) ≤ (ℓ:ℝ) / a + a := by
    have e1 : Real.log ((ℓ:ℝ) / a) ≤ (ℓ:ℝ) / a - 1 := Real.log_le_sub_one_of_pos (div_pos hℓpos ha)
    have e2 : Real.log a ≤ a - 1 := Real.log_le_sub_one_of_pos ha
    have e3 : Real.log (ℓ:ℝ) = Real.log a + Real.log ((ℓ:ℝ) / a) := by
      rw [← Real.log_mul (ne_of_gt ha) (ne_of_gt (div_pos hℓpos ha))]
      congr 1
      field_simp
    rw [e3]; linarith
  -- K·log ℓ ≤ (L2/400)·ℓ + K·a
  have hKa_eq : K * ((ℓ:ℝ) / a) = (L2 / 400) * (ℓ:ℝ) := by
    rw [hadef]; field_simp
  have hKlog : K * Real.log (ℓ:ℝ) ≤ (L2 / 400) * (ℓ:ℝ) + K * a := by
    have h := mul_le_mul_of_nonneg_left hlogℓ_tan (le_of_lt hK)
    have : K * ((ℓ:ℝ) / a + a) = (L2 / 400) * (ℓ:ℝ) + K * a := by rw [← hKa_eq]; ring
    linarith [h, this.le, this.ge]
  -- upper bound in ℓ² form
  have hstep2 : K * (ℓ:ℝ) * Real.log (ℓ:ℝ) ≤ (L2 / 400) * (ℓ:ℝ)^2 + K * a * (ℓ:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hKlog (le_of_lt hℓpos)
    nlinarith [h]
  have hlogH_le2 : logH ≤ D + (L2 / 400) * (ℓ:ℝ)^2 + K * a * (ℓ:ℝ) := by
    linarith [hlogH_le1, hstep2]
  -- lower bound on t (the nat-division floor)
  have hnat_div : ∀ n : ℕ, (n : ℝ) / 100 - 1 ≤ ((n / 100 : ℕ) : ℝ) := by
    intro n
    have hdm : 100 * (n / 100) + n % 100 = n := Nat.div_add_mod n 100
    have hmod : n % 100 < 100 := Nat.mod_lt n (by norm_num)
    have h1 : (100 : ℝ) * ((n / 100 : ℕ) : ℝ) + ((n % 100 : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
    have h2 : ((n % 100 : ℕ) : ℝ) < 100 := by exact_mod_cast hmod
    linarith
  set t := (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) with htdef
  have hcast : (((ℓ - 1) ^ 2 : ℕ) : ℝ) = ((ℓ:ℝ) - 1)^2 := by
    push_cast [Nat.cast_sub h1le]
    ring
  have ht_lb : ((ℓ:ℝ) - 1)^2 / 100 - 1 ≤ t := by
    have h := hnat_div ((ℓ - 1) ^ 2)
    rw [htdef, ← hcast]
    exact h
  -- (ℓ-1)² ≥ ℓ²/2 for ℓ ≥ 4
  have hquad : (ℓ:ℝ)^2 / 2 ≤ ((ℓ:ℝ) - 1)^2 := by nlinarith [hℓ4]
  have ht_ell2 : (ℓ:ℝ)^2 / 200 - 1 ≤ t := by nlinarith [ht_lb, hquad]
  -- threshold consequences
  have hAfin : K * a * (ℓ:ℝ) ≤ (L2 / 800) * (ℓ:ℝ)^2 := by
    have h800 : 800 * K * a ≤ (ℓ:ℝ) * L2 := by rw [div_le_iff₀ hL2] at hA_le; exact hA_le
    nlinarith [mul_le_mul_of_nonneg_right h800 (le_of_lt hℓpos), hℓpos]
  have hBfin : D + L2 + 1 ≤ (L2 / 800) * (ℓ:ℝ)^2 := by
    have h800 : 800 * (D + L2 + 1) ≤ (ℓ:ℝ) * L2 := by rw [div_le_iff₀ hL2] at hB_le; exact hB_le
    have hℓsq : (ℓ:ℝ) ≤ (ℓ:ℝ)^2 := by nlinarith [hℓ4]
    nlinarith [h800, hℓsq, hL2]
  -- assemble the three goals
  refine ⟨Real.rpow_pos_of_pos h2rd _, hgoal2, ?_⟩
  -- P6
  have htL2 : ((ℓ:ℝ)^2 / 200 - 1) * L2 ≤ t * L2 :=
    mul_le_mul_of_nonneg_right ht_ell2 (le_of_lt hL2)
  -- work with s = ℓ² as an opaque nonneg atom to keep the final step linear
  have htL2' : L2 * (ℓ:ℝ)^2 / 200 - L2 ≤ t * L2 := by nlinarith [htL2]
  have hAfin' : K * a * (ℓ:ℝ) ≤ L2 * (ℓ:ℝ)^2 / 800 := by nlinarith [hAfin]
  have hBfin' : D + L2 + 1 ≤ L2 * (ℓ:ℝ)^2 / 800 := by nlinarith [hBfin]
  have hlogH_le2' : logH ≤ D + L2 * (ℓ:ℝ)^2 / 400 + K * a * (ℓ:ℝ) := by nlinarith [hlogH_le2]
  linarith [htL2', hAfin', hBfin', hlogH_le2']

open scoped NumberField
open Workspace.Types.SplittingRamification
open Polynomial

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000

theorem SublemmaSplitInQiModFour
    (Qi : Type*) [Field Qi] [NumberField Qi] [Algebra ℚ Qi]
    (hi : ∃ x : Qi, x ^ 2 = -1) (hdeg : Module.finrank ℚ Qi = 2)
    (q : ℕ) (hq : q.Prime) :
    SplitsCompletelyRat q Qi → q % 4 = 1 := by
  intro hsplit
  obtain ⟨hqP, hncard, hef⟩ := hsplit
  haveI : Fact (Nat.Prime q) := ⟨hqP⟩
  -- integral element ι with ι² = -1, a unit
  obtain ⟨x, hx⟩ := hi
  have hxint : IsIntegral ℤ x := by
    refine ⟨X ^ 2 + 1, ?_, ?_⟩
    · have h : (X ^ 2 + 1 : ℤ[X]) = X ^ 2 + C 1 := by simp
      rw [h]; exact monic_X_pow_add_C 1 (by norm_num)
    · simp [hx]
  set ι : 𝓞 Qi := ⟨x, hxint⟩ with hιdef
  have hcoe : (algebraMap (𝓞 Qi) Qi) ι = x := rfl
  have hι2 : ι ^ 2 = -1 := by
    apply FaithfulSMul.algebraMap_injective (𝓞 Qi) Qi
    rw [map_pow, map_neg, map_one, hcoe, hx]
  have hιunit : IsUnit ι :=
    isUnit_of_mul_eq_one (-ι) (by
      have h : ι * (-ι) = -(ι ^ 2) := by ring
      rw [h, hι2]; ring)
  -- basic prime facts
  have hqb_ne : (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hqP.ne_zero
  -- pick a prime 𝔮 over (q)
  have hne0 : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Qi)).ncard ≠ 0 := by
    have h2 : (Ideal.primesOver (Ideal.span {(q : ℤ)}) (𝓞 Qi)).ncard = 2 := by
      rw [hncard]; convert hdeg using 2; exact Subsingleton.elim _ _
    omega
  obtain ⟨𝔮, h𝔮mem⟩ := Set.nonempty_of_ncard_ne_zero hne0
  obtain ⟨hqp, hqlo⟩ := h𝔮mem
  haveI : 𝔮.IsPrime := hqp
  haveI : 𝔮.LiesOver (Ideal.span {(q : ℤ)}) := hqlo
  have hq_ne : 𝔮 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hqb_ne 𝔮
  haveI : 𝔮.IsMaximal := hqp.isMaximal hq_ne
  -- e = f = 1
  have he1 : Ideal.ramificationIdx (Ideal.span {(q : ℤ)}) 𝔮 = 1 := (hef 𝔮 ⟨hqp, hqlo⟩).1
  have hf1 : Ideal.inertiaDeg (Ideal.span {(q : ℤ)}) 𝔮 = 1 := (hef 𝔮 ⟨hqp, hqlo⟩).2
  -- residue field cardinality = q
  letI hMod : Module (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) := inferInstance
  haveI hFinF : Finite (𝓞 Qi ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 hq_ne
  haveI hFtF : Fintype (𝓞 Qi ⧸ 𝔮) := Fintype.ofFinite _
  haveI hFinZ : Finite (ℤ ⧸ Ideal.span {(q : ℤ)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hqb_ne
  haveI hFtZ : Fintype (ℤ ⧸ Ideal.span {(q : ℤ)}) := Fintype.ofFinite _
  letI hFieldZ : Field (ℤ ⧸ Ideal.span {(q : ℤ)}) := Ideal.Quotient.field _
  have hfr : Module.finrank (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) = 1 := by
    have h := Ideal.inertiaDeg_algebraMap (Ideal.span {(q : ℤ)}) 𝔮
    rw [hf1] at h; exact h.symm
  have hcard : Fintype.card (𝓞 Qi ⧸ 𝔮)
      = Fintype.card (ℤ ⧸ Ideal.span {(q : ℤ)}) ^
          Module.finrank (ℤ ⧸ Ideal.span {(q : ℤ)}) (𝓞 Qi ⧸ 𝔮) := Module.card_eq_pow_finrank
  rw [hfr, pow_one] at hcard
  have hcardZ : Fintype.card (ℤ ⧸ Ideal.span {(q : ℤ)}) = q := by
    haveI : NeZero q := ⟨hqP.ne_zero⟩
    rw [Fintype.card_congr (Int.quotientSpanEquivZMod (q : ℤ)).toEquiv, ZMod.card]
    exact Int.natAbs_natCast q
  rw [hcardZ] at hcard
  -- IsSquare(-1) in the residue field, via the image of ι
  letI hFieldF : Field (𝓞 Qi ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  have hsq : IsSquare (-1 : 𝓞 Qi ⧸ 𝔮) := by
    refine ⟨Ideal.Quotient.mk 𝔮 ι, ?_⟩
    have hmm : (Ideal.Quotient.mk 𝔮 ι) * (Ideal.Quotient.mk 𝔮 ι)
        = Ideal.Quotient.mk 𝔮 (ι ^ 2) := by rw [← map_mul]; ring_nf
    rw [hmm, hι2, map_neg, map_one]
  -- q % 4 ≠ 3
  have hmod3 : q % 4 ≠ 3 := by
    have h := (FiniteField.isSquare_neg_one_iff (F := 𝓞 Qi ⧸ 𝔮)).mp hsq
    rwa [hcard] at h
  -- q ≠ 2
  have hq2 : q ≠ 2 := by
    intro hq2eq
    have helt : (2 : 𝓞 Qi) = ι * (1 - ι) ^ 2 := by linear_combination (2 - ι) * hι2
    have h1ι_ne : (1 - ι : 𝓞 Qi) ≠ 0 := by
      intro h
      have hι1 : ι = 1 := by linear_combination -h
      rw [hι1] at hι2; simp only [one_pow] at hι2
      have : (2 : 𝓞 Qi) = 0 := by linear_combination hι2
      exact two_ne_zero this
    have hmap : Ideal.map (algebraMap ℤ (𝓞 Qi)) (Ideal.span {(q : ℤ)})
        = (Ideal.span {(1 - ι : 𝓞 Qi)}) ^ 2 := by
      rw [Ideal.map_span]
      have himg : (algebraMap ℤ (𝓞 Qi)) '' {(q : ℤ)} = {(q : 𝓞 Qi)} := by simp
      rw [himg]
      have hqcoe : (q : 𝓞 Qi) = 2 := by rw [hq2eq]; norm_num
      rw [hqcoe, helt, ← Ideal.span_singleton_mul_span_singleton ι ((1 - ι) ^ 2),
        Ideal.span_singleton_eq_top.mpr hιunit, Ideal.top_mul, ← Ideal.span_singleton_pow]
    have hspan_ne : Ideal.span {(1 - ι : 𝓞 Qi)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact h1ι_ne
    have hmap_ne : Ideal.map (algebraMap ℤ (𝓞 Qi)) (Ideal.span {(q : ℤ)}) ≠ ⊥ := by
      rw [hmap]; exact pow_ne_zero 2 hspan_ne
    have hcount := Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count
      hmap_ne hqp hq_ne
    rw [he1, hmap, UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
      at hcount
    omega
  -- conclude
  have hodd : q % 2 = 1 := hqP.eq_two_or_odd.resolve_left hq2
  omega

open scoped NumberField Pointwise
open Workspace.Types.SplittingRamification Workspace.Types.FrobeniusSplitting

set_option maxHeartbeats 800000

theorem SublemmaSplitCompletelyFrobTrivial
    (F E : Type*) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [FiniteDimensional F E]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime)
    (hsplit : SplitsCompletely (F := F) (M := E) v)
    (φ : E ≃ₐ[F] E) (hφ : IsFrobeniusAt φ v) :
    φ = 1 := by
  classical
  obtain ⟨P, hP_prime, hP_lies, hFrobP⟩ := hφ
  haveI : P.IsPrime := hP_prime
  haveI : P.LiesOver v := hP_lies
  have hPmem : P ∈ v.primesOver (𝓞 E) := ⟨hP_prime, hP_lies⟩
  let Psub : ↑(v.primesOver (𝓞 E)) := ⟨P, hPmem⟩
  -- Linchpin: the Galois action on `𝓞 E` is `galRestrict`.
  have hlinch : ∀ (σ : E ≃ₐ[F] E) (x : 𝓞 E),
      σ • x = galRestrict (𝓞 F) F E (𝓞 E) σ x := by
    intro σ x
    have hcompat : (algebraMap (𝓞 E) E) (σ • x) = σ ((algebraMap (𝓞 E) E) x) := rfl
    apply IsFractionRing.injective (𝓞 E) E
    rw [hcompat, algebraMap_galRestrict_apply]
  -- Hence the pointwise action on ideals is `Ideal.map (galRestrict σ)`.
  have hraw : ∀ (σ : E ≃ₐ[F] E) (I : Ideal (𝓞 E)),
      σ • I = Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) σ) I := by
    intro σ I
    rw [Ideal.pointwise_smul_def]
    congr 1
    exact RingHom.ext (fun x => by rw [MulSemiringAction.toRingHom_apply]; exact hlinch σ x)
  -- Transport pretransitivity from the generic action to the AlgEquiv action on primesOver.
  haveI hpre : MulAction.IsPretransitive (E ≃ₐ[F] E) ↑(v.primesOver (𝓞 E)) := by
    refine ⟨fun a b => ?_⟩
    obtain ⟨σ, hσ⟩ :=
      (Ideal.isPretransitive_of_isGaloisGroup (B := 𝓞 E) v (E ≃ₐ[F] E)).exists_smul_eq a b
    refine ⟨σ, ?_⟩
    apply Subtype.ext
    rw [Ideal.coe_smul_primesOver_eq_map_galRestrict F E σ a]
    rw [Subtype.ext_iff, Ideal.coe_smul_primesOver σ a, hraw σ ↑a] at hσ
    exact hσ
  -- φ fixes P, hence φ ∈ stabilizer Psub
  have hmap : Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ) P = P := by
    have hc := hFrobP.comap_eq
    calc Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ) P
        = Ideal.map (galRestrict (𝓞 F) F E (𝓞 E) φ)
            (Ideal.comap (galRestrict (𝓞 F) F E (𝓞 E) φ).toAlgHom P) := by rw [hc]
      _ = P := Ideal.map_comap_of_surjective _
            (galRestrict (𝓞 F) F E (𝓞 E) φ).surjective P
  have hφstab : φ ∈ MulAction.stabilizer (E ≃ₐ[F] E) Psub := by
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    rw [Ideal.coe_smul_primesOver_eq_map_galRestrict F E φ Psub]
    exact hmap
  -- orbit-stabilizer forces the stabilizer to be trivial
  have hcardprimes : Nat.card ↑(v.primesOver (𝓞 E)) = Module.finrank F E := by
    rw [Nat.card_coe_set_eq]; exact hsplit.1
  have hcardG : Nat.card (E ≃ₐ[F] E) = Module.finrank F E := IsGalois.card_aut_eq_finrank F E
  have hindex : (MulAction.stabilizer (E ≃ₐ[F] E) Psub).index = Module.finrank F E := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ, hcardprimes]
  have hidxcard := Subgroup.index_mul_card (MulAction.stabilizer (E ≃ₐ[F] E) Psub)
  rw [hindex, hcardG] at hidxcard
  have hfr_pos : 0 < Module.finrank F E := Module.finrank_pos
  have hstab1 : Nat.card ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub) = 1 :=
    Nat.eq_of_mul_eq_mul_left hfr_pos (by rw [mul_one]; exact hidxcard)
  haveI : Subsingleton ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub) :=
    (Nat.card_eq_one_iff_unique.mp hstab1).1
  have h1mem : (1 : E ≃ₐ[F] E) ∈ MulAction.stabilizer (E ≃ₐ[F] E) Psub :=
    (MulAction.stabilizer (E ≃ₐ[F] E) Psub).one_mem
  have := Subsingleton.elim (⟨φ, hφstab⟩ : ↥(MulAction.stabilizer (E ≃ₐ[F] E) Psub)) ⟨1, h1mem⟩
  exact Subtype.ext_iff.mp this

open scoped NumberField
open Polynomial

set_option maxHeartbeats 800000

/-- **Normal closure over ℚ of `E(i)`.** Given a finite Galois extension `E/F` of number fields
with `[Algebra ℚ E]` and `[IsScalarTower ℚ F E]`, adjoining a root `i` of `X² + 1` and taking the
normal closure over `ℚ` yields a number field `N` such that:
* `N` is finite Galois over `ℚ` (`IsGalois ℚ N`, `NumberField N`);
* `N` contains a copy of `E` (hence of `F`): `[Algebra E N]` with `[IsScalarTower ℚ E N]`;
* `N` contains a copy of `ℚ(i)`: `∃ x : N, x ^ 2 = -1`.

Because `E`, `F`, and `ℚ(i)` are realised as genuine subfields of the single object `N`, every
splitting statement in the descent is computed for the same objects appearing in the goal. -/
theorem SublemmaFieldNormalClosure
    (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [Algebra ℚ E] [IsScalarTower ℚ F E] :
    ∃ (N : Type) (_ : Field N) (_ : NumberField N) (_ : IsGalois ℚ N)
      (_ : Algebra E N) (_ : IsScalarTower ℚ E N),
      ∃ x : N, x ^ 2 = -1 := by
  -- Ambient algebraic closure of ℚ, which is Galois over ℚ.
  haveI hAC : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hGal : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
  -- Realise `E` as a subfield of the algebraic closure.
  let φ : E →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift
  have hφinj : Function.Injective φ := φ.toRingHom.injective
  -- A square root `i` of `-1`.
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure ℚ) (n := 2) (by norm_num)
  have hiint : IsIntegral ℚ i := ⟨X ^ 2 + 1, by monicity!, by simp [hi]⟩
  -- `M = E(i)` as an intermediate field, finite over ℚ.
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := φ.fieldRange ⊔ IntermediateField.adjoin ℚ {i}
  have hEfin : FiniteDimensional ℚ ↥(φ.fieldRange) :=
    (AlgEquiv.ofInjective φ hφinj).toLinearEquiv.finiteDimensional
  have hifin : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {i}) :=
    IntermediateField.adjoin.finiteDimensional hiint
  haveI : FiniteDimensional ℚ ↥M := IntermediateField.finiteDimensional_sup _ _
  -- The normal closure `N` of `M` over ℚ: finite Galois number field.
  set N := IntermediateField.normalClosure ℚ (↥M) (AlgebraicClosure ℚ) with hN
  haveI hNGal : IsGalois ℚ ↥N := IsGalois.normalClosure ℚ (↥M) (AlgebraicClosure ℚ)
  haveI hNfin : FiniteDimensional ℚ ↥N := inferInstance
  haveI hNF : NumberField ↥N := NumberField.of_module_finite ℚ _
  -- `M ≤ N`, so `E`'s image and `i` both lie in `N`.
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  have hrangeN : φ.fieldRange ≤ N := le_trans le_sup_left hMN
  -- Bundle `Algebra E N` from the embedding `E ≃ φ(E) ⊆ N`.
  let e : E ≃ₐ[ℚ] ↥(φ.fieldRange) := AlgEquiv.ofInjective φ hφinj
  let ψ : E →ₐ[ℚ] ↥N := (IntermediateField.inclusion hrangeN).comp e.toAlgHom
  letI algEN : Algebra E ↥N := ψ.toRingHom.toAlgebra
  haveI hst : IsScalarTower ℚ E ↥N :=
    IsScalarTower.of_algebraMap_eq (fun q => (ψ.commutes q).symm)
  -- `i ∈ N`.
  have hiM : i ∈ M := by
    have hle : IntermediateField.adjoin ℚ {i} ≤ M := le_sup_right
    exact hle (IntermediateField.mem_adjoin_simple_self ℚ i)
  have hiN : i ∈ N := hMN hiM
  refine ⟨↥N, inferInstance, hNF, hNGal, algEN, hst, ⟨i, hiN⟩, ?_⟩
  apply Subtype.ext
  push_cast
  simpa using hi

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

/-- **The Frattini quotient extension `E/F`.** -/
theorem SublemmaFrattiniQuotientField
    (F : Type) [Field F] [NumberField F]
    (hpro : IsProP 3 (galUr 3 F))
    (hfg : TopFinitelyGenerated (galUr 3 F)) :
    IsOpen (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) ∧
      (frattiniOpen (galUr 3 F)).Normal ∧
      (∃ k : ℕ, (frattiniOpen (galUr 3 F)).index = 3 ^ k) ∧
      FiniteDimensional F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F))) ∧
      ∃ _hgal : IsGalois F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F))),
        (AlgEquiv.restrictNormalHom
            (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)))).ker
          = frattiniOpen (galUr 3 F) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- Burnside basis for the pro-3 group G = galUr 3 F
  obtain ⟨hcomm, hpow, d, hdrank, hcard⟩ := ProPBurnsideBasis 3 (galUr 3 F) hpro hfg
  -- normality of Φ from commutator containment
  have hnormal : (frattiniOpen (galUr 3 F)).Normal := by
    constructor
    intro n hn g
    have hc := hcomm g n
    have hrw : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [hrw]; exact Subgroup.mul_mem _ hc hn
  -- Φ is closed (intersection of closed maximal-open subgroups)
  have hclosed : IsClosed (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) := by
    have h : (frattiniOpen (galUr 3 F) : Set (galUr 3 F))
        = ⋂ s ∈ {H : Subgroup (galUr 3 F) | IsMaximalOpenSubgroup H}, (s : Set (galUr 3 F)) := by
      rw [frattiniOpen, Subgroup.coe_sInf]
    rw [h]
    exact isClosed_biInter (fun s hs => Subgroup.isClosed_of_isOpen s hs.1)
  -- Φ has finite index 3^d, hence FiniteIndex
  haveI hfinq : Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  haveI hfi : (frattiniOpen (galUr 3 F)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  -- closed + finite index ⇒ open
  have hopen : IsOpen (frattiniOpen (galUr 3 F) : Set (galUr 3 F)) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ hclosed
  -- index = 3^d
  have hindex : ∃ k : ℕ, (frattiniOpen (galUr 3 F)).index = 3 ^ k := ⟨d, hcard⟩
  -- FiniteDimensional + IsGalois of E = fixedFieldOf 3 F Φ (Krull correspondence)
  obtain ⟨hfd, hgal, hn, _hsurj, _hker, _hpg⟩ :=
    SublemmaKrullLayerFinite3Group F hpro (frattiniOpen (galUr 3 F)) hopen hnormal
  refine ⟨hopen, hnormal, hindex, hfd, hgal, ?_⟩
  -- kernel identity via the fixed-field kernel sublemma
  haveI : Normal F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) := hn
  exact SublemmaFixedFieldKernel F (frattiniOpen (galUr 3 F)) hopen hnormal

-- Cited from J. Neukirch, Algebraic Number Theory, Springer, 1999, Ch. VII (infinite
-- Galois theory / Chebotarev setup).
-- The existence of a Frobenius representative at a prime v in the profinite Galois group
-- Gal(F^{ur,3}/F) is obtained by a compactness / finite-intersection-property argument.
--
-- Proof outline:
--   * `galoisOmega`   : F^{ur,3} = sSup of finite Galois everywhere-unramified 3-group layers is
--                       Galois over F (Normal via `normal_iSup`, separable via `isSeparable_iSup`),
--                       hence `galUr 3 F` is a `CompactSpace` (Mathlib profinite Galois instance).
--   * `frobSet`       : for each finite Galois layer E of F^{ur,3}/F, the set of σ ∈ galUr whose
--                       restriction to E is a Frobenius at v; it is CLOSED (continuous restriction
--                       into a discrete finite Galois group).
--   * `frobSet_nonempty` (finite-layer Frobenius EXISTENCE): from Mathlib's
--                       `IsArithFrobAt.exists_of_isInvariant` at the layer E, lifted to galUr via
--                       surjectivity of `restrictNormalHom`. The group Frobenius bridges to the
--                       workspace's `IsFrobeniusAtPrime` via `galRestrict`.
--   * `frobSet_antitone` (finite-layer Frobenius RESTRICTION-COMPATIBILITY): a Frobenius on a
--                       larger layer restricts to a Frobenius on a smaller one, via `galRestrict'`
--                       naturality and the pure `isArithFrobAt_comap_of_comm` compatibility lemma.
--   * The family `{frobSet E}` is directed (compositum) with the finite-intersection property, so
--     by Cantor's intersection theorem for a compact space the total intersection is nonempty; any
--     element is a Frobenius representative on every finite layer, i.e. `IsFrobeniusRepAt`.
--
-- Paper label: prerequisite of §3.1 Chebotarev application (Proposition 3.6).
-- NL statement: For every number field F and every nonzero prime v of 𝓞 F, there exists an
-- element σ of galUr 3 F = Gal(F^{ur,3}/F) that is a Frobenius representative at v, i.e. whose
-- restriction to every finite-dimensional Galois layer F ≤ E ≤ F^{ur,3} is a Frobenius element at v.



open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.FrobeniusSplitting

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

namespace FrobRepProof

variable (F : Type*) [Field F] [NumberField F]

/-- `F^{ur,3}` is Galois over `F` (compositum of finite Galois layers). -/
instance galoisOmega : IsGalois F (maxUnramifiedProPExt 3 F) := by
  set S : Set (IntermediateField F (AlgebraicClosure F)) :=
    {E | IsFiniteUnramifiedProPExt 3 F E} with hS
  have hnorm : ∀ i : ↥S, Normal F (i : IntermediateField F (AlgebraicClosure F)) := by
    rintro ⟨E, hE⟩; obtain ⟨hfd, hgal, -, -⟩ := hE; haveI := hfd; exact hgal.to_normal
  have hsep : ∀ i : ↥S, Algebra.IsSeparable F (i : IntermediateField F (AlgebraicClosure F)) := by
    rintro ⟨E, hE⟩; obtain ⟨hfd, hgal, -, -⟩ := hE; haveI := hfd; exact hgal.to_isSeparable
  have hmax : maxUnramifiedProPExt 3 F = ⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)) := by
    rw [maxUnramifiedProPExt, sSup_eq_iSup']
  rw [hmax]
  haveI : Normal F (↥(⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)))) :=
    IntermediateField.normal_iSup F (AlgebraicClosure F) (h := hnorm)
  haveI : Algebra.IsSeparable F (↥(⨆ i : ↥S, (i : IntermediateField F (AlgebraicClosure F)))) :=
    IntermediateField.isSeparable_iSup (h := hsep)
  exact ⟨⟩

/-- The set of `σ ∈ galUr 3 F` whose restriction to the finite Galois layer `E` is a Frobenius
at `v`. -/
noncomputable def frobSet (v : Ideal (𝓞 F))
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) : Set (galUr 3 F) :=
  letI := hfd
  letI := hgal
  letI : NumberField E := NumberField.of_module_finite (K := F) (L := (E : Type _))
  (AlgEquiv.restrictNormalHom (E : Type _)) ⁻¹' {τ | IsFrobeniusAt τ v}

/-- Pure ring-theoretic compatibility of an arithmetic Frobenius under an algebra map. -/
theorem isArithFrobAt_comap_of_comm
    {R Sa Sb : Type*} [CommRing R] [CommRing Sa] [CommRing Sb]
    [Algebra R Sa] [Algebra R Sb] (j : Sa →ₐ[R] Sb)
    {φ : Sa →ₐ[R] Sa} {φ' : Sb →ₐ[R] Sb} {Q' : Ideal Sb}
    (hcomm : ∀ x, j (φ x) = φ' (j x)) (H' : φ'.IsArithFrobAt Q') :
    φ.IsArithFrobAt (Q'.comap (j : Sa →+* Sb)) := by
  have hunder : (Q'.comap (j : Sa →+* Sb)).under R = Q'.under R := by
    simp only [Ideal.under_def]
    rw [Ideal.comap_comap]
    congr 1
    exact j.comp_algebraMap
  intro x
  rw [hunder, Ideal.mem_comap, map_sub, map_pow]
  simp only [RingHom.coe_coe]
  rw [hcomm]
  exact H' (j x)

/-- Finite-layer Frobenius EXISTENCE: some `σ ∈ galUr 3 F` restricts to a Frobenius at `v` on `E`. -/
theorem frobSet_nonempty (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime)
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) :
    (frobSet F v E hfd hgal).Nonempty := by
  letI := hfd
  letI := hgal
  haveI : Normal F (E : Type _) := hgal.to_normal
  letI : NumberField (E : Type _) := NumberField.of_module_finite (K := F) (L := (E : Type _))
  haveI : v.IsPrime := hvp
  obtain ⟨Q, hQp, hQlo⟩ :=
    (inferInstance : Nonempty (Ideal.primesOver v (𝓞 (E : Type _)))).some
  haveI : Q.IsPrime := hQp
  haveI : Q.LiesOver v := hQlo
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hv
    have hunder : v = Q.under (𝓞 F) := hQlo.over
    rw [h] at hunder
    rw [Ideal.under_def, Ideal.comap_bot_of_injective _
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 (E : Type _)))] at hunder
    exact hunder
  haveI : Q.IsMaximal := hQp.isMaximal hQbot
  haveI : Finite (𝓞 (E : Type _) ⧸ Q) := inferInstance
  obtain ⟨τ, hτ⟩ :=
    IsArithFrobAt.exists_of_isInvariant (𝓞 F) ((E : Type _) ≃ₐ[F] (E : Type _)) Q
  have hbridge : (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ).toAlgHom
      = MulSemiringAction.toAlgHom (𝓞 F) (𝓞 (E : Type _)) τ := by
    apply AlgHom.ext
    intro x
    apply IsFractionRing.injective (𝓞 (E : Type _)) (E : Type _)
    show algebraMap (𝓞 (E : Type _)) (E : Type _)
          (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ x)
        = algebraMap (𝓞 (E : Type _)) (E : Type _) (τ • x)
    rw [algebraMap_galRestrict_apply]
    rfl
  have hfrob : IsFrobeniusAtPrime τ Q := by
    show (galRestrict (𝓞 F) F (E : Type _) (𝓞 (E : Type _)) τ).toAlgHom.IsArithFrobAt Q
    rw [hbridge]; exact hτ
  obtain ⟨s, hs⟩ := AlgEquiv.restrictNormalHom_surjective (F := F)
    (K₁ := (E : Type _)) (maxUnramifiedProPExt 3 F : Type _) τ
  refine ⟨s, ?_⟩
  show IsFrobeniusAt (AlgEquiv.restrictNormalHom (E : Type _) s) v
  rw [hs]
  exact ⟨Q, hQp, hQlo, hfrob⟩

/-- Finite-layer Frobenius RESTRICTION-COMPATIBILITY: a Frobenius on a larger layer `E₂` restricts
to a Frobenius on a smaller layer `E₁ ≤ E₂`. -/
theorem frobSet_antitone (v : Ideal (𝓞 F))
    (E₁ E₂ : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd₁ : FiniteDimensional F E₁) (hgal₁ : IsGalois F E₁)
    (hfd₂ : FiniteDimensional F E₂) (hgal₂ : IsGalois F E₂)
    (hle : E₁ ≤ E₂) :
    frobSet F v E₂ hfd₂ hgal₂ ⊆ frobSet F v E₁ hfd₁ hgal₁ := by
  letI := hfd₁; letI := hfd₂; letI := hgal₁; letI := hgal₂
  haveI : Normal F (E₁ : Type _) := hgal₁.to_normal
  haveI : Normal F (E₂ : Type _) := hgal₂.to_normal
  letI : NumberField (E₁ : Type _) := NumberField.of_module_finite (K := F) (L := (E₁ : Type _))
  letI : NumberField (E₂ : Type _) := NumberField.of_module_finite (K := F) (L := (E₂ : Type _))
  intro σ hσ
  simp only [frobSet, Set.mem_preimage, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨Q₂, hQ₂p, hQ₂lo, hQ₂frob⟩ := hσ
  haveI : Q₂.IsPrime := hQ₂p
  set τ₁ := AlgEquiv.restrictNormalHom (F := F)
    (K₁ := (maxUnramifiedProPExt 3 F : Type _)) (E₁ : Type _) σ with hτ₁
  set τ₂ := AlgEquiv.restrictNormalHom (F := F)
    (K₁ := (maxUnramifiedProPExt 3 F : Type _)) (E₂ : Type _) σ with hτ₂
  let incl : (E₁ : Type _) →ₐ[F] (E₂ : Type _) := IntermediateField.inclusion hle
  let j : 𝓞 (E₁ : Type _) →ₐ[𝓞 F] 𝓞 (E₂ : Type _) :=
    galRestrict' (𝓞 F) (𝓞 (E₁ : Type _)) (𝓞 (E₂ : Type _)) incl
  have hincl : ∀ z : (E₁ : Type _),
      algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (incl z)
      = algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) z := by
    intro z
    show algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _)
        (IntermediateField.inclusion hle z)
      = algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) z
    simp only [IntermediateField.algebraMap_apply, IntermediateField.coe_inclusion]
  have hfield : ∀ y : (E₁ : Type _), incl (τ₁ y) = τ₂ (incl y) := by
    intro y
    apply FaithfulSMul.algebraMap_injective (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _)
    have e1 : algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (incl (τ₁ y))
        = σ (algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) y) := by
      rw [hincl (τ₁ y)]
      exact AlgEquiv.restrictNormal_commutes σ (E₁ : Type _) y
    have e2 : algebraMap (E₂ : Type _) (maxUnramifiedProPExt 3 F : Type _) (τ₂ (incl y))
        = σ (algebraMap (E₁ : Type _) (maxUnramifiedProPExt 3 F : Type _) y) := by
      have h := AlgEquiv.restrictNormal_commutes σ (E₂ : Type _) (incl y)
      rw [hincl y] at h
      exact h
    rw [e1, e2]
  have hcomm : ∀ x, j ((galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁).toAlgHom x)
      = (galRestrict (𝓞 F) F (E₂ : Type _) (𝓞 (E₂ : Type _)) τ₂).toAlgHom (j x) := by
    intro x
    apply IsFractionRing.injective (𝓞 (E₂ : Type _)) (E₂ : Type _)
    show algebraMap (𝓞 (E₂ : Type _)) (E₂ : Type _)
          (j (galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁ x))
        = algebraMap (𝓞 (E₂ : Type _)) (E₂ : Type _)
          (galRestrict (𝓞 F) F (E₂ : Type _) (𝓞 (E₂ : Type _)) τ₂ (j x))
    rw [algebraMap_galRestrict'_apply, algebraMap_galRestrict_apply,
      algebraMap_galRestrict_apply, algebraMap_galRestrict'_apply, hfield]
  refine ⟨Q₂.comap (j : 𝓞 (E₁ : Type _) →+* 𝓞 (E₂ : Type _)), inferInstance, ?_, ?_⟩
  · refine ⟨?_⟩
    have : v = Q₂.under (𝓞 F) := hQ₂lo.over
    rw [this, Ideal.under_def, Ideal.under_def, Ideal.comap_comap]
    congr 1
    exact (j.comp_algebraMap).symm
  · show (galRestrict (𝓞 F) F (E₁ : Type _) (𝓞 (E₁ : Type _)) τ₁).toAlgHom.IsArithFrobAt _
    exact isArithFrobAt_comap_of_comm j hcomm hQ₂frob

/-- Closedness of the finite-layer Frobenius set. -/
theorem frobSet_isClosed (v : Ideal (𝓞 F))
    (E : IntermediateField F (maxUnramifiedProPExt 3 F))
    (hfd : FiniteDimensional F E) (hgal : IsGalois F E) :
    IsClosed (frobSet F v E hfd hgal) := by
  letI := hfd
  letI := hgal
  letI : NumberField (E : Type _) := NumberField.of_module_finite (K := F) (L := (E : Type _))
  haveI : DiscreteTopology ((E : Type _) ≃ₐ[F] (E : Type _)) :=
    krullTopology_discreteTopology_of_finiteDimensional F (E : Type _)
  exact (isClosed_discrete _).preimage (InfiniteGalois.restrictNormalHom_continuous E)

end FrobRepProof

open FrobRepProof

/-- **Existence of a Frobenius representative in `Gal(F^{ur,3}/F)` at an unramified prime.**
Proved from Mathlib (infinite Galois theory, compactness): the decomposition system at a prime `v`
assembles, by the finite-intersection property in the compact profinite group `galUr 3 F`, into a
single element restricting to a Frobenius on every finite Galois layer. -/
theorem FrobRepExistsMaxUnramified
    (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime) :
    ∃ σ : galUr 3 F, IsFrobeniusRepAt 3 F σ v := by
  haveI : CompactSpace (galUr 3 F) := inferInstance
  set Idx := {E : IntermediateField F (maxUnramifiedProPExt 3 F) //
    FiniteDimensional F E ∧ IsGalois F E} with hIdx
  set t : Idx → Set (galUr 3 F) := fun EE => frobSet F v EE.1 EE.2.1 EE.2.2 with ht
  haveI : Nonempty Idx := ⟨⟨⊥, inferInstance, inferInstance⟩⟩
  have hclosed : ∀ EE : Idx, IsClosed (t EE) := fun EE => frobSet_isClosed F v EE.1 EE.2.1 EE.2.2
  have hcompact : ∀ EE : Idx, IsCompact (t EE) := fun EE => (hclosed EE).isCompact
  have hne : ∀ EE : Idx, (t EE).Nonempty := fun EE => frobSet_nonempty F v hv hvp EE.1 EE.2.1 EE.2.2
  have hdir : Directed (· ⊇ ·) t := by
    rintro ⟨E₁, hfd₁, hgal₁⟩ ⟨E₂, hfd₂, hgal₂⟩
    haveI := hfd₁; haveI := hfd₂; haveI := hgal₁; haveI := hgal₂
    haveI : FiniteDimensional F (↥(E₁ ⊔ E₂)) := IntermediateField.finiteDimensional_sup E₁ E₂
    haveI : IsGalois F (↥(E₁ ⊔ E₂)) := inferInstance
    refine ⟨⟨E₁ ⊔ E₂, ⟨‹_›, ‹_›⟩⟩, ?_, ?_⟩
    · exact frobSet_antitone F v E₁ (E₁ ⊔ E₂) hfd₁ hgal₁ ‹_› ‹_› le_sup_left
    · exact frobSet_antitone F v E₂ (E₁ ⊔ E₂) hfd₂ hgal₂ ‹_› ‹_› le_sup_right
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    t hdir hne hcompact hclosed
  refine ⟨σ, ?_⟩
  intro E hfdE hgalE
  have := Set.mem_iInter.mp hσ ⟨E, hfdE, hgalE⟩
  exact this

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension

set_option maxHeartbeats 800000

/-- **Existence of a Frobenius representative at a finite prime.** For every number field `F` and
every prime `v : Ideal (𝓞 F)` with `v ≠ ⊥` and `v.IsPrime`, there exists `σ : galUr 3 F` that is a
Frobenius representative at `v` (`IsFrobeniusRepAt 3 F σ v`): a compatible system of Frobenii
restricting to a Frobenius element on every finite Galois layer of `F^{ur,3}/F`. Unconditional in
`v` (every finite layer is everywhere unramified over `F`). -/
theorem SublemmaFrobRepExists
    (F : Type*) [Field F] [NumberField F]
    (v : Ideal (𝓞 F)) (hv : v ≠ ⊥) (hvp : v.IsPrime) :
    ∃ σ : galUr 3 F, IsFrobeniusRepAt 3 F σ v :=
  FrobRepExistsMaxUnramified F v hv hvp

/-!
# Infinitely many rational primes split completely in a finite Galois extension of `ℚ`

Proof that infinitely many rational primes split completely in a finite Galois extension `N/ℚ`
(the input the paper draws from Chebotarev density), by an elementary Schur/Kummer–Dedekind argument.

The full Chebotarev density theorem is not in Mathlib.  But the statement
actually used by the paper is much weaker — *there exist `t` distinct primes outside a finite set `T`
splitting completely in `N`* — and that has a classical elementary proof, formalised here:

* `exists_prime_gt_dvd_eval` (**Schur**): a nonconstant `f ∈ ℤ[X]` has values divisible by
  arbitrarily large primes.  Proof: with `c = f(0) ≠ 0` and `M = c·n₀!`, every value `f(M y)` equals
  `c·(1 + n₀!·k)`; a prime factor of the second factor is coprime to `n₀!`, hence `> n₀`.
* `exists_int_mul_mem_adjoin` / `exponent_ne_zero`: for a primitive integral generator `θ` of `N`,
  the Kummer–Dedekind exponent of `θ` is nonzero (clear denominators using
  `Algebra.discr_mul_isIntegral_mem_adjoin`).
* `ramificationIdx_one_of_not_dvd_discr`: a prime not dividing `|D_N|` is unramified (via
  `NumberField.absNorm_differentIdeal` and `not_dvd_differentIdeal_iff`).
* `splitsCompletelyRat_of_root`: if `minpoly ℤ θ` has a root mod `p` and `p` divides neither the
  exponent nor the discriminant, then `p` splits completely.  Kummer–Dedekind
  (`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`) turns the root into a prime of residue
  degree `1`; since `N/ℚ` is Galois *all* residue degrees are then `1`
  (`Ideal.inertiaDeg_eq_of_isGaloisGroup`), and the fundamental identity gives exactly `[N:ℚ]`
  primes above `p`.
* `infinite_splitsCompletelyRat` and `chebotarevManySplitPrimes` assemble these.
-/

open scoped NumberField
open Polynomial Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Workspace.ProofLemmas.ChebotarevSplitPrimes

/-- The set of integers at which `f` takes one of finitely many prescribed nonzero-polynomial
values is finite: here, the `x` with `f.eval x ∈ ({0, c, -c} : Set ℤ)`. -/
private theorem finite_bad (f : ℤ[X]) (hf : 0 < f.natDegree) (c : ℤ) :
    {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c}.Finite := by
  have hne : ∀ d : ℤ, (f - C d) ≠ 0 := by
    intro d hd
    have : f = C d := by linear_combination (norm := ring_nf) hd
    rw [this] at hf
    simp at hf
  have h : ∀ d : ℤ, {x : ℤ | f.eval x = d}.Finite := by
    intro d
    have : {x : ℤ | f.eval x = d} ⊆ {x : ℤ | (f - C d).IsRoot x} := by
      intro x hx
      simp only [Set.mem_setOf_eq, IsRoot.def, eval_sub, eval_C] at *
      omega
    exact Set.Finite.subset (Polynomial.finite_setOf_isRoot (hne d)) this
  have : {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c}
      = {x : ℤ | f.eval x = 0} ∪ ({x : ℤ | f.eval x = c} ∪ {x : ℤ | f.eval x = -c}) := by
    ext x; simp [Set.mem_union]
  rw [this]
  exact (h 0).union ((h c).union (h (-c)))

/-- **Schur's theorem.**  For a nonconstant integer polynomial `f` and any bound `n₀`, there is a
prime `p > n₀` dividing some value of `f`. -/
theorem exists_prime_gt_dvd_eval (f : ℤ[X]) (hf : 0 < f.natDegree) (n₀ : ℕ) :
    ∃ p : ℕ, p.Prime ∧ n₀ < p ∧ ∃ m : ℤ, (p : ℤ) ∣ f.eval m := by
  classical
  set c : ℤ := f.eval 0 with hc
  by_cases hc0 : c = 0
  · obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (n₀ + 1)
    exact ⟨p, hp, by omega, 0, by rw [← hc, hc0]; exact dvd_zero _⟩
  -- `M = c * n₀!`; every value `f (M * y)` is `c * (1 + n₀! * k)`
  set N : ℤ := (Nat.factorial n₀ : ℤ) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; exact_mod_cast Nat.factorial_ne_zero n₀
  set M : ℤ := c * N with hM
  have hM0 : M ≠ 0 := mul_ne_zero hc0 hN0
  -- choose `y` avoiding the finitely many bad values
  have hbad := finite_bad f hf c
  have hinj : Function.Injective (fun y : ℤ => M * y) := fun a b h => by
    simpa [hM0] using mul_left_cancel₀ hM0 h
  have hfiny : {y : ℤ | f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c}.Finite := by
    have : {y : ℤ | f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c}
        ⊆ (fun y : ℤ => M * y) ⁻¹' {x : ℤ | f.eval x = 0 ∨ f.eval x = c ∨ f.eval x = -c} := by
      intro y hy; exact hy
    exact Set.Finite.subset (Set.Finite.preimage hinj.injOn hbad) this
  obtain ⟨y, hy⟩ : ∃ y : ℤ, ¬ (f.eval (M * y) = 0 ∨ f.eval (M * y) = c ∨ f.eval (M * y) = -c) := by
    by_contra hcon
    push_neg at hcon
    exact Set.infinite_univ (α := ℤ) (Set.Finite.subset hfiny (fun y _ => hcon y))
  push_neg at hy
  obtain ⟨hy0, hyc, hync⟩ := hy
  -- `M ∣ f (M*y) - c`
  set D : ℤ := f.eval (M * y) with hD
  have hdvd : M ∣ D - c := by
    have := sub_dvd_eval_sub (M * y) 0 f
    simp only [sub_zero] at this
    exact dvd_trans (Dvd.intro y rfl) this
  obtain ⟨k, hk⟩ := hdvd
  set B : ℤ := 1 + N * k with hB
  have hDB : D = c * B := by
    rw [hB, hD]
    have : D - c = c * N * k := by rw [hk, hM]
    linarith [this]
  -- `|B| ≥ 2`
  have hB2 : B.natAbs ≠ 1 ∧ B.natAbs ≠ 0 := by
    constructor
    · intro h
      rcases Int.natAbs_eq_iff.mp h with h1 | h1
      · exact hyc (by rw [hDB, h1]; ring)
      · exact hync (by rw [hDB, h1]; ring)
    · intro h
      have : B = 0 := by omega
      exact hy0 (by rw [hDB, this, mul_zero])
  set p : ℕ := B.natAbs.minFac with hp
  have hpprime : p.Prime := Nat.minFac_prime hB2.1
  have hpB : (p : ℤ) ∣ B :=
    dvd_trans (Int.natCast_dvd_natCast.mpr (Nat.minFac_dvd _)) (Int.natAbs_dvd.mpr dvd_rfl)
  refine ⟨p, hpprime, ?_, M * y, ?_⟩
  · -- `p ∤ n₀!`, hence `p > n₀`
    by_contra hple
    push_neg at hple
    have hdvdfac : (p : ℤ) ∣ N := by
      rw [hN]
      exact_mod_cast Nat.dvd_factorial hpprime.pos hple
    have : (p : ℤ) ∣ 1 := by
      have h1 : (1 : ℤ) = B - N * k := by rw [hB]; ring
      rw [h1]
      exact dvd_sub hpB (Dvd.dvd.mul_right hdvdfac k)
    have := Int.le_of_dvd one_pos this
    have := hpprime.two_le
    omega
  · rw [← hD, hDB]
    exact Dvd.dvd.mul_left hpB c

/-- For a primitive integral generator `θ` of a number field, some nonzero integer multiplies all of
`𝓞 N` into `ℤ[θ]` (clear denominators via the discriminant of the power basis). -/
theorem exists_int_mul_mem_adjoin (N : Type*) [Field N] [NumberField N] (θ : 𝓞 N)
    (hθ : Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ z : 𝓞 N, (d : 𝓞 N) * z ∈ Algebra.adjoin ℤ ({θ} : Set (𝓞 N)) := by
  have hint : IsIntegral ℚ (θ : N) := IsIntegral.of_finite ℚ _
  -- the power basis generated by `θ`
  let pb0 : PowerBasis ℚ ↥(Algebra.adjoin ℚ ({(θ : N)} : Set N)) := Algebra.adjoin.powerBasis hint
  let e : ↥(Algebra.adjoin ℚ ({(θ : N)} : Set N)) ≃ₐ[ℚ] N :=
    (Subalgebra.equivOfEq _ ⊤ hθ).trans Subalgebra.topEquiv
  let pb : PowerBasis ℚ N := pb0.map e
  have hgen : pb.gen = (θ : N) := by
    show e pb0.gen = (θ : N)
    rw [Algebra.adjoin.powerBasis_gen]
    rfl
  have hbint : ∀ i, IsIntegral ℤ (pb.basis i) := by
    intro i
    rw [pb.basis_eq_pow, hgen]
    exact (θ.isIntegral_coe).pow _
  have hdQint : IsIntegral ℤ (Algebra.discr ℚ pb.basis) := Algebra.discr_isIntegral ℚ hbint
  obtain ⟨d, hdeq⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdQint
  have hdQne : Algebra.discr ℚ pb.basis ≠ 0 := Algebra.discr_not_zero_of_basis ℚ pb.basis
  have hd0 : d ≠ 0 := by
    intro h
    apply hdQne
    rw [← hdeq, h]
    simp
  refine ⟨d, hd0, ?_⟩
  intro z
  have hz : IsIntegral ℤ (z : N) := z.isIntegral_coe
  have hmem : Algebra.discr ℚ pb.basis • (z : N) ∈ Algebra.adjoin ℤ ({pb.gen} : Set N) :=
    Algebra.discr_mul_isIntegral_mem_adjoin ℚ (hgen ▸ (θ.isIntegral_coe)) hz
  rw [hgen] at hmem
  -- rewrite the ℚ-scalar action as multiplication by the integer `d`
  have hsmul : Algebra.discr ℚ pb.basis • (z : N) = ((d : 𝓞 N) * z : 𝓞 N) := by
    rw [← hdeq, Algebra.smul_def]
    push_cast
    simp [algebraMap_int_eq]
  rw [hsmul] at hmem
  -- descend the membership from `N` to `𝓞 N`
  have hmapadj : Algebra.adjoin ℤ ({(θ : N)} : Set N)
      = (Algebra.adjoin ℤ ({θ} : Set (𝓞 N))).map (IsScalarTower.toAlgHom ℤ (𝓞 N) N) := by
    rw [AlgHom.map_adjoin]
    congr 1
    simp
  rw [hmapadj] at hmem
  obtain ⟨w, hw, hwz⟩ := hmem
  have : w = (d : 𝓞 N) * z := by
    apply NumberField.RingOfIntegers.coe_injective
    exact hwz
  rwa [this] at hw


/-- The Kummer–Dedekind exponent of a primitive integral generator is nonzero. -/
theorem exponent_ne_zero (N : Type*) [Field N] [NumberField N] (θ : 𝓞 N)
    (hθ : Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤) :
    RingOfIntegers.exponent θ ≠ 0 := by
  obtain ⟨d, hd0, hd⟩ := exists_int_mul_mem_adjoin N θ hθ
  have hmem : (d : 𝓞 N) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    exact hd
  have hmem' : d ∈ Ideal.under ℤ (conductor ℤ θ) := by
    rw [Ideal.under, Ideal.mem_comap]
    simpa using hmem
  intro hzero
  rw [RingOfIntegers.exponent, Ideal.absNorm_eq_zero_iff] at hzero
  rw [hzero, Ideal.mem_bot] at hmem'
  exact hd0 hmem'

/-- A number field has an integral primitive element. -/
theorem exists_integral_primitive_element (N : Type*) [Field N] [NumberField N] :
    ∃ θ : 𝓞 N, Algebra.adjoin ℚ ({(θ : N)} : Set N) = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ N
  haveI : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.IsAlgebraic ℤ N := Algebra.IsAlgebraic.trans (R := ℤ) (S := ℚ) (A := N)
  obtain ⟨y, hy0, hyint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) α).exists_integral_multiple
  refine ⟨⟨y • α, hyint⟩, ?_⟩
  show Algebra.adjoin ℚ ({y • α} : Set N) = ⊤
  rw [← Int.cast_smul_eq_zsmul ℚ y α]
  have hy0' : (y : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hy0
  have hsmul : IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N)
      = IntermediateField.adjoin ℚ ({α} : Set N) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have h1 : α ∈ IntermediateField.adjoin ℚ ({α} : Set N) :=
        IntermediateField.mem_adjoin_simple_self ℚ α
      show (y : ℚ) • α ∈ IntermediateField.adjoin ℚ ({α} : Set N)
      rw [Algebra.smul_def]
      exact mul_mem (IntermediateField.algebraMap_mem _ _) h1
    · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
      have h1 : (y : ℚ) • α ∈ IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N) :=
        IntermediateField.mem_adjoin_simple_self ℚ _
      have h2 : (algebraMap ℚ N ((y : ℚ)⁻¹)) * ((y : ℚ) • α)
          ∈ IntermediateField.adjoin ℚ ({(y : ℚ) • α} : Set N) :=
        mul_mem (IntermediateField.algebraMap_mem _ _) h1
      have h3 : (algebraMap ℚ N ((y : ℚ)⁻¹)) * ((y : ℚ) • α) = α := by
        rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hy0', one_smul]
      rwa [h3] at h2
  have hint2 : IsIntegral ℚ ((y : ℚ) • α) := IsIntegral.of_finite ℚ _
  have hEq := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (hint2.isAlgebraic (R := ℚ))
  rw [← hEq, hsmul, hα]
  rfl

/-- A rational prime not dividing the absolute discriminant is unramified. -/
theorem ramificationIdx_one_of_not_dvd_discr (N : Type*) [Field N] [NumberField N]
    (p : ℕ) (hp : p.Prime) (hdiscr : ¬ p ∣ (NumberField.discr N).natAbs)
    (P : Ideal (𝓞 N)) (hP : P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N)) :
    Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 := by
  obtain ⟨hPprime, hPlies⟩ := hP
  haveI : P.IsPrime := hPprime
  haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPlies
  have hspan : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by
    simp [Ideal.span_singleton_eq_bot, hp.ne_zero]
  have hPne : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspan P
  -- if `P` divided the different ideal, `p` would divide the discriminant
  have hnotdvd : ¬ P ∣ differentIdeal ℤ (𝓞 N) := by
    intro hdvd
    have h1 : Ideal.absNorm P ∣ Ideal.absNorm (differentIdeal ℤ (𝓞 N)) := map_dvd _ hdvd
    rw [NumberField.absNorm_differentIdeal N] at h1
    refine hdiscr (dvd_trans ?_ h1)
    -- `p ∣ absNorm P` because `absNorm P ∈ P` and `P ∩ ℤ = pℤ`
    have h2 : ((Ideal.absNorm P : ℤ) : 𝓞 N) ∈ P := by
      have := Ideal.absNorm_mem P
      exact_mod_cast this
    have h3 : (Ideal.absNorm P : ℤ) ∈ Ideal.under ℤ P := by
      rw [Ideal.under, Ideal.mem_comap]
      simpa using h2
    rw [← hPlies.over, Ideal.mem_span_singleton] at h3
    exact_mod_cast h3
  haveI : Algebra.IsUnramifiedAt ℤ P := (not_dvd_differentIdeal_iff).mp hnotdvd
  rw [hPlies.over]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := ℤ) (S := 𝓞 N) (p := P) hPne

open NumberField RingOfIntegers NumberField.Ideal in
/-- If the minimal polynomial of a primitive integral generator has a root mod `p`, and `p` divides
neither the Kummer–Dedekind exponent nor the discriminant, then `p` splits completely. -/
theorem splitsCompletelyRat_of_root (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]
    (θ : 𝓞 N) (p : ℕ) (hpprime : p.Prime)
    (hexp : ¬ p ∣ RingOfIntegers.exponent θ)
    (hdiscr : ¬ p ∣ (NumberField.discr N).natAbs)
    (m : ℤ) (hm : (p : ℤ) ∣ (minpoly ℤ θ).eval m) :
    SplitsCompletelyRat p N := by
  haveI : Fact p.Prime := ⟨hpprime⟩
  classical
  letI act : MulSemiringAction (N ≃ₐ[ℚ] N) (𝓞 N) :=
    IsIntegralClosure.MulSemiringAction ℤ ℚ N (𝓞 N)
  haveI : IsGaloisGroup (N ≃ₐ[ℚ] N) ℤ (𝓞 N) := IsGaloisGroup.of_isFractionRing _ _ _ ℚ N
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hspan : (Ideal.span {(p : ℤ)}) ≠ ⊥ := by simp [hpprime.ne_zero]
  set f : ℤ[X] := minpoly ℤ θ with hf
  have hfmonic : f.Monic := minpoly.monic θ.isIntegral
  have hfbar : f.map (Int.castRingHom (ZMod p)) ≠ 0 :=
    (hfmonic.map (Int.castRingHom (ZMod p))).ne_zero
  set a : ZMod p := (m : ZMod p) with ha
  set Q : (ZMod p)[X] := X - C a with hQdef
  have hroot : (f.map (Int.castRingHom (ZMod p))).eval a = 0 := by
    rw [ha, eval_map]
    have hcast : ((Int.castRingHom (ZMod p)) m) = (m : ZMod p) := rfl
    rw [← hcast, eval₂_hom]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hm
  have hQ : Q ∈ monicFactorsMod θ p := by
    rw [monicFactorsMod, Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hfbar]
    exact ⟨irreducible_X_sub_C a, monic_X_sub_C a, (dvd_iff_isRoot).mpr hroot⟩
  set P₀ := (primesOverSpanEquivMonicFactorsMod hexp).symm ⟨Q, hQ⟩ with hP₀
  have hP₀mem : (P₀ : Ideal (𝓞 N)) ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N) := P₀.2
  have hinertia₀ : Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) (P₀ : Ideal (𝓞 N)) = 1 := by
    rw [hP₀, inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hexp hQ, hQdef]
    simp
  have hall : ∀ P ∈ Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 N),
      Ideal.ramificationIdx (Ideal.span {(p : ℤ)}) P = 1 ∧
        Ideal.inertiaDeg (Ideal.span {(p : ℤ)}) P = 1 := by
    intro P hP
    refine ⟨ramificationIdx_one_of_not_dvd_discr N p hpprime hdiscr P hP, ?_⟩
    obtain ⟨hPprime, hPlies⟩ := hP
    haveI : P.IsPrime := hPprime
    haveI : P.LiesOver (Ideal.span {(p : ℤ)}) := hPlies
    obtain ⟨hP₀prime, hP₀lies⟩ := hP₀mem
    haveI : (P₀ : Ideal (𝓞 N)).IsPrime := hP₀prime
    haveI : (P₀ : Ideal (𝓞 N)).LiesOver (Ideal.span {(p : ℤ)}) := hP₀lies
    rw [← hinertia₀]
    exact Ideal.inertiaDeg_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)
  haveI : (P₀ : Ideal (𝓞 N)).IsPrime := hP₀mem.1
  haveI : (P₀ : Ideal (𝓞 N)).LiesOver (Ideal.span {(p : ℤ)}) := hP₀mem.2
  have hridx : Ideal.ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 N) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)})
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)]
    exact (hall _ hP₀mem).1
  have hidxin : Ideal.inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 N) = 1 := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg (Ideal.span {(p : ℤ)})
      (P₀ : Ideal (𝓞 N)) (N ≃ₐ[ℚ] N)]
    exact hinertia₀
  have hfund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn hspan (𝓞 N)
    (N ≃ₐ[ℚ] N)
  rw [hridx, hidxin, one_mul, mul_one] at hfund
  refine ⟨hpprime, ?_, fun P hP => hall P hP⟩
  rw [hfund]
  exact IsGalois.card_aut_eq_finrank ℚ N

section Assembly

variable (N : Type*) [Field N] [NumberField N] [IsGalois ℚ N]

/-- There are infinitely many rational primes splitting completely in a finite Galois `N/ℚ`. -/
theorem infinite_splitsCompletelyRat :
    {p : ℕ | p.Prime ∧ SplitsCompletelyRat p N}.Infinite := by
  classical
  obtain ⟨θ, hθ⟩ := exists_integral_primitive_element N
  have hexp0 : RingOfIntegers.exponent θ ≠ 0 := exponent_ne_zero N θ hθ
  have hdiscr0 : (NumberField.discr N).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero N)
  have hdeg : 0 < (minpoly ℤ θ).natDegree := minpoly.natDegree_pos θ.isIntegral
  rw [← Nat.frequently_atTop_iff_infinite]
  refine Filter.frequently_atTop.2 fun n => ?_
  obtain ⟨p, hpprime, hgt, m, hm⟩ :=
    exists_prime_gt_dvd_eval (minpoly ℤ θ) hdeg
      (max n (max (RingOfIntegers.exponent θ) (NumberField.discr N).natAbs))
  have h1 : n ≤ p := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hgt)
  have h2 : ¬ p ∣ RingOfIntegers.exponent θ := by
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hexp0) hdvd
    have : RingOfIntegers.exponent θ < p :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hgt
    omega
  have h3 : ¬ p ∣ (NumberField.discr N).natAbs := by
    intro hdvd
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hdiscr0) hdvd
    have : (NumberField.discr N).natAbs < p :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hgt
    omega
  exact ⟨p, h1, hpprime, splitsCompletelyRat_of_root N θ p hpprime h2 h3 m hm⟩

/-- **Chebotarev, weak form used by the paper.**  For a finite Galois `N/ℚ`, a finite excluded set
`T` of rational primes and any `t`, there are `t` distinct rational primes outside `T` splitting
completely in `N`. -/
theorem chebotarevManySplitPrimes (T : Finset ℕ) (t : ℕ) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧
      ∀ b, (q b).Prime ∧ q b ∉ T ∧ SplitsCompletelyRat (q b) N := by
  classical
  have hinf : ({p : ℕ | p.Prime ∧ SplitsCompletelyRat p N} \ (T : Set ℕ)).Infinite :=
    (infinite_splitsCompletelyRat N).diff T.finite_toSet
  obtain ⟨u, husub, hucard⟩ := hinf.exists_subset_card_eq t
  refine ⟨fun i => ((u.orderIsoOfFin hucard i : ℕ)), ?_, ?_⟩
  · intro i j hij
    exact (u.orderIsoOfFin hucard).injective (Subtype.ext hij)
  · intro b
    have hmem : ((u.orderIsoOfFin hucard b : ℕ)) ∈ ({p : ℕ | p.Prime ∧ SplitsCompletelyRat p N}
        \ (T : Set ℕ)) := husub (u.orderIsoOfFin hucard b).2
    exact ⟨hmem.1.1, fun hcon => hmem.2 hcon, hmem.1.2⟩

end Assembly

end Workspace.ProofLemmas.ChebotarevSplitPrimes

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

open scoped NumberField
open Polynomial
open Workspace.Types.SplittingRamification
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

theorem Prop36ChebotarevApplication
    (F : Type) [Field F] [NumberField F]
    (hfg : TopFinitelyGenerated (galUr 3 F))
    (t : ℕ) (ht : 0 < t) (T : Finset ℕ) :
    ∃ q : Fin t → ℕ, Function.Injective q ∧
      (∀ b, (q b).Prime ∧ q b ∉ T) ∧
      ∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) F ∧
        ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 F),
          ∃ σ : galUr 3 F,
            Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 F σ v ∧
              σ ∈ frattiniOpen (galUr 3 F) := by
  classical
  -- Step 0: pro-3 structure of G = galUr 3 F
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  -- Step 1: Frattini quotient extension E := fixedFieldOf 3 F Φ
  obtain ⟨hΦopen, hΦnormal, ⟨kk, hkindex⟩, hEfd, hEgal, hker⟩ :=
    SublemmaFrattiniQuotientField F hpro hfg
  haveI hEfd' := hEfd
  haveI hEgal' := hEgal
  haveI hnfE : NumberField (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) :=
    NumberField.of_module_finite (K := F)
      (L := (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _))
  -- Step 2: N = normal closure of E(i) over ℚ.  Peel the instance telescope one
  -- existential at a time, registering each instance before elaborating the next.
  have hNC := SublemmaFieldNormalClosure F (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _)
  obtain ⟨Nn, hNC⟩ := hNC
  obtain ⟨fN, hNC⟩ := hNC; letI := fN
  obtain ⟨nfN, hNC⟩ := hNC; letI := nfN
  obtain ⟨galQN, hNC⟩ := hNC; letI := galQN
  obtain ⟨algEN, hNC⟩ := hNC; letI := algEN
  obtain ⟨twQEN, hNC⟩ := hNC; letI := twQEN
  obtain ⟨ii, hii⟩ := hNC
  -- Step 3: Chebotarev on N
  obtain ⟨q, hqinj, hq⟩ := ChebotarevManySplitPrimes Nn T t
  refine ⟨q, hqinj, fun b => ⟨(hq b).1, (hq b).2.1⟩, ?_⟩
  intro b
  set qb := q b with hqb
  have hqbP : qb.Prime := (hq b).1
  have hqN : SplitsCompletelyRat qb Nn := (hq b).2.2
  -- descend N → E
  haveI hEN_fd : FiniteDimensional (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) Nn :=
    Module.Finite.right ℚ (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) Nn
  have hqE : SplitsCompletelyRat qb (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) :=
    SublemmaCompleteSplittingDescends Nn
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) qb hqN
  -- transitivity in F ⊆ E: property 2 and the per-prime splitting
  obtain ⟨hqF, hvall⟩ :=
    (SublemmaSplittingTransitive F
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) qb).mp hqE
  -- Property 1: q % 4 = 1 via ℚ(i)
  have hq4 : qb % 4 = 1 := by
    set Qi := IntermediateField.adjoin ℚ ({ii} : Set Nn) with hQi
    have hmem : ii ∈ Qi := IntermediateField.mem_adjoin_simple_self ℚ ii
    haveI hnfQi : NumberField (Qi : Type _) :=
      NumberField.of_module_finite (K := ℚ) (L := (Qi : Type _))
    haveI hQiN_fd : FiniteDimensional (Qi : Type _) Nn := Module.Finite.right ℚ (Qi : Type _) Nn
    have hwit : ∃ x : (Qi : Type _), x ^ 2 = -1 := by
      refine ⟨⟨ii, hmem⟩, ?_⟩; apply Subtype.ext; push_cast; exact hii
    have hdeg : Module.finrank ℚ (Qi : Type _) = 2 := by
      haveI : Algebra.IsIntegral ℚ Nn := Algebra.IsIntegral.of_finite ℚ Nn
      have hint : IsIntegral ℚ ii := Algebra.IsIntegral.isIntegral ii
      have hmonic : (X ^ 2 + 1 : ℚ[X]).Monic := by
        have h : (X ^ 2 + 1 : ℚ[X]) = X ^ 2 + C 1 := by simp
        rw [h]; exact monic_X_pow_add (by simp)
      have haeval : (Polynomial.aeval ii) (X ^ 2 + 1 : ℚ[X]) = 0 := by simp [hii]
      have hnd : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
      have hirr : Irreducible (X ^ 2 + 1 : ℚ[X]) := by
        by_contra hcon
        rw [Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff hmonic hnd] at hcon
        obtain ⟨c₁, c₂, hc0, hc1⟩ := hcon
        simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.coeff_one] at hc0 hc1
        norm_num at hc0 hc1
        nlinarith [sq_nonneg c₁, sq_nonneg c₂]
      have hmin : minpoly ℚ ii = X ^ 2 + 1 :=
        (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm
      rw [IntermediateField.adjoin.finrank hint, hmin, hnd]
    have hqQi : SplitsCompletelyRat qb (Qi : Type _) :=
      SublemmaCompleteSplittingDescends Nn (Qi : Type _) qb hqN
    exact SublemmaSplitInQiModFour (Qi : Type _) hwit hdeg qb hqbP hqQi
  refine ⟨hq4, hqF, ?_⟩
  -- Property 3: Frobenius representative in Φ at each v ∣ q
  intro v hv
  have hvmem := hv
  simp only [Ideal.primesOver, Set.mem_setOf_eq] at hv
  obtain ⟨hvprime, hvlies⟩ := hv
  haveI := hvprime
  haveI := hvlies
  have hspanne : Ideal.span {(qb : ℤ)} ≠ ⊥ := by
    simp only [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hqbP.ne_zero
  have hvne : v ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanne v
  have hvsplit : SplitsCompletely (F := F)
      (M := (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _)) v := hvall v hvmem
  obtain ⟨σ, hσfrob⟩ := SublemmaFrobRepExists F v hvne hvprime
  have hφfrob := hσfrob (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)))
  have hφ1 := SublemmaSplitCompletelyFrobTrivial F
      (fixedFieldOf 3 F (frattiniOpen (galUr 3 F)) : Type _) v hvne hvprime hvsplit _ hφfrob
  have hσΦ : σ ∈ frattiniOpen (galUr 3 F) := by
    rw [← hker]; exact MonoidHom.mem_ker.mpr hφ1
  exact ⟨σ, hσfrob, hσΦ⟩

/-!
# `hfg`-free maximality lemma for pro-`p` groups (shared auxiliary)

`maxOpen_normal_index_p` : in a pro-`p` group every maximal proper *open* subgroup is normal of
index `p`.  This is the `TopFinitelyGenerated`-free form of `ProPMaximalOpenNormalIndexP`; it is
extracted into its own file so that both `GalUrFrattiniQuotientFinite` and `GalUrTopFinGen` can use
it without circularity (the frozen sibling `ProPMaximalOpenNormalIndexP` carries a spurious
`TopFinitelyGenerated G` hypothesis, which is exactly what those two results are proving).
-/

set_option maxHeartbeats 800000

open Workspace.Types.ProPGroup

namespace Workspace.ProofLemmas.ProPMaxOpenFree

/-- (hfg-free re-derivation of R1 `ProPMaximalOpenNormalIndexP`.) In a pro-`p` group `G`, every
maximal proper open subgroup `H` is normal of index `p`. The original sibling carries a spurious
`TopFinitelyGenerated G` hypothesis (unused in its proof); we re-derive it here without that
hypothesis so it can be used to *prove* topological finite generation without circularity. -/
theorem maxOpen_normal_index_p (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (H : Subgroup G) (hH : IsMaximalOpenSubgroup H) :
    H.Normal ∧ H.index = p := by
  obtain ⟨_, hcompact, _hT2, _hTD, hPindex⟩ := hpro
  haveI := hcompact
  obtain ⟨hHopen, hHne, hHmax⟩ := hH
  haveI hHfq : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI hHfi : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hNH : H.normalCore ≤ H := Subgroup.normalCore_le H
  have hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHopen
  have hNclosed : IsClosed (H.normalCore : Set G) := Subgroup.normalCore_isClosed H hHclosed
  have hNopen : IsOpen (H.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex H.normalCore hNclosed
  obtain ⟨k, hk⟩ := hPindex H.normalCore inferInstance hNopen
  haveI hPfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hcardP : Nat.card (G ⧸ H.normalCore) = p ^ k := by
    rw [← Subgroup.index_eq_card]; exact hk
  haveI hPgroup : IsPGroup p (G ⧸ H.normalCore) := IsPGroup.of_card hcardP
  haveI hPnil : Group.IsNilpotent (G ⧸ H.normalCore) := hPgroup.isNilpotent
  have hNC : NormalizerCondition (G ⧸ H.normalCore) := normalizerCondition_of_isNilpotent
  set f := QuotientGroup.mk' H.normalCore with hfdef
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective H.normalCore
  have hker : f.ker = H.normalCore := QuotientGroup.ker_mk' H.normalCore
  set Hbar := Subgroup.map f H with hHbardef
  have hcomapHbar : Subgroup.comap f Hbar = H := by
    rw [hHbardef, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNH
  have hcoatom : IsCoatom Hbar := by
    constructor
    · intro htop
      apply hHne
      have hc : Subgroup.comap f Hbar = Subgroup.comap f ⊤ := by rw [htop]
      rw [hcomapHbar, Subgroup.comap_top] at hc
      exact hc
    · intro Kbar hKbar
      have hNK : H.normalCore ≤ Subgroup.comap f Kbar := by
        have h1 : f.ker ≤ Subgroup.comap f Kbar := by
          rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
        rwa [hker] at h1
      have hKopen : IsOpen ((Subgroup.comap f Kbar) : Set G) := Subgroup.isOpen_mono hNK hNopen
      have hHK : H ≤ Subgroup.comap f Kbar :=
        Subgroup.map_le_iff_le_comap.mp (by rw [← hHbardef]; exact hKbar.le)
      have hmapK : Subgroup.map f (Subgroup.comap f Kbar) = Kbar :=
        Subgroup.map_comap_eq_self_of_surjective hfsurj Kbar
      rcases hHmax (Subgroup.comap f Kbar) hKopen hHK with hKH | hKtop
      · have hcontra : Kbar = Hbar := by rw [← hmapK, hKH, ← hHbardef]
        exact absurd hcontra.symm (ne_of_lt hKbar)
      · rw [← hmapK, hKtop]; exact Subgroup.map_top_of_surjective f hfsurj
  have hHbarNormal : Hbar.Normal := Subgroup.NormalizerCondition.normal_of_coatom Hbar hNC hcoatom
  haveI := hHbarNormal
  have hHnormal : H.Normal := by rw [← hcomapHbar]; exact hHbarNormal.comap f
  refine ⟨hHnormal, ?_⟩
  have hkerle : f.ker ≤ H := by rw [hker]; exact hNH
  have hmapidx : (Subgroup.map f H).index = H.index := H.index_map_eq hfsurj hkerle
  have hindexeq : H.index = Hbar.index := by rw [hHbardef]; exact hmapidx.symm
  rw [hindexeq]
  haveI hQnt : Nontrivial ((G ⧸ H.normalCore) ⧸ Hbar) :=
    QuotientGroup.nontrivial_iff.mpr hcoatom.1
  haveI hQpgroup : IsPGroup p ((G ⧸ H.normalCore) ⧸ Hbar) := hPgroup.to_quotient Hbar
  set g := QuotientGroup.mk' Hbar with hgdef
  have hgsurj : Function.Surjective g := QuotientGroup.mk'_surjective Hbar
  have hgker : g.ker = Hbar := QuotientGroup.ker_mk' Hbar
  have hsimple : ∀ K : Subgroup ((G ⧸ H.normalCore) ⧸ Hbar), K = ⊥ ∨ K = ⊤ := by
    intro K
    have hHbarK' : Hbar ≤ Subgroup.comap g K := by
      have h1 : g.ker ≤ Subgroup.comap g K := by
        rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
      rwa [hgker] at h1
    have hmapK' : Subgroup.map g (Subgroup.comap g K) = K :=
      Subgroup.map_comap_eq_self_of_surjective hgsurj K
    rcases eq_or_lt_of_le hHbarK' with heq | hlt
    · left
      rw [← hmapK', ← heq, Subgroup.map_eq_bot_iff]
      exact le_of_eq hgker.symm
    · right
      rw [← hmapK', hcoatom.2 (Subgroup.comap g K) hlt]
      exact Subgroup.map_top_of_surjective g hgsurj
  haveI hcenterNt : Nontrivial (Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar)) :=
    hQpgroup.center_nontrivial
  have hcenterTop : Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar) = ⊤ := by
    rcases hsimple (Subgroup.center _) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hcenterNt)
    · exact h
  have hcomm : ∀ a b : ((G ⧸ H.normalCore) ⧸ Hbar), a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center _ := by rw [hcenterTop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  letI : CommGroup ((G ⧸ H.normalCore) ⧸ Hbar) := { mul_comm := hcomm }
  haveI hQsimple : IsSimpleGroup ((G ⧸ H.normalCore) ⧸ Hbar) :=
    ⟨fun K _ => hsimple K⟩
  have hprime : (Nat.card ((G ⧸ H.normalCore) ⧸ Hbar)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn0, hn⟩ := hQpgroup.nontrivial_iff_card.mp hQnt
  have hpdvd : p ∣ Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) := by
    rw [hn]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn0)
  have hpeq : p = Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) :=
    (Nat.prime_dvd_prime_iff_eq Fact.out hprime).mp hpdvd
  rw [Subgroup.index_eq_card]
  exact hpeq.symm


end Workspace.ProofLemmas.ProPMaxOpenFree

/-!
# Finiteness of the Frattini quotient of `Gal(F^{ur,3}/F)`

Finiteness of the Frattini quotient of `G = Gal(F^{ur,3}/F)`, via the Hermite/discriminant bound.

The cited route went through unramified class field theory (the Artin map identifies the maximal
elementary-abelian-`3` quotient of `G = Gal(F^{ur,3}/F)` with `Cl_F ⊗ ℤ/3ℤ`, which is finite because
the class group is).  Artin reciprocity is not in Mathlib, so we take the **Hermite** route instead,
which is entirely Mathlib-supported and gives the same conclusion:

* every maximal proper open subgroup `H ≤ G` is normal of index `3`
  (`ProPMaxOpenFree.maxOpen_normal_index_p`, from pro-`3`-ness);
* by the infinite Galois correspondence (`UnramifiedProPTowerCorrespondence_partA`) the assignment
  `H ↦ fixedFieldOf 3 F H` is injective, and each fixed field is a degree-`3` extension of `F`;
* each such layer is everywhere unramified over `F` (`SublemmaSubextUnramified`), so its relative
  different ideal is trivial and the tower formula gives `|D_E| = |D_F|³`;
* **Hermite's theorem** (`NumberField.finite_of_discr_bdd`) then bounds the number of such fields,
  so there are only finitely many maximal open subgroups;
* hence `Φ(G)` — their intersection — is open, and `G` is compact, so `G/Φ(G)` is finite.
-/

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup
open Workspace.Types.SplittingRamification

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.GalUrFrattiniFinite

open Workspace.ProofLemmas.UnramifiedDiscriminant

/-- **Hermite, relative form.** For a number field `F` there are only finitely many
finite-dimensional intermediate fields of `AlgebraicClosure F / F` whose absolute discriminant is
bounded by `N`. -/
theorem finite_subfields_discr_le (F : Type) [Field F] [NumberField F] (N : ℕ) :
    {E : IntermediateField F (AlgebraicClosure F) | ∃ _ : FiniteDimensional F ↥E,
        haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
        (NumberField.discr ↥E).natAbs ≤ N}.Finite := by
  haveI : CharZero (AlgebraicClosure F) := charZero_of_injective_algebraMap
    (algebraMap ℚ (AlgebraicClosure F)).injective
  haveI : IsScalarTower ℚ F (AlgebraicClosure F) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hHermite := NumberField.finite_of_discr_bdd (AlgebraicClosure F) N
  set g : IntermediateField F (AlgebraicClosure F) → IntermediateField ℚ (AlgebraicClosure F) :=
    fun E => E.restrictScalars ℚ with hg
  have hginj : Function.Injective g := IntermediateField.restrictScalars_injective ℚ
  refine Set.Finite.of_finite_image ?_ (hginj.injOn)
  refine Set.Finite.subset (hHermite.image Subtype.val) ?_
  rintro _ ⟨E, ⟨hfd, hdisc⟩, rfl⟩
  haveI := hfd
  haveI : NumberField ↥E := NumberField.of_module_finite (K := F) (L := ↥E)
  haveI hfd' : FiniteDimensional ℚ ↥(g E) := by
    show FiniteDimensional ℚ ↥E
    exact Module.Finite.trans (R := ℚ) F ↥E
  refine ⟨⟨g E, hfd'⟩, ?_, rfl⟩
  haveI : NumberField ↥(g E) := inferInstanceAs (NumberField ↥E)
  show |NumberField.discr ↥(g E)| ≤ (N : ℤ)
  have h2 : NumberField.discr ↥(g E) = NumberField.discr ↥E := rfl
  rw [h2, Int.abs_eq_natAbs]
  exact_mod_cast hdisc

/-- The set of maximal proper open subgroups of `Gal(F^{ur,3}/F)` is finite. -/
theorem finite_maximalOpen_galUr (F : Type) [Field F] [NumberField F] :
    {H : Subgroup (galUr 3 F) | IsMaximalOpenSubgroup H}.Finite := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  obtain ⟨hpartA, hinj, _⟩ := UnramifiedProPTowerCorrespondence_partA F
  set ι := IntermediateField.val (maxUnramifiedProPExt 3 F) with hι
  set ff : Subgroup (galUr 3 F) → IntermediateField F (AlgebraicClosure F) :=
    fun H => IntermediateField.map ι (fixedFieldOf 3 F H) with hff
  -- the target finite set
  set N : ℕ := (NumberField.discr F).natAbs ^ 3 with hN
  refine Set.Finite.of_finite_image (f := ff) ?_ ?_
  · refine Set.Finite.subset (finite_subfields_discr_le F N) ?_
    rintro _ ⟨H, hH, rfl⟩
    obtain ⟨hHnorm, hHidx⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H hH
    haveI := hHnorm
    obtain ⟨hgalL, hfdL, hrankL, _⟩ := hpartA H hHnorm hH.1
    haveI := hfdL
    letI : NumberField ↥(fixedFieldOf 3 F H) :=
      NumberField.of_module_finite (K := F) (L := ↥(fixedFieldOf 3 F H))
    -- the F-algebra equivalence onto the image inside `AlgebraicClosure F`
    have e : (fixedFieldOf 3 F H) ≃ₐ[F] ↥(ff H) :=
      IntermediateField.equivMap (fixedFieldOf 3 F H) ι
    haveI hfd'' : FiniteDimensional F ↥(ff H) := LinearEquiv.finiteDimensional e.toLinearEquiv
    letI : NumberField ↥(ff H) := NumberField.of_module_finite (K := F) (L := ↥(ff H))
    refine ⟨hfd'', ?_⟩
    -- discriminants agree
    have hdd : NumberField.discr ↥(ff H) = NumberField.discr ↥(fixedFieldOf 3 F H) :=
      (NumberField.discr_eq_discr_of_ringEquiv _ (e.toRingEquiv)).symm
    -- the layer is everywhere unramified
    have hunr : EverywhereUnramified F ↥(fixedFieldOf 3 F H) :=
      SublemmaSubextUnramified F (fixedFieldOf 3 F H)
    have hdiscr :
        (NumberField.discr ↥(fixedFieldOf 3 F H)).natAbs
          = (NumberField.discr F).natAbs ^ Module.finrank F ↥(fixedFieldOf 3 F H) :=
      natAbs_discr_of_unramified F ↥(fixedFieldOf 3 F H)
        (fun p hp hpp P hP => hunr.1 p hp hpp P hP)
    rw [hdd, hdiscr, hrankL, hHidx, hN]
  · -- injectivity
    intro H₁ h₁ H₂ h₂ heq
    obtain ⟨hn₁, _⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H₁ h₁
    obtain ⟨hn₂, _⟩ :=
      Workspace.ProofLemmas.ProPMaxOpenFree.maxOpen_normal_index_p 3 (galUr 3 F) hpro H₂ h₂
    exact hinj H₁ H₂ hn₁ h₁.1 hn₂ h₂.1
      (IntermediateField.map_injective ι heq)

/-- **The Frattini quotient of `Gal(F^{ur,3}/F)` is finite.** -/
theorem galUrFrattiniQuotientFinite (F : Type) [Field F] [NumberField F] :
    Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) := by
  have hpro : IsProP 3 (galUr 3 F) := GalUrIsProP F
  obtain ⟨_, hcompact, _, _, _⟩ := hpro
  haveI := hcompact
  have hfin := finite_maximalOpen_galUr F
  have hopen : IsOpen ((frattiniOpen (galUr 3 F) : Subgroup (galUr 3 F)) : Set (galUr 3 F)) := by
    rw [frattiniOpen, Subgroup.coe_sInf]
    exact hfin.isOpen_biInter (fun H hH => hH.1)
  exact Subgroup.quotient_finite_of_isOpen _ hopen

end Workspace.ProofLemmas.GalUrFrattiniFinite

-- Cited from: unramified class field theory. For a number field F, the Artin reciprocity map of
-- the maximal everywhere-unramified abelian extension induces an isomorphism of the
-- abelianized Galois group Gal(F^{ur}/F)^{ab} with the ideal class group Cl_F (Hilbert class
-- field theory), and passing to the 3-part gives Gal(F^{ur,3}/F)^{ab}/3 ≅ Cl_F ⊗ Z/3Z. The
-- Frattini quotient galUr 3 F / Φ(galUr 3 F) of the pro-3 group G = Gal(F^{ur,3}/F) is the maximal
-- elementary-abelian-3 quotient of G, hence a quotient of G^{ab}/3 ≅ Cl_F ⊗ Z/3Z; since the class
-- group Cl_F is finite (Minkowski / NumberField.instFintypeClassGroup in Mathlib), the Frattini
-- quotient is finite. See: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd
-- ed., Springer, 2008, Ch. X (unramified extensions and class groups); H. Koch, Galois Theory of
-- p-Extensions, Springer, 2002, §11 (Golod–Shafarevich, generator rank of the class-field tower).
--
-- Paper label: [NSW08, Ch X] / [Koch §11] (Artin-map bridge, background to Prop A.10)
--
-- Classically (unramified class field theory) this follows from the Artin reciprocity
-- correspondence between the Frattini quotient of the unramified pro-3 Galois group and the 3-part
-- of the class group, which is not currently a Mathlib lemma: the Artin map gives
-- G^{ab}/3 ≅ Cl_F ⊗ Z/3Z, and Cl_F is finite via class-group finiteness
-- (NumberField.instFintypeClassGroup), so the Frattini quotient is finite.
--
-- NL statement: For every number field F, the topological Frattini quotient of the Galois group
-- G = galUr 3 F of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F is finite:
-- Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)). Equivalently, the maximal elementary-abelian-3
-- quotient of G is finite, which by the unramified Artin map is a quotient of Cl_F ⊗ Z/3Z and hence
-- finite because the class group is finite.
--
-- The Artin-reciprocity route is not available in Mathlib; the proof instead uses the **Hermite**
-- route, which reaches the statement from Mathlib alone:
--   * every maximal proper open subgroup of `G = galUr 3 F` is normal of index 3 (pro-3-ness);
--   * `H ↦ fixedFieldOf 3 F H` is injective on them (infinite Galois correspondence, the already
--     proved `UnramifiedProPTowerCorrespondence_partA`);
--   * each such fixed field is a degree-3 everywhere-unramified extension of `F`
--     (`SublemmaSubextUnramified`), so its relative different ideal is trivial and the
--     different/discriminant tower formula gives `|D_E| = |D_F|³`;
--   * **Hermite's theorem** `NumberField.finite_of_discr_bdd` bounds the number of number fields of
--     bounded discriminant, so there are finitely many maximal open subgroups;
--   * therefore `Φ(G)` is open (a finite intersection of open subgroups) and `G` is compact, so
--     `G ⧸ Φ(G)` is finite.
-- The proof lives in `Workspace.ProofLemmas.GalUrFrattiniFinite`.




open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

/-- For a number field `F`, the topological Frattini quotient of `G = galUr 3 F` (the Galois group
of the maximal everywhere-unramified pro-`3` extension `F^{ur,3}/F`) is finite.

Proved from Mathlib via Hermite's finiteness theorem for number fields of bounded discriminant — see
`Workspace.ProofLemmas.GalUrFrattiniFinite`. -/
theorem GalUrFrattiniQuotientFinite :
    ∀ (F : Type) [Field F] [NumberField F],
      Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) :=
  fun F _ _ => Workspace.ProofLemmas.GalUrFrattiniFinite.galUrFrattiniQuotientFinite F

-- Cited from: Neukirch, J., Schmidt, A., Wingberg, K. (2008). Cohomology of Number Fields, 2nd ed., Grundlehren der math. Wissenschaften 323, Springer. Chapter X, Section 10 (Galois groups of maximal unramified pro-p extensions of number fields are topologically finitely generated). See also Koch, H. (2002), Galois Theory of p-Extensions.
-- Paper label: [NSW08, Ch X, Section 10] (background to Prop A.10)
--
-- The only content admitted here is `GalUrFrattiniQuotientFinite`
--   GalUrFrattiniQuotientFinite : Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F))
-- (the unramified class-field-theory bridge: by the Artin map the Frattini quotient of Gal(F^{ur,3}/F)
-- is a quotient of Cl_F ⊗ Z/3Z, hence finite because the class group is finite; the Artin-map
-- correspondence itself is not currently in Mathlib).
--
-- Proof structure (reverse Burnside/Nakayama):
--   * `maxOpen_normal_index_p`: in a pro-p group every maximal proper open subgroup is normal of
--     index p.
--   * `frattini_normal` / `commutator_in_frattini` / `pow_in_frattini` / `frattini_quot_comm` /
--     `frattini_quot_expp`: the Frattini quotient G/Φ(G) is elementary abelian of exponent p, from the
--     above.
--   * `frattini_quot_card`: given `Finite (G/Φ(G))`, G/Φ(G) has order p^d.
--   * `nakayama_topfingen`: lift an F_p-basis of G/Φ(G) to a finset S ⊆ G (via
--     `ProPTopologicalNakayamaAux.exists_gen_finset`); the closed subgroup ⟨S⟩‾ maps onto G/Φ(G), and
--     if proper it would sit in a maximal open M ⊇ Φ(G) (the compactness step
--     `ProPTopologicalNakayamaAux.exists_maximalOpen_ge`) whose image in G/Φ(G) is a proper subgroup
--     containing all generators — contradiction. Hence S topologically generates G.
--   * Pro-3-ness of G = galUr 3 F is the lemma `Workspace.ProofLemmas.GalUrIsProP`.
--
-- NL statement: For every totally real cubic number field F, the Galois group galUr 3 F of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F is topologically finitely generated: TopFinitelyGenerated (galUr 3 F), i.e. some finite subset of galUr 3 F topologically generates it.






open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000

namespace GalUrTopFinGenAux

/-- In a pro-`p` group `G`, every maximal proper open subgroup `H` is normal of index `p`. -/
theorem maxOpen_normal_index_p (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (H : Subgroup G) (hH : IsMaximalOpenSubgroup H) :
    H.Normal ∧ H.index = p := by
  obtain ⟨_, hcompact, _hT2, _hTD, hPindex⟩ := hpro
  haveI := hcompact
  obtain ⟨hHopen, hHne, hHmax⟩ := hH
  haveI hHfq : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHopen
  haveI hHfi : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hNH : H.normalCore ≤ H := Subgroup.normalCore_le H
  have hHclosed : IsClosed (H : Set G) := Subgroup.isClosed_of_isOpen H hHopen
  have hNclosed : IsClosed (H.normalCore : Set G) := Subgroup.normalCore_isClosed H hHclosed
  have hNopen : IsOpen (H.normalCore : Set G) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex H.normalCore hNclosed
  obtain ⟨k, hk⟩ := hPindex H.normalCore inferInstance hNopen
  haveI hPfin : Finite (G ⧸ H.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  have hcardP : Nat.card (G ⧸ H.normalCore) = p ^ k := by
    rw [← Subgroup.index_eq_card]; exact hk
  haveI hPgroup : IsPGroup p (G ⧸ H.normalCore) := IsPGroup.of_card hcardP
  haveI hPnil : Group.IsNilpotent (G ⧸ H.normalCore) := hPgroup.isNilpotent
  have hNC : NormalizerCondition (G ⧸ H.normalCore) := normalizerCondition_of_isNilpotent
  set f := QuotientGroup.mk' H.normalCore with hfdef
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective H.normalCore
  have hker : f.ker = H.normalCore := QuotientGroup.ker_mk' H.normalCore
  set Hbar := Subgroup.map f H with hHbardef
  have hcomapHbar : Subgroup.comap f Hbar = H := by
    rw [hHbardef, Subgroup.comap_map_eq, hker]; exact sup_eq_left.mpr hNH
  have hcoatom : IsCoatom Hbar := by
    constructor
    · intro htop
      apply hHne
      have hc : Subgroup.comap f Hbar = Subgroup.comap f ⊤ := by rw [htop]
      rw [hcomapHbar, Subgroup.comap_top] at hc
      exact hc
    · intro Kbar hKbar
      have hNK : H.normalCore ≤ Subgroup.comap f Kbar := by
        have h1 : f.ker ≤ Subgroup.comap f Kbar := by
          rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
        rwa [hker] at h1
      have hKopen : IsOpen ((Subgroup.comap f Kbar) : Set G) := Subgroup.isOpen_mono hNK hNopen
      have hHK : H ≤ Subgroup.comap f Kbar :=
        Subgroup.map_le_iff_le_comap.mp (by rw [← hHbardef]; exact hKbar.le)
      have hmapK : Subgroup.map f (Subgroup.comap f Kbar) = Kbar :=
        Subgroup.map_comap_eq_self_of_surjective hfsurj Kbar
      rcases hHmax (Subgroup.comap f Kbar) hKopen hHK with hKH | hKtop
      · have hcontra : Kbar = Hbar := by rw [← hmapK, hKH, ← hHbardef]
        exact absurd hcontra.symm (ne_of_lt hKbar)
      · rw [← hmapK, hKtop]; exact Subgroup.map_top_of_surjective f hfsurj
  have hHbarNormal : Hbar.Normal := Subgroup.NormalizerCondition.normal_of_coatom Hbar hNC hcoatom
  haveI := hHbarNormal
  have hHnormal : H.Normal := by rw [← hcomapHbar]; exact hHbarNormal.comap f
  refine ⟨hHnormal, ?_⟩
  have hkerle : f.ker ≤ H := by rw [hker]; exact hNH
  have hmapidx : (Subgroup.map f H).index = H.index := H.index_map_eq hfsurj hkerle
  have hindexeq : H.index = Hbar.index := by rw [hHbardef]; exact hmapidx.symm
  rw [hindexeq]
  haveI hQnt : Nontrivial ((G ⧸ H.normalCore) ⧸ Hbar) :=
    QuotientGroup.nontrivial_iff.mpr hcoatom.1
  haveI hQpgroup : IsPGroup p ((G ⧸ H.normalCore) ⧸ Hbar) := hPgroup.to_quotient Hbar
  set g := QuotientGroup.mk' Hbar with hgdef
  have hgsurj : Function.Surjective g := QuotientGroup.mk'_surjective Hbar
  have hgker : g.ker = Hbar := QuotientGroup.ker_mk' Hbar
  have hsimple : ∀ K : Subgroup ((G ⧸ H.normalCore) ⧸ Hbar), K = ⊥ ∨ K = ⊤ := by
    intro K
    have hHbarK' : Hbar ≤ Subgroup.comap g K := by
      have h1 : g.ker ≤ Subgroup.comap g K := by
        rw [← MonoidHom.comap_bot]; exact Subgroup.comap_mono bot_le
      rwa [hgker] at h1
    have hmapK' : Subgroup.map g (Subgroup.comap g K) = K :=
      Subgroup.map_comap_eq_self_of_surjective hgsurj K
    rcases eq_or_lt_of_le hHbarK' with heq | hlt
    · left
      rw [← hmapK', ← heq, Subgroup.map_eq_bot_iff]
      exact le_of_eq hgker.symm
    · right
      rw [← hmapK', hcoatom.2 (Subgroup.comap g K) hlt]
      exact Subgroup.map_top_of_surjective g hgsurj
  haveI hcenterNt : Nontrivial (Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar)) :=
    hQpgroup.center_nontrivial
  have hcenterTop : Subgroup.center ((G ⧸ H.normalCore) ⧸ Hbar) = ⊤ := by
    rcases hsimple (Subgroup.center _) with h | h
    · exact absurd h ((Subgroup.nontrivial_iff_ne_bot _).mp hcenterNt)
    · exact h
  have hcomm : ∀ a b : ((G ⧸ H.normalCore) ⧸ Hbar), a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center _ := by rw [hcenterTop]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  letI : CommGroup ((G ⧸ H.normalCore) ⧸ Hbar) := { mul_comm := hcomm }
  haveI hQsimple : IsSimpleGroup ((G ⧸ H.normalCore) ⧸ Hbar) :=
    ⟨fun K _ => hsimple K⟩
  have hprime : (Nat.card ((G ⧸ H.normalCore) ⧸ Hbar)).Prime := IsSimpleGroup.prime_card
  obtain ⟨n, hn0, hn⟩ := hQpgroup.nontrivial_iff_card.mp hQnt
  have hpdvd : p ∣ Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) := by
    rw [hn]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hn0)
  have hpeq : p = Nat.card ((G ⧸ H.normalCore) ⧸ Hbar) :=
    (Nat.prime_dvd_prime_iff_eq Fact.out hprime).mp hpdvd
  rw [Subgroup.index_eq_card]
  exact hpeq.symm

/-- `Φ(G)` is normal (from the hfg-free `maxOpen_normal_index_p`). -/
theorem frattini_normal (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) :
    (frattiniOpen G).Normal := by
  rw [frattiniOpen]
  constructor
  intro n hn g
  rw [Subgroup.mem_sInf] at hn ⊢
  intro H hH
  obtain ⟨hnorm, _⟩ := maxOpen_normal_index_p p G hpro H hH
  haveI := hnorm
  exact hnorm.conj_mem n (hn H hH) g

/-- Every commutator lies in `Φ(G)`. -/
theorem commutator_in_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) (x y : G) :
    x * y * x⁻¹ * y⁻¹ ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := maxOpen_normal_index_p p G hpro H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  haveI : IsCyclic (G ⧸ H) := isCyclic_of_prime_card hcard
  haveI : IsMulCommutative (G ⧸ H) := IsCyclic.isMulCommutative
  rw [← QuotientGroup.eq_one_iff]
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  rw [mul_comm' (x : G ⧸ H) (y : G ⧸ H)]
  group

/-- Every `p`-th power lies in `Φ(G)`. -/
theorem pow_in_frattini (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G) (x : G) :
    x ^ p ∈ frattiniOpen G := by
  rw [frattiniOpen, Subgroup.mem_sInf]
  intro H hH
  obtain ⟨hnorm, hidx⟩ := maxOpen_normal_index_p p G hpro H hH
  haveI := hnorm
  have hcard : Nat.card (G ⧸ H) = p := hidx
  haveI : Finite (G ⧸ H) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (Fact.out : p.Prime).pos.ne')
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hcard]
  exact pow_card_eq_one'

/-- `G/Φ(G)` is abelian. -/
theorem frattini_quot_comm (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    [(frattiniOpen G).Normal] :
    ∀ a b : G ⧸ frattiniOpen G, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on with
  | _ x =>
    induction b using QuotientGroup.induction_on with
    | _ y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      simpa [mul_assoc] using commutator_in_frattini p G hpro y⁻¹ x⁻¹

/-- `G/Φ(G)` has exponent dividing `p`. -/
theorem frattini_quot_expp (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    [(frattiniOpen G).Normal] :
    ∀ q : G ⧸ frattiniOpen G, q ^ p = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_in_frattini p G hpro x

/-- `G/Φ(G)` is a finite elementary abelian `p`-group: its cardinality is `p^d`, using finiteness of
the Frattini quotient. -/
theorem frattini_quot_card (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfin : Finite (G ⧸ frattiniOpen G)) :
    ∃ d : ℕ, Nat.card (G ⧸ frattiniOpen G) = p ^ d := by
  haveI : (frattiniOpen G).Normal := frattini_normal p G hpro
  have hcomm := frattini_quot_comm p G hpro
  have hpow_all := frattini_quot_expp p G hpro
  haveI := hfin
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := hcomm }
  have hexp : ∀ a : Additive (G ⧸ frattiniOpen G), (p : ℕ) • a = 0 := by
    intro a
    have h1 : (Additive.toMul a) ^ p = 1 := hpow_all (Additive.toMul a)
    simpa [← ofMul_pow] using congrArg Additive.ofMul h1
  letI : Module (ZMod p) (Additive (G ⧸ frattiniOpen G)) := AddCommGroup.zmodModule hexp
  haveI : Fintype (G ⧸ frattiniOpen G) := Fintype.ofFinite _
  haveI : Fintype (Additive (G ⧸ frattiniOpen G)) := Fintype.ofFinite _
  refine ⟨Module.finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)), ?_⟩
  have hcard := @Module.card_eq_pow_finrank (ZMod p) (Additive (G ⧸ frattiniOpen G)) _ _ _ _ _
  rw [ZMod.card, ← Nat.card_eq_fintype_card] at hcard
  exact hcard

/-- **Reverse Nakayama / Burnside.** A pro-`p` group `G` whose topological Frattini
quotient `G/Φ(G)` is finite is topologically finitely generated. Proof: `G/Φ(G)` is a finite
elementary abelian `p`-group of order `p^d`; lift an `𝔽_p`-basis to a finset `S ⊆ G` of size `≤ d`;
the closed subgroup `⟨S⟩‾` surjects onto `G/Φ(G)`, and if it were proper it would sit inside a
maximal open `M ⊇ Φ(G)` whose image in `G/Φ(G)` is a proper subgroup containing all generators —
contradiction. -/
theorem nakayama_topfingen (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (hpro : IsProP p G)
    (hfin : Finite (G ⧸ frattiniOpen G)) :
    TopFinitelyGenerated G := by
  classical
  haveI hN : (frattiniOpen G).Normal := frattini_normal p G hpro
  haveI hQfin : Finite (G ⧸ frattiniOpen G) := hfin
  letI : CommGroup (G ⧸ frattiniOpen G) := { mul_comm := frattini_quot_comm p G hpro }
  have hexp := frattini_quot_expp p G hpro
  obtain ⟨d, hd⟩ := frattini_quot_card p G hpro hfin
  obtain ⟨T, hTcard, hTgen⟩ :=
    ProPTopologicalNakayamaAux.exists_gen_finset p (G ⧸ frattiniOpen G) hexp d hd
  set π : G →* (G ⧸ frattiniOpen G) := QuotientGroup.mk' (frattiniOpen G) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set sec : (G ⧸ frattiniOpen G) → G := Function.surjInv hπsurj with hsec
  have hsecspec : ∀ t, π (sec t) = t := fun t => Function.surjInv_eq hπsurj t
  set S : Finset G := T.image sec with hS
  refine ⟨S, ?_⟩
  have hHtop : (Subgroup.closure (↑S : Set G)).topologicalClosure = ⊤ := by
    by_contra hne
    obtain ⟨M, hMmax, hHM⟩ := ProPTopologicalNakayamaAux.exists_maximalOpen_ge p G hpro
      ((Subgroup.closure (↑S : Set G)).topologicalClosure)
      (Subgroup.isClosed_topologicalClosure _) hne
    have hΦM : frattiniOpen G ≤ M := by rw [frattiniOpen]; exact sInf_le hMmax
    have hcomap : Subgroup.comap π (Subgroup.map π M) = M := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hΦM
    have hMbarne : Subgroup.map π M ≠ ⊤ := by
      intro htop
      apply hMmax.2.1
      have hc : Subgroup.comap π (Subgroup.map π M) = Subgroup.comap π ⊤ := by rw [htop]
      rwa [hcomap, Subgroup.comap_top] at hc
    have hTM : ∀ t ∈ T, t ∈ Subgroup.map π M := by
      intro t ht
      have hsecmem : sec t ∈ (Subgroup.closure (↑S : Set G)).topologicalClosure := by
        apply Subgroup.le_topologicalClosure
        apply Subgroup.subset_closure
        rw [hS, Finset.coe_image]
        exact ⟨t, ht, rfl⟩
      have hmemM : sec t ∈ M := hHM hsecmem
      rw [← hsecspec t]
      exact Subgroup.mem_map_of_mem π hmemM
    have hle : (⊤ : Subgroup (G ⧸ frattiniOpen G)) ≤ Subgroup.map π M := by
      rw [← hTgen, Subgroup.closure_le]
      intro t ht
      exact hTM t (Finset.mem_coe.mp ht)
    exact hMbarne (top_le_iff.mp hle)
  show _root_.closure ((Subgroup.closure (↑S : Set G) : Subgroup G) : Set G) = Set.univ
  rw [← Subgroup.topologicalClosure_coe, hHtop, Subgroup.coe_top]

end GalUrTopFinGenAux

open GalUrTopFinGenAux in
/-- For a totally real cubic number field `F`, the Galois group `galUr 3 F` of the maximal
everywhere-unramified pro-`3` extension is topologically finitely generated. -/
theorem GalUrTopFinGen :
    ∀ (F : Type) [Field F] [NumberField F],
      NumberField.IsTotallyReal F → Module.finrank ℚ F = 3 →
        TopFinitelyGenerated (galUr 3 F) := by
  intro F _ _ _ _
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact nakayama_topfingen 3 (galUr 3 F) (GalUrIsProP F) (GalUrFrattiniQuotientFinite F)

open scoped NumberField
open Workspace.Types.PlanarCounting
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.MinkowskiWindow
open Workspace.Types.UnramifiedProPExtension

theorem Prop38FieldConstruction :
    ∃ C : ℝ, 0 < C ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ L₀ : ℕ, 0 < L₀ ∧
      ∀ ℓ : ℕ, L₀ ≤ ℓ →
        ∃ (F : Type) (_ : Field F) (_ : NumberField F)
          (q : Fin ((ℓ - 1) ^ 2 / 100) → ℕ)
          (Fj : ℕ → IntermediateField F (AlgebraicClosure F))
          (H : ℝ),
          -- (P1)
          (NumberField.IsTotallyReal F ∧ IsGalois ℚ F ∧ Module.finrank ℚ F = 3 ∧
            (¬ ∃ x : F, IsPrimitiveRoot x 3) ∧
            Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ)) ∧
          -- (P2): tower base, strictly increasing, degrees → ∞
          (Fj 0 = ⊥ ∧ StrictMono Fj ∧
            Filter.Tendsto (fun j => Module.finrank ℚ ↥(Fj j)) Filter.atTop Filter.atTop) ∧
          -- primes: distinct and prime
          (Function.Injective q ∧ ∀ b, (q b).Prime) ∧
          -- per-layer properties (P2 layer data, P3, P4, P5 body)
          (∀ j, ∃ (_ : FiniteDimensional F ↥(Fj j)) (_ : NumberField ↥(Fj j)),
            IsGalois F ↥(Fj j) ∧
            EverywhereUnramified F ↥(Fj j) ∧
            IsPGroup 3 (↥(Fj j) ≃ₐ[F] ↥(Fj j)) ∧
            NumberField.IsTotallyReal ↥(Fj j) ∧
            rootDiscriminant ↥(Fj j) = rootDiscriminant F ∧
            (∀ b, q b % 4 = 1 ∧ SplitsCompletelyRat (q b) ↥(Fj j)) ∧
            (∀ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra ↥(Fj j) K),
              IsAdjoinI ↥(Fj j) K →
                rootDiscriminant K ≤ 2 * rootDiscriminant F ∧
                (classNumber K : ℝ) ≤ H ^ (Module.finrank ℚ ↥(Fj j)))) ∧
          -- (P5) tail: bound on H_ℓ
          (0 < H ∧ Real.log H ≤ C' * (ℓ : ℝ) * Real.log (ℓ : ℝ)) ∧
          -- (P6)
          (0 < (((ℓ - 1) ^ 2 / 100 : ℕ) : ℝ) * Real.log 2 - Real.log H) := by
  -- ===== Step 1: absolute constants =====
  obtain ⟨Cclass, hCclass_pos, hClass⟩ := ClassNumberRootDiscriminantBound
  obtain ⟨C_D, hC_D_pos, ℓ₀_D, hD_body⟩ := BaseRootDiscriminantBound
  obtain ⟨C', hC'_pos, L₀_I, hL₀_I_pos, hI_body⟩ :=
    FieldConstructionNumericBounds Cclass hCclass_pos C_D hC_D_pos
  obtain ⟨L₀_E, hE⟩ := FrobeniusKillingInfiniteQuotient
  refine ⟨C_D, hC_D_pos, C', hC'_pos, max (max (max ℓ₀_D L₀_I) L₀_E) 11, ?_, ?_⟩
  · have h11 : (11 : ℕ) ≤ max (max (max ℓ₀_D L₀_I) L₀_E) 11 := le_max_right _ _
    omega
  intro ℓ hℓ
  -- threshold clauses
  have h1 : max (max ℓ₀_D L₀_I) L₀_E ≤ ℓ := le_trans (le_max_left _ 11) hℓ
  have h2 : max ℓ₀_D L₀_I ≤ ℓ := le_trans (le_max_left _ L₀_E) h1
  have hℓ0D : ℓ₀_D ≤ ℓ := le_trans (le_max_left _ L₀_I) h2
  have hL0I : L₀_I ≤ ℓ := le_trans (le_max_right ℓ₀_D _) h2
  have hL0E : L₀_E ≤ ℓ := le_trans (le_max_right _ L₀_E) h1
  have hℓ11 : 11 ≤ ℓ := le_trans (le_max_right _ 11) hℓ
  have hℓ2 : 2 ≤ ℓ := by omega
  have ht_pos : 0 < (ℓ - 1) ^ 2 / 100 := by
    have h10 : 10 ≤ ℓ - 1 := by omega
    have : 100 ≤ (ℓ - 1) ^ 2 := by nlinarith
    omega
  -- ===== Step 2: base field package (Group A) =====
  obtain ⟨r, hr_mono, hp, hm, hskip, D, hD_prod, chi, hchi_ord, hchi_cond,
      Fbase, Mbase, hF_eq, hM_eq, hFM_le, nfF, nfM, algFM,
      hst, hTR, hGal, hdeg, hno, hUnr, hGalM_iso, hDF, M', hM'fin, hM'iso⟩ :=
    Prop38BaseFieldConstruction ℓ hℓ2
  haveI : NumberField (↥Fbase) := nfF
  -- pro-3, top-fin-gen
  have hpro : IsProP 3 (galUr 3 (↥Fbase)) := GalUrIsProP (↥Fbase)
  have hfg : TopFinitelyGenerated (galUr 3 (↥Fbase)) := GalUrTopFinGen (↥Fbase) hTR hdeg
  -- ===== Step 3: generator lower bound (Group C) =====
  obtain ⟨φ⟩ := hM'iso
  have hd_lb : ((ℓ - 1 : ℕ) : ℕ∞) ≤ dRank (galUr 3 (↥Fbase)) :=
    GalUrGeneratorLowerBound (↥Fbase) hTR hGal hdeg ℓ hℓ2 M' hM'fin φ
  -- ===== Step 5.3: split primes (Prop36) =====
  obtain ⟨q, hqInj, hqPrimeNotT, hqRest⟩ :=
    Prop36ChebotarevApplication (↥Fbase) hfg ((ℓ - 1) ^ 2 / 100) ht_pos ∅
  have hqSplitF : ∀ b, SplitsCompletelyRat (q b) (↥Fbase) := fun b => (hqRest b).2.1
  -- Frobenius section σ over the (prime b, prime v | q b) index
  have hqRest2 : ∀ w : (Σ b : Fin ((ℓ - 1) ^ 2 / 100),
        {v : Ideal (𝓞 (↥Fbase)) //
          v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 (↥Fbase))}),
      ∃ s : galUr 3 (↥Fbase),
        Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 (↥Fbase) s
            (w.2 : Ideal (𝓞 (↥Fbase))) ∧
          s ∈ frattiniOpen (galUr 3 (↥Fbase)) :=
    fun w => (hqRest w.1).2.2 (w.2 : Ideal (𝓞 (↥Fbase))) w.2.2
  choose σ hσfrob hσfrat using hqRest2
  -- N := closed normal closure of the killed Frobenius family
  set N := (Subgroup.normalClosure (Set.range σ)).topologicalClosure with hN_def
  haveI hNnorm : N.Normal := by
    rw [hN_def]
    exact Subgroup.is_normal_topologicalClosure (Subgroup.normalClosure (Set.range σ))
  have hNclosed : IsClosed (N : Set (galUr 3 (↥Fbase))) := by
    rw [hN_def]; exact Subgroup.isClosed_topologicalClosure _
  -- ===== Steps 6-7: infinite quotient (Group E) =====
  obtain ⟨hNontriv, hInf, hFGbar, hProPbar, hdbar, hrbar⟩ :=
    hE (↥Fbase) hTR hGal hdeg hno hpro hfg ℓ hL0E hd_lb q hqInj hqSplitF σ hσfrob hσfrat N hN_def
  -- ===== Step 8: descending chain (correspondence (b)) =====
  obtain ⟨_, _, _, hCorrB⟩ := UnramifiedProPTowerCorrespondence (↥Fbase)
  obtain ⟨Hchain, hHnorm, hHopen, hNH, hH0, hHanti, hHidxpos, hHidxtop⟩ :=
    hCorrB N hNnorm hNclosed hInf hFGbar hProPbar
  -- ===== Step 9: tower fields (Group F) =====
  obtain ⟨Fj, hFjeq, hFj0, hFjmono, hFjtop⟩ :=
    UnramifiedProPTowerFields (↥Fbase) N hNnorm hNclosed hInf hFGbar hProPbar
      Hchain hHnorm hHopen hNH hH0 hHanti hHidxpos hHidxtop
  -- Frobenius reps lie in N (needed for Group G)
  have hq_G : ∀ b, (q b).Prime ∧ q b % 4 = 1 ∧ SplitsCompletelyRat (q b) (↥Fbase) ∧
      ∀ v ∈ Ideal.primesOver (Ideal.span {(q b : ℤ)}) (𝓞 (↥Fbase)),
        ∃ s : galUr 3 (↥Fbase),
          Workspace.Types.UnramifiedProPExtension.IsFrobeniusRepAt 3 (↥Fbase) s v ∧ s ∈ N := by
    intro b
    refine ⟨(hqPrimeNotT b).1, (hqRest b).1, (hqRest b).2.1, ?_⟩
    intro v hv
    refine ⟨σ ⟨b, ⟨v, hv⟩⟩, hσfrob ⟨b, ⟨v, hv⟩⟩, ?_⟩
    rw [hN_def]
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨⟨b, ⟨v, hv⟩⟩, rfl⟩)
  -- ===== Step 10: per-layer package (Group G) =====
  have hlayer := TowerLayerProperties (↥Fbase) hTR hGal hdeg N Hchain hHopen hHnorm hNH Fj hFjeq
    ((ℓ - 1) ^ 2 / 100) q hq_G
  -- ===== Step 4: root-discriminant bound (Group D) via the Nat.nth bridge =====
  have hbridge : ∀ i : Fin ℓ, (r i : ℕ) = Nat.nth (fun n => n.Prime ∧ n % 3 = 1) (i : ℕ) := by
    intro i
    have hr_inj : Function.Injective r := hr_mono.injective
    have hri_inj : Function.Injective (fun a : Fin ℓ => (r a : ℕ)) :=
      fun a b h => hr_inj (PNat.coe_injective h)
    have hpi : (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ) := ⟨hp i, hm i⟩
    have hcount : Nat.count (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ) = (i : ℕ) := by
      rw [Nat.count_eq_card_filter_range]
      have hset : {x ∈ Finset.range (r i : ℕ) | (fun n => n.Prime ∧ n % 3 = 1) x}
          = (Finset.Iio i).image (fun a : Fin ℓ => (r a : ℕ)) := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_Iio]
        constructor
        · rintro ⟨hylt, hyp, hym⟩
          by_contra hnex
          push_neg at hnex
          have hnoteq : ¬ ∃ k, (r k : ℕ) = y := by
            rintro ⟨k, hk⟩
            have hlt : (r k : ℕ) < (r i : ℕ) := by rw [hk]; exact hylt
            have hki : k < i := hr_mono.lt_iff_lt.mp ((PNat.coe_lt_coe _ _).mp hlt)
            exact hnex k hki hk
          have := hskip y hyp hym hnoteq i
          omega
        · rintro ⟨a, hai, hay⟩
          subst hay
          exact ⟨(PNat.coe_lt_coe _ _).mpr (hr_mono hai), hp a, hm a⟩
      rw [hset, Finset.card_image_of_injective _ hri_inj, Fin.card_Iio]
    calc (r i : ℕ)
        = Nat.nth (fun n => n.Prime ∧ n % 3 = 1)
            (Nat.count (fun n => n.Prime ∧ n % 3 = 1) (r i : ℕ)) := (Nat.nth_count hpi).symm
      _ = Nat.nth (fun n => n.Prime ∧ n % 3 = 1) (i : ℕ) := by rw [hcount]
  have hDeq : (D : ℕ) = ∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i := by
    rw [hD_prod,
      ← Fin.prod_univ_eq_prod_range (fun k => Nat.nth (fun n => n.Prime ∧ n % 3 = 1) k) ℓ]
    exact Finset.prod_congr rfl (fun i _ => hbridge i)
  have hDF_prod : (NumberField.discr (↥Fbase)).natAbs
      = (∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i) ^ 2 := by
    rw [hDF, hDeq]
  obtain ⟨_, hP1_rd⟩ := hD_body ℓ hℓ0D (↥Fbase) hTR hdeg hDF_prod
  -- ===== Step 11-12: P5 tail + P6 (Group I) =====
  obtain ⟨hIpos, hIlog, hIP6⟩ := hI_body ℓ hL0I (↥Fbase) hTR hdeg hP1_rd
  -- ===== Step 13: assemble =====
  refine ⟨↥Fbase, inferInstance, nfF, q, Fj,
    (2 * rootDiscriminant (↥Fbase)) ^ (2 * Cclass), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hTR, hGal, hdeg, hno, hP1_rd⟩
  · exact ⟨hFj0, hFjmono, hFjtop⟩
  · exact ⟨hqInj, fun b => (hqPrimeNotT b).1⟩
  · intro j
    obtain ⟨instFD, instNF, hGalj, hUnrj, hPGj, hTRj, hrdj, hsplitj⟩ := hlayer j
    haveI := instNF
    haveI : NumberField.IsTotallyReal (↥Fbase) := hTR
    haveI : NumberField.IsTotallyReal (↥(Fj j)) := hTRj
    obtain ⟨_, hKbound⟩ :=
      CMModelDiscriminantClassNumberBounds (↥Fbase) (↥(Fj j)) hrdj Cclass hCclass_pos hClass
        ((2 * rootDiscriminant (↥Fbase)) ^ (2 * Cclass)) rfl
    exact ⟨instFD, instNF, hGalj, hUnrj, hPGj, hTRj, hrdj, hsplitj, hKbound⟩
  · exact ⟨hIpos, hIlog⟩
  · exact hIP6

open Polynomial
open scoped NumberField ComplexConjugate
open Workspace.Types.CMAdjoinI

theorem SublemmaCMModelExists (L : Type) [Field L] [NumberField L]
    [NumberField.IsTotallyReal L] :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K), IsAdjoinI L K := by
  -- -1 is not a square in L (L is totally real)
  have hnsq : ∀ a : L, a ^ 2 ≠ -1 := by
    intro a ha2
    obtain ⟨φ⟩ := (inferInstance : Nonempty (L →+* ℂ))
    have hreal : NumberField.ComplexEmbedding.IsReal φ :=
      NumberField.IsTotallyReal.complexEmbedding_isReal φ
    have hconj : conj (φ a) = φ a := by
      have h1 : NumberField.ComplexEmbedding.conjugate φ = φ :=
        NumberField.ComplexEmbedding.isReal_iff.mp hreal
      have h2 := RingHom.congr_fun h1 a
      rwa [NumberField.ComplexEmbedding.conjugate_coe_eq] at h2
    have hsq2 : (φ a) ^ 2 = -1 := by rw [← map_pow, ha2, map_neg, map_one]
    have key : ((Complex.normSq (φ a) : ℝ) : ℂ) = -1 := by
      rw [← Complex.mul_conj, hconj, ← pow_two]; exact hsq2
    have hcast : Complex.normSq (φ a) = -1 := by exact_mod_cast key
    have hnn := Complex.normSq_nonneg (φ a)
    linarith
  -- X^2 + 1 is irreducible over L
  have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
  have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
  have hirr : Irreducible (X ^ 2 + 1 : L[X]) := by
    by_contra hcon
    rw [Polynomial.Monic.not_irreducible_iff_exists_add_mul_eq_coeff hmonic hnd] at hcon
    obtain ⟨c₁, c₂, hc0, hc1⟩ := hcon
    have hcoeff0 : (X ^ 2 + 1 : L[X]).coeff 0 = 1 := by simp
    have hcoeff1 : (X ^ 2 + 1 : L[X]).coeff 1 = 0 := by simp [Polynomial.coeff_one]
    rw [hcoeff0] at hc0
    rw [hcoeff1] at hc1
    exact hnsq c₁ (by linear_combination c₁ * hc1.symm - hc0.symm)
  -- Construct K = L(i) = AdjoinRoot (X^2+1)
  haveI hfact : Fact (Irreducible (X ^ 2 + 1 : L[X])) := ⟨hirr⟩
  set K := AdjoinRoot (X ^ 2 + 1 : L[X]) with hKdef
  have hne : (X ^ 2 + 1 : L[X]) ≠ 0 := hmonic.ne_zero
  haveI : Module.Finite L K := Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  haveI : NumberField K := NumberField.of_module_finite L K
  refine ⟨K, inferInstance, inferInstance, inferInstance, ?_⟩
  · -- IsAdjoinI L K
    refine ⟨AdjoinRoot.root (X ^ 2 + 1 : L[X]), ?_, ?_⟩
    · -- root ^ 2 = -1
      have h := AdjoinRoot.eval₂_root (X ^ 2 + 1 : L[X])
      simp only [eval₂_add, eval₂_pow, eval₂_X, eval₂_one] at h
      linear_combination h
    · -- IntermediateField.adjoin L {root} = ⊤
      have htop : Algebra.adjoin L {AdjoinRoot.root (X ^ 2 + 1 : L[X])} = ⊤ :=
        AdjoinRoot.adjoinRoot_eq_top
      have hle := IntermediateField.algebra_adjoin_le_adjoin L
        {AdjoinRoot.root (X ^ 2 + 1 : L[X])}
      rw [htop] at hle
      have htopsub : (IntermediateField.adjoin L
          {AdjoinRoot.root (X ^ 2 + 1 : L[X])}).toSubalgebra = ⊤ :=
        top_le_iff.mp hle
      exact (IntermediateField.toSubalgebra_injective (by rw [htopsub]; rfl))



open scoped NumberField
open Workspace.Types.PlanarCounting
open Workspace.Types.SplittingRamification
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Workspace.Types.AdmissibleDatum
open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank
open Workspace.Types.CyclotomicCharacterFields
open Workspace.Types.FrobeniusSplitting
open Workspace.Types.MinkowskiWindow
open Workspace.Types.UnramifiedProPExtension

namespace Workspace.MainTheorem

theorem theorem_1_1_unit_distance :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  obtain ⟨C, hC, C', hC', L₀, hL₀, hmain⟩ := Prop38FieldConstruction
  set ℓ := max L₀ 11 with hℓ_def
  have hℓ : L₀ ≤ ℓ := le_max_left _ _
  have h11 : 11 ≤ ℓ := le_max_right _ _
  have hsq : 100 ≤ (ℓ - 1) ^ 2 := by
    have h10 : 10 ≤ ℓ - 1 := by omega
    calc (100 : ℕ) = 10 ^ 2 := by norm_num
      _ ≤ (ℓ - 1) ^ 2 := Nat.pow_le_pow_left h10 2
  have ht : 0 < (ℓ - 1) ^ 2 / 100 := by omega
  obtain ⟨F, instF, instNF, q, Fj, H, hP1, hP2, hprimes, hlayer, hP5, hP6⟩ := hmain ℓ hℓ
  choose finFj nfFj hbody using hlayer
  have hcm : ∀ j, ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (_ : Algebra (↥(Fj j)) K), IsAdjoinI (↥(Fj j)) K := by
    intro j
    haveI := nfFj j
    haveI : NumberField.IsTotallyReal (↥(Fj j)) := (hbody j).2.2.2.1
    exact SublemmaCMModelExists (↥(Fj j))
  choose Kj fieldKj nfKj algKj hadjKj using hcm
  let data : ℕ → AdmissibleDatum := fun j =>
    { L := ↥(Fj j)
      K := Kj j
      fieldL := inferInstance
      fieldK := fieldKj j
      nfL := nfFj j
      nfK := nfKj j
      trL := (hbody j).2.2.2.1
      algLK := algKj j
      h_adjoin := hadjKj j
      t := (ℓ - 1) ^ 2 / 100
      ht := ht
      q := q
      hq_prime := hprimes.2
      hq_distinct := hprimes.1
      hq_mod4 := fun b => ((hbody j).2.2.2.2.2.1 b).1
      hq_split := fun b => ((hbody j).2.2.2.2.2.1 b).2 }
  have hdeg : Filter.Tendsto (fun j => deg (data j)) Filter.atTop Filter.atTop := hP2.2.2
  have hclass : ∀ j, (classNumber (data j).K : ℝ) ≤ H ^ (deg (data j)) := by
    intro j
    exact ((hbody j).2.2.2.2.2.2 (Kj j) (fieldKj j) (nfKj j) (algKj j) (hadjKj j)).2
  exact Theorem23GeometricCriterion ((ℓ - 1) ^ 2 / 100) ht q data
    (fun j => rfl) (fun j => HEq.rfl) hdeg H hP5.1 hclass hP6

end Workspace.MainTheorem
