import Mathlib
import Workspace.Types.ProPGroup

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
