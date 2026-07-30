import Mathlib

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
