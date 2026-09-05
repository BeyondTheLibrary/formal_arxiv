import Mathlib
import Workspace.Types.Core

/-!
# The four "features" of Section 1 of the Strong Perfect Graph Theorem paper

This module transcribes the four decompositions that Chudnovsky, Robertson,
Seymour and Thomas introduce on printed pages 2-3 of *The Strong Perfect Graph
Theorem* (the June 20 2002 / revised July 19 2005 *Annals* version), together
with the two historical notions (*star cutset* and *even pair*), introduced on
printed page 5 of the same section for the conjectures 1.6 and 1.7.

Each `Is…` predicate takes the witnessing sets as explicit arguments, and each
`Admits…` / `Has…` predicate existentially quantifies them; that way statements
in later sections can either name the witnesses or not, as the paper does.

The basic vocabulary (paths, components, complete/anticomplete, connected,
balanced) is imported from `Workspace.Types.Core` and never restated here.
-/

namespace Workspace.Types.Decompositions

open Workspace.Types.Core

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Proper 2-joins -/

/-- PAPER (printed page 2): *"First, a special case of the '2-join' due to
Cornuéjols and Cunningham [13] — a proper 2-join in `G` is a partition
`(X₁,X₂)` of `V(G)` such that there exist disjoint nonempty `Aᵢ, Bᵢ ⊆ Xᵢ`
`(i = 1,2)` satisfying:*

* *every vertex of `A₁` is adjacent to every vertex of `A₂`, and every vertex of
  `B₁` is adjacent to every vertex of `B₂`,*
* *there are no other edges between `X₁` and `X₂`,*
* *for `i = 1,2`, every component of `G|Xᵢ` meets both `Aᵢ` and `Bᵢ`, and*
* *for `i = 1,2`, if `|Aᵢ| = |Bᵢ| = 1` and `G|Xᵢ` is a path joining the members
  of `Aᵢ` and `Bᵢ`, then it has odd length `≥ 3`."*

*"(Thanks to Kristina Vušković for pointing out that we could include the 'odd
length' condition above with no change to the proof.)"*

Notes on the transcription.

* *"a partition `(X₁,X₂)` of `V(G)`"* is `X₁ ∪ X₂ = Set.univ` together with
  `Disjoint X₁ X₂`.
* *"disjoint nonempty `Aᵢ, Bᵢ ⊆ Xᵢ`"*: for each `i`, the two sets `Aᵢ` and `Bᵢ`
  are disjoint from one another, each is nonempty, and each is contained in
  `Xᵢ`.
* The **first two bullets together** say exactly which pairs `(u,v) ∈ X₁ × X₂`
  are adjacent, so they are transcribed as a single *if and only if*: the first
  bullet is the `←` direction and *"there are no other edges between `X₁` and
  `X₂`"* is the `→` direction.
* *"every component of `G|Xᵢ`"* uses `Core`'s `IsComponent G Xᵢ C` (a maximal
  connected subset of `Xᵢ`), and *"meets both"* is nonemptiness of the two
  intersections.
* *"`G|Xᵢ` is a path joining the members of `Aᵢ` and `Bᵢ`"* is: some list `p`
  of vertices is a path of `G` with ends the unique member `a` of `Aᵢ` and the
  unique member `b` of `Bᵢ`, whose vertex set is the whole of `Xᵢ`.  (Because
  the vertex set is inside `Xᵢ`, being an induced path of `G` and of `G|Xᵢ`
  agree.)  Both conjuncts of the conclusion, *odd* and *`≥ 3`*, are required. -/
def IsProper2Join (G : SimpleGraph V) (X₁ X₂ : Set V) : Prop :=
  X₁ ∪ X₂ = Set.univ ∧ Disjoint X₁ X₂ ∧
  ∃ A₁ B₁ A₂ B₂ : Set V,
    -- `Aᵢ, Bᵢ ⊆ Xᵢ`
    A₁ ⊆ X₁ ∧ B₁ ⊆ X₁ ∧ A₂ ⊆ X₂ ∧ B₂ ⊆ X₂ ∧
    -- nonempty
    A₁.Nonempty ∧ B₁.Nonempty ∧ A₂.Nonempty ∧ B₂.Nonempty ∧
    -- disjoint (`Aᵢ` from `Bᵢ`)
    Disjoint A₁ B₁ ∧ Disjoint A₂ B₂ ∧
    -- bullets 1 and 2: `A₁` is complete to `A₂`, `B₁` is complete to `B₂`,
    -- and there are no other edges between `X₁` and `X₂`
    (∀ u ∈ X₁, ∀ v ∈ X₂, G.Adj u v ↔ ((u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂))) ∧
    -- bullet 3: every component of `G|Xᵢ` meets both `Aᵢ` and `Bᵢ`
    (∀ C : Set V, SPGT.IsComponent G X₁ C → (C ∩ A₁).Nonempty ∧ (C ∩ B₁).Nonempty) ∧
    (∀ C : Set V, SPGT.IsComponent G X₂ C → (C ∩ A₂).Nonempty ∧ (C ∩ B₂).Nonempty) ∧
    -- bullet 4: if `|Aᵢ| = |Bᵢ| = 1` and `G|Xᵢ` is a path joining their members,
    -- then that path has odd length `≥ 3`
    (∀ a b : V, A₁ = {a} → B₁ = {b} → ∀ p : List V, SPGT.IsPathFrom G p a b →
        {v : V | v ∈ p} = X₁ → Odd (SPGT.pathLength p) ∧ 3 ≤ SPGT.pathLength p) ∧
    (∀ a b : V, A₂ = {a} → B₂ = {b} → ∀ p : List V, SPGT.IsPathFrom G p a b →
        {v : V | v ∈ p} = X₂ → Odd (SPGT.pathLength p) ∧ 3 ≤ SPGT.pathLength p)

/-- PAPER (printed page 2): *"`G` admits a proper 2-join"* — that is, there is a
partition `(X₁,X₂)` of `V(G)` which is a proper 2-join in `G`. -/
def AdmitsProper2Join (G : SimpleGraph V) : Prop :=
  ∃ X₁ X₂ : Set V, IsProper2Join G X₁ X₂

/-! ### Proper homogeneous pairs -/

/-- PAPER (printed page 2): *"Our second decomposition is a slight variation of
the 'homogeneous pair' of Chvátal and Sbihi [7] — a proper homogeneous pair in
`G` is a pair of disjoint nonempty subsets `(A,B)` of `V(G)`, such that, if
`A₁,A₂` respectively denote the sets of all `A`-complete vertices and all
`A`-anticomplete vertices in `V(G)`, and `B₁,B₂` are defined similarly, then:*

* *`A₁ ∪ A₂ = B₁ ∪ B₂ = V(G) \ (A ∪ B)` (and in particular, every vertex in `A`
  has a neighbour in `B` and a nonneighbour in `B`, and vice versa)*
* *the four sets `A₁ ∩ B₁, A₁ ∩ B₂, A₂ ∩ B₁, A₂ ∩ B₂` are all nonempty."*

Notes on the transcription.

* `A₁ = {v ∈ V(G) \ A | VertexComplete G v A}` and
  `A₂ = {v ∈ V(G) \ A | VertexAnticomplete G v A}`, and likewise `B₁`, `B₂`
  with `B` in place of `A` — i.e. the `A`-sets range over `V(G) \ A` and the
  `B`-sets over `V(G) \ B`; these are spelled out inline below.  For the
  *complete* half the guard is automatic, since `VertexComplete G v A` already
  forces `v ∉ A` (no vertex is adjacent to itself) — exactly the paper's own
  parenthetical *"(and consequently `v ∉ X`)"* in its definition of
  `X`-complete.  Only the *anticomplete* half needs the guard written out, and
  it is written out only in the two union clauses (see `FIXES.md` §F3).
* Why the restriction is the faithful reading.  Over all of `V(G)`, a vertex of
  `A` with no neighbour inside `A` would be `A`-anticomplete, so the clause
  `A₁ ∪ A₂ = V(G) \ (A ∪ B)` would silently impose the unstated extra condition
  that every vertex of `A` has a neighbour in `A` (likewise for `B`).  Taking
  the `A`-sets over `V(G) \ A` and the `B`-sets over `V(G) \ B` yields *exactly*
  the consequence the authors record — every vertex of `A` has a neighbour and a
  nonneighbour in `B`, and vice versa — and nothing beyond it; restricting to
  `V(G) \ (A ∪ B)` instead would be too weak to yield even that.
* The restricted reading is moreover the one the paper uses: it makes the notion
  invariant under complementation, which §13 requires — the proof of 13.4
  (printed page 84) argues *"possibly by replacing `G` by its complement"* and
  concludes *"But then `(A,B)` is a proper homogeneous pair in `G`"*, and the
  derivation of 1.8(5) from 13.4 applies 13.4 to `Ḡ`.  Under the unrestricted
  reading complement-invariance genuinely fails (an explicit 8-vertex
  counterexample is recorded in `FIXES.md` §F3).
* `V(G) \ (A ∪ B)` is the set complement `(A ∪ B)ᶜ`.
* The parenthetical *"(and in particular, …)"* is a consequence that the authors
  point out, **not** a further condition, so it is deliberately not a
  conjunct.
* The four `Nonempty` intersection clauses are left ranging over all of `V(G)`:
  the two union clauses already force every vertex occurring in them into
  `(A ∪ B)ᶜ`, so guarding them too would change nothing. -/
def IsProperHomogeneousPair (G : SimpleGraph V) (A B : Set V) : Prop :=
  Disjoint A B ∧ A.Nonempty ∧ B.Nonempty ∧
  -- `A₁ ∪ A₂ = V(G) \ (A ∪ B)`, with `A₁, A₂` taken over `V(G) \ A`
  {v : V | SPGT.VertexComplete G v A} ∪ {v : V | v ∉ A ∧ SPGT.VertexAnticomplete G v A}
    = (A ∪ B)ᶜ ∧
  -- `B₁ ∪ B₂ = V(G) \ (A ∪ B)`, with `B₁, B₂` taken over `V(G) \ B`
  {v : V | SPGT.VertexComplete G v B} ∪ {v : V | v ∉ B ∧ SPGT.VertexAnticomplete G v B}
    = (A ∪ B)ᶜ ∧
  -- `A₁ ∩ B₁` is nonempty
  ({v : V | SPGT.VertexComplete G v A} ∩ {v : V | SPGT.VertexComplete G v B}).Nonempty ∧
  -- `A₁ ∩ B₂` is nonempty
  ({v : V | SPGT.VertexComplete G v A} ∩ {v : V | SPGT.VertexAnticomplete G v B}).Nonempty ∧
  -- `A₂ ∩ B₁` is nonempty
  ({v : V | SPGT.VertexAnticomplete G v A} ∩ {v : V | SPGT.VertexComplete G v B}).Nonempty ∧
  -- `A₂ ∩ B₂` is nonempty
  ({v : V | SPGT.VertexAnticomplete G v A} ∩ {v : V | SPGT.VertexAnticomplete G v B}).Nonempty

/-- PAPER (printed page 2): *"`G` admits a proper homogeneous pair"* — that is,
there is a pair `(A,B)` of subsets of `V(G)` which is a proper homogeneous pair
in `G`. -/
def AdmitsProperHomogeneousPair (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsProperHomogeneousPair G A B

/-! ### Skew partitions -/

/-- PAPER (printed page 3): *"The third kind of decomposition we use is due to
Chvátal [6] — a skew partition in `G` is a partition `(A,B)` of `V(G)` such that
`A` is not connected and `B` is not anticonnected."*

Here *connected* and *anticonnected* are `Core`'s `ConnectedSet` and
`AnticonnectedSet`, which follow the paper in counting `∅` as connected; so this
definition already forces `A` and `B` to be nonempty. -/
def IsSkewPartition (G : SimpleGraph V) (A B : Set V) : Prop :=
  A ∪ B = Set.univ ∧ Disjoint A B ∧ ¬ SPGT.ConnectedSet G A ∧ ¬ SPGT.AnticonnectedSet G B

/-- PAPER (printed page 3): *"`G` admits a skew partition"* — that is, there is a
partition `(A,B)` of `V(G)` which is a skew partition in `G`. -/
def AdmitsSkewPartition (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsSkewPartition G A B

/-- PAPER (printed pages 2-3): the paper speaks throughout of a *"balanced skew
partition"*, meaning a skew partition `(A,B)` of `V(G)` for which the pair
`(A,B)` is balanced in the sense recalled in `Core`: *"there is no odd path
between nonadjacent vertices in `B` with interior in `A`, and there is no odd
antipath between adjacent vertices in `A` with interior in `B`."* -/
def IsBalancedSkewPartition (G : SimpleGraph V) (A B : Set V) : Prop :=
  IsSkewPartition G A B ∧ SPGT.Balanced G A B

/-- PAPER (printed page 3, statement 1.4 and following): *"`G` admits a balanced
skew partition"* — that is, there is a partition `(A,B)` of `V(G)` which is a
balanced skew partition in `G`. -/
def AdmitsBalancedSkewPartition (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsBalancedSkewPartition G A B

/-! ### Star cutsets and even pairs -/

/-- PAPER (printed page 5): *"A star cutset is a skew partition `(A,B)` such that
some vertex of `B` is adjacent to all other vertices of `B`."* -/
def IsStarCutset (G : SimpleGraph V) (A B : Set V) : Prop :=
  IsSkewPartition G A B ∧ ∃ v ∈ B, ∀ u ∈ B, u ≠ v → G.Adj v u

/-- PAPER (printed page 5, conjecture 1.6): *"one of them has a star cutset"* —
that is, there is a partition `(A,B)` of `V(G)` which is a star cutset of
`G`. -/
def AdmitsStarCutset (G : SimpleGraph V) : Prop :=
  ∃ A B : Set V, IsStarCutset G A B

/-- PAPER (printed page 5): *"An even pair means a pair of vertices `u,v` in a
graph such that every path between them has even length."*

*Path* is the paper's (induced) notion, recalled in `Core` as `IsPathFrom`, and
*length* is the number of edges, `pathLength`. -/
def IsEvenPair (G : SimpleGraph V) (u v : V) : Prop :=
  ∀ p : List V, SPGT.IsPathFrom G p u v → Even (SPGT.pathLength p)

/-- PAPER (printed page 5, conjecture 1.6): *"one of them has … an even pair"* —
that is, there are two distinct vertices `u, v` of `G` forming an even pair. -/
def HasEvenPair (G : SimpleGraph V) : Prop :=
  ∃ u v : V, u ≠ v ∧ IsEvenPair G u v

end SPGT

end Workspace.Types.Decompositions
