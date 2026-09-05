import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances

/-!
# Knots, strips and striations  (§9, "Double split graphs")

Section 9 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas;
published/Annals version), printed pages 47–56.

The section opens: *"In this section we handle degenerate appearances of `K₄`.  There is
another way to view them, not as line graphs but as sets of paths and antipaths with certain
properties, as we shall see."*

## Encoding choices

* Paths and antipaths are lists of vertices (`Core.IsPathList`, `Core.IsAntipathList`), so the
  vertex set `V(P)` of a path `P` given by a list `p` is `{v | v ∈ p}`.
* A **strip** `S = (A, C, B)` and an **antistrip** `T = (X, Z, Y)` are triples of vertex sets,
  encoded as `Set V × Set V × Set V` **in the printed order** `(A, C, B)` resp. `(X, Z, Y)`.
* A **striation** is a pair of finite families `S : Fin m → …`, `T : Fin n → …`; the paper's
  index ranges `1 ≤ i ≤ m` and `1 ≤ j ≤ n` become `Fin m` and `Fin n`, and `i < i'` is the
  order of `Fin m`.

## Two conventions of §9 that are *not* definitions

* **"Up to symmetry"** (printed p. 48).  PAPER: *"(The expression 'up to symmetry' means here
  'possibly after exchanging `P₁` and `P₂` and exchanging `Q₁` and `Q₂`, and renaming the ends
  of `P₁, P₂, Q₁, Q₂` accordingly.')"*  This is a reading convention for the four outcomes of
  9.3, not a definable notion; it is discharged where 9.3 is stated, by writing out the
  relevant exchanged quadruples.
* **The naming convention for rung ends** (printed p. 50).  PAPER: *"If `P` is a rung with
  ends `a ∈ A` and `b ∈ B`, we speak of the 'rung `a`-`P`-`b`' for brevity; the reader can
  deduce which end is in which set from the names of the ends, because we shall always use
  `a, a', a₁` etc. for ends in a set called something like `A`, and so on."*  This is purely a
  notational convention about variable names, so it has no formal counterpart; `IsSRung`
  already records which end lies in `A` and which in `B`.

## Terms of §9 deliberately not given their own `def`

* **antirung** (printed p. 50): *"An antistrip is a triple that is a strip in `Ḡ`, and the
  corresponding antipaths are called antirungs."*  A `T`-antirung is therefore literally
  `IsSRung Gᶜ T p`; no separate name is needed.
* **disagree** (printed p. 50): *"and they disagree if one pair is parallel and the other pair
  is co-parallel."*  Note that this is *not* the negation of `AgreeOn` (a pair could be
  neither parallel nor co-parallel).  It occurs only inside the definition of a twist, and is
  written out there.
* **offspring** (printed p. 52) is introduced inside the proof of 9.5 and used only there, so
  it is not part of the interface of this module.
-/

set_option autoImplicit false

namespace Workspace.Types.Knots

open Workspace.Types.Core Workspace.Types.Appearances

namespace SPGT

variable {V : Type*}

/-! ### Knots -/

/-- **Knot** (printed p. 47).

PAPER: *"Let `P₁, P₂` be paths in a graph `G`, and let `Q₁, Q₂` be antipaths.  Suppose that
`P₁, P₂, Q₁, Q₂` are pairwise disjoint, and we can label the ends of each `Pᵢ` as `aᵢ, bᵢ`, and
label the ends of each `Qⱼ` as `xⱼ, yⱼ`, such that:*

*• `P₁, P₂, Q₁, Q₂` all have length `≥ 1`*

*• there are no edges between `P₁` and `P₂`, and `Q₁` is complete to `Q₂`*

*• for `(i,j) = (1,1), (1,2)` or `(2,1)`, the only edges between `V(Pᵢ)` and `{xⱼ, yⱼ}` are
`aᵢxⱼ` and `bᵢyⱼ`, and the only edges between `V(P₂)` and `{x₂, y₂}` are `a₂y₂` and `b₂x₂`,*

*• for `(i,j) = (1,1), (1,2)` or `(2,1)`, the only nonedges between `V(Qⱼ)` and `{aᵢ, bᵢ}` are
`aᵢyⱼ` and `bᵢxⱼ`, and the only nonedges between `V(Q₂)` and `{a₂, b₂}` are `a₂x₂` and `b₂y₂`.*

*In these circumstances we call the quadruple `(P₁, P₂, Q₁, Q₂)` a knot in `G`.  Note that if
`(P₁, P₂, Q₁, Q₂)` is a knot then so is `(P₂, P₁, Q₁, Q₂)`, with a suitable relabelling of the
ends of the paths and antipaths."*

Being a knot is a property of the quadruple alone — the paper's closing note ("*so is
`(P₂,P₁,Q₁,Q₂)`, with a suitable relabelling*") only makes sense that way — so the eight end
labels are existentially quantified, exactly as in "*we can label the ends … such that*".

"The only edges between `V(Pᵢ)` and `{xⱼ, yⱼ}` are `aᵢxⱼ` and `bᵢyⱼ`" is rendered as an
if-and-only-if: those two pairs *are* edges and no other pair is.  Likewise for the nonedges in
the last bullet. -/
def IsKnot (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) : Prop :=
  ∃ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V,
    SPGT.IsPathFrom G P₁ a₁ b₁ ∧ SPGT.IsPathFrom G P₂ a₂ b₂ ∧
    SPGT.IsAntipathFrom G Q₁ x₁ y₁ ∧ SPGT.IsAntipathFrom G Q₂ x₂ y₂ ∧
    (∀ v ∈ P₁, v ∉ P₂) ∧ (∀ v ∈ P₁, v ∉ Q₁) ∧ (∀ v ∈ P₁, v ∉ Q₂) ∧
    (∀ v ∈ P₂, v ∉ Q₁) ∧ (∀ v ∈ P₂, v ∉ Q₂) ∧ (∀ v ∈ Q₁, v ∉ Q₂) ∧
    1 ≤ SPGT.pathLength P₁ ∧ 1 ≤ SPGT.pathLength P₂ ∧
    1 ≤ SPGT.pathLength Q₁ ∧ 1 ≤ SPGT.pathLength Q₂ ∧
    SPGT.Anticomplete G {v : V | v ∈ P₁} {v : V | v ∈ P₂} ∧
    SPGT.Complete G {v : V | v ∈ Q₁} {v : V | v ∈ Q₂} ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₁) ∨ (u = b₁ ∧ w = y₁)))) ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₂) ∨ (u = b₁ ∧ w = y₂)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = x₁) ∨ (u = b₂ ∧ w = y₁)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = y₂) ∨ (u = b₂ ∧ w = x₂)))) ∧
    (∀ u ∈ Q₁, ∀ w ∈ ({a₁, b₁} : Set V),
      (¬ G.Adj u w ↔ ((w = a₁ ∧ u = y₁) ∨ (w = b₁ ∧ u = x₁)))) ∧
    (∀ u ∈ Q₂, ∀ w ∈ ({a₁, b₁} : Set V),
      (¬ G.Adj u w ↔ ((w = a₁ ∧ u = y₂) ∨ (w = b₁ ∧ u = x₂)))) ∧
    (∀ u ∈ Q₁, ∀ w ∈ ({a₂, b₂} : Set V),
      (¬ G.Adj u w ↔ ((w = a₂ ∧ u = y₁) ∨ (w = b₂ ∧ u = x₁)))) ∧
    (∀ u ∈ Q₂, ∀ w ∈ ({a₂, b₂} : Set V),
      (¬ G.Adj u w ↔ ((w = a₂ ∧ u = x₂) ∨ (w = b₂ ∧ u = y₂))))

/-- **The knot induces `K`** (printed p. 47).

PAPER: *"Let `(P₁, P₂, Q₁, Q₂)` be a knot in a Berge graph `G`; we define `K` to be the
subgraph of `G` induced on `V(P₁) ∪ V(P₂) ∪ V(Q₁) ∪ V(Q₂)`.  (For brevity we say that the knot
induces `K`.)"*

Induced subgraphs of `G` are throughout this project given by their vertex sets (`G.induce K`
for `K : Set V`), so "the knot induces `K`" says that `K` is that union of vertex sets; the
graph `G` itself plays no role in the condition. -/
def KnotInduces (P₁ P₂ Q₁ Q₂ : List V) (K : Set V) : Prop :=
  K = {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}

/-- **Local with respect to the knot** (printed p. 47).

PAPER: *"We say a subset `X ⊆ V(K)` is local (with respect to the knot) if `X` is disjoint from
one of `V(P₁), V(P₂)`, and `X` includes neither of `V(Q₁), V(Q₂)`, and `X ∩ (V(P₁) ∪ V(P₂))` is
complete to `X ∩ (V(Q₁) ∪ V(Q₂))`."*

"`X` includes neither of `V(Q₁), V(Q₂)`" is `¬ (V(Q₁) ⊆ X) ∧ ¬ (V(Q₂) ⊆ X)`.  Following the
style of `Core` (and of `Appearances.LocalForLineGraph`), the preamble "`X ⊆ V(K)`" records
where the notion is applied and is a hypothesis of the surrounding statements, not a conjunct
of the definition; consequently `K` is not an argument. -/
def LocalForKnot (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (X : Set V) : Prop :=
  (Disjoint X {v : V | v ∈ P₁} ∨ Disjoint X {v : V | v ∈ P₂}) ∧
  ¬ ({v : V | v ∈ Q₁} ⊆ X) ∧ ¬ ({v : V | v ∈ Q₂} ⊆ X) ∧
  SPGT.Complete G (X ∩ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂}))
    (X ∩ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}))

/-- **`X` resolves the knot** (printed pp. 47–48).

PAPER: *"We say `X` resolves the knot if `V(K) \ X` is local with respect to the knot
`(Q₁, Q₂, P₁, P₂)` in `Ḡ`; that is, if `X` includes one of `V(Q₁), V(Q₂)`, and `X` meets both
`P₁` and `P₂`, and `X` contains at least one end of every edge between `V(P₁) ∪ V(P₂)` and
`V(Q₁) ∪ V(Q₂)`."*

The paper gives the two forms as the same condition; the second ("*that is, …*") is the one
transcribed here, because it is self-contained and is what 9.2, 9.3 and 9.4 use. -/
def ResolvesKnot (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V) (X : Set V) : Prop :=
  ({v : V | v ∈ Q₁} ⊆ X ∨ {v : V | v ∈ Q₂} ⊆ X) ∧
  (X ∩ {v : V | v ∈ P₁}).Nonempty ∧ (X ∩ {v : V | v ∈ P₂}).Nonempty ∧
  ∀ u ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} : Set V),
    ∀ w ∈ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V), G.Adj u w → (u ∈ X ∨ w ∈ X)

/-! ### Strips and antistrips -/

/-- **Rung of a strip, `S`-rung** (printed p. 50).

PAPER: *"We call `S = (A, C, B)` a strip if `A, B` are nonempty, and every vertex of
`A ∪ B ∪ C` belongs to a path between `A` and `B` with only its first vertex in `A`, only its
last vertex in `B`, and interior in `C`.  Such a path is called a rung of the strip `S`, or an
`S`-rung."*

The condition on the path does not itself refer to `S` being a strip, so it is stated first and
reused in `IsStrip`.  "Only its first vertex in `A`" is: the first vertex is in `A` and no
later vertex is (`p.tail`); "only its last vertex in `B`" is dual (`p.dropLast`); "interior in
`C`" uses the paper's `P*`, `Core.interior`.

Naming convention (printed p. 50), which is notation only and has no formal content: *"If `P`
is a rung with ends `a ∈ A` and `b ∈ B`, we speak of the 'rung `a`-`P`-`b`' for brevity; the
reader can deduce which end is in which set from the names of the ends, because we shall always
use `a, a', a₁` etc. for ends in a set called something like `A`, and so on."*

This is §9's own notion of a rung, and is unrelated to the `uv`-rungs of §8.

Note that `IsSRung Gᶜ T p` is the paper's *antirung* of the antistrip `T`. -/
def IsSRung (G : SimpleGraph V) : Set V × Set V × Set V → List V → Prop
  | (A, C, B), p =>
      ∃ a b : V, SPGT.IsPathFrom G p a b ∧ a ∈ A ∧ b ∈ B ∧
        (∀ v ∈ p.tail, v ∉ A) ∧ (∀ v ∈ p.dropLast, v ∉ B) ∧
        (∀ v ∈ SPGT.interior p, v ∈ C)

/-- **Strip** (printed p. 50).

PAPER: *"Let `A, B, C` be disjoint subsets of `V(G)`.  We call `S = (A, C, B)` a strip if
`A, B` are nonempty, and every vertex of `A ∪ B ∪ C` belongs to a path between `A` and `B` with
only its first vertex in `A`, only its last vertex in `B`, and interior in `C`.  Such a path is
called a rung of the strip `S`, or an `S`-rung."*

The three sets being pairwise disjoint is part of the data of a strip (it is what makes the
labels `A`, `C`, `B` meaningful, and it is not implied by the covering condition), so unlike a
standing hypothesis about the ambient graph it is recorded as a conjunct. -/
def IsStrip (G : SimpleGraph V) : Set V × Set V × Set V → Prop
  | (A, C, B) =>
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A.Nonempty ∧ B.Nonempty ∧
      ∀ v ∈ A ∪ B ∪ C, ∃ p : List V, IsSRung G (A, C, B) p ∧ v ∈ p

/-- **`V(S)`** (printed p. 50).

PAPER: *"When `S = (A, C, B)` is a strip, `V(S)` means `A ∪ B ∪ C`."* -/
def stripVertices : Set V × Set V × Set V → Set V
  | (A, C, B) => A ∪ B ∪ C

/-- **Reverse of a strip** (printed p. 50).

PAPER: *"The reverse of a strip `(A, C, B)` is the strip `(B, C, A)`."* -/
def reverseStrip : Set V × Set V × Set V → Set V × Set V × Set V
  | (A, C, B) => (B, C, A)

/-- **Antistrip** (printed p. 50).

PAPER: *"An antistrip is a triple that is a strip in `Ḡ`, and the corresponding antipaths are
called antirungs."*

The antirungs of `T` are then the lists `p` with `IsSRung Gᶜ T p`. -/
def IsAntistrip (G : SimpleGraph V) (T : Set V × Set V × Set V) : Prop := IsStrip Gᶜ T

/-! ### Parallel, co-parallel, agreement, twists -/

/-- **A strip and an antistrip are parallel** (printed p. 50).

PAPER: *"Let `S = (A, C, B)` be a strip and `T = (X, Z, Y)` an antistrip, with
`V(S) ∩ V(T) = ∅`.  We say `S, T` are parallel if:*

*• `A` is complete to `X ∪ Z`, and `B` is complete to `Y ∪ Z`, and*

*• `X` is anticomplete to `B ∪ C`, and `Y` is anticomplete to `A ∪ C`."*

This is the published two-bullet form, transcribed as printed.  The preamble — `S` a strip,
`T` an antistrip, `V(S) ∩ V(T) = ∅` — is a hypothesis of the surrounding statements (in a
striation, for instance, disjointness of all the strips and antistrips is required separately),
so, as for `Core.Complete`, it is not a conjunct here. -/
def ParallelStripAntistrip (G : SimpleGraph V) :
    Set V × Set V × Set V → Set V × Set V × Set V → Prop
  | (A, C, B), (X, Z, Y) =>
      (SPGT.Complete G A (X ∪ Z) ∧ SPGT.Complete G B (Y ∪ Z)) ∧
      (SPGT.Anticomplete G X (B ∪ C) ∧ SPGT.Anticomplete G Y (A ∪ C))

/-- **Co-parallel** (printed p. 50).

PAPER: *"We say `S, T` are co-parallel if `S, T'` are parallel, where `T'` is the reverse of
`T`."* -/
def CoParallel (G : SimpleGraph V) (S T : Set V × Set V × Set V) : Prop :=
  ParallelStripAntistrip G S (reverseStrip T)

/-- **Two strips agree on an antistrip** (printed p. 50).

PAPER: *"Now let `S₁, S₂` be strips and `T` an antistrip, where `S₁, S₂, T` are pairwise
disjoint.  We say that `S₁, S₂` agree on `T` if either `S₁, T` are parallel and `S₂, T` are
parallel, or both pairs are co-parallel; and they disagree if one pair is parallel and the
other pair is co-parallel.  If `S` is a strip and `T₁, T₂` are antistrips, pairwise disjoint,
we define whether `T₁, T₂` agree or disagree on `S` similarly."*

The dual notion ("`T₁, T₂` agree on `S`", defined "similarly") is the same condition with the
roles of the two families exchanged, i.e. `ParallelStripAntistrip G S T₁ ∧
ParallelStripAntistrip G S T₂` or both co-parallel; the paper flags in the definition of a
twist that the two readings give the same quadruples, so only this one is named.  Note also
that "disagree" is *not* the negation of "agree on"; it is written out inside `IsTwist`.

The preamble "`S₁, S₂, T` are pairwise disjoint" is a hypothesis of the surrounding statements
and is not a conjunct. -/
def AgreeOn (G : SimpleGraph V) (S₁ S₂ T : Set V × Set V × Set V) : Prop :=
  (ParallelStripAntistrip G S₁ T ∧ ParallelStripAntistrip G S₂ T) ∨
  (CoParallel G S₁ T ∧ CoParallel G S₂ T)

/-- **Twist** (printed p. 50).

PAPER: *"Now let `S₁, S₂` be strips, and let `T₁, T₂` be antistrips, all pairwise disjoint.  We
call the quadruple `(S₁, S₂, T₁, T₂)` a twist if `S₁, S₂` agree on one of `T₁, T₂` and disagree
on the other.  (Equivalently, if `T₁, T₂` agree on one of `S₁, S₂`, and disagree on the other.)
Note that if `(S₁, S₂, T₁, T₂)` is a twist, then so is `(S₁', S₂, T₁, T₂)`, where `S₁'` is the
reverse of `S₁`."*

`S₁, S₂` *disagree* on `T` (printed p. 50) means "*one pair is parallel and the other pair is
co-parallel*", which is written out here because it is not the negation of `AgreeOn`.  The
parenthetical reformulation is flagged by the paper as an equivalent, so it is not a further
conjunct; the preamble "all pairwise disjoint" is a hypothesis of the surrounding statements.
-/
def IsTwist (G : SimpleGraph V) (S₁ S₂ T₁ T₂ : Set V × Set V × Set V) : Prop :=
  (AgreeOn G S₁ S₂ T₁ ∧
      ((ParallelStripAntistrip G S₁ T₂ ∧ CoParallel G S₂ T₂) ∨
        (CoParallel G S₁ T₂ ∧ ParallelStripAntistrip G S₂ T₂))) ∨
  (AgreeOn G S₁ S₂ T₂ ∧
      ((ParallelStripAntistrip G S₁ T₁ ∧ CoParallel G S₂ T₁) ∨
        (CoParallel G S₁ T₁ ∧ ParallelStripAntistrip G S₂ T₁)))

/-! ### Striations -/

/-- **Striation** (printed p. 50).

PAPER: *"A striation in a graph `G` is a family of strips `Sᵢ = (Aᵢ, Cᵢ, Bᵢ)` `(1 ≤ i ≤ m)`
together with a family of antistrips `Tⱼ = (Xⱼ, Zⱼ, Yⱼ)` `(1 ≤ j ≤ n)`, satisfying the
following conditions:*

*• all the strips and antistrips are pairwise disjoint, and all their rungs and antirungs have
odd length*

*• `m, n ≥ 2`*

*• for `1 ≤ i < i' ≤ m`, `Sᵢ` is anticomplete to `Sᵢ'`, and for `1 ≤ j < j' ≤ n`, `Tⱼ` is
complete to `Tⱼ'`*

*• for `1 ≤ i ≤ m` and `1 ≤ j ≤ n`, `Sᵢ` and `Tⱼ` are either parallel or co-parallel*

*• for `1 ≤ i < i' ≤ m` there exist distinct `j, j'` with `1 ≤ j, j' ≤ n` such that
`(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` is a twist*

*• for `1 ≤ j < j' ≤ n` there exist distinct `i, i'` with `1 ≤ i, i' ≤ m` such that
`(Sᵢ, Sᵢ', Tⱼ, Tⱼ')` is a twist.*

*(Note that if we replace some `(Aᵢ, Cᵢ, Bᵢ)` by its reverse, we obtain another striation.)  We
denote the striation by `L`, and the union of the vertex sets of all its strips and antistrips
by `V(L)`."*

"`Sᵢ` is anticomplete to `Sᵢ'`" is anticompleteness of the vertex sets `V(Sᵢ), V(Sᵢ')`, and
likewise for "`Tⱼ` is complete to `Tⱼ'`"; "pairwise disjoint" is disjointness of the vertex
sets, over all three kinds of pair.  A `Tⱼ`-antirung is an `IsSRung Gᶜ (T j)`. -/
def IsStriation (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V) : Prop :=
  (∀ i : Fin m, IsStrip G (S i)) ∧
  (∀ j : Fin n, IsAntistrip G (T j)) ∧
  (∀ i i' : Fin m, i ≠ i' → Disjoint (stripVertices (S i)) (stripVertices (S i'))) ∧
  (∀ j j' : Fin n, j ≠ j' → Disjoint (stripVertices (T j)) (stripVertices (T j'))) ∧
  (∀ (i : Fin m) (j : Fin n), Disjoint (stripVertices (S i)) (stripVertices (T j))) ∧
  (∀ (i : Fin m) (p : List V), IsSRung G (S i) p → Odd (SPGT.pathLength p)) ∧
  (∀ (j : Fin n) (p : List V), IsSRung Gᶜ (T j) p → Odd (SPGT.pathLength p)) ∧
  2 ≤ m ∧ 2 ≤ n ∧
  (∀ i i' : Fin m, i < i' →
    SPGT.Anticomplete G (stripVertices (S i)) (stripVertices (S i'))) ∧
  (∀ j j' : Fin n, j < j' →
    SPGT.Complete G (stripVertices (T j)) (stripVertices (T j'))) ∧
  (∀ (i : Fin m) (j : Fin n),
    ParallelStripAntistrip G (S i) (T j) ∨ CoParallel G (S i) (T j)) ∧
  (∀ i i' : Fin m, i < i' →
    ∃ j j' : Fin n, j ≠ j' ∧ IsTwist G (S i) (S i') (T j) (T j')) ∧
  (∀ j j' : Fin n, j < j' →
    ∃ i i' : Fin m, i ≠ i' ∧ IsTwist G (S i) (S i') (T j) (T j'))

/-- **`V(L)`** (printed p. 50).

PAPER: *"We denote the striation by `L`, and the union of the vertex sets of all its strips and
antistrips by `V(L)`."* -/
def striationVertices {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V) : Set V :=
  (⋃ i : Fin m, stripVertices (S i)) ∪ (⋃ j : Fin n, stripVertices (T j))

/-- **Local with respect to `L`** (printed pp. 50–51).

PAPER: *"By analogy with what we did for knots, let us say that a subset `X ⊆ V(L)` is local
with respect to `L` if*

*• at most one of `X ∩ V(S₁), …, X ∩ V(S_m)` is nonempty,*

*• for `1 ≤ j ≤ n`, every `Tⱼ`-antirung has a vertex not in `X`, and*

*• `X ∩ (V(S₁) ∪ ⋯ ∪ V(S_m))` is complete to `X ∩ (V(T₁) ∪ ⋯ ∪ V(T_n))`."*

"At most one of `X ∩ V(S₁), …, X ∩ V(S_m)` is nonempty" is rendered as: any two indices whose
intersections with `X` are nonempty coincide.  As for `LocalForKnot`, the preamble `X ⊆ V(L)`
records where the notion is applied and is a hypothesis of the surrounding statements. -/
def LocalForStriation (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (X : Set V) : Prop :=
  (∀ i i' : Fin m, (X ∩ stripVertices (S i)).Nonempty →
      (X ∩ stripVertices (S i')).Nonempty → i = i') ∧
  (∀ (j : Fin n) (p : List V), IsSRung Gᶜ (T j) p → ∃ v ∈ p, v ∉ X) ∧
  SPGT.Complete G (X ∩ (⋃ i : Fin m, stripVertices (S i)))
    (X ∩ (⋃ j : Fin n, stripVertices (T j)))

/-- **`X` resolves `L`** (printed p. 51).

PAPER: *"We say `X` resolves `L` if `V(L) \ X` is local with respect to the striation in `Ḡ`
obtained from `L` by exchanging the strips and antistrips; that is, if*

*• there is at most one of `T₁, …, T_n` that is not a subset of `X`,*

*• for `1 ≤ i ≤ m`, every `Sᵢ`-rung meets `X`, and*

*• `X` contains at least one end of every edge between `V(S₁) ∪ ⋯ ∪ V(S_m)` and
`V(T₁) ∪ ⋯ ∪ V(T_n)`."*

The paper gives the two forms as the same condition; the second ("*that is, …*") is the one
transcribed here.  "`Tⱼ` is a subset of `X`" means `V(Tⱼ) ⊆ X`. -/
def ResolvesStriation (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (X : Set V) : Prop :=
  (∀ j j' : Fin n, ¬ (stripVertices (T j) ⊆ X) → ¬ (stripVertices (T j') ⊆ X) → j = j') ∧
  (∀ (i : Fin m) (p : List V), IsSRung G (S i) p → ∃ v ∈ p, v ∈ X) ∧
  (∀ u ∈ (⋃ i : Fin m, stripVertices (S i)), ∀ w ∈ (⋃ j : Fin n, stripVertices (T j)),
    G.Adj u w → (u ∈ X ∨ w ∈ X))

/-- **Maximal striation** (printed p. 51).

PAPER: *"A striation `L` in `G` is maximal if there is no striation `L'` in `G` with
`V(L) ⊂ V(L')`."*

The paper's `⊂` is proper inclusion, Mathlib's `⊂`.  Being a *maximal striation* includes being
a striation, as in "*let `L` be a maximal striation in `G`*" (9.4, 9.5). -/
def MaximalStriation (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V) : Prop :=
  IsStriation G S T ∧
  ¬ ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V),
      IsStriation G S' T' ∧ striationVertices S T ⊂ striationVertices S' T'

end SPGT

end Workspace.Types.Knots
