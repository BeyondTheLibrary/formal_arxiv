import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms

/-!
# Step-connected strips (§11) and staircases (§12)

Transcription of the definitions of Section 11 (*Step-connected strips*, printed
pp. 63–66) and Section 12 (*Attachments in a staircase*, printed pp. 69–74) of
Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*
(published version).

Conventions (see `paper/spec/CONVENTIONS.md`):

* a path of the paper is given by the list of its vertices in order
  (`SPGT.IsPathList`, `SPGT.IsPathFrom`); its length is `SPGT.pathLength`
  (one less than the number of vertices) and its interior `P*` is
  `SPGT.interior`;
* the vertex set `V(P)` of such a list `P` is `{v | v ∈ P}`, so "`u ∈ V(P)`" is
  written `u ∈ P`;
* a strip `S = (A, C, B)` is carried by its three vertex sets `A C B : Set V`,
  in that order, and `V(S) = A ∪ B ∪ C`;
* a staircase `K = (S = (A, C, B), a₀-R₀-b₀)` is carried by the seven pieces of
  data `A C B : Set V`, `a₀ : V`, `R₀ : List V`, `b₀ : V`, in that order — the
  strip first, then the banister with its two ends, exactly as in the paper's
  abbreviated notation; `V(K)` is `staircaseVertices`.

The words *local*, *minor*, *major* and *central* are each defined several
times in the paper, for different objects; the names below carry the suffix
`…ForStaircase` to keep those senses apart, and the paper's bare *local, minor,
major, left-diagonal, right-diagonal, central* of §12 are all read "with respect
to `K`".

`Workspace.Types.Prisms` is imported because it is listed as a dependency of
this module; none of the *definitions* of §11 and §12 mentions a prism (prisms
enter only through the hypotheses "no even prism in `G`" of the numbered
statements 11.3–11.5 and 12.1–12.5).
-/

namespace Workspace.Types.Staircases

open Workspace.Types.Core Workspace.Types.Prisms

namespace SPGT

variable {V : Type*}

/-! ### The §9 notion of a rung, restated

Sections 11 and 12 use the notions *strip*, *rung* and `V(S)` of Section 9
without redefining them; the transcription of §11 quotes §9 for them.  The §9
module (`Knots`) is not among this module's dependencies, so the rung is
restated here — this is the only auxiliary definition of the file, and it is
used exactly twice, in `IsStep` and in `StepConnected`. -/

/-- PAPER (§9, printed p. 49; quoted in the §11 transcription's list of terms
defined in earlier sections): *"Let `A, B, C` be disjoint subsets of `V(G)`.  We
call `S = (A, C, B)` a strip if `A, B` are nonempty, and every vertex of
`A ∪ B ∪ C` belongs to a path between `A` and `B` with only its first vertex in
`A`, only its last vertex in `B`, and interior in `C`.  Such a path is called a
rung of the strip `S`, or an `S`-rung.  When `S = (A, C, B)` is a strip, `V(S)`
means `A ∪ B ∪ C`. … If `P` is a rung with ends `a ∈ A` and `b ∈ B`, we speak of
the "rung `a`-`P`-`b`" for brevity …"*

`IsRungOfStrip G A C B a p b` is the paper's "rung `a`-`p`-`b`" of the strip
`S = (A, C, B)`: `p` is a path of `G` from `a` to `b`, its first vertex `a` is
the only vertex of `p` in `A`, its last vertex `b` is the only vertex of `p` in
`B`, and every internal vertex of `p` lies in `C`. -/
def IsRungOfStrip (G : SimpleGraph V) (A C B : Set V) (a : V) (p : List V) (b : V) : Prop :=
  SPGT.IsPathFrom G p a b ∧ a ∈ A ∧ b ∈ B ∧
    (∀ w ∈ p, w ∈ A → w = a) ∧ (∀ w ∈ p, w ∈ B → w = b) ∧
    (∀ w ∈ SPGT.interior p, w ∈ C)

/-! ### Section 11: step-connected strips -/

/-- PAPER (§11, printed pp. 63–64): *"Let `(A, C, B)` be a strip in `G`.  A step is a
pair `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` of rungs such that*

* *`V(R₁) ∩ V(R₂) = ∅`*
* *`a₁` is adjacent to `a₂`, and `b₁` to `b₂`, and there are no other edges
  between `V(R₁)` and `V(R₂)`."*

The second bullet asserts both that `a₁a₂` and `b₁b₂` are edges and that no
other edge runs between `V(R₁)` and `V(R₂)`, so it is rendered as an `↔`
(exactly as the analogous clause of a prism is in `FormPrism`).  That
`(A, C, B)` is a strip is a hypothesis of the surrounding sentence, not part of
the definition of a step. -/
def IsStep (G : SimpleGraph V) (A C B : Set V)
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V) : Prop :=
  IsRungOfStrip G A C B a₁ R₁ b₁ ∧ IsRungOfStrip G A C B a₂ R₂ b₂ ∧
    (∀ v : V, v ∈ R₁ → v ∉ R₂) ∧
    (∀ u ∈ R₁, ∀ v ∈ R₂, (G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = b₁ ∧ v = b₂)))

/-- PAPER (§11, printed pp. 63–64): *"The edges `a₁a₂` and `b₁b₂` such that there
exists a step as above are called stepped edges."*

`steppedEdges G A C B` is the set of stepped edges of the strip `S = (A, C, B)`,
an edge being an unordered pair `s(x, y) : Sym2 V` as in Mathlib's
`SimpleGraph.edgeSet`. -/
def steppedEdges (G : SimpleGraph V) (A C B : Set V) : Set (Sym2 V) :=
  {e : Sym2 V | ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
    IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ (e = s(a₁, a₂) ∨ e = s(b₁, b₂))}

/-- PAPER (§11, printed pp. 63–64): *"We say that the strip is step-connected if
every vertex of `A ∪ B ∪ C` is in a step, and for every partition `(X, Y)` of
`A` or of `B` into two nonempty sets, there is a step `R₁, R₂` such that `R₁`
has an end in `X` and `R₂` has an end in `Y`.  (This second condition is
equivalent to requiring that the subgraph of `G` with vertex set `A` and edges
the stepped edges within `A` be connected, and the same for `B`.)"*

`StepConnected G A C B` says that `S = (A, C, B)` **is a step-connected strip in
`G`**, which is how §11 and §12 always use the term: the first three conjuncts
are the §9 definition of a strip (`A, B, C` disjoint; `A, B` nonempty; every
vertex of `A ∪ B ∪ C` lies on a rung), and the last two are the two conditions
quoted above.  The parenthetical sentence is a remark about the second
condition, not an extra requirement, so it is not formalized.  "`R₁` has an end
in `X`" is read literally: one of the two ends `a₁, b₁` of `R₁` lies in `X`. -/
def StepConnected (G : SimpleGraph V) (A C B : Set V) : Prop :=
  (Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) ∧
  (A.Nonempty ∧ B.Nonempty) ∧
  (∀ v ∈ A ∪ B ∪ C, ∃ (a : V) (p : List V) (b : V), IsRungOfStrip G A C B a p b ∧ v ∈ p) ∧
  (∀ v ∈ A ∪ B ∪ C,
    ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ (v ∈ R₁ ∨ v ∈ R₂)) ∧
  (∀ X Y : Set V, (X ∪ Y = A ∨ X ∪ Y = B) → Disjoint X Y → X.Nonempty → Y.Nonempty →
    ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ (a₁ ∈ X ∨ b₁ ∈ X) ∧ (a₂ ∈ Y ∨ b₂ ∈ Y))

/-- PAPER (§11, printed pp. 63–64): *"Let `(A, C, B)` be a step-connected strip
in a Berge graph `G`.  A vertex `v ∈ V(G) \ (A ∪ B ∪ C)` is a left-star for the
strip if it is complete to `A` and anticomplete to `B ∪ C`,"*

That `G` is Berge and that `(A, C, B)` is step-connected are hypotheses of the
surrounding sentence, not part of the property of `v`. -/
def IsLeftStar (G : SimpleGraph V) (A C B : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∧ SPGT.VertexComplete G v A ∧ SPGT.VertexAnticomplete G v (B ∪ C)

/-- PAPER (§11, printed pp. 63–64): *"… and it is a right-star if it is complete
to `B` and anticomplete to `A ∪ C`."*

(The ambient hypotheses are the same as for a left-star: `v` is a vertex of
`V(G) \ (A ∪ B ∪ C)`, and `(A, C, B)` is a step-connected strip in a Berge
graph `G`.) -/
def IsRightStar (G : SimpleGraph V) (A C B : Set V) (v : V) : Prop :=
  v ∉ A ∪ B ∪ C ∧ SPGT.VertexComplete G v B ∧ SPGT.VertexAnticomplete G v (A ∪ C)

/-- PAPER (§11, printed pp. 63–64): *"A banister (with respect to the strip) is a
path `a`-`R`-`b` of `G \ (A ∪ B ∪ C)`, such that `a` is a left-star, `b` is a
right-star, and there are no edges between the interior of `R` and `V(S)`.
(Here we distinguish between `a`-`R`-`b` and `b`-`R`-`a`; we follow the
convention that when describing a banister relative to a strip, the end which is
the left-star is listed first.)  A banister can have length 1."*

"A path of `G \ (A ∪ B ∪ C)`" is a path of `G` none of whose vertices lies in
`A ∪ B ∪ C`.  The paper's ordering convention is captured by the argument order
`a`, `R`, `b`.  "A banister can have length 1" is a remark, not a constraint, so
no length condition is imposed. -/
def IsBanister (G : SimpleGraph V) (A C B : Set V) (a : V) (R : List V) (b : V) : Prop :=
  SPGT.IsPathFrom G R a b ∧ (∀ v ∈ R, v ∉ A ∪ B ∪ C) ∧
    IsLeftStar G A C B a ∧ IsRightStar G A C B b ∧
    SPGT.Anticomplete G {u : V | u ∈ SPGT.interior R} (A ∪ B ∪ C)

/-- PAPER (§11, printed p. 66, stated between 11.4 and 11.5): *"A triple
`(S, F, Q)` is called a 1-breaker in `G` if it satisfies the following.*

* *`S = (A, C, B)` is a step-connected strip in `G`,*
* *`F ⊆ V(G) \ V(S)` is connected, such that there are no edges between `F` and
  `V(S)`, and there is a left- and right-star, both with neighbours in `F`,*
* *`Q ⊆ V(G) \ (V(S) ∪ F)` is anticonnected,*
* *some vertex in `A` has a nonneighbour in `Q`, and so does some vertex in
  `B`,*
* *every vertex in `Q` has a neighbour in `F` and a neighbour in `A ∪ B ∪ C`,*
* *some left-star with a neighbour in `F` is `Q`-complete,*
* *no vertex in `Q` is a left-star."*

Here `V(S) = A ∪ B ∪ C`.  The triple `(S, F, Q)` is carried by the five sets
`A, C, B, F, Q`. -/
def IsOneBreaker (G : SimpleGraph V) (A C B F Q : Set V) : Prop :=
  StepConnected G A C B ∧
  ((∀ v ∈ F, v ∉ A ∪ B ∪ C) ∧ SPGT.ConnectedSet G F ∧
      SPGT.Anticomplete G F (A ∪ B ∪ C) ∧
      (∃ u : V, IsLeftStar G A C B u ∧ ∃ f ∈ F, G.Adj u f) ∧
      (∃ w : V, IsRightStar G A C B w ∧ ∃ f ∈ F, G.Adj w f)) ∧
  ((∀ v ∈ Q, v ∉ (A ∪ B ∪ C) ∪ F) ∧ SPGT.AnticonnectedSet G Q) ∧
  ((∃ a ∈ A, ∃ q ∈ Q, ¬ G.Adj a q) ∧ (∃ b ∈ B, ∃ q ∈ Q, ¬ G.Adj b q)) ∧
  (∀ q ∈ Q, (∃ f ∈ F, G.Adj q f) ∧ (∃ w ∈ A ∪ B ∪ C, G.Adj q w)) ∧
  (∃ u : V, IsLeftStar G A C B u ∧ (∃ f ∈ F, G.Adj u f) ∧ SPGT.VertexComplete G u Q) ∧
  (∀ q ∈ Q, ¬ IsLeftStar G A C B q)

/-! ### Section 12: staircases -/

/-- PAPER (§12, printed p. 69): *"Let `S = (A, C, B)` be a step-connected strip
in `G`, and let `a₀`-`R₀`-`b₀` be a banister of length ≥ 3.  We call the pair
`K = (S, R₀)` a staircase, and define `V(K) = V(R₀) ∪ V(S)`.  (For brevity we
often speak of the staircase `K = (S = (A, C, B), a₀`-`R₀`-`b₀)`, meaning that
`K = (S, R₀)` is a staircase, and `S = (A, C, B)`, and `R₀` has ends `a₀, b₀`,
where `a₀` is a left-star and `b₀` is a right-star.)"*

The arguments mirror the paper's abbreviated notation
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)` exactly: `A, C, B` are the three sets of the
strip `S`, in the printed order, and `a₀, R₀, b₀` are the banister with its
ends, the left-star end first (the parenthesis's "where `a₀` is a left-star and
`b₀` is a right-star" is part of `IsBanister`, by the convention of §11).  "A
banister of length ≥ 3" is `3 ≤ SPGT.pathLength R₀`. -/
def IsStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) : Prop :=
  StepConnected G A C B ∧ IsBanister G A C B a₀ R₀ b₀ ∧ 3 ≤ SPGT.pathLength R₀

/-- PAPER (§12, printed p. 69): *"We call the pair `K = (S, R₀)` a staircase, and
define `V(K) = V(R₀) ∪ V(S)`."*

With `V(S) = A ∪ B ∪ C` and `V(R₀) = {v | v ∈ R₀}`. -/
def staircaseVertices (A C B : Set V) (R₀ : List V) : Set V :=
  {v : V | v ∈ R₀} ∪ (A ∪ B ∪ C)

/-- PAPER (§12, printed p. 69): *"The staircase is maximal if there is no
staircase `(S' = (A', C', B'), a₀'`-`R₀'`-`b₀')` such that `A ⊆ A'`, `B ⊆ B'`,
`C ⊆ C'` and `V(S) ⊂ V(S')`."*

`V(S) ⊂ V(S')` is strict inclusion, i.e. `⊂` of `Set V`.  Being maximal is a
property of a staircase, so `IsStaircase` is a conjunct. -/
def MaximalStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V)
    (b₀ : V) : Prop :=
  IsStaircase G A C B a₀ R₀ b₀ ∧
    ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' : V),
        IsStaircase G A' C' B' a₀' R₀' b₀' ∧
          A ⊆ A' ∧ B ⊆ B' ∧ C ⊆ C' ∧ (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C')

/-- PAPER (§12, printed p. 69): *"Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a
staircase in `G`.  Some definitions (all with respect to `K`): A subset
`X ⊆ V(K)` is local if `X` is a subset of one of `V(S), V(R₀), A ∪ {a₀},
B ∪ {b₀}`."*

The four alternatives are listed in the printed order.  The ambient assumption
`X ⊆ V(K)` is not restated as a conjunct: it is implied by each of the four
alternatives, since `V(S) ⊆ V(K)`, `V(R₀) ⊆ V(K)`, and `a₀, b₀ ∈ V(R₀)`. -/
def LocalForStaircase (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (X : Set V) : Prop :=
  X ⊆ A ∪ B ∪ C ∨ X ⊆ {v : V | v ∈ R₀} ∨ X ⊆ A ∪ {a₀} ∨ X ⊆ B ∪ {b₀}

/-- PAPER (§12, printed p. 69, with respect to a staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)`): *"`v ∈ V(G) \ V(K)` is minor if its set of
neighbours in `V(K)` is local."*

The set of neighbours of `v` in `V(K)` is `G.neighborSet v ∩ V(K)`. -/
def MinorForStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (v : V) : Prop :=
  v ∉ staircaseVertices A C B R₀ ∧
    LocalForStaircase A C B a₀ R₀ b₀ (G.neighborSet v ∩ staircaseVertices A C B R₀)

/- All six §12 notions "with respect to `K`" take the whole staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)` as arguments, in the paper's order, even
where a particular one of them does not mention every component; the linter is
silenced for those. -/
set_option linter.unusedVariables false in
/-- PAPER (§12, printed p. 69, with respect to a staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)`): *"`v ∈ V(G) \ V(K)` is major if it has
neighbours in all of `A, B` and `V(R₀)`."* -/
def MajorForStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (v : V) : Prop :=
  v ∉ staircaseVertices A C B R₀ ∧
    (∃ x ∈ A, G.Adj v x) ∧ (∃ y ∈ B, G.Adj v y) ∧ (∃ z : V, z ∈ R₀ ∧ G.Adj v z)

set_option linter.unusedVariables false in
/-- PAPER (§12, printed p. 69, with respect to a staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)`): *"`v ∈ V(G) \ V(K)` is left-diagonal if `v`
is `(A ∪ {b₀})`-complete, and right-diagonal if it is `(B ∪ {a₀})`-complete."* -/
def LeftDiagonal (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (v : V) : Prop :=
  v ∉ staircaseVertices A C B R₀ ∧ SPGT.VertexComplete G v (A ∪ {b₀})

set_option linter.unusedVariables false in
/-- PAPER (§12, printed p. 69, with respect to a staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)`): *"`v ∈ V(G) \ V(K)` is left-diagonal if `v`
is `(A ∪ {b₀})`-complete, and right-diagonal if it is `(B ∪ {a₀})`-complete."* -/
def RightDiagonal (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (v : V) : Prop :=
  v ∉ staircaseVertices A C B R₀ ∧ SPGT.VertexComplete G v (B ∪ {a₀})

/-- PAPER (§12, printed p. 69, with respect to a staircase
`K = (S = (A, C, B), a₀`-`R₀`-`b₀)`): *"`v ∈ V(G) \ V(K)` is central if it is
`(A ∪ B)`-complete, and is nonadjacent to both `a₀` and `b₀`."* -/
def CentralForStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (v : V) : Prop :=
  v ∉ staircaseVertices A C B R₀ ∧ SPGT.VertexComplete G v (A ∪ B) ∧
    ¬ G.Adj v a₀ ∧ ¬ G.Adj v b₀

/-- PAPER (§12, printed p. 74): *"Now we turn to anticonnected sets of major
vertices.  We have already defined what it is for a staircase to be maximal in
`G`.  We say a staircase `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` is strongly maximal
if it is maximal, and in addition, either `C ≠ ∅`, or there is no staircase
`(S', R')` in `G̅` with `V(S) ⊂ V(S')`."*

The complement `G̅` is `Gᶜ`.  A staircase of `Gᶜ` is again a pair (strip,
banister), written `(S', R')` in the printed order; here `S' = (A', C', B')` and
`R'` is the banister, whose two ends must be named to state that it is one, so
they appear as the bound variables `a₀'` and `b₀'`.  `C ≠ ∅` is `C.Nonempty`. -/
def StronglyMaximalStaircase (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V)
    (b₀ : V) : Prop :=
  MaximalStaircase G A C B a₀ R₀ b₀ ∧
    (C.Nonempty ∨
      ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R' : List V) (b₀' : V),
          IsStaircase Gᶜ A' C' B' a₀' R' b₀' ∧ (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C'))

/-- PAPER (§12, printed p. 74, immediately after the definition of *strongly
maximal*): *"A 2-breaker in `G` is a pair `(K, Q)` such
that*

* *`K = (S = (A, C, B), a₀`-`R₀`-`b₀)` is a strongly maximal staircase in `G`,*
* *`Q ⊆ V(G) \ V(K)` is anticonnected,*
* *some vertex of `A` is `Q`-complete, and some vertex of `B` is `Q`-complete*
* *`a₀, b₀` are not `Q`-complete, and*
* *some vertex of `R₀` is `Q`-complete."*

The pair `(K, Q)` is carried by the staircase data `A, C, B, a₀, R₀, b₀`
together with the set `Q`. -/
def IsTwoBreaker (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (Q : Set V) : Prop :=
  StronglyMaximalStaircase G A C B a₀ R₀ b₀ ∧
  ((∀ q ∈ Q, q ∉ staircaseVertices A C B R₀) ∧ SPGT.AnticonnectedSet G Q) ∧
  ((∃ a ∈ A, SPGT.VertexComplete G a Q) ∧ (∃ b ∈ B, SPGT.VertexComplete G b Q)) ∧
  (¬ SPGT.VertexComplete G a₀ Q ∧ ¬ SPGT.VertexComplete G b₀ Q) ∧
  (∃ r : V, r ∈ R₀ ∧ SPGT.VertexComplete G r Q)

end SPGT

end Workspace.Types.Staircases
