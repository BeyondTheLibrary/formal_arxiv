import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions

/-!
# Section 13: the long odd prism

Transcription of the definitions of Section 13 (*The long odd prism*, printed
pp. 78-86, PDF pp. 80-88) of Chudnovsky-Robertson-Seymour-Thomas, *The Strong
Perfect Graph Theorem* (published version).

Ambient data throughout the section (printed p. 78): a staircase
`K = ((A, C, B), a₀-R₀-b₀)` in a Berge graph `G`, in the encoding fixed by
`Workspace.Types.Staircases` (the strip `S = (A, C, B)` carried by its three
vertex sets, the banister by `a₀ : V`, `R₀ : List V`, `b₀ : V`).  As everywhere
in this project, the hypotheses of the *surrounding sentence* ("let `K` be a
staircase in a Berge graph `G`") are not repeated inside the definitions; they
are supplied by the numbered statements that use them.

Encoding conventions specific to this module.

* The paper's sequence `x₁, …, x_t` is carried by a list `x : List V`, so the
  paper's 1-based `x_i` is `x[i-1]` and, for `i : ℕ` a 0-based index, `x[i]` is
  the paper's `x_{i+1}`.
* The paper's set `X = {x₁, …, x_t}` is `{y : V | y ∈ x}`, and the paper's
  `{x₁, …, x_{i-1}}` (the terms strictly earlier than the term at 0-based
  position `i`) is `x.take i`.
* The paper's `w₁-⋯-w_n` and `v-w₁-⋯-w_n` are again lists of vertices in order.

Two passages of the section are deliberately **not** formalized.

* The opening paragraph (printed pp. 77-78) motivates the construction by
  building a set `X` recursively ("initially let `X` be the set of all
  `B`-complete vertices adjacent to some but not all of `A`.  Then enlarge `X`
  by repeatedly applying the following two rules, in any order …  The process
  eventually stops with some set `X`").  The authors then say *"Let us start
  again, more formally"* and replace that process by the **right-sequence** and
  its three **right-sequence axioms**; the axioms are what is formalized below,
  in `IsRightSequence`.  The same paragraph's informal use of the word "hit"
  ("Any banister `a-R-b` is automatically hit") is not a definition either.
* *"Clearly the trajectory is unique, and is an antipath"* (printed p. 79) is a
  remark about the definition of *trajectory*, flagged by the authors as a
  consequence, so it is not a conjunct of `trajectoryOfIndex`.
-/

namespace Workspace.Types.LongOddPrism

open Workspace.Types.Core Workspace.Types.Prisms Workspace.Types.Staircases
open Workspace.Types.BasicClasses Workspace.Types.Decompositions

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (§13, printed p. 78): *"Let us start again, more formally.  Let
`K = ((A, C, B), a₀-R₀-b₀)` be a staircase in a Berge graph `G`.  We define a
right-sequence to be a sequence `x₁, …, x_t`, with the following properties
(which we refer to as the right-sequence axioms):*

1. *`x₁, …, x_t` are distinct and `B`-complete*
2. *for `1 ≤ i ≤ t`, if `x_i` is `A`-complete then there exists `h` with
   `1 ≤ h < i` such that `x_h` is nonadjacent to `x_i`*
3. *for `1 ≤ i ≤ t`, if `x_i` is `A`-anticomplete then there is a banister
   `r`-`R`-`x_i` such that `r` has a nonneighbour in `{x₁, …, x_{i-1}}`."*

*"Any initial subsequence of a right-sequence is therefore another
right-sequence."*  (That last sentence is a remark, not an axiom.)

The sequence is the list `x`; "distinct" is `x.Nodup`, and the paper's
`{x₁, …, x_{i-1}}`, the set of terms strictly earlier than the term at 0-based
position `i`, is `x.take i`.  The staircase enters only through the strip
`(A, C, B)`: axioms 1 and 2 mention `B` and `A`, and axiom 3 mentions a banister
with respect to `(A, C, B)` (`Staircases.SPGT.IsBanister`, whose left end is
automatically a left-star and whose right end is automatically a right-star). -/
def IsRightSequence (G : SimpleGraph V) (A C B : Set V) (x : List V) : Prop :=
  (x.Nodup ∧ ∀ v ∈ x, SPGT.VertexComplete G v B) ∧
  (∀ (i : ℕ) (_hi : i < x.length), SPGT.VertexComplete G x[i] A →
      ∃ y ∈ x.take i, ¬ G.Adj y x[i]) ∧
  (∀ (i : ℕ) (_hi : i < x.length), SPGT.VertexAnticomplete G x[i] A →
      ∃ (r : V) (R : List V), SPGT.IsBanister G A C B r R x[i] ∧
        ∃ y ∈ x.take i, ¬ G.Adj r y)

/-- PAPER (§13, printed p. 78): *"We say `x_i` is earlier than `x_j` if
`i < j`."*

`Earlier x u v` says that `u` occurs in the right-sequence `x` strictly before
`v` does.  (Since the terms of a right-sequence are distinct, the position of a
term determines it and conversely, so this relation between the *vertices*
`u = x_i` and `v = x_j` is exactly the paper's relation between their
positions.) -/
def Earlier (x : List V) (u v : V) : Prop :=
  ∃ (i j : ℕ) (_hi : i < x.length) (_hj : j < x.length), x[i] = u ∧ x[j] = v ∧ i < j

/-- PAPER (§13, printed p. 78): *"Let `X = {x₁, …, x_t}`.  For each `x_i ∈ X`
that has an earlier nonneighbour, we define its predecessor to be `x_h`, where
`h` is minimum such that `1 ≤ h < i` and `x_h` is nonadjacent to `x_i`."*

`Predecessor G x u p` says that `p` **is the predecessor of** `u` (first the
vertex, then its predecessor): `u` is the term of `x` at some position `i`, `p`
is the term at position `h < i`, `p` is nonadjacent to `u`, and `h` is minimum
with those properties, i.e. every term at a position `k < h` *is* adjacent to
`u`.

The predecessor is a partial function (it exists exactly for those `x_i` that
have an earlier nonneighbour), so it is rendered as a relation; the guard "for
each `x_i ∈ X` that has an earlier nonneighbour" is then automatic, no `p` being
related to a term without an earlier nonneighbour. -/
def Predecessor (G : SimpleGraph V) (x : List V) (u p : V) : Prop :=
  ∃ (i : ℕ) (_hi : i < x.length), x[i] = u ∧
    ∃ (h : ℕ) (_hh : h < i), x[h] = p ∧ ¬ G.Adj x[h] x[i] ∧
      ∀ (k : ℕ) (_hk : k < h), G.Adj x[k] x[i]

/-- PAPER (§13, printed pp. 78-79): *"From the second axiom, every `x_i` either
has a nonneighbour in `A` or a predecessor, so we can follow the sequence of
predecessors until we get to some vertex that is not `A`-complete.  For each
`x_i` we therefore define the trajectory of `x_i` to be the sequence
`w₁-⋯-w_n` with the following properties:*

* *`n ≥ 1`, and `w₁ = x_i`*
* *`w_n` has a nonneighbour in `A`*
* *for `1 ≤ j < n`, `w_j` is `A`-complete, and `w_{j+1}` is the predecessor of
  `w_j`."*

*"Clearly the trajectory is unique, and is an antipath."*

This is the **first** of the section's two `trajectory` definitions: the
trajectory of a vertex `x_i` **of the right-sequence**, identified here by its
position `i` in the list `x` (0-based, so `x[i]` is the paper's `x_{i+1}`).  The
companion definition `trajectoryOfVertex` is the trajectory of a general vertex
`v` of `G`, which is one vertex longer and begins at `v`.

`1 ≤ w.length` is the paper's `n ≥ 1`, and `w.head? = x[i]?` is `w₁ = x_i` (it
also forces `i` to be a legitimate position of `x`, since `w` is non-null).  The
condition `1 ≤ j < n` on the third bullet becomes `j + 1 < w.length` for the
0-based index `j`.  The concluding sentence is a remark of the authors, not a
further requirement, so uniqueness and being an antipath are not conjuncts. -/
def trajectoryOfIndex (G : SimpleGraph V) (A : Set V) (x : List V) (i : ℕ)
    (w : List V) : Prop :=
  (1 ≤ w.length ∧ w.head? = x[i]?) ∧
  (∃ u : V, w.getLast? = some u ∧ ∃ a ∈ A, ¬ G.Adj u a) ∧
  (∀ (j : ℕ) (_hj : j + 1 < w.length),
      SPGT.VertexComplete G w[j] A ∧ Predecessor G x w[j] w[j + 1])

/-- PAPER (§13, printed p. 79): *"If `v ∈ V(G)` is `A`-complete, not in `X` and
not `X`-complete, we define the trajectory of `v` to be the antipath
`v-w₁-⋯-w_n`, where `w₁` is the earliest nonneighbour of `v` in `X`, and
`w₁-⋯-w_n` is the trajectory of `w₁`."*

This is the **second** of the section's two `trajectory` definitions: the
trajectory of a *general* vertex `v` of `G`, as opposed to `trajectoryOfIndex`,
which is the trajectory of a vertex `x_i` of the right-sequence itself.  The two
are different objects: this one starts at `v ∉ X` and its tail is the trajectory
of the earliest nonneighbour of `v` in `X`.

`trajectoryOfVertex G A x v q` says that the list `q` is the trajectory of `v`,
so `q = v :: w` where `w = w₁-⋯-w_n`.  The three conditions of the opening
clause ("`v` is `A`-complete, not in `X` and not `X`-complete") are the paper's
own applicability condition for the definition and are transcribed as the first
conjunct, with `X = {y | y ∈ x}`.  "`w₁` is the earliest nonneighbour of `v` in
`X`" is: `w₁ = x[i]` is a nonneighbour of `v`, and every earlier term `x[k]`
(`k < i`) is a neighbour of `v`. -/
def trajectoryOfVertex (G : SimpleGraph V) (A : Set V) (x : List V) (v : V)
    (q : List V) : Prop :=
  (SPGT.VertexComplete G v A ∧ v ∉ x ∧ ¬ SPGT.VertexComplete G v {y : V | y ∈ x}) ∧
  ∃ (i : ℕ) (_hi : i < x.length) (w : List V),
      (¬ G.Adj v x[i] ∧ ∀ (k : ℕ) (_hk : k < i), G.Adj v x[k]) ∧
      trajectoryOfIndex G A x i w ∧ q = v :: w

/-- PAPER (§13, printed p. 79): *"Let `a` be a left-star.  If it is not
`X`-complete, we define the birth of `a` to be the earliest nonneighbour of `a`
in `X`."*

`birth G A C B x a u` says that `u` **is the birth of** `a`: `a` is a left-star
for the strip `(A, C, B)`, `a` is not `X`-complete (with `X = {y | y ∈ x}`), and
`u = x[i]` is the earliest nonneighbour of `a` in `X`, i.e. `a` is nonadjacent
to `x[i]` and adjacent to every earlier term `x[k]`, `k < i`.

The birth is a partial function, so it is rendered as a relation; the paper's
guard "if it is not `X`-complete" is transcribed literally, and is in any case
implied by the existence of the nonneighbour `x[i]`. -/
def birth (G : SimpleGraph V) (A C B : Set V) (x : List V) (a u : V) : Prop :=
  SPGT.IsLeftStar G A C B a ∧ ¬ SPGT.VertexComplete G a {y : V | y ∈ x} ∧
    ∃ (i : ℕ) (_hi : i < x.length),
      x[i] = u ∧ ¬ G.Adj a x[i] ∧ ∀ (k : ℕ) (_hk : k < i), G.Adj a x[k]

/-- PAPER (§13, printed p. 79): *"Now let `b` be a right-star.  A banister
`a`-`R`-`b` is said to be `b`-optimal if `a` is not `X`-complete, and there is
no banister `a'`-`R'`-`b` such that `a'` is not `X`-complete and the birth of
`a'` is earlier than the birth of `a`."*

That `b` is a right-star, and that `a` is a left-star, are part of
`Staircases.SPGT.IsBanister` (by the convention of §11, the left-star end of a
banister is listed first), so the opening sentence needs no separate conjunct.
`X` is `{y | y ∈ x}`, "the birth of `a'`" and "the birth of `a`" are the
vertices `u'` and `u` related to `a'` and `a` by `birth`, and "earlier" is
`Earlier` — the paper's order on the terms of the right-sequence. -/
def BOptimalBanister (G : SimpleGraph V) (A C B : Set V) (x : List V) (a : V)
    (R : List V) (b : V) : Prop :=
  SPGT.IsBanister G A C B a R b ∧
  ¬ SPGT.VertexComplete G a {y : V | y ∈ x} ∧
  ¬ ∃ (a' : V) (R' : List V), SPGT.IsBanister G A C B a' R' b ∧
      ¬ SPGT.VertexComplete G a' {y : V | y ∈ x} ∧
      ∃ u' u : V, birth G A C B x a' u' ∧ birth G A C B x a u ∧ Earlier x u' u

/-- PAPER (§13, printed p. 83): *"Now we are ready to apply 13.2 to produce a
skew partition.  Let us say a 3-breaker in `G` is a pair `(K, x)` such that
`K = (S = (A, C, B), a₀-R₀-b₀)` is a strongly maximal staircase in `G`, and
`x ∈ V(G) \ V(K)` is `B`-complete, and not `A`-complete, and not
`A`-anticomplete."*

The pair `(K, x)` is carried by the staircase data `A, C, B, a₀, R₀, b₀`
together with the vertex `x`, exactly as `Staircases.SPGT.IsTwoBreaker` carries
the pair `(K, Q)`.  `V(K)` is `Staircases.SPGT.staircaseVertices`. -/
def IsThreeBreaker (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V)
    (b₀ : V) (x : V) : Prop :=
  SPGT.StronglyMaximalStaircase G A C B a₀ R₀ b₀ ∧
  x ∉ SPGT.staircaseVertices A C B R₀ ∧
  SPGT.VertexComplete G x B ∧
  ¬ SPGT.VertexComplete G x A ∧
  ¬ SPGT.VertexAnticomplete G x A

/-- PAPER (§13, printed p. 86): *"Let us say a graph `G` is recalcitrant if:*

* *`G` is Berge*
* *`G` and `Ḡ` are not line graphs, and `G` is not a double split graph*
* *`G` and `Ḡ` do not admit proper 2-joins, and*
* *`G` does not admit a proper homogeneous pair or balanced skew partition."*

The four conjuncts below are the four printed bullets, in the printed order.

Reading of the second bullet.  *"are not line graphs"* abbreviates *"are not
line graphs of bipartite graphs"*, the class occurring in the definition of
*basic* in Section 1 (printed p. 2: *"`G` is basic if either `G` or `Ḡ` is
bipartite or is the line graph of a bipartite graph, or is a double split
graph"*).  This is the reading forced by the sentence that immediately follows
13.5 (printed p. 86), *"Clearly any counterexample to 1.3 is recalcitrant, so
13.5 will imply 1.3"*: a counterexample to 1.3 is a Berge graph that is not
basic and admits none of the decompositions, so what it fails to be is a line
graph **of a bipartite graph**.  Accordingly the bullet is rendered with
`BasicClasses.SPGT.IsLineGraphOfBipartite`.

The paper's `Ḡ` is `Gᶜ`; note that the second and fourth bullets say `G` only
(`Ḡ` is not required to fail to be a double split graph, nor to fail to admit a
proper homogeneous pair or a balanced skew partition), while the second half of
the second bullet and the third and fourth bullets use the *proper* forms of the
2-join and of the homogeneous pair, as in the published text. -/
def Recalcitrant (G : SimpleGraph V) : Prop :=
  SPGT.Berge G ∧
  (¬ SPGT.IsLineGraphOfBipartite G ∧ ¬ SPGT.IsLineGraphOfBipartite Gᶜ ∧
    ¬ SPGT.IsDoubleSplitGraph G) ∧
  (¬ SPGT.AdmitsProper2Join G ∧ ¬ SPGT.AdmitsProper2Join Gᶜ) ∧
  (¬ SPGT.AdmitsProperHomogeneousPair G ∧ ¬ SPGT.AdmitsBalancedSkewPartition G)

end SPGT

end Workspace.Types.LongOddPrism
