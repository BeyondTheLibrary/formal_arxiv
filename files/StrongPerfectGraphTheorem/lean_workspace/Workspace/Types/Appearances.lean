import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks

/-!
# Appearances of a graph `J` in `G` as a line graph  (§5)

Section 5 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas;
published/Annals version), printed pages 18–25.

This module transcribes the §5 vocabulary attached to the notion of an *appearance*: a
bipartite subdivision `H` of `J` whose line graph `L(H)` sits inside `G` as an induced
subgraph.

**On the "equality convention".**  The paper (printed p. 20) observes that whenever `L(H)` is
isomorphic to an induced subgraph `K` of `G`, one may rename the vertices of `H`'s subdivision
so that `L(H) = K` on the nose, and it then works with `E(H) = V(K)`.  We do **not** silently
identify the two vertex types: an appearance is the pair `(H, K)` together with an isomorphism
`H.lineGraph ≃g G.induce K`.  Wherever a definition genuinely has to move between the two
sides — only `MajorForLineGraph` does — the isomorphism is an explicit argument.

**Standing hypotheses are not built into definitions.**  Following the style of
`Workspace.Types.Core`, a sentence of the form "*Let `H` be bipartite and cyclically
3-connected … we say that `X` saturates `L(H)` if …*" contributes only the material after
"if"; the preamble is a hypothesis of the surrounding statements and is supplied there.
-/

set_option autoImplicit false

namespace Workspace.Types.Appearances

open Workspace.Types.Core Workspace.Types.Tracks
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT

namespace SPGT

/-- **Attachment** (printed p. 20).

PAPER: *"In general, if `F, K` are induced subgraphs of `G` with `V(F ∩ K) = ∅`, a vertex in
`V(K)` is said to be an attachment of `F` (or of `V(F)`) if it has a neighbour in `V(F)`."*

The induced subgraphs `F` and `K` are given by their vertex sets `F K : Set V` (the paper says
"an attachment of `F` (or of `V(F)`)", so the notion depends only on the vertex sets).  The
standing hypothesis `V(F ∩ K) = ∅` is a hypothesis of the surrounding statements, exactly as
disjointness is for `Complete`/`Anticomplete` in `Core`, and so is not part of the definition.
-/
def IsAttachment {V : Type*} (G : SimpleGraph V) (F K : Set V) (v : V) : Prop :=
  v ∈ K ∧ ∃ f ∈ F, G.Adj v f

/-- **The set of attachments of `F` in `K`** (printed p. 20).

PAPER: *"a vertex in `V(K)` is said to be an attachment of `F` (or of `V(F)`) if it has a
neighbour in `V(F)`."*

The set of all attachments of `F` lying in `K`; unfolded, `{k ∈ K | ∃ f ∈ F, G.Adj k f}`. -/
def attachments {V : Type*} (G : SimpleGraph V) (F K : Set V) : Set V :=
  {v : V | IsAttachment G F K v}

/-- **Appearance** (printed p. 20).

PAPER: *"If `G, J` are graphs, we say that `J` appears in `G` if there is a bipartite
subdivision `H` of `J` so that `L(H)` is isomorphic to an induced subgraph of `G`.  We call
`L(H)` an appearance of `J` in `G`."*

An *appearance* is therefore the data of a bipartite subdivision `H` of `J` together with the
induced subgraph of `G` that `L(H)` is isomorphic to.  Induced subgraphs of `G` are the
`G.induce K` for `K : Set V`, and `L(H)` is Mathlib's `H.lineGraph : SimpleGraph H.edgeSet`.
Keeping `K` and the isomorphism explicit is the honest form of the paper's equality convention
(printed p. 20): it records that the vertices of `L(H)` — which are the edges of `H` — are
matched up with the vertices of `G` lying in `K`. -/
def IsAppearance {V U W : Type*} (G : SimpleGraph V) (J : SimpleGraph U) (H : SimpleGraph W)
    (K : Set V) : Prop :=
  IsBipartiteSubdivision J H ∧ Nonempty (H.lineGraph ≃g G.induce K)

/-- **`J` appears in `G`** (printed p. 20).

PAPER: *"If `G, J` are graphs, we say that `J` appears in `G` if there is a bipartite
subdivision `H` of `J` so that `L(H)` is isomorphic to an induced subgraph of `G`."*

"There is a bipartite subdivision `H`" quantifies over all finite graphs, which throughout this
project is rendered by `∃ (n : ℕ) (H : SimpleGraph (Fin n))`. -/
def Appears {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V), IsAppearance G J H K

/-- **Degenerate `L(H)`, for `H` a bipartite subdivision of `K₄`** (printed p. 18).

PAPER: *"If `H` is a bipartite subdivision of `K₄`, we say that `L(H)` is degenerate if there
is a cycle of `H` of length four containing the four vertices of `H` that have degree three in
`H`, and nondegenerate otherwise."*

A cycle of `H` of length four is a subgraph of `H` (not an induced subgraph), so it is given by
four distinct vertices `a, b, c, d` that are cyclically adjacent in `H`.  When `H` is a
subdivision of `K₄`, the vertices of `H` of degree three are exactly its branch-vertices
(vertices of degree `≥ 3`, `Tracks.branchVertices`), and there are exactly four of them; the
cycle *contains* them means that all four are among `a, b, c, d`.

The standing hypothesis "*`H` is a bipartite subdivision of `K₄`*" is supplied at the use
sites (e.g. in 5.1), and so is not part of the definition. -/
def DegenerateK4Appearance {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ a b c d : W,
    [a, b, c, d].Nodup ∧
    H.Adj a b ∧ H.Adj b c ∧ H.Adj c d ∧ H.Adj d a ∧
    branchVertices H ⊆ ({a, b, c, d} : Set W)

/-- **Degenerate appearance** (printed pp. 20–21).

PAPER: *"When `J = K₄`, we have already defined what we mean by a degenerate appearance of
`J`.  When `J ≠ K₄`, let us say that an appearance `L(H)` of `J` in `G` is degenerate if
`J = H = K₃,₃`, and otherwise it is nondegenerate.  So all appearances of any graph
`J ≠ K₄, K₃,₃` are nondegenerate."*

The definition dispatches on whether `J` is `K₄`.  Equality of graphs given on different vertex
types is isomorphism (`Nonempty (· ≃g ·)`), as everywhere in this project.  `K₄` is the
complete graph `⊤ : SimpleGraph (Fin 4)` and `K₃,₃` is `completeBipartiteGraph (Fin 3)
(Fin 3)`.

Whether an appearance is degenerate depends only on `J` and on the subdivision `H` — in the
`K₄` case on the cycle structure of `H`, in the other case on the isomorphism types of `J` and
`H` — so `G` and the induced subgraph are not arguments; a use site always carries the
accompanying `IsAppearance G J H K` hypothesis. -/
def DegenerateAppearance {U W : Type*} (J : SimpleGraph U) (H : SimpleGraph W) : Prop :=
  (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧ DegenerateK4Appearance H) ∨
  (¬ Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)))

/-- **Nondegenerate appearance** (printed pp. 18 and 20–21).

PAPER: *"… we say that `L(H)` is degenerate if there is a cycle of `H` of length four
containing the four vertices of `H` that have degree three in `H`, and nondegenerate
otherwise."*  and  *"let us say that an appearance `L(H)` of `J` in `G` is degenerate if
`J = H = K₃,₃`, and otherwise it is nondegenerate."*

In both cases "nondegenerate" is exactly the negation of "degenerate". -/
def NondegenerateAppearance {U W : Type*} (J : SimpleGraph U) (H : SimpleGraph W) : Prop :=
  ¬ DegenerateAppearance J H

/-- **`J`-enlargement** (printed p. 21).

PAPER: *"If `J` is 3-connected, we say a graph `J'` is a `J`-enlargement if `J'` is
3-connected, and has a proper subgraph which is isomorphic to a subdivision of `J`."*

A subgraph of `J'` is a `SimpleGraph.Subgraph J'` (a set of vertices together with a set of
edges among them), and it is *proper* when it is not the whole of `J'`, i.e. `S ≠ ⊤`.  The
graph that such a subgraph *is* is `S.coe : SimpleGraph S.verts`.  "Isomorphic to a subdivision
of `J`" quantifies over all finite graphs, rendered as usual by
`∃ (n : ℕ) (D : SimpleGraph (Fin n))`.

The preamble "*if `J` is 3-connected*" is a hypothesis of the surrounding statements (e.g. 5.4
begins "Let `J` be a 3-connected graph") and so is not part of the definition; `3`-connectivity
of `J'` — which the paper does state as part of the definition — is `Tracks.IsKConnected J' 3`.
-/
def IsJEnlargement {U U' : Type*} [Fintype U'] (J : SimpleGraph U) (J' : SimpleGraph U') :
    Prop :=
  IsKConnected J' 3 ∧
    ∃ S : J'.Subgraph, S ≠ ⊤ ∧
      ∃ (n : ℕ) (D : SimpleGraph (Fin n)), IsSubdivision J D ∧ Nonempty (S.coe ≃g D)

/-- **`X` saturates `L(H)`** (printed p. 22).

PAPER: *"Let `H` be bipartite and cyclically 3-connected, and let `X` be some set.  We say that
`X` saturates `L(H)` if for every branch-vertex `v` of `H`, at most one edge of `δ_H(v)` is not
in `X` (or equivalently, for every `K₃` subgraph of `L(H)`, at least two of its vertices are in
`X`)."*

The vertices of `L(H)` are the edges of `H`, so `X` is a set of edges of `H` (in 5.7 it is used
with `X ⊆ E(H)`); `δ_H(v)` is `Tracks.incidentEdges H v`.  "At most one edge of `δ_H(v)` is not
in `X`" says that `δ_H(v) \ X` has at most one element, i.e. is a subsingleton.  The
parenthetical reformulation is flagged by the paper as an equivalent, not as a further
requirement, so it is not part of the definition; nor is the preamble "*let `H` be bipartite
and cyclically 3-connected*", which is a hypothesis of the surrounding statements. -/
def SaturatesLineGraph {W : Type*} (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  ∀ v ∈ branchVertices H, (incidentEdges H v \ X).Subsingleton

/-- **Local subset of `V(L(H))`** (printed p. 25).

PAPER: *"Suppose that `L(H)` is an appearance of `J` in `G`.  We recall that `H` is a
subdivision of `J`, and `L(H)` is an induced subgraph of `G`.  If `X ⊆ V(L(H)`, we say that `X`
is local if either `X ⊆ δ_H(v)` for some `v ∈ V(J)`, or `X` is a subset of the edge-set of some
branch of `H`."*

(The published text writes "`X ⊆ V(L(H)`" with an unbalanced parenthesis; the intended reading
is `X ⊆ V(L(H))`.  Since the vertices of `L(H)` are the edges of `H`, `X` is here a set of
edges of `H`.  The precondition `X ⊆ V(L(H))` merely says when the notion is applied — and both
alternatives force it anyway — so it is not a conjunct of the definition.)

`V(J)`, for `H` a subdivision of `J`, is the set of branch-vertices of `H`: the paper records
this as a fact on printed p. 20, *"If `H` is a subdivision of `J` then `V(J)` is the set of
branch-vertices of `H`"*.  Under the standing hypothesis that `L(H)` is an appearance of `J`
(so `H` is a subdivision of `J`), the first alternative below is therefore exactly the printed
one, and it avoids having to expose the embedding of `V(J)` into `V(H)`.  The second
alternative uses `Tracks.IsBranch` and the edge-set `Tracks.trackEdges` of a branch. -/
def LocalForLineGraph {W : Type*} (H : SimpleGraph W) (X : Set (Sym2 W)) : Prop :=
  (∃ v ∈ branchVertices H, X ⊆ incidentEdges H v) ∨
  (∃ q : List W, IsBranch H q ∧ X ⊆ trackEdges q)

/-- **Major vertex, with respect to `L(H)`** (printed p. 25).

PAPER: *"We say a vertex `v ∈ V(G) \ V(L(H))` is major (with respect to `L(H)`) if the set of
its neighbours in `L(H)` saturates `L(H)`."*

This is the one notion of §5 that has to cross between the two sides of an appearance, so the
isomorphism `φ : H.lineGraph ≃g G.induce K` identifying `L(H)` with the induced subgraph of `G`
on `K` is an explicit argument.  `V(L(H))` is then `K`, so `v ∈ V(G) \ V(L(H))` is `v ∉ K`, and
the set of neighbours of `v` in `L(H)`, read back as a set of edges of `H` (= vertices of
`L(H)`), is `{e ∈ E(H) | v is adjacent in G to the vertex φ e}`. -/
def MajorForLineGraph {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (v : V) : Prop :=
  v ∉ K ∧
    SaturatesLineGraph H {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)}

end SPGT

end Workspace.Types.Appearances
