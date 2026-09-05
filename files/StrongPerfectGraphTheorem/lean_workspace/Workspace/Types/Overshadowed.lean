import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# Section 6 vocabulary: overshadowed appearances

Verbatim transcriptions of the `## Definitions` block of
`paper/pdf/S06_Major_attachments_to_a_line_graph.md` (Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem*, published/Annals version, printed pages 28–34).

Conventions (see `paper/spec/CONVENTIONS.md`):

* an *appearance* `L(H)` of `J` in `G` is the pair `(H, K)` of a bipartite subdivision `H` of
  `J` and an induced subgraph `G|K` of `G`, together with an isomorphism
  `φ : H.lineGraph ≃g G.induce K` (`Appearances.IsAppearance`).  The vertices of `L(H)` are
  the *edges* of `H`, and `φ` is the identification that the paper's "equality convention"
  (printed p. 20) makes silent;
* a *track* of `H` is given by the list of its vertices in order (`Tracks.IsTrackList`), a
  *branch* by `Tracks.IsBranch`, and `δ_H(v)` is `Tracks.incidentEdges H v`.

Only the definition of *overshadowed* is transcribed here; see the closing comment for the two
proof-local notions of §6 that are deliberately not formalized.
-/

set_option autoImplicit false

namespace Workspace.Types.Overshadowed

open Workspace.Types.Core Workspace.Types.Tracks Workspace.Types.Appearances
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT Workspace.Types.Appearances.SPGT

namespace SPGT

/-- **Overshadowed appearance** (printed p. 28).

PAPER: *"An appearance `L(H)` of `J` in `G` is overshadowed if there is a branch `B` of `H`
with odd length `≥ 3`, with ends `b₁, b₂`, such that some vertex of `G` is nonadjacent in `G`
to at most one vertex in `δ_H(b₁)` and at most one in `δ_H(b₂)`.  Thus for instance an
appearance is overshadowed if there is a major vertex and some branch has odd length at least
3."*

The second sentence is flagged by the paper as an illustration ("thus for instance"), not as a
further requirement, and so is not part of the definition.

Encoding.  The branch `B` is a track of `H`, given by the list of its vertices in order, with
`Tracks.IsBranch`; its ends `b₁, b₂` are named by `Tracks.IsTrackFrom`.  "Odd length `≥ 3`" is
both conjuncts, `Odd (trackLength B)` and `3 ≤ trackLength B`.

`δ_H(b₁)` is a set of *edges of `H`*, i.e. of *vertices of `L(H)`*, so the phrase "nonadjacent
in `G` to at most one vertex in `δ_H(b₁)`" has to cross between the two sides of the
appearance; exactly as in `Appearances.MajorForLineGraph`, the identification
`φ : H.lineGraph ≃g G.induce K` is therefore an explicit argument.  The set of neighbours of
`v` in `L(H)`, read back as a set of edges of `H`, is
`{e ∈ E(H) | v is adjacent in G to the vertex φ e}`, so the vertices of `δ_H(bᵢ)` that `v` is
*non*adjacent to are the members of `δ_H(bᵢ)` minus that set; "at most one" is
`Set.Subsingleton`.  (`φ` is injective, so counting these as edges of `H` and counting them as
vertices of `G` give the same answer.)

The standing hypothesis "*`L(H)` is an appearance of `J` in `G`*" — i.e.
`Appearances.IsAppearance G J H K` — is supplied by the surrounding statements, following the
style of `Workspace.Types.Appearances`, where such preambles are never built into a
definition; note that the argument `φ` already witnesses the second half of it. -/
def IsOvershadowedAppearance {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) : Prop :=
  ∃ (B : List W) (b₁ b₂ : W),
    IsBranch H B ∧ IsTrackFrom H B b₁ b₂ ∧
    Odd (trackLength B) ∧ 3 ≤ trackLength B ∧
    ∃ v : V,
      (incidentEdges H b₁ \
          {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)}).Subsingleton ∧
      (incidentEdges H b₂ \
          {e : Sym2 W | ∃ he : e ∈ H.edgeSet, G.Adj v (↑(φ ⟨e, he⟩) : V)}).Subsingleton

/-- **Penultimate vertex of a track** (printed p. 32).

PAPER: *"A vertex of a track `P` is penultimate if it is adjacent in `P` to an end of `P`."*

Encoding.  The track `P` is given by the list of its vertices in order; "a vertex of `P`" is
`x ∈ P`; an end of `P` is its first or its last vertex; and "adjacent **in `P`**" means
adjacent in the track — that is, `x` and that end are consecutive on `P`, i.e. `xu` is an edge
of the track (`Tracks.trackEdges`).  Adjacency in the host graph `H` is *not* what is meant: a
track is a subgraph and not an induced subgraph, so `H` may have further edges between vertices
of `P`.

Consequently the notion depends only on the list `P`, and the standing hypothesis "*`P` is a
track (of `H`)*" is supplied at the use sites, exactly as for `Tracks.trackLength`,
`Tracks.trackEdges` and `Tracks.trackInterior`.  The conjunct `x ∈ P` transcribes the paper's
"a vertex of `P`"; it is in fact implied by the second conjunct. -/
def IsPenultimate {W : Type*} (P : List W) (x : W) : Prop :=
  x ∈ P ∧ ∃ u : W, (P.head? = some u ∨ P.getLast? = some u) ∧ s(x, u) ∈ trackEdges P

end SPGT

end Workspace.Types.Overshadowed

/-
Deliberately not formalized in this module.

* **triad** (printed p. 30): *"We say a branch-vertex `b` of `H` is a triad if `b` is incident
  with at most one edge in `X`."*  Here `X` is not ambient data of the section: it is
  introduced at the start of the *proof* of 6.1 as the set of all `Y`-complete vertices of
  `L(H)` for the anticonnected set `Y` fixed there, and the word "triad" occurs only inside
  that proof (claims (4) and (5)).  It appears in no numbered statement — 6.1 is the only
  numbered statement of §6, and none of the thirteen claims of its proof is cited anywhere
  else in the paper.  A standalone `IsTriad` would have to invent a parameter for `X` and,
  with it, a choice of which side of the appearance `X` lives on (the paper can write "edge in
  `X`" for a set `X` of *vertices of `L(H)`* only because of its equality convention).  Per
  the project's faithfulness rules that is an invention rather than a transcription, so the
  term is omitted.  The sentence that follows it in the paper — *"It follows that every triad
  has degree 3 in `H`, and is incident with exactly one edge in each of `X, X₁, X₂`"* — is in
  any case flagged as a consequence, not as part of the definition.

* **`L(H')`** (printed p. 30): *"for every subgraph `H'` of `H` we denote by `L(H')` the
  induced subgraph of `L(H)` formed by the edges of `H'`"* is notation introduced inside the
  proof of 6.1 for readability, not a defined mathematical term, and is likewise not
  transcribed.
-/
