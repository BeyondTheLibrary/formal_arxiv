import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# `J`-strip systems  (§8, "Generalized line graphs")

Section 8 of *The Strong Perfect Graph Theorem* (Chudnovsky, Robertson, Seymour, Thomas;
published / *Annals* version), printed pages 39–47.

Section 8 assembles, for each edge `uv` of a 3-connected graph `J`, *all* the alternative
rungs joining the two ends into a single "strip" `S_{uv}`.  The resulting object is a
`J`-strip system, a common generalisation of an appearance of `J` as a line graph.

**Data shape.**  For `J : SimpleGraph U` and `G : SimpleGraph V`, a `J`-strip system is the
pair of families

* `S : U → U → Set V`, indexed by the *edges* of `J` (so `S u v = S v u`; only the values at
  edges of `J` play any role), and
* `N : U → Set V`, indexed by the vertices of `J`.

Both `S_{uv} ⊆ V(G)` and `N_v ⊆ V(G)` are automatic, since `V(G)` is the whole type `V`.

**Standing hypotheses are not built into definitions.**  Following `Workspace.Types.Core` and
`Workspace.Types.Appearances`, a preamble such as "*Let `J` be 3-connected, and let `G` be
Berge*", or a precondition such as "*`X ⊆ V(S,N)`*", is a hypothesis of the surrounding
numbered statements and is supplied there, not baked into the definition.
-/

set_option autoImplicit false

namespace Workspace.Types.StripSystems

open Workspace.Types.Core Workspace.Types.Tracks Workspace.Types.Appearances

namespace SPGT

/-- **`uv`-rung** (printed p. 39).

PAPER: *"… satisfying the following conditions (for `uv ∈ E(J)`, a `uv`-rung means a path `R`
of `G` with ends `s,t` say, where `V(R) ⊆ S_{uv}`, and `s` is the unique vertex of `R` in
`N_u`, and `t` is the unique vertex of `R` in `N_v`):"*

The notion is introduced for `uv ∈ E(J)`, so that hypothesis is the first conjunct.  A path of
`G` is `Core.IsPathList` (an *induced* subgraph, non-null, connected, not a cycle, all degrees
`≤ 2`), presented as the list `R` of its vertices in order, and `V(R)` is `{x | x ∈ R}`.  The
paper's "*with ends `s,t` say*" merely names the two ends; here `s` is taken to be the first
and `t` the last entry of the list (`Core.IsPathFrom`), which fixes no extra content because
the reverse of a path is a path.

*"`s` is the unique vertex of `R` in `N_u`"* is rendered by `∀ x ∈ R, (x ∈ N u ↔ x = s)`:
instantiating at `x = s` (which lies on `R`, being its first vertex) gives `s ∈ N_u`, and the
other instances give the uniqueness.  Likewise for `t` and `N_v`.  Both uniqueness clauses are
part of the definition. -/
def IsUVRung {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (u v : U) (R : List V) : Prop :=
  J.Adj u v ∧
    ∃ s t : V, SPGT.IsPathFrom G R s t ∧
      (∀ x ∈ R, x ∈ S u v) ∧
      (∀ x ∈ R, (x ∈ N u ↔ x = s)) ∧
      (∀ x ∈ R, (x ∈ N v ↔ x = t))

/-- **`J`-strip system `(S,N)` in `G`** (printed p. 39).

PAPER: *"Let `J` be 3-connected, and let `G` be Berge.  A `J`-strip system `(S,N)` in `G`
means:*

* *for each edge `uv` of `J`, a subset `S_{uv} = S_{vu} ⊆ V(G)`*
* *for each vertex `v` of `J`, a subset `N_v ⊆ V(G)`*

*satisfying the following conditions (for `uv ∈ E(J)`, a `uv`-rung means a path `R` of `G` with
ends `s,t` say, where `V(R) ⊆ S_{uv}`, and `s` is the unique vertex of `R` in `N_u`, and `t` is
the unique vertex of `R` in `N_v`):*

* *The sets `S_{uv}` `(uv ∈ E(J))` are pairwise disjoint*
* *For each `u ∈ V(J)`, `N_u ⊆ ⋃(S_{uv} : v ∈ V(J)` adjacent to `u)`*
* *For each `uv ∈ E(J)`, every vertex of `S_{uv}` is in a `uv`-rung*
* *If `uv, wx ∈ E(J)` with `u,v,w,x` all distinct, then there are no edges between `S_{uv}` and
  `S_{wx}`*
* *If `uv, uw ∈ E(J)` with `v ≠ w`, then `N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`, and
  there are no other edges between `S_{uv}` and `S_{uw}`*
* *For each `uv ∈ E(J)` there is a special `uv`-rung such that for every cycle `C` of `J`, the
  sum of the lengths of the special `uv`-rungs for `uv ∈ E(C)` has the same parity as
  `|V(C)|`."*

Notes on the transcription.

* The preamble "*Let `J` be 3-connected, and let `G` be Berge*" is a hypothesis of the numbered
  statements of §8 and is supplied there; `S_{uv} ⊆ V(G)` and `N_v ⊆ V(G)` are automatic.  The
  displayed equation `S_{uv} = S_{vu}` — which is what makes an `U → U → Set V` family really
  indexed by the *edges* of `J` — is the first conjunct below.
* Edges of `J` are compared as `Sym2` elements, so "*the sets `S_{uv}` `(uv ∈ E(J))` are
  pairwise disjoint*" is disjointness of `S u v` and `S w x` for `s(u,v) ≠ s(w,x)`.
* "*there are no edges between …*" is `Core.Anticomplete`, and "*complete to*" is
  `Core.Complete`.  "*and there are no other edges between `S_{uv}` and `S_{uw}`*" says that
  any edge of `G` between `S_{uv}` and `S_{uw}` is one of the edges just listed, i.e. that both
  of its ends lie in `N_u`.
* In the last axiom the published text designates, once and for all, **one special `uv`-rung
  for each edge `uv`**, *before* quantifying over the cycles `C`; that is what makes the axiom
  well-formed.  It is rendered by an existentially quantified family `R : U → U → List V` with
  `R u v` a `uv`-rung for every edge `uv`, followed by the parity condition for every cycle.
  A *cycle* `C` of `J` here is a cycle in the ordinary (non-induced) sense; it is given by the
  list `c` of its vertices in cyclic order, so `c` has at least three entries, no repeated
  entry, and cyclically consecutive entries — the pairs in `c.zip (c.rotate 1)` — are adjacent
  in `J`.  Those same pairs are exactly the edges `uv ∈ E(C)`, one per edge, so the sum of the
  lengths of the special rungs over `E(C)` is the sum of `pathLength (R u v)` over that list,
  and `|V(C)| = c.length`.

The sentence that follows the definition in the paper — *"It follows that for distinct
`u,v ∈ V(J)`, `N_u ∩ N_v` is empty if `u`,`v` are nonadjacent, and otherwise
`N_u ∩ N_v ⊆ S_{uv}`; and for `uv ∈ E(J)` and `w ∈ V(J)`, if `w ≠ u,v` then
`S_{uv} ∩ N_w = ∅`"* — is flagged by the authors as a *consequence* ("It follows that"), not as
a further axiom, and so is deliberately not included. -/
def IsJStripSystem {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) : Prop :=
  -- "for each edge `uv` of `J`, a subset `S_{uv} = S_{vu} ⊆ V(G)`"
  (∀ u v : U, J.Adj u v → S u v = S v u) ∧
  -- "The sets `S_{uv}` `(uv ∈ E(J))` are pairwise disjoint"
  (∀ u v w x : U, J.Adj u v → J.Adj w x → s(u, v) ≠ s(w, x) →
      Disjoint (S u v) (S w x)) ∧
  -- "For each `u ∈ V(J)`, `N_u ⊆ ⋃(S_{uv} : v ∈ V(J)` adjacent to `u)`"
  (∀ u : U, N u ⊆ ⋃ (v : U) (_ : J.Adj u v), S u v) ∧
  -- "For each `uv ∈ E(J)`, every vertex of `S_{uv}` is in a `uv`-rung"
  (∀ u v : U, J.Adj u v → ∀ x ∈ S u v, ∃ R : List V, IsUVRung G J S N u v R ∧ x ∈ R) ∧
  -- "If `uv, wx ∈ E(J)` with `u,v,w,x` all distinct, then there are no edges between
  -- `S_{uv}` and `S_{wx}`"
  (∀ u v w x : U, J.Adj u v → J.Adj w x → [u, v, w, x].Nodup →
      SPGT.Anticomplete G (S u v) (S w x)) ∧
  -- "If `uv, uw ∈ E(J)` with `v ≠ w`, then `N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`, and
  -- there are no other edges between `S_{uv}` and `S_{uw}`"
  (∀ u v w : U, J.Adj u v → J.Adj u w → v ≠ w →
      (SPGT.Complete G (N u ∩ S u v) (N u ∩ S u w) ∧
        ∀ a ∈ S u v, ∀ b ∈ S u w, G.Adj a b → (a ∈ N u ∧ b ∈ N u))) ∧
  -- "For each `uv ∈ E(J)` there is a *special* `uv`-rung such that for every cycle `C` of `J`,
  -- the sum of the lengths of the special `uv`-rungs for `uv ∈ E(C)` has the same parity as
  -- `|V(C)|`."
  (∃ R : U → U → List V,
      (∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v)) ∧
      ∀ c : List U, 3 ≤ c.length → c.Nodup →
        (∀ p ∈ c.zip (c.rotate 1), J.Adj p.1 p.2) →
        ((c.zip (c.rotate 1)).map (fun p => SPGT.pathLength (R p.1 p.2))).sum
          ≡ c.length [MOD 2])

/-- **A choice of rungs *forms* `L(H)`** (printed p. 40, immediately after the proof of 8.1).

PAPER: *"For each edge `uv` of `J`, choose a `uv`-rung `R_{uv}`.  It follows from 8.1 and the
final axiom above that the subgraph of `G` induced on the union of the vertex sets of these
rungs is a line graph of a bipartite subdivision `H` of `J`.  For brevity we say that this
choice of rungs forms `L(H)`."*

A *choice of rungs* is a family `R : U → U → List V` with `R u v` a `uv`-rung for each edge
`uv` of `J`; the union of the vertex sets of these rungs is
`⋃ (uv ∈ E(J)), {x | x ∈ R u v}`.  "*The subgraph of `G` induced on that union is a line graph
of a bipartite subdivision `H` of `J`*" is exactly `Appearances.IsAppearance G J H K` for `K`
that union: `H` is a bipartite subdivision of `J`, and `L(H) = H.lineGraph` is isomorphic to
`G.induce K`. -/
def FormsLineGraph {V U W : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (R : U → U → List V) (H : SimpleGraph W) : Prop :=
  (∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v)) ∧
    SPGT.IsAppearance G J H (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v})

/-- **Nondegenerate `J`-strip system** (printed p. 40, immediately after the proof of 8.2).

PAPER: *"A `J`-strip system is nondegenerate if there is some choice of rungs such that the
line graph `L(H)` they form is a nondegenerate appearance of `J`."*

"*Some choice of rungs*" is an existentially quantified family `R`, and the graph `H` it forms
is an arbitrary finite graph, rendered as everywhere in this project by
`∃ (n : ℕ) (H : SimpleGraph (Fin n))`.  Nondegeneracy of the appearance is
`Appearances.NondegenerateAppearance J H`. -/
def NondegenerateStripSystem {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) : Prop :=
  ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V),
    FormsLineGraph G J S N R H ∧ SPGT.NondegenerateAppearance J H

/-- **`V(S,N)`** (printed p. 40, immediately after the proof of 8.3).

PAPER: *"Given a `J`-strip system `(S,N)`, we define `V(S,N) = ⋃(S_{uv} : uv ∈ E(J))`.  Hence
every `N_v ⊆ V(S,N)`."*

The union is over the edges of `J`, so only `J` and the family `S` occur on the right-hand side
(the paper's notation `V(S,N)` mentions `N` for symmetry only); the second sentence,
"*Hence every `N_v ⊆ V(S,N)`*", is flagged as a consequence of the second axiom of a `J`-strip
system and so is not part of the definition. -/
def stripSystemVertices {V U : Type*} (J : SimpleGraph U) (S : U → U → Set V) : Set V :=
  ⋃ (u : U) (v : U) (_ : J.Adj u v), S u v

/-- **`N_{uv}`** (printed p. 40, same paragraph).

PAPER: *"If `u,v ∈ V(J)` are adjacent, we define `N_{uv} = N_u ∩ S_{uv}`.  So every vertex of
`N_u` belongs to `N_{uv}` for exactly one `v`.  Note that `N_{uv}` is in general different from
`N_{vu}`, but `S_{uv}` and `S_{vu}` mean the same thing."*

The hypothesis "*`u,v ∈ V(J)` are adjacent*" says when the notation is used; the sentence
"*every vertex of `N_u` belongs to `N_{uv}` for exactly one `v`*" is a consequence of the
`J`-strip system axioms and is not part of the definition.  As the paper notes, this operation
is **not** symmetric in `u` and `v`. -/
def stripSystemNuv {V U : Type*} (S : U → U → Set V) (N : U → Set V) (u v : U) : Set V :=
  N u ∩ S u v

/-- **`X` *saturates* the strip system** (printed p. 40, same paragraph).

PAPER: *"We say `X ⊆ V(S,N)` saturates the strip system if for every `u ∈ V(J)`, there is at
most one neighbour `v` of `u` in `J` such that `N_{uv} ⊄ X`;"*

"*At most one*" is `Set.Subsingleton` of the set of those neighbours `v`.  The precondition
`X ⊆ V(S,N)` records where the notion is applied (at the only use, `MajorForStripSystem`, it
holds automatically) and, as in `Appearances.LocalForLineGraph`, is not made a conjunct. -/
def SaturatesStripSystem {V U : Type*} (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (X : Set V) : Prop :=
  ∀ u : U, {v : U | J.Adj u v ∧ ¬ (stripSystemNuv S N u v ⊆ X)}.Subsingleton

/-- **Major vertex, with respect to the strip system** (printed p. 40, same paragraph).

PAPER: *"and a vertex `y ∈ V(G) \ V(S,N)` is major (with respect to the strip system) if the
set of its neighbours in `V(S,N)` saturates `(S,N)`."*

`V(G) \ V(S,N)` is `y ∉ stripSystemVertices J S`, and the set of neighbours of `y` in `V(S,N)`
is `G.neighborSet y ∩ stripSystemVertices J S`. -/
def MajorForStripSystem {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (y : V) : Prop :=
  y ∉ stripSystemVertices J S ∧
    SaturatesStripSystem J S N (G.neighborSet y ∩ stripSystemVertices J S)

/-- **Local subset, with respect to the strip system** (printed p. 40, same paragraph).

PAPER: *"We say `X ⊆ V(S,N)` is local (with respect to the strip system) if either
`X ⊆ N_v` for some `v ∈ V(J)`, or `X ⊆ S_{uv}` for some edge `uv ∈ E(J)`."*

`V(J)` is the whole vertex type `U`, so "*for some `v ∈ V(J)`*" is `∃ v : U`; "*for some edge
`uv ∈ E(J)`*" is `∃ u v : U, J.Adj u v ∧ …`.  As above, the precondition `X ⊆ V(S,N)` records
where the notion is applied and is not a conjunct. -/
def LocalForStripSystem {V U : Type*} (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (X : Set V) : Prop :=
  (∃ v : U, X ⊆ N v) ∨ (∃ u v : U, J.Adj u v ∧ X ⊆ S u v)

/-- **Maximal `J`-strip system** (printed p. 42, immediately after the proof of 8.4).

PAPER: *"A `J`-strip system `(S,N)` in `G` is maximal if there is no `J`-strip system `(S',N')`
in `G` such that `V(S,N) ⊂ V(S',N')`, and `S'_{uv} ∩ V(S,N) = S_{uv}` for every `uv ∈ E(J)`,
and `N_v ⊆ N'_v` for every `v ∈ V(J)`."*

`V(S,N) ⊂ V(S',N')` is the *proper* inclusion `⊂` of `Set V`.  The preamble "*a `J`-strip
system `(S,N)` in `G`*" is a hypothesis of 8.5 and is supplied there, so `IsJStripSystem G J S
N` is not a conjunct here; being a `J`-strip system *is* of course demanded of the competitor
`(S',N')`, since the paper says so explicitly. -/
def MaximalStripSystem {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) : Prop :=
  ¬ ∃ (S' : U → U → Set V) (N' : U → Set V),
      IsJStripSystem G J S' N' ∧
      stripSystemVertices J S ⊂ stripSystemVertices J S' ∧
      (∀ u v : U, J.Adj u v → S' u v ∩ stripSystemVertices J S = S u v) ∧
      (∀ v : U, N v ⊆ N' v)

/-- **Strip of the strip system** (printed p. 42, same paragraph).

PAPER: *"We need to analyze maximal strip systems.  For an edge `uv ∈ E(J)`, we call the set
`S_{uv}` a strip of the strip system."*

So a set `T ⊆ V(G)` is a strip of `(S,N)` exactly when `T = S_{uv}` for some edge `uv` of
`J`. -/
def IsStripOfStripSystem {V U : Type*} (J : SimpleGraph U) (S : U → U → Set V) (T : Set V) :
    Prop :=
  ∃ u v : U, J.Adj u v ∧ T = S u v

end SPGT

end Workspace.Types.StripSystems

/-
Deliberate omissions from §8.

The section also introduces the *fork number* of a choice of rungs (printed p. 41), a
*saturated* choice of rungs (printed p. 41), a *broad* choice of rungs together with the
notation `r_{uv}`, `r_{vu}` (printed p. 43), the *traversal* for a choice of rungs (printed
p. 44), and an *optimal* choice of rungs (printed p. 44).  Each of these is **proof-local**: it
is defined inside the proof of 8.4 or of 8.5 and refers to data (`X`, `F`, `K`) bound only
there, and none of them occurs in any numbered statement of the paper.  They are therefore not
formalized here.
-/
