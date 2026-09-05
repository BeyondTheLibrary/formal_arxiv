import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels

/-!
# Section 18 — pseudowheels

Verbatim source: `paper/pdf/S18_Pseudowheels.md`, `## Definitions` block (the two
definitions of the section: *pseudowheel*, printed p. 109, at the very start of
Section 18; and *optimal*, printed p. 111, placed between 18.4 and 18.5).  Each
definition below quotes the paper's own sentence.

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a path is the list `P` of its vertices in order (`SPGT.IsPathList`), and the
  paper's `p₁`-`⋯`-`pₙ` names the entries of that list in order, so `n` is
  `P.length`;
* "`P` is a path of `G \ (X ∪ Y)`" is `SPGT.IsPathList G P` together with the
  requirement that no vertex of `P` lies in `X ∪ Y`;
* the ends `p₁, pₙ` of `P` are pinned down by `SPGT.IsPathFrom G P p₁ pₙ`, and the
  second vertex `p₂` by `P.tail.head? = some p₂`;
* a vertex set is a `Set V`, and `v` is `X`-complete iff `SPGT.VertexComplete G v X`.
-/

namespace Workspace.Types.Pseudowheels

open Workspace.Types.Core Workspace.Types.Wheels

namespace SPGT

variable {V : Type*}

/-- PAPER (printed p. 109): *"Let us say a pseudowheel in a graph `G` is a triple
`(X,Y,P)`, satisfying:*

* `X,Y` *are disjoint nonempty anticonnected subsets of* `V(G)`*, complete to each
  other*
* `P` *is a path* `p₁`-`⋯`-`pₙ` *of* `G \ (X ∪ Y)`*, where* `n ≥ 5`
* `p₁,pₙ` *are the only* `X`*-complete vertices of* `P`
* `p₁` *is* `Y`*-complete, and so is at least one other vertex of* `P`*; and*
  `p₂,pₙ` *are not* `Y`*-complete."*

PAPER (printed p. 109, immediately following, published version only): *"A wheel
`(C,Y)` with a `Y`-segment `S` of length one can be viewed as a pseudowheel,
taking `X` to consist of one of the vertices of `S`.  We recommend that the
reader think of a general pseudowheel as such an odd wheel, where a vertex of `S`
has 'blown up' to become the anticonnected set `X`."*  That paragraph is offered
by the paper as intuition for the reader (relating this notion to
`Workspace.Types.Wheels.SPGT.IsWheel` and
`Workspace.Types.Wheels.SPGT.IsSegment`), not as a further condition, so it is
recorded here and not formalized.

Encoding notes.

* *"disjoint"* is `Disjoint X Y`; *"nonempty"* is `.Nonempty`; *"anticonnected"*
  is `SPGT.AnticonnectedSet`.
* *"complete to each other"* is `SPGT.Complete G X Y`: every vertex of `X` is
  adjacent to every vertex of `Y`.  Since adjacency is symmetric this is the same
  condition as `SPGT.Complete G Y X`, so one of the two suffices.
* *"`P` is a path `p₁`-`⋯`-`pₙ` of `G \ (X ∪ Y)`, where `n ≥ 5`"*: `P` is a path
  of `G` (in the paper's sense, so induced) none of whose vertices lies in `X` or
  in `Y`, with at least `5` vertices.  The names `p₁, p₂, pₙ` used in the last two
  bullets are the first, second and last entries of `P`.
* *"`p₁,pₙ` are the only `X`-complete vertices of `P`"* is an "if and only if" over
  the vertices of `P`: it asserts both that `p₁` and `pₙ` are `X`-complete and that
  no other vertex of `P` is.
* *"at least one other vertex of `P`"* is a vertex of `P` different from `p₁`. -/
def IsPseudowheel (G : SimpleGraph V) (X Y : Set V) (P : List V) : Prop :=
  (Disjoint X Y ∧ X.Nonempty ∧ Y.Nonempty ∧
      SPGT.AnticonnectedSet G X ∧ SPGT.AnticonnectedSet G Y ∧
      SPGT.Complete G X Y) ∧
  ∃ p₁ p₂ pₙ : V,
    (SPGT.IsPathFrom G P p₁ pₙ ∧ P.tail.head? = some p₂ ∧
        (∀ v ∈ P, v ∉ X ∧ v ∉ Y) ∧ 5 ≤ P.length) ∧
    (∀ v ∈ P, SPGT.VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ)) ∧
    (SPGT.VertexComplete G p₁ Y ∧
        (∃ v ∈ P, v ≠ p₁ ∧ SPGT.VertexComplete G v Y) ∧
        ¬ SPGT.VertexComplete G p₂ Y ∧ ¬ SPGT.VertexComplete G pₙ Y)

/-- PAPER (printed p. 111): *"A pseudowheel `(X,Y,P)` in `G` is optimal if*

* *there is no pseudowheel* `(X',Y',P')` *in* `G` *such that the number of*
  `Y'`*-complete vertices in* `P'` *is less than the number of* `Y`*-complete
  vertices in* `P`*, and*
* *there is no pseudowheel* `(X,Y',P)` *in* `G` *such that* `Y ⊂ Y'`*."*

Encoding notes.

* The paper's subject is *a pseudowheel* `(X,Y,P)`, so `IsPseudowheel G X Y P` is
  part of the definition.
* *"the number of `Y'`-complete vertices in `P'`"* is the number of vertices of the
  path `P'` that are `Y'`-complete, i.e. `Set.ncard` of
  `{v | v ∈ P' ∧ SPGT.VertexComplete G v Y'}`.  This set is finite (it is a set of
  entries of a list), so its `ncard` is its genuine cardinality, and no
  decidability or finiteness assumption on `V` is needed.
* The second bullet quantifies over `Y'` only: `X` and `P` are the very same `X`
  and `P`.  The paper's `⊂` is proper inclusion, which is Lean's `Y ⊂ Y'`;
  reading it as `⊆` would make the condition unsatisfiable, since `Y' := Y` always
  gives a pseudowheel `(X,Y,P)`. -/
def OptimalPseudowheel (G : SimpleGraph V) (X Y : Set V) (P : List V) : Prop :=
  IsPseudowheel G X Y P ∧
  (¬ ∃ (X' Y' : Set V) (P' : List V),
      IsPseudowheel G X' Y' P' ∧
      {v : V | v ∈ P' ∧ SPGT.VertexComplete G v Y'}.ncard <
        {v : V | v ∈ P ∧ SPGT.VertexComplete G v Y}.ncard) ∧
  (¬ ∃ Y' : Set V, IsPseudowheel G X Y' P ∧ Y ⊂ Y')

end SPGT

end Workspace.Types.Pseudowheels
