import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio

/-!
# Section 17 vocabulary: reflections of a triangle, and catching a triangle

Verbatim transcriptions of the `## Definitions` block of
`paper/pdf/S17_Another_extension_of_RR.md` (Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem*, published/Annals version, printed pages 102–109).

Conventions (see `paper/spec/CONVENTIONS.md`):

* a triangle is a set of three mutually adjacent vertices, `RousselRubio.IsTriangle`;
* a *connected* subset of `V(G)` is `Core.ConnectedSet` (`(G|X)` is preconnected, so that the
  empty set counts as connected, as the paper requires);
* following `Workspace.Types.RousselRubio`, the standing context of a definition — here "*let
  `{a₁,a₂,a₃}` be a triangle in `G`*", and "*the triangle `{a₁,a₂,a₃}`*" in the definition of
  *catch* — is carried as a conjunct of the definition, exactly as `IsHatForHole` carries
  "*let `C` be a hole in `G`*".
-/

set_option autoImplicit false

namespace Workspace.Types.TriangleCatching

open Workspace.Types.Core Workspace.Types.RousselRubio
open Workspace.Types.Core.SPGT Workspace.Types.RousselRubio.SPGT

namespace SPGT

variable {V : Type*}

/-- **Reflection of a triangle** (printed p. 102).

PAPER: *"Let `{a₁,a₂,a₃}` be a triangle in `G`.  A reflection of this triangle is another
triangle `{b₁,b₂,b₃}` of `G`, disjoint from the first, such that `a₁b₁, a₂b₂, a₃b₃` are edges,
and these are the only edges between the two triangles.  Hence these six vertices induce a
prism."*

The last sentence is flagged by the paper as a consequence ("hence"), not as a further
requirement, and so is not part of the definition.

Encoding.  The definition matches up the two triples vertex by vertex (`aᵢ` with `bᵢ`), so the
six vertices are taken as separate arguments rather than as two sets; the two triangles
themselves are the sets `{a₁,a₂,a₃}` and `{b₁,b₂,b₃}`, and `IsTriangle` already forces each
triple to consist of three distinct, mutually adjacent vertices.

"*`a₁b₁, a₂b₂, a₃b₃` are edges, and these are the only edges between the two triangles*" is a
uniqueness statement, so — as for the "unique edge" bullets of
`RousselRubio.VertexLinkedOntoTriangle` — it is rendered as an *if and only if*: a vertex of
the first triangle and a vertex of the second are adjacent exactly when they are `aᵢ` and `bᵢ`
for the same `i`.  ("Another triangle, disjoint from the first" already implies that the two
triangles are distinct, so that is not a separate conjunct.) -/
def IsReflectionOfTriangle (G : SimpleGraph V) (a₁ a₂ a₃ b₁ b₂ b₃ : V) : Prop :=
  IsTriangle G {a₁, a₂, a₃} ∧
  IsTriangle G {b₁, b₂, b₃} ∧
  Disjoint ({a₁, a₂, a₃} : Set V) ({b₁, b₂, b₃} : Set V) ∧
  ∀ x ∈ ({a₁, a₂, a₃} : Set V), ∀ y ∈ ({b₁, b₂, b₃} : Set V),
    (G.Adj x y ↔ ((x = a₁ ∧ y = b₁) ∨ (x = a₂ ∧ y = b₂) ∨ (x = a₃ ∧ y = b₃)))

/-- **Catching a triangle** (printed p. 102).

PAPER: *"A subset `F` of `V(G)` is said to catch the triangle `{a₁,a₂,a₃}` if it is connected
and disjoint from that triangle and `a₁,a₂,a₃` all have neighbours in `F`."*

Encoding.  The notion is symmetric in `a₁, a₂, a₃`, so the triangle is taken as a set `T`
(which is how 17.1 uses it: "*let `A` be a triangle in a graph `G ∈ F₇`, and let
`F ⊆ V(G) \ A` catch `A`*").  The three conjuncts after `IsTriangle G T` are the paper's three,
in the printed order: `F` is connected (`Core.ConnectedSet`), `F` is disjoint from `T`, and
every vertex of `T` has a neighbour in `F`. -/
def Catches (G : SimpleGraph V) (F T : Set V) : Prop :=
  IsTriangle G T ∧ ConnectedSet G F ∧ Disjoint F T ∧ ∀ a ∈ T, ∃ f ∈ F, G.Adj a f

end SPGT

end Workspace.Types.TriangleCatching

/-
Deliberately not formalized in this module: the two remaining entries of the §17
`## Definitions` block are both proof-local and appear in no numbered statement.

* the **"optimality" of `P, X, Y`** (printed pp. 105–106) is a minimal-counterexample
  convention fixed inside the proof of 17.5, referring to the `P, X, Y` chosen there;
* a **line** (printed p. 106), *"a minimal subpath of `P \ p₁` meeting both `W₁` and `W₂`"*, is
  introduced inside claim (2) of that same proof and refers to `P`, `W₁`, `W₂` bound only
  there.

Section 17 defines no notion called a "strip": the strings `RRstrip`, `RRstrip2` are internal
LaTeX labels of 17.2 and 17.3 in the arXiv source and are never rendered.
-/
