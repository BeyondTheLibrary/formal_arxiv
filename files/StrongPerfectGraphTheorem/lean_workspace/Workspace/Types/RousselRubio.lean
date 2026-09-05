import Mathlib
import Workspace.Types.Core

/-!
# Section 2 vocabulary: the Roussel–Rubio lemma

Verbatim transcriptions of the `## Definitions` block of
`paper/pdf/S02_Roussel_Rubio.md` (Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem*, printed pages 8–12).

Conventions (see `paper/spec/CONVENTIONS.md`):

* a path of the paper is given by the list `p : List V` of its vertices in
  order, together with `SPGT.IsPathList G p`; its vertex set `V(P)` is
  `{v | v ∈ p}`;
* a hole is given by the list `c : List V` of its vertices in cyclic order,
  together with `SPGT.IsHoleList G c`;
* the paper's `G \ e` (delete the edge `e`) is Mathlib's
  `G.deleteEdges {s(u, v)}`.
-/

namespace Workspace.Types.RousselRubio

open Workspace.Types.Core

namespace SPGT

open Workspace.Types.Core.SPGT

variable {V : Type*}

/-- PAPER (printed p. 8): *"Let `P` be a path in `G` (we remind the reader that
this means `P` is an induced subgraph which is a path), of length `≥ 2`, and let
the vertices of `P` be `p₁,…,pₙ` in order.  A leap for `P` (in `G`) is a pair of
nonadjacent vertices `a,b` of `G` such that there are exactly six edges of `G`
between `a,b` and `V(P)`, namely `ap₁, ap₂, apₙ, bp₁, bpₙ₋₁, bpₙ`."*

The standing hypothesis of the definition — that `P` is a path of `G` of length
at least `2` — is carried as the first two conjuncts.

"There are exactly six edges of `G` between `a,b` and `V(P)`, **namely** …" is
rendered as an *if and only if*: for each of the two vertices `a` and `b`, and
for each vertex `pᵢ` of `P`, adjacency to `pᵢ` holds precisely for the listed
indices.  With `a ≠ b` and `n ≥ 3` the six listed pairs are pairwise distinct,
so this says exactly that the edges between `{a,b}` and `V(P)` number six and
are the six printed ones.  In `0`-based indexing `p₁ = p[0]`, `p₂ = p[1]`,
`pₙ₋₁ = p[n-2]` and `pₙ = p[n-1]`.

Nothing further need be assumed: `a, b ∉ V(P)` already follows, since
`a ∈ V(P)` would make one of the required adjacencies a loop or would contradict
inducedness of `P`. -/
def IsLeapForPath (G : SimpleGraph V) (p : List V) (a b : V) : Prop :=
  IsPathList G p ∧ 2 ≤ pathLength p ∧
    a ≠ b ∧ ¬ G.Adj a b ∧
    (∀ (i : ℕ) (hi : i < p.length),
        (G.Adj a (p[i]'hi) ↔ (i = 0 ∨ i = 1 ∨ i = p.length - 1))) ∧
    (∀ (i : ℕ) (hi : i < p.length),
        (G.Adj b (p[i]'hi) ↔ (i = 0 ∨ i = p.length - 2 ∨ i = p.length - 1)))

/-- PAPER (printed p. 9): *"A triangle in `G` is a set of three vertices,
mutually adjacent."* -/
def IsTriangle (G : SimpleGraph V) (T : Set V) : Prop :=
  T.ncard = 3 ∧ ∀ u ∈ T, ∀ v ∈ T, u ≠ v → G.Adj u v

/-- PAPER (printed p. 9): *"We say a vertex `v` can be linked onto a triangle
`{a₁,a₂,a₃}` (via paths `P₁,P₂,P₃`) if:*

* *the three paths `P₁,P₂,P₃` are mutually vertex-disjoint*
* *for `i = 1,2,3` `aᵢ` is an end of `Pᵢ`*
* *for `1 ≤ i < j ≤ 3`, `aᵢaⱼ` is the unique edge of `G` between `V(Pᵢ)` and
  `V(Pⱼ)`*
* *`v` has a neighbour in each of `P₁,P₂` and `P₃`."*

The third bullet is a uniqueness statement, so it is rendered as an *if and only
if*: a vertex of `Pᵢ` and a vertex of `Pⱼ` are adjacent exactly when they are
`aᵢ` and `aⱼ`.  (Together with the second bullet this already gives
`G.Adj aᵢ aⱼ`, and together with the first bullet it gives `aᵢ ≠ aⱼ`; hence
`{a₁,a₂,a₃}` is automatically a triangle and that is not repeated here.)

"`aᵢ` is an end of `Pᵢ`" means `aᵢ` is the first or the last vertex of the
list `pᵢ`. -/
def VertexLinkedOntoTriangle (G : SimpleGraph V) (v a₁ a₂ a₃ : V)
    (p₁ p₂ p₃ : List V) : Prop :=
  (IsPathList G p₁ ∧ IsPathList G p₂ ∧ IsPathList G p₃) ∧
  ((∀ x ∈ p₁, x ∉ p₂) ∧ (∀ x ∈ p₁, x ∉ p₃) ∧ (∀ x ∈ p₂, x ∉ p₃)) ∧
  ((p₁.head? = some a₁ ∨ p₁.getLast? = some a₁) ∧
    (p₂.head? = some a₂ ∨ p₂.getLast? = some a₂) ∧
    (p₃.head? = some a₃ ∨ p₃.getLast? = some a₃)) ∧
  ((∀ x ∈ p₁, ∀ y ∈ p₂, (G.Adj x y ↔ (x = a₁ ∧ y = a₂))) ∧
    (∀ x ∈ p₁, ∀ y ∈ p₃, (G.Adj x y ↔ (x = a₁ ∧ y = a₃))) ∧
    (∀ x ∈ p₂, ∀ y ∈ p₃, (G.Adj x y ↔ (x = a₂ ∧ y = a₃)))) ∧
  ((∃ x ∈ p₁, G.Adj v x) ∧ (∃ x ∈ p₂, G.Adj v x) ∧ (∃ x ∈ p₃, G.Adj v x))

/-- PAPER (printed p. 9): *"We say a vertex `v` can be linked onto a triangle
`{a₁,a₂,a₃}` (via paths `P₁,P₂,P₃`) if: …"*

The "can be linked" form: some choice of the three paths witnesses
`VertexLinkedOntoTriangle`.  This is the phrase used in 2.4 ("suppose `v` can be
linked onto a triangle `{a₁,a₂,a₃}`"). -/
def VertexCanBeLinkedOntoTriangle (G : SimpleGraph V) (v a₁ a₂ a₃ : V) : Prop :=
  ∃ p₁ p₂ p₃ : List V, VertexLinkedOntoTriangle G v a₁ a₂ a₃ p₁ p₂ p₃

/-- PAPER (printed p. 10): *"We already said what we mean by linking a vertex
onto a triangle, but now we do the same for an anticonnected set.  We say an
anticonnected set `X` can be linked onto a triangle `{a₁,a₂,a₃}` (via paths
`P₁,P₂,P₃`) if:*

* *the three paths `P₁,P₂,P₃` are mutually vertex-disjoint*
* *for `i = 1,2,3` `aᵢ` is an end of `Pᵢ`*
* *for `1 ≤ i < j ≤ 3`, `aᵢaⱼ` is the unique edge of `G` between `V(Pᵢ)` and
  `V(Pⱼ)`*
* *each of `P₁,P₂` and `P₃` contains an `X`-complete vertex."*

The first three bullets are literally those of `VertexLinkedOntoTriangle`; only
the fourth differs.  Anticonnectedness of `X` is *not* built in: the paper
states it as a separate hypothesis at each place where the notion is used
(e.g. 2.8: "let `X` be an anticonnected set, and suppose `X` can be linked …").
`X`-completeness of a vertex is `Core`'s `VertexComplete G x X`. -/
def SetLinkedOntoTriangle (G : SimpleGraph V) (X : Set V) (a₁ a₂ a₃ : V)
    (p₁ p₂ p₃ : List V) : Prop :=
  (IsPathList G p₁ ∧ IsPathList G p₂ ∧ IsPathList G p₃) ∧
  ((∀ x ∈ p₁, x ∉ p₂) ∧ (∀ x ∈ p₁, x ∉ p₃) ∧ (∀ x ∈ p₂, x ∉ p₃)) ∧
  ((p₁.head? = some a₁ ∨ p₁.getLast? = some a₁) ∧
    (p₂.head? = some a₂ ∨ p₂.getLast? = some a₂) ∧
    (p₃.head? = some a₃ ∨ p₃.getLast? = some a₃)) ∧
  ((∀ x ∈ p₁, ∀ y ∈ p₂, (G.Adj x y ↔ (x = a₁ ∧ y = a₂))) ∧
    (∀ x ∈ p₁, ∀ y ∈ p₃, (G.Adj x y ↔ (x = a₁ ∧ y = a₃))) ∧
    (∀ x ∈ p₂, ∀ y ∈ p₃, (G.Adj x y ↔ (x = a₂ ∧ y = a₃)))) ∧
  ((∃ x ∈ p₁, VertexComplete G x X) ∧ (∃ x ∈ p₂, VertexComplete G x X) ∧
    (∃ x ∈ p₃, VertexComplete G x X))

/-- PAPER (printed p. 10): *"We say an anticonnected set `X` can be linked onto
a triangle `{a₁,a₂,a₃}` (via paths `P₁,P₂,P₃`) if: …"*

The "can be linked" form: some choice of the three paths witnesses
`SetLinkedOntoTriangle`.  As above, anticonnectedness of `X` is left to the
surrounding statement. -/
def SetCanBeLinkedOntoTriangle (G : SimpleGraph V) (X : Set V) (a₁ a₂ a₃ : V) :
    Prop :=
  ∃ p₁ p₂ p₃ : List V, SetLinkedOntoTriangle G X a₁ a₂ a₃ p₁ p₂ p₃

/-- PAPER (printed p. 11): *"Let `C` be a hole in `G`, and let `e = uv` be an
edge of it.  A leap for `C` (in `G`, at `uv`) is a leap for the path `C \ e` in
`G \ e`."*

Encoding.  `c` lists the vertices of the hole `C` in cyclic order.  "`e = uv` is
an edge of `C`" means that `u` and `v` are cyclically consecutive in `c`; the
two arguments are named in the cyclic order of `c`, so that `v` is the
successor of `u`.  Cutting the cycle at `e` leaves the path `C \ e` on the same
vertex set, running from `v` round to `u`; as a list this is the rotation of `c`
whose first vertex is `v` and whose last vertex is `u` (`List.rotate i` moves
the first `i` entries to the back, so its rotations are exactly the cyclic
shifts of `c`).  The existence of such a rotation is precisely the statement
that `uv` is an edge of `C`.  The paper's `G \ e` is `G.deleteEdges {s(u, v)}`.

The requirement that this list is a path of `G \ e` of length `≥ 2` is part of
`IsLeapForPath`; for a hole (which has at least four vertices) it holds
automatically. -/
def IsLeapForHole (G : SimpleGraph V) (c : List V) (u v a b : V) : Prop :=
  IsHoleList G c ∧
    ∃ i : ℕ, (c.rotate i).head? = some v ∧ (c.rotate i).getLast? = some u ∧
      IsLeapForPath (G.deleteEdges {s(u, v)}) (c.rotate i) a b

/-- PAPER (printed p. 11): *"A hat for `C` (in `G`, at `uv`) is a vertex of `G`
adjacent to `u` and `v` and to no other vertex of `C`."*

The standing context of the previous sentence — *"Let `C` be a hole in `G`, and
let `e = uv` be an edge of it"* — is carried as the first conjuncts.  "`uv` is
an edge of `C`" is stated here as `u, v ∈ V(C)` together with `G.Adj u v`: by
`IsHoleList` two vertices of `c` are adjacent in `G` exactly when they are
cyclically consecutive, so this is literally "`uv` is an edge of the hole", and
it is symmetric in `u` and `v` as the unordered edge `e = uv` is.

"To no other vertex of `C`" means: to no vertex of `C` besides `u` and `v`. -/
def IsHatForHole (G : SimpleGraph V) (c : List V) (u v h : V) : Prop :=
  IsHoleList G c ∧ u ∈ c ∧ v ∈ c ∧ G.Adj u v ∧
    G.Adj h u ∧ G.Adj h v ∧
    (∀ x ∈ c, x ≠ u → x ≠ v → ¬ G.Adj h x)

end SPGT

end Workspace.Types.RousselRubio
