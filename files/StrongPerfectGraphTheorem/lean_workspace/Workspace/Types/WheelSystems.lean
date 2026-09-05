import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels

/-!
# Sections 19, 20, 22 — frames, wheel systems, diamonds, squares, kites and tails

Verbatim sources: `paper/pdf/S19_Wheel_systems.md`,
`paper/pdf/S20_Diamond_and_square_wheel_systems.md`,
`paper/pdf/S22_Wheels_and_tails.md` (the `## Definitions` blocks of each).
Every definition below quotes the paper's own sentence and cites the *printed*
page of `perfect.pdf` (the published, July 19 2005 revision).

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a vertex set is a `Set V`; `V(C)` for a list `C` is `{v | v ∈ C}`;
* a hole is the list of its vertices in cyclic order (`SPGT.IsHoleList`), a path
  the list of its vertices in order (`SPGT.IsPathList`);
* the paper's `X`-complete is `SPGT.VertexComplete`, connected/anticonnected are
  `SPGT.ConnectedSet` / `SPGT.AnticonnectedSet`;
* a cyclically consecutive block of a list `H` is `S <+: H.rotate k` for some
  `k : ℕ`.

**Data shape for a wheel system.**  A wheel system is a *sequence* `x₀,…,x_t`,
and sections 20–22 constantly build new systems out of old ones by truncating
and appending (`x₀,…,x_r,x_{t+1}`).  It is therefore represented by a function
`x : ℕ → V` together with its *height* `t : ℕ`; only the values `x 0, …, x t`
are constrained by any of the definitions below.
-/

namespace Workspace.Types.WheelSystems

open Workspace.Types.Core Workspace.Types.Wheels

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (printed p. 116): *"Let `G` be a graph.  A frame in `G` is a pair
`(z, A₀)`, where `z ∈ V(G)`, and `A₀` is a nonnull connected subset of
`V(G) \ {z}`, containing no neighbours of `z`."*

Encoding notes.

* *"nonnull"* is `A₀.Nonempty`, *"connected"* is `SPGT.ConnectedSet G A₀`.
* *"subset of `V(G) \ {z}`"* is `z ∉ A₀` (every `Set V` is a subset of `V(G)`).
* *"containing no neighbours of `z`"* is `∀ v ∈ A₀, ¬ G.Adj z v`.  This is a
  genuinely separate condition from `z ∉ A₀`, since `z` is not adjacent to
  itself; both conjuncts are stated. -/
def IsFrame (G : SimpleGraph V) (z : V) (A₀ : Set V) : Prop :=
  A₀.Nonempty ∧ SPGT.ConnectedSet G A₀ ∧ z ∉ A₀ ∧ ∀ v ∈ A₀, ¬ G.Adj z v

/-- PAPER (printed p. 116): *"Let `x₀,…,x_t` be a wheel system of height `t`.
For `1 ≤ i ≤ t` we define `Xᵢ = {x₀,…,xᵢ}` ..."*

`wheelSystemX x i` is the paper's `Xᵢ`, the set of the first `i + 1` terms of the
sequence.  The paper only names `Xᵢ` for `1 ≤ i ≤ t`, but the formula makes sense
for every `i : ℕ` and is used here at every index (in particular `X₀ = {x₀}`
occurs implicitly as `{x₀,…,x_{i-1}}` with `i = 1`).  It does not depend on `G`,
`z` or `A₀`. -/
def wheelSystemX (x : ℕ → V) (i : ℕ) : Set V := {v : V | ∃ j ≤ i, v = x j}

/-- PAPER (printed p. 116): *"... and we define `Aᵢ` to be the maximal connected
subset of `V(G)` that includes `A₀`, contains no neighbour of `z`, and contains
no `Xᵢ`-complete vertex.  So for each `i`, `A_{i-1} ⊆ Aᵢ`."*

Encoding note — why the union realises the paper's *maximal* set.  Write
`𝒜` for the family of all `A : Set V` that include `A₀`, are connected, contain
no neighbour of `z`, and contain no `Xᵢ`-complete vertex; `wheelSystemA` is
`⋃₀ 𝒜`.  This union is itself a member of `𝒜`, and hence is its greatest
element, i.e. exactly the paper's `Aᵢ`:

* it includes `A₀`, since `A₀ ∈ 𝒜` whenever `(z, A₀)` is a frame and no vertex of
  `A₀` is `Xᵢ`-complete — and in any case every member of `𝒜` includes `A₀`;
* the last two conditions ("contains no neighbour of `z`", "contains no
  `Xᵢ`-complete vertex") are *pointwise* conditions on the members of the set,
  so they are inherited by any union of sets satisfying them;
* connectedness is inherited too: all the sets united contain the *nonempty*
  set `A₀`, so any two vertices of the union are joined through `A₀` inside the
  union.

The paper's `A₀` is not `wheelSystemA … 0`: `A₀` is the given part of the frame,
whereas `wheelSystemA … 0` is built from `X₀ = {x₀}`.  So no separate
`wheelSystemA0` is defined. -/
def wheelSystemA (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (i : ℕ) : Set V :=
  ⋃₀ {A : Set V | A₀ ⊆ A ∧ SPGT.ConnectedSet G A ∧ (∀ v ∈ A, ¬ G.Adj z v) ∧
        (∀ v ∈ A, ¬ SPGT.VertexComplete G v (wheelSystemX x i))}

/-- PAPER (printed p. 116): *"For the moment, fix a frame `(z, A₀)`.  With
respect to the given frame, a wheel system in `G` of height `t ≥ 1` is a sequence
`x₀,…,x_t` of distinct vertices of `G \ (A₀ ∪ {z})`, satisfying the following
conditions:*

1. *`A₀` contains neighbours of `x₀` and of `x₁`, and no vertex in `A₀` is
   `{x₀,x₁}`-complete.*
2. *For `2 ≤ i ≤ t`, there is a connected subset of `V(G)` including `A₀`,
   containing a neighbour of `xᵢ`, containing no neighbour of `z`, and containing
   no `{x₀,…,x_{i−1}}`-complete vertex.*
3. *For `1 ≤ i ≤ t`, `xᵢ` is not `{x₀,…,x_{i−1}}`-complete.*
4. *`z` is adjacent to all of `x₀,…,x_t`."*

PAPER (printed p. 116), a remark following the definition: *"Note that this
definition is symmetric between `x₀, x₁`, so `x₁, x₀, x₂,…,x_t` is another wheel
system."*  That is a remark about the definition, not a further condition, and so
is not part of the `def`.

PAPER (printed p. 116), a second remark: *"Note that condition 2 above just says
that `xᵢ` has a neighbour in `A_{i−1}`."*  Also a remark; condition 2 is
formalized below in the existential form in which it is printed, not via
`wheelSystemA`.

Encoding notes.

* *"of height `t ≥ 1`"* is `1 ≤ t`.
* *"a sequence `x₀,…,x_t` of distinct vertices"* constrains only the first `t + 1`
  values of `x : ℕ → V`: they are pairwise distinct.
* *"of `G \ (A₀ ∪ {z})`"* is `x j ∉ A₀ ∧ x j ≠ z` for every `j ≤ t`.
* `{x₀,x₁}` in condition 1 is the two-element set `{x 0, x 1}` (which is `X₁`),
  and `{x₀,…,x_{i−1}}` in conditions 2 and 3 is `wheelSystemX x (i - 1)`; both
  conditions are guarded by `1 ≤ i`, so the natural subtraction `i - 1` is the
  intended one. -/
def IsWheelSystem (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) : Prop :=
  1 ≤ t ∧
  (∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k) ∧
  (∀ j ≤ t, x j ∉ A₀ ∧ x j ≠ z) ∧
  ((∃ a ∈ A₀, G.Adj (x 0) a) ∧ (∃ a ∈ A₀, G.Adj (x 1) a) ∧
    ∀ a ∈ A₀, ¬ SPGT.VertexComplete G a ({x 0, x 1} : Set V)) ∧
  (∀ i, 2 ≤ i → i ≤ t →
    ∃ B : Set V, A₀ ⊆ B ∧ SPGT.ConnectedSet G B ∧ (∃ b ∈ B, G.Adj (x i) b) ∧
      (∀ v ∈ B, ¬ G.Adj z v) ∧
      (∀ v ∈ B, ¬ SPGT.VertexComplete G v (wheelSystemX x (i - 1)))) ∧
  (∀ i, 1 ≤ i → i ≤ t → ¬ SPGT.VertexComplete G (x i) (wheelSystemX x (i - 1))) ∧
  (∀ j ≤ t, G.Adj z (x j))

/-- PAPER (printed p. 116): *"Let `x₀,…,x_t` be a wheel system, and let `Y` be a
nonempty anticonnected subset of `V(G) \ (A₀ ∪ {z})`.  We say `Y` is a hub for the
wheel system if `z, x₀,…,x_{t−1}` are all `Y`-complete and `x_t` is not."*

Encoding notes.

* The preamble *"Let `x₀,…,x_t` be a wheel system"* and the standing hypotheses on
  `Y` are conjuncts of the definition, so that `IsHubForWheelSystem` is exactly
  the paper's relation "`Y` is a hub for the wheel system `x₀,…,x_t`".
* *"subset of `V(G) \ (A₀ ∪ {z})`"* is `y ∉ A₀ ∧ y ≠ z` for every `y ∈ Y`.  This
  is the hub condition of §19 and is deliberately *not* the same as the
  disjointness condition in the `Y`-diamond / `Y`-square preamble of §20, which
  is disjointness from `{z, x₀,…,x_t}`.
* *"`z, x₀,…,x_{t−1}` are all `Y`-complete"*: since `1 ≤ t`, the indices
  `0,…,t−1` are exactly the `i` with `i < t`. -/
def IsHubForWheelSystem (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (Y : Set V) : Prop :=
  IsWheelSystem G z A₀ x t ∧
  Y.Nonempty ∧ SPGT.AnticonnectedSet G Y ∧ (∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z) ∧
  SPGT.VertexComplete G z Y ∧
  (∀ i < t, SPGT.VertexComplete G (x i) Y) ∧
  ¬ SPGT.VertexComplete G (x t) Y

/-- PAPER (printed p. 123), the common preamble: *"Let `x₀,…,x_t` be a wheel
system, and define `Xᵢ, Aᵢ` as usual.  Let `Y ⊆ V(G)` be nonempty and
anticonnected, such that `Y` is disjoint from `{z, x₀,…,x_t}`, and `x₀,…,x_{t−1}`
are all `Y`-complete and `x_t` is not.  We say `x₀,…,x_t` is a*

*   *`Y`-diamond if `t ≥ 3`, `x_t` is `X_{t−2}`-complete, and `x_t` has a
    neighbour in `A_{t−2}`"*

Encoding notes.

* The common preamble is part of the definition, so `IsYDiamond` is exactly the
  paper's relation "`x₀,…,x_t` is a `Y`-diamond".
* *"`Y` is disjoint from `{z, x₀,…,x_t}`"* is `z ∉ Y` together with `x i ∉ Y` for
  every `i ≤ t`.  Note this is a *different* condition from the hub condition
  `Y ⊆ V(G) \ (A₀ ∪ {z})` of §19; the two are kept distinct.
* Since `t ≥ 3`, the natural subtraction in `X_{t−2}` and `A_{t−2}` is the
  intended one. -/
def IsYDiamond (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (Y : Set V) : Prop :=
  IsWheelSystem G z A₀ x t ∧
  Y.Nonempty ∧ SPGT.AnticonnectedSet G Y ∧ (z ∉ Y ∧ ∀ i ≤ t, x i ∉ Y) ∧
  (∀ i < t, SPGT.VertexComplete G (x i) Y) ∧
  ¬ SPGT.VertexComplete G (x t) Y ∧
  3 ≤ t ∧
  SPGT.VertexComplete G (x t) (wheelSystemX x (t - 2)) ∧
  (∃ a ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x t) a)

/-- PAPER (printed p. 123), the common preamble: *"Let `x₀,…,x_t` be a wheel
system, and define `Xᵢ, Aᵢ` as usual.  Let `Y ⊆ V(G)` be nonempty and
anticonnected, such that `Y` is disjoint from `{z, x₀,…,x_t}`, and `x₀,…,x_{t−1}`
are all `Y`-complete and `x_t` is not.  We say `x₀,…,x_t` is a*

*   *`Y`-square if `t ≥ 3`, `x_t` is adjacent to `x_{t−1}`, `x_t` has no
    neighbour in `A_{t−2}`, and there is a vertex in `A_{t−1}` adjacent to `x_t`
    with a neighbour in `A_{t−2}`"*

Encoding notes are as for `IsYDiamond`: the common preamble is part of the
definition, *"`Y` is disjoint from `{z, x₀,…,x_t}`"* is `z ∉ Y` and `x i ∉ Y` for
`i ≤ t`, and `t ≥ 3` makes the natural subtractions in `A_{t−1}`, `A_{t−2}` the
intended ones.  The last bullet clause is read as printed: some `a ∈ A_{t−1}` is
adjacent to `x_t` *and* has a neighbour in `A_{t−2}`. -/
def IsYSquare (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (Y : Set V) : Prop :=
  IsWheelSystem G z A₀ x t ∧
  Y.Nonempty ∧ SPGT.AnticonnectedSet G Y ∧ (z ∉ Y ∧ ∀ i ≤ t, x i ∉ Y) ∧
  (∀ i < t, SPGT.VertexComplete G (x i) Y) ∧
  ¬ SPGT.VertexComplete G (x t) Y ∧
  3 ≤ t ∧
  G.Adj (x t) (x (t - 1)) ∧
  (∀ a ∈ wheelSystemA G z A₀ x (t - 2), ¬ G.Adj (x t) a) ∧
  (∃ a ∈ wheelSystemA G z A₀ x (t - 1),
    G.Adj a (x t) ∧ ∃ b ∈ wheelSystemA G z A₀ x (t - 2), G.Adj a b)

/-- PAPER (printed p. 124): *"A `Y`-diamond `x₀,…,x_t` is said to be polished if
`t ≥ 4`, `x_{t−1}` is not `X_{t−3}`-complete, `x_t` has no neighbour in `A_{t−3}`,
`x_{t−1}` has a neighbour in `A_{t−3}`, and there is a vertex in `A_{t−2}`
adjacent to both `x_t, x_{t−1}` with a neighbour in `A_{t−3}`."*

So a polished `Y`-diamond is a `Y`-diamond satisfying, in addition, those five
conditions; `t ≥ 4` makes the natural subtractions in `X_{t−3}`, `A_{t−3}`,
`A_{t−2}` the intended ones. -/
def IsPolishedYDiamond (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (Y : Set V) : Prop :=
  IsYDiamond G z A₀ x t Y ∧
  4 ≤ t ∧
  ¬ SPGT.VertexComplete G (x (t - 1)) (wheelSystemX x (t - 3)) ∧
  (∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a) ∧
  (∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a) ∧
  (∃ a ∈ wheelSystemA G z A₀ x (t - 2),
    G.Adj a (x t) ∧ G.Adj a (x (t - 1)) ∧
      ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj a b)

/-- PAPER (printed p. 136): *"If `(C,Y)` is a wheel in `G`, and there is no wheel
`(C',Y')` with `Y ⊂ Y'`, we say `(C,Y)` is an optimal wheel."*

Encoding notes.

* `SPGT.IsWheel` is the §16 notion of a wheel (rim `C`, hub `Y`).
* The maximality is over the **hub only**: the rim `C'` of the competing wheel is
  unconstrained, and `⊂` is *strict* inclusion of sets. -/
def OptimalWheel (G : SimpleGraph V) (C : List V) (Y : Set V) : Prop :=
  SPGT.IsWheel G C Y ∧ ¬ ∃ (C' : List V) (Y' : Set V), SPGT.IsWheel G C' Y' ∧ Y ⊂ Y'

/-- PAPER (printed p. 136): *"Let `(C,Y)` be a wheel in `G`.  A kite for `(C,Y)`
is a vertex `y ∈ V(G) \ (Y ∪ V(C))`, not `Y`-complete, that has at least four
neighbours in `C`, three of which are consecutive and `Y`-complete."*

Encoding notes.

* The preamble *"Let `(C,Y)` be a wheel in `G`"* is a conjunct, so `IsKite` is
  exactly the paper's relation "`y` is a kite for `(C,Y)`".
* *"`y ∈ V(G) \ (Y ∪ V(C))`"* is `y ∉ Y` and `y ∉ C`.
* *"at least four neighbours in `C`"* counts the vertices of the rim adjacent to
  `y`: `4 ≤ {c | c ∈ C ∧ G.Adj y c}.ncard`.  The rim has no repeated vertex
  (`SPGT.IsHoleList` includes `Nodup`), so counting the vertex *set* is the
  intended count.
* *"three of which are consecutive and `Y`-complete"*: three of those neighbours,
  say `a, b, c`, occupy three **cyclically** consecutive positions of the hole
  `C` — rendered `∃ k : ℕ, [a, b, c] <+: C.rotate k` — and each is `Y`-complete.
  Only one orientation of the triple is needed, since `a, b, c` are existentially
  quantified. -/
def IsKite (G : SimpleGraph V) (C : List V) (Y : Set V) (y : V) : Prop :=
  SPGT.IsWheel G C Y ∧
  y ∉ Y ∧ y ∉ C ∧
  ¬ SPGT.VertexComplete G y Y ∧
  4 ≤ {c : V | c ∈ C ∧ G.Adj y c}.ncard ∧
  (∃ a b c : V, (∃ k : ℕ, [a, b, c] <+: C.rotate k) ∧
    G.Adj y a ∧ G.Adj y b ∧ G.Adj y c ∧
    SPGT.VertexComplete G a Y ∧ SPGT.VertexComplete G b Y ∧ SPGT.VertexComplete G c Y)

/-- PAPER (printed p. 136): *"Let `(C,Y)` be a wheel in `G`, let `z ∈ V(C)`, and
let `x₀, x₁` be the neighbours of `z` in `C`.  A path `T` of `G \ {x₀,x₁}` from
`z` to `V(C) \ {z,x₀,x₁}` is called a tail for `z` (with respect to the wheel
`(C,Y)`) if*

*   *`x₀, z, x₁` are all `Y`-complete, and there is a `Y`-complete edge in
    `C \ {x₀,z,x₁}`*
*   *the neighbour of `z` in `T` is adjacent to `x₀, x₁`, and*
*   *no internal vertex of `T` is in `Y` or is `Y`-complete."*

This is the **published** three-bullet definition.  (The earlier arXiv draft has
six bullets: it forbids *all* vertices of `T` — not only the internal ones — from
lying in `Y`, and it folds in "no vertex of `G` is a kite for `(C,Y)`".  The
published version promotes that last clause to an explicit hypothesis of 22.4, so
the published notion of tail is strictly weaker and 22.5 correspondingly
stronger.  Nothing from the draft is imported here.)

Encoding notes.

* The preamble is part of the definition: `(C,Y)` is a wheel, `z ∈ V(C)`, and
  `x₀, x₁` are *the* neighbours of `z` in `C` — two distinct vertices of `C`
  adjacent to `z` such that every vertex of `C` adjacent to `z` is one of them.
* *"a path `T` of `G \ {x₀,x₁}`"* is `SPGT.IsPathList` together with
  `∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁`.
* *"from `z` to `V(C) \ {z,x₀,x₁}`"*: the first vertex of `T` is `z` and its last
  vertex is some `w ∈ C` with `w ∉ {z, x₀, x₁}`.
* *"the neighbour of `z` in `T`"* is the second vertex of `T`, exhibited by the
  list shape `T = z :: y :: R`.
* *"a `Y`-complete edge in `C \ {x₀,z,x₁}`"* is an edge of the rim
  (`SPGT.EdgeComplete`, which already contains `G.Adj`) both of whose ends are
  vertices of `C` other than `x₀, z, x₁`.
* *"internal vertex"* is a vertex of `SPGT.interior T`, the paper's `T*`. -/
def IsTail (G : SimpleGraph V) (C : List V) (Y : Set V) (z : V) (x₀ x₁ : V)
    (T : List V) : Prop :=
  SPGT.IsWheel G C Y ∧
  z ∈ C ∧
  (x₀ ≠ x₁ ∧ x₀ ∈ C ∧ x₁ ∈ C ∧ G.Adj z x₀ ∧ G.Adj z x₁ ∧
    ∀ c ∈ C, G.Adj z c → c = x₀ ∨ c = x₁) ∧
  (∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁) ∧
  (∃ w : V, SPGT.IsPathFrom G T z w ∧ w ∈ C ∧ w ≠ z ∧ w ≠ x₀ ∧ w ≠ x₁) ∧
  ((SPGT.VertexComplete G x₀ Y ∧ SPGT.VertexComplete G z Y ∧
      SPGT.VertexComplete G x₁ Y) ∧
    ∃ u v : V, u ∈ C ∧ v ∈ C ∧
      (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧ (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧
      SPGT.EdgeComplete G Y u v) ∧
  (∃ (y : V) (R : List V), T = z :: y :: R ∧ G.Adj y x₀ ∧ G.Adj y x₁) ∧
  (∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ SPGT.VertexComplete G v Y)

end SPGT

end Workspace.Types.WheelSystems
