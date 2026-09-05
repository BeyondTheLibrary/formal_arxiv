import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.DoubleDiamond
import Workspace.Types.Wheels
import Workspace.Types.Pseudowheels

/-!
# The classes `F₁, …, F₁₁`  (§1, printed pages 6–7)

Transcription of the eleven classes of Berge graphs introduced in Section 1 of
Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*
(published/*Annals* version).  They are the scaffolding of 1.8 and are quantified
over throughout Sections 16–24.

PAPER (printed p. 6), the preamble: *"Let `F₁,…,F₁₁` be the classes of Berge
graphs defined as follows (each is a subclass of the previous class):"*

## Two quirks of the printed text, reproduced and not repaired

Both are present in the arXiv draft as well; see `AMBIGUITIES.md` §A2.  The rule
of this project is to formalize **what is printed**, not what the preamble
claims.

1. **`F₅` is defined from `F₃`, not from `F₄`.**  The preamble asserts that each
   class is a subclass of the previous one, but the printed bullet reads
   *"`F₅` is the class of all `G ∈ F₃` such that …"* — exactly as `F₄` does.
   Accordingly `InF5` below unfolds `InF3`, not `InF4`.  (The same slippage
   appears in 1.8(4), whose hypothesis is `G ∈ F₁` while its conclusion is
   `G ∈ F₄ ⊆ F₃`.)

2. **`F₂` is defined for "all graphs `G`", not for "all Berge graphs `G`".**  The
   printed bullet reads *"`F₂` is the class of all graphs `G` such that …"*, so
   no Bergeness hypothesis is added to `InF2`.  Nothing is lost: `InF1 G` already
   contains `Berge G`, so every member of `F₂` is Berge anyway.

## Conventions

See `paper/spec/CONVENTIONS.md`.  In particular:

* `Ḡ` is `Gᶜ` and `G|K` is `G.induce K`; "is isomorphic to" is
  `Nonempty (· ≃g ·)`;
* quantification over *all finite graphs* (here: over all bipartite subdivisions
  `H` of `K₄`) is rendered `∃/∀ (n : ℕ) (H : SimpleGraph (Fin n))`;
* `K₄` is `(⊤ : SimpleGraph (Fin 4))` and `K₃,₃` is
  `completeBipartiteGraph (Fin 3) (Fin 3)`;
* a hole is given by the list of its vertices in cyclic order, and a *cyclically
  consecutive block* of such a list `C` is a prefix of some rotation of `C`.

The undefined terms of the bullets — *degenerate*, *bipartite subdivision*,
*even prism*, *long prism*, *double diamond*, *odd wheel*, *pseudowheel*,
*wheel* — are the ones the paper defers to later sections; each is taken from
the module that transcribes the section defining it.
-/

set_option autoImplicit false

namespace Workspace.Types.Classes

open Workspace.Types.Core Workspace.Types.Tracks Workspace.Types.Appearances
open Workspace.Types.Prisms Workspace.Types.DoubleDiamond
open Workspace.Types.Wheels Workspace.Types.Pseudowheels

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`F₁`** (printed p. 6).

PAPER: *"`F₁` is the class of all Berge graphs `G` such that for every bipartite
subdivision `H` of `K₄`, every induced subgraph of `G` isomorphic to `L(H)` is
degenerate"*.

Encoding notes.

* *"for every bipartite subdivision `H` of `K₄`"* quantifies over all finite
  graphs `H`, rendered as usual by `∀ (n : ℕ) (H : SimpleGraph (Fin n))` together
  with `Tracks.IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H`.
* *"every induced subgraph of `G` isomorphic to `L(H)` is degenerate"*: being
  degenerate is a property of `L(H)`, equivalently of the subdivision `H`
  (`Appearances.DegenerateK4Appearance H`, printed p. 18: *"there is a cycle of
  `H` of length four containing the four vertices of `H` that have degree three
  in `H`"*), not of the copy sitting inside `G`.  So the quantifier structure is:
  whenever some induced subgraph `G|K` of `G` is isomorphic to `L(H)`, that
  `L(H)` is degenerate.  Equivalently, every appearance of `K₄` in `G` (in the
  sense of `Appearances.IsAppearance`) is degenerate. -/
def InF1 (G : SimpleGraph V) : Prop :=
  SPGT.Berge G ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      SPGT.IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H →
        (∃ K : Set V, Nonempty (G.induce K ≃g H.lineGraph)) →
          SPGT.DegenerateK4Appearance H

/-- **`F₂`** (printed p. 6).

PAPER: *"`F₂` is the class of all graphs `G` such that `G,Ḡ ∈ F₁` and no induced
subgraph of `G` is isomorphic to `L(K₃,₃)`"*.

**Printed quirk, reproduced:** this bullet says *"all graphs `G`"*, whereas every
other bullet of the list restricts to Berge graphs.  No Bergeness hypothesis is
added here.  It would in any case be redundant: `InF1 G` already contains
`Berge G`.

Encoding notes.

* `K₃,₃` is `completeBipartiteGraph (Fin 3) (Fin 3)`, whose vertex type is the
  sum `Fin 3 ⊕ Fin 3`; `L(K₃,₃)` is its `lineGraph`.
* *"no induced subgraph of `G` is isomorphic to `L(K₃,₃)`"* is the negation of
  the existence of a vertex subset `K` with `G|K ≅ L(K₃,₃)`.  Note that this
  condition is imposed on `G` only, not on `Ḡ`. -/
def InF2 (G : SimpleGraph V) : Prop :=
  InF1 G ∧ InF1 Gᶜ ∧
    ¬ ∃ K : Set V,
        Nonempty (G.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)

/-- **`F₃`** (printed p. 7).

PAPER: *"`F₃` is the class of all Berge graphs `G` such that for every bipartite
subdivision `H` of `K₄`, no induced subgraph of `G` or of `Ḡ` is isomorphic to
`L(H)`"*.

Encoding notes.

* The Bergeness hypothesis is stated here explicitly, exactly as printed; the
  bullet is *not* phrased as a restriction of `F₂`.
* *"no induced subgraph of `G` or of `Ḡ` is isomorphic to `L(H)`"* is a
  conjunction of two negated existentials, one for `G` and one for `Gᶜ`. -/
def InF3 (G : SimpleGraph V) : Prop :=
  SPGT.Berge G ∧
    ∀ (n : ℕ) (H : SimpleGraph (Fin n)),
      SPGT.IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H →
        (¬ ∃ K : Set V, Nonempty (G.induce K ≃g H.lineGraph)) ∧
          (¬ ∃ K : Set V, Nonempty (Gᶜ.induce K ≃g H.lineGraph))

/-- **`F₄`** (printed p. 7).

PAPER: *"`F₄` is the class of all `G ∈ F₃` such that no induced subgraph of `G`
is an even prism"*.

Encoding note.  A prism of `G` (printed pp. 34–35) is presented by its two
triangles `{a₁,a₂,a₃}`, `{b₁,b₂,b₃}` and the three paths `R₁, R₂, R₃` forming
it, and it is by construction an *induced* subgraph of `G`; it is even when all
three paths have even length (printed p. 56).  So *"no induced subgraph of `G` is
an even prism"* is the negation of the existence of such data in `G`. -/
def InF4 (G : SimpleGraph V) : Prop :=
  InF3 G ∧
    ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), SPGT.IsEvenPrism G a b R₁ R₂ R₃

/-- **`F₅`** (printed p. 7).

PAPER: *"`F₅` is the class of all `G ∈ F₃` such that no induced subgraph of `G`
or of `Ḡ` is a long prism"*.

**Printed quirk, reproduced:** the preamble to the list claims that each class is
a subclass of the previous one, but this bullet is literally defined from `F₃`,
not from `F₄` — just as `F₄` itself is.  It is `InF3` that appears below.

Encoding note.  A prism is *long* when at least one of its three paths has
length `> 1` (printed p. 35).  As for `F₄`, "no induced subgraph … is a long
prism" negates the existence of the presenting data, here in `G` and in `Gᶜ`
separately. -/
def InF5 (G : SimpleGraph V) : Prop :=
  InF3 G ∧
    (¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V), SPGT.IsLongPrism G a b P₁ P₂ P₃) ∧
      (¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V), SPGT.IsLongPrism Gᶜ a b P₁ P₂ P₃)

/-- **`F₆`** (printed p. 7).

PAPER: *"`F₆` is the class of all `G ∈ F₅` such that no induced subgraph of `G`
is isomorphic to a double diamond"*.

Encoding note.  A double diamond (printed p. 87) is the graph on eight vertices
`a₁,…,a₄,b₁,…,b₄` with a prescribed adjacency pattern; an induced subgraph of `G`
isomorphic to it is exactly a choice of eight vertices of `G` realising that
pattern *and no other adjacency among them*, which is what
`DoubleDiamond.IsDoubleDiamond` records.  The condition is imposed on `G` only,
not on `Ḡ`. -/
def InF6 (G : SimpleGraph V) : Prop :=
  InF5 G ∧
    ¬ ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V,
        SPGT.IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄

/-- **`F₇`** (printed p. 7).

PAPER: *"`F₇` is the class of all `G ∈ F₆` such that `G` and `Ḡ` do not contain
odd wheels"*.

Encoding note.  A wheel (printed p. 96) is a pair `(C, Y)` with `C` a hole of
length `≥ 6`, `Y` a non-null anticonnected set disjoint from `C`, and two
disjoint `Y`-complete edges of `C`; it is *odd* when some `Y`-segment of the rim
`C` has odd length.  "`G` does not contain an odd wheel" is therefore the
negation of `∃ C Y, IsOddWheel G C Y`, and likewise for `Gᶜ`. -/
def InF7 (G : SimpleGraph V) : Prop :=
  InF6 G ∧
    (¬ ∃ (C : List V) (Y : Set V), SPGT.IsOddWheel G C Y) ∧
      (¬ ∃ (C : List V) (Y : Set V), SPGT.IsOddWheel Gᶜ C Y)

/-- **`F₈`** (printed p. 7).

PAPER: *"`F₈` is the class of all `G ∈ F₇` such that `G` and `Ḡ` do not contain
pseudowheels"*.

Encoding note.  A pseudowheel (printed p. 109) is a triple `(X, Y, P)`; "`G` does
not contain a pseudowheel" negates the existence of such a triple in `G`, and
likewise for `Gᶜ`. -/
def InF8 (G : SimpleGraph V) : Prop :=
  InF7 G ∧
    (¬ ∃ (X Y : Set V) (P : List V), SPGT.IsPseudowheel G X Y P) ∧
      (¬ ∃ (X Y : Set V) (P : List V), SPGT.IsPseudowheel Gᶜ X Y P)

/-- **`F₉`** (printed p. 7).

PAPER: *"`F₉` is the class of all `G ∈ F₈` such that `G` and `Ḡ` do not contain
wheels"*.

Encoding note.  Same shape as `InF7`, with the wheel condition
(`Wheels.IsWheel`) in place of the odd-wheel condition. -/
def InF9 (G : SimpleGraph V) : Prop :=
  InF8 G ∧
    (¬ ∃ (C : List V) (Y : Set V), SPGT.IsWheel G C Y) ∧
      (¬ ∃ (C : List V) (Y : Set V), SPGT.IsWheel Gᶜ C Y)

/-- **`F₁₀`** (printed p. 7).

PAPER: *"`F₁₀` is the class of all `G ∈ F₉` such that, for every hole `C` in `G`
of length `≥ 6`, no vertex of `G` has three consecutive neighbours in `C`, and
the same holds in `Ḡ`"*.

Encoding notes.

* A hole is given by the list `C` of its vertices in cyclic order
  (`Core.IsHoleList`), and its length is `Core.holeLength C = C.length`.
* *"three consecutive neighbours in `C`"* means three vertices `x, y, z` that are
  consecutive along the hole — cyclically, so the block may wrap around the end
  of the list — and are all adjacent to the vertex in question.  A cyclically
  consecutive block of `C` is a prefix of some rotation of `C`, so the three
  vertices are those of `[x, y, z] <+: C.rotate k` for some `k`.  Since `C` has
  no repeated vertex, `x, y, z` are automatically distinct.
* *"no vertex of `G`"* quantifies over all of `V`; no vertex of the hole itself
  can qualify, since a hole is induced and so each of its vertices has exactly
  two neighbours on it.
* *"and the same holds in `Ḡ`"*: the identical condition with `Gᶜ` throughout —
  holes of `Gᶜ`, and adjacency in `Gᶜ`. -/
def InF10 (G : SimpleGraph V) : Prop :=
  InF9 G ∧
    (∀ C : List V, SPGT.IsHoleList G C → 6 ≤ SPGT.holeLength C →
        ¬ ∃ v x y z : V,
            (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
              G.Adj v x ∧ G.Adj v y ∧ G.Adj v z) ∧
      (∀ C : List V, SPGT.IsHoleList Gᶜ C → 6 ≤ SPGT.holeLength C →
          ¬ ∃ v x y z : V,
              (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
                Gᶜ.Adj v x ∧ Gᶜ.Adj v y ∧ Gᶜ.Adj v z)

/-- **`F₁₁`** (printed p. 7).

PAPER: *"`F₁₁` is the class of all `G ∈ F₁₀` such that every antihole in `G` has
length 4."*

Encoding note.  An antihole of `G` is a hole of `Gᶜ` (`Core.IsAntiholeList`), and
its length is again the number of its vertices, `Core.holeLength`. -/
def InF11 (G : SimpleGraph V) : Prop :=
  InF10 G ∧ ∀ c : List V, SPGT.IsAntiholeList G c → SPGT.holeLength c = 4

end SPGT

end Workspace.Types.Classes
