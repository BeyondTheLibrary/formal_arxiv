import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# Skew partitions from separators, and the paths a graph with no skew partition must contain

Several times, and never with an argument, the paper uses the following move.  Let
`X ⊆ V(G)`, write

  `N := {v ∈ V(G) | v is X-complete}`,   `B := X ∪ N`,   `A := V(G) \ B`,

and note that `(A, B)` is a partition of `V(G)`.  Then:

* `B` is **not anticonnected** as soon as `X` and `N` are both nonempty.  Indeed an
  `X`-complete vertex is `G`-adjacent to every vertex of `X`, hence `Ḡ`-**non**adjacent to
  every vertex of `X`, so `Ḡ|B` has no edge at all between `X` and `N` and both parts are
  nonempty.  (`not_anticonnectedSet_separator_of_nonempty`.)
* Consequently, if `A` is **not connected** then `(A, B)` is a skew partition of `G`
  (`isSkewPartition_of_separator`); so in a graph admitting no skew partition, `A` **is**
  connected (`connectedSet_compl_separator`), and any two vertices attached to `A` are
  joined by an induced path whose interior lies in `A` — i.e. a path avoiding `X` entirely
  and containing no `X`-complete vertex in its interior.

That last sentence is the form the paper uses.  Printed proof of **23.4**:

> *"Since `G` admits no skew partition by 15.1, there is a path `P` from `{z,y}` to `A₀`,
> disjoint from `{x₀,…,x_t}` and containing no `{x₀,…,x_t}`-complete vertex in its
> interior."*

and printed proof of **23.2**:

> *"Since `G` does not admit a skew partition, there is a path `T` of `G\{x₀,x₁}` from `z`
> to `A₀`, such that no vertex in its interior is in `Y` or `Y`-complete."*

Note in both cases that only the **interior** is required to avoid `X`-complete vertices:
the endpoints (`y`, `z` in 23.4; `z` in 23.2) are themselves `X`-complete.  That is why the
headline lemma is stated in the "endpoint-exempt" form
`exists_path_interior_avoiding_of_no_skew_partition`, with an endpoint hypothesis
`u ∈ A ∨ (u has a neighbour in A)`.  A caller whose endpoints do lie in `A` supplies
`Or.inl` and gets the stronger conclusion from
`exists_path_avoiding_of_no_skew_partition` instead.

The endpoint hypothesis is not free, but it is *supplied by the same no-skew-partition
assumption*: `exists_adj_compl_separator_of_no_skew_partition` shows that an `X`-complete
vertex with no neighbour in `A` would itself be an isolated vertex of `A ∪ {u}`, giving the
skew partition `(A ∪ {u}, B \ {u})`.

Nothing in this module has a counterpart in the paper; it is all infrastructure.

## Contents

*The `B`-side (three ways to get it).*
`not_anticonnectedSet_of_meets` (the engine — a set covered by `S ∪ T` with `S` complete to
`T` and meeting both is not anticonnected), `not_anticonnectedSet_separator_of_nonempty`,
`not_anticonnectedSet_separator` (from `¬ AnticonnectedSet G X`), and
`not_anticonnectedSet_of_isClique`.

*The constructive half.*
`isSkewPartition_of_separator`, `admitsSkewPartition_of_separator`,
`admitsSkewPartition_of_isolated`, `not_connectedSet_of_not_reachable`.

*The extraction half.*
`connectedSet_compl_separator`, `exists_adj_compl_separator_of_no_skew_partition`,
`exists_path_of_connected_attach` (abstract), `exists_path_avoiding_of_connectedSet`,
`exists_path_avoiding_of_connected`, `exists_path_interior_avoiding_of_connected`.

*The headlines.*
`exists_path_avoiding_of_no_skew_partition` (ends inside `A`; every vertex of the path
avoids `X` and is not `X`-complete) and
`exists_path_interior_avoiding_of_no_skew_partition` (ends merely attached to `A`; every
vertex avoids `X`, every **interior** vertex is not `X`-complete).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.SkewPartitionFromSeparator

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Walks cannot leave a closed set -/

/-- If no edge of `H` leaves `E` inside `D`, a walk of `H|D` starting in `E` stays in `E`. -/
private theorem walk_stays {H : SimpleGraph V} {D E : Set V}
    (hclosed : ∀ a ∈ E, ∀ b ∈ D, H.Adj a b → b ∈ E)
    {x y : ↥D} (p : (H.induce D).Walk x y) (hx : (x : V) ∈ E) : (y : V) ∈ E := by
  revert hx
  induction p with
  | nil => exact id
  | @cons a b _ hab _ ih => exact fun ha => ih (hclosed _ ha _ b.2 hab)

/-- **The engine of the `B`-side.**  If `S` is complete to `T`, then no subset of `S ∪ T`
meeting both `S` and `T` is anticonnected: in `Ḡ` there is no edge from `S` to `T`, so a
`Ḡ`-walk inside such a set that starts in `S` can never reach `T`.

Every *"`Ḡ` is not connected"* / *"`(A,B)` is a skew partition"* step of §§15, 23 is an
instance of this.  (The same argument occurs as a `private` lemma at the head of
`ProofAttempts/thm_15_2/Attempt_1.lean`; this is the importable copy.) -/
theorem not_anticonnectedSet_of_meets {S T D : Set V}
    (hsub : D ⊆ S ∪ T) (hc : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    {a b : V} (haD : a ∈ D) (haS : a ∈ S) (hbD : b ∈ D) (hbT : b ∈ T) :
    ¬ AnticonnectedSet G D := by
  intro hconn
  obtain ⟨p⟩ := hconn ⟨a, haD⟩ ⟨b, hbD⟩
  have hstay : ∀ u ∈ S, ∀ v ∈ D, Gᶜ.Adj u v → v ∈ S := by
    intro u hu v hv hadj
    rcases hsub hv with h | h
    · exact h
    · exact absurd (hc u hu v h) hadj.2
  exact G.irrefl (hc b (walk_stays hstay p haS) b hbT)

/-! ### `X`-complete vertices and the separator `X ∪ {X-complete vertices}` -/

/-- Every `X`-complete vertex is adjacent to every vertex of `X`. -/
theorem adj_of_vertexComplete {X : Set V} {s t : V} (hs : s ∈ X)
    (ht : VertexComplete G t X) : G.Adj s t := (ht s hs).symm

/-- An `X`-complete vertex lies outside `X` — the paper's parenthetical *"(and consequently
`v ∉ X`)"*. -/
theorem notMem_of_vertexComplete {X : Set V} {u : V} (hu : VertexComplete G u X) : u ∉ X :=
  fun h => G.irrefl (hu u h)

/-- Membership in `A := (X ∪ {X-complete vertices})ᶜ` decoded. -/
theorem mem_compl_separator_iff {X : Set V} {w : V} :
    w ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ↔ (w ∉ X ∧ ¬ VertexComplete G w X) := by
  simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or]

/-- The empty set is anticonnected (the paper counts `∅` as connected). -/
private theorem anticonnectedSet_empty (G : SimpleGraph V) :
    AnticonnectedSet G (∅ : Set V) := fun a => (Set.notMem_empty (a : V) a.2).elim

/-! ### The `B`-side: three ways to see the separator is not anticonnected -/

/-- **`B`-side, the form both known callers need.**  If `X` is nonempty and *some* vertex is
`X`-complete, then `X ∪ {X-complete vertices}` is not anticonnected.

Note this needs **no** assumption on `X` itself; in particular `X` may perfectly well be
anticonnected, which it is in the §23 applications. -/
theorem not_anticonnectedSet_separator_of_nonempty {X : Set V}
    (hX : X.Nonempty) (hN : {z : V | VertexComplete G z X}.Nonempty) :
    ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}) := by
  obtain ⟨a, haX⟩ := hX
  obtain ⟨b, hbN⟩ := hN
  exact not_anticonnectedSet_of_meets (S := X) (T := {z : V | VertexComplete G z X})
    (Set.Subset.refl _) (fun s hs t ht => adj_of_vertexComplete hs ht)
    (Or.inl haX) haX (Or.inr hbN) hbN

/-- **`B`-side, alternative.**  Adding the `X`-complete vertices to a set that is already not
anticonnected keeps it not anticonnected. -/
theorem not_anticonnectedSet_separator {X : Set V} (hX : ¬ AnticonnectedSet G X) :
    ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}) := by
  by_cases hN : ({z : V | VertexComplete G z X}).Nonempty
  · refine not_anticonnectedSet_separator_of_nonempty ?_ hN
    rcases Set.eq_empty_or_nonempty X with rfl | h
    · exact absurd (anticonnectedSet_empty G) hX
    · exact h
  · rw [Set.not_nonempty_iff_eq_empty] at hN
    rw [hN, Set.union_empty]
    exact hX

/-- A clique with at least two vertices is not anticonnected: in `Ḡ` it is edgeless. -/
theorem not_anticonnectedSet_of_isClique {X : Set V} (hX : G.IsClique X)
    {x y : V} (hx : x ∈ X) (hy : y ∈ X) (hxy : x ≠ y) :
    ¬ AnticonnectedSet G X := by
  refine not_anticonnectedSet_of_meets (S := ({x} : Set V)) (T := X \ {x})
    (fun z hz => ?_) (fun s hs t ht => ?_) hx rfl hy ⟨hy, hxy.symm⟩
  · by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr ⟨hz, hzx⟩
  · have hsx : s = x := hs
    subst hsx
    exact hX hx ht.1 (fun h => ht.2 h.symm)

/-! ### The constructive half -/

/-- Two vertices of `A` that cannot be joined inside `A` witness that `A` is not connected. -/
theorem not_connectedSet_of_not_reachable {A : Set V} {u v : V} (hu : u ∈ A) (hv : v ∈ A)
    (h : ¬ (G.induce A).Reachable ⟨u, hu⟩ ⟨v, hv⟩) : ¬ ConnectedSet G A :=
  fun hc => h (hc ⟨u, hu⟩ ⟨v, hv⟩)

/-- **The constructive half.**  If the separator `X ∪ {X-complete vertices}` is not
anticonnected and its complement is not connected, that pair *is* a skew partition of `G`. -/
theorem isSkewPartition_of_separator {X : Set V}
    (hB : ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}))
    (hA : ¬ ConnectedSet G (X ∪ {z : V | VertexComplete G z X})ᶜ) :
    IsSkewPartition G (X ∪ {z : V | VertexComplete G z X})ᶜ
      (X ∪ {z : V | VertexComplete G z X}) :=
  ⟨Set.compl_union_self _, disjoint_compl_left, hA, hB⟩

/-- The existential form of `isSkewPartition_of_separator`. -/
theorem admitsSkewPartition_of_separator {X : Set V}
    (hB : ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}))
    (hA : ¬ ConnectedSet G (X ∪ {z : V | VertexComplete G z X})ᶜ) :
    AdmitsSkewPartition G :=
  ⟨_, _, isSkewPartition_of_separator hB hA⟩

/-- **The constructive half, isolated-vertex case.**  If an `X`-complete vertex `u` has no
neighbour in `A := (X ∪ {X-complete vertices})ᶜ`, then `u` is an isolated vertex of
`A ∪ {u}`, so — provided `A` is nonempty, `X` is nonempty and some *other* vertex is
`X`-complete — the pair `(A ∪ {u}, (X ∪ {X-complete vertices}) \ {u})` is a skew partition. -/
theorem admitsSkewPartition_of_isolated {X : Set V} {u : V}
    (hX : X.Nonempty) (hu : VertexComplete G u X)
    (hw : ∃ w, VertexComplete G w X ∧ w ≠ u)
    (hA : ((X ∪ {z : V | VertexComplete G z X})ᶜ).Nonempty)
    (hiso : ∀ a ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, ¬ G.Adj u a) :
    AdmitsSkewPartition G := by
  obtain ⟨x0, hx0⟩ := hX
  obtain ⟨w, hwc, hwu⟩ := hw
  have huB : u ∈ X ∪ {z : V | VertexComplete G z X} := Or.inr hu
  refine ⟨(X ∪ {z : V | VertexComplete G z X})ᶜ ∪ {u},
    (X ∪ {z : V | VertexComplete G z X}) \ {u}, ?_, ?_, ?_, ?_⟩
  -- the two sides cover `V(G)`
  · ext y
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_diff,
      Set.mem_univ, iff_true]
    by_cases hyB : y ∈ X ∪ {z : V | VertexComplete G z X}
    · by_cases hyu : y = u
      · exact Or.inl (Or.inr hyu)
      · exact Or.inr ⟨hyB, hyu⟩
    · exact Or.inl (Or.inl hyB)
  -- and are disjoint
  · rw [Set.disjoint_left]
    rintro y (hy | hy) ⟨hyB, hyu⟩
    · exact hy hyB
    · exact hyu hy
  -- `A ∪ {u}` is not connected: `u` is isolated in it and `A` is nonempty
  · intro hc
    obtain ⟨a, haA⟩ := hA
    obtain ⟨p⟩ := hc ⟨u, Or.inr rfl⟩ ⟨a, Or.inl haA⟩
    have hstay : ∀ s ∈ ({u} : Set V),
        ∀ t ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ∪ {u}, G.Adj s t → t ∈ ({u} : Set V) := by
      intro s hs t ht hadj
      have hsu : s = u := hs
      subst hsu
      rcases ht with ht | ht
      · exact absurd hadj (hiso t ht)
      · exact ht
    have hau : a = u := walk_stays hstay p rfl
    rw [hau] at haA
    exact haA huB
  -- `B \ {u}` is not anticonnected: `X` is complete to the remaining `X`-complete vertices
  · refine not_anticonnectedSet_of_meets (S := X) (T := {z : V | VertexComplete G z X} \ {u})
      (fun y hy => ?_) (fun s hs t ht => adj_of_vertexComplete hs ht.1)
      ⟨Or.inl hx0, fun h => notMem_of_vertexComplete hu (by rw [← (h : x0 = u)]; exact hx0)⟩
      hx0 ⟨Or.inr hwc, hwu⟩ ⟨hwc, hwu⟩
    rcases hy.1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hy.2⟩

/-! ### The extraction half -/

/-- **`A`-side.**  In a graph admitting no skew partition, the complement of the separator is
connected. -/
theorem connectedSet_compl_separator {X : Set V}
    (hno : ¬ AdmitsSkewPartition G)
    (hB : ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X})) :
    ConnectedSet G (X ∪ {z : V | VertexComplete G z X})ᶜ := by
  by_contra h
  exact hno (admitsSkewPartition_of_separator hB h)

/-- **The endpoint hypothesis comes free.**  In a graph admitting no skew partition, an
`X`-complete vertex `u` *does* have a neighbour in `A := (X ∪ {X-complete vertices})ᶜ`,
provided `X` is nonempty, `A` is nonempty, and some other vertex is `X`-complete.
Otherwise `u` would be an isolated vertex of `A ∪ {u}` (`admitsSkewPartition_of_isolated`). -/
theorem exists_adj_compl_separator_of_no_skew_partition {X : Set V} {u : V}
    (hno : ¬ AdmitsSkewPartition G) (hX : X.Nonempty) (hu : VertexComplete G u X)
    (hw : ∃ w, VertexComplete G w X ∧ w ≠ u)
    (hA : ((X ∪ {z : V | VertexComplete G z X})ᶜ).Nonempty) :
    ∃ a ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, G.Adj u a := by
  by_contra h
  push Not at h
  exact hno (admitsSkewPartition_of_isolated hX hu hw hA h)

/-- **Abstract attachment lemma.**  Two vertices each of which either lies in a connected set
`A` or has a neighbour in `A` are joined by an induced path of `G` all of whose vertices lie
in `A ∪ {u, v}` and all of whose **interior** vertices lie in `A`.

This is the general form of the paper's *"a path from `u` to `v` whose interior lies in
`A`"*; the `Gᶜ` analogue is `InducedPathExtraction.exists_antipath_interior_in`. -/
theorem exists_path_of_connected_attach {A : Set V} {u v : V}
    (hconn : ConnectedSet G A)
    (hua : u ∈ A ∨ ∃ a ∈ A, G.Adj u a)
    (hvb : v ∈ A ∨ ∃ b ∈ A, G.Adj v b) :
    ∃ p : List V, IsPathFrom G p u v ∧ (∀ w ∈ p, w ∈ A ∨ w = u ∨ w = v) ∧
      (∀ w ∈ SPGT.interior p, w ∈ A) := by
  have h1 : ConnectedSet G (A ∪ {u}) := by
    rcases hua with h | h
    · rw [Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr h)]
      exact hconn
    · exact ConnectedSetUnionAttach.connectedSet_union_singleton hconn h
  have h2 : ConnectedSet G ((A ∪ {u}) ∪ {v}) := by
    rcases hvb with h | h
    · have hvmem : v ∈ A ∪ ({u} : Set V) := Or.inl h
      have hsub : (A ∪ ({u} : Set V)) ∪ ({v} : Set V) = A ∪ ({u} : Set V) :=
        Set.union_eq_self_of_subset_right (Set.singleton_subset_iff.mpr hvmem)
      rw [hsub]
      exact h1
    · obtain ⟨b, hb, hadj⟩ := h
      exact ConnectedSetUnionAttach.connectedSet_union_singleton h1 ⟨b, Or.inl hb, hadj⟩
  obtain ⟨p, hp, hmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected h2 (Or.inl (Or.inr rfl)) (Or.inr rfl)
  refine ⟨p, hp, ?_, ?_⟩
  · intro w hw
    rcases hmem w hw with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · intro w hw
    rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hw
    obtain ⟨hwp, hwu, hwv⟩ := hw
    rcases hmem w hwp with (h | h) | h
    · exact h
    · exact absurd h hwu
    · exact absurd h hwv

/-- **Extraction, general form.**  Inside any connected set `S` all of whose vertices avoid
`X` and are not `X`-complete, any two vertices are joined by an induced path with the same
property. -/
theorem exists_path_avoiding_of_connectedSet {X S : Set V} {u v : V}
    (hS : ConnectedSet G S)
    (hSX : ∀ z ∈ S, z ∉ X ∧ ¬ VertexComplete G z X)
    (hu : u ∈ S) (hv : v ∈ S) :
    ∃ p : List V, IsPathFrom G p u v ∧ ∀ z ∈ p, z ∉ X ∧ ¬ VertexComplete G z X := by
  obtain ⟨p, hp, hmem⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hS hu hv
  exact ⟨p, hp, fun z hz => hSX z (hmem z hz)⟩

/-- **Extraction.**  If `A := (X ∪ {X-complete vertices})ᶜ` is connected, any two of its
vertices are joined by an induced path avoiding `X` and avoiding `X`-complete vertices. -/
theorem exists_path_avoiding_of_connected {X : Set V} {u v : V}
    (hconn : ConnectedSet G (X ∪ {z : V | VertexComplete G z X})ᶜ)
    (hu : u ∉ X) (hu' : ¬ VertexComplete G u X)
    (hv : v ∉ X) (hv' : ¬ VertexComplete G v X) :
    ∃ p : List V, IsPathFrom G p u v ∧ ∀ z ∈ p, z ∉ X ∧ ¬ VertexComplete G z X :=
  exists_path_avoiding_of_connectedSet hconn
    (fun z hz => mem_compl_separator_iff.mp hz)
    (mem_compl_separator_iff.mpr ⟨hu, hu'⟩) (mem_compl_separator_iff.mpr ⟨hv, hv'⟩)

/-- **Extraction, endpoint-exempt.**  The shape 23.2 and 23.4 use: the two ends need only
avoid `X` and be attached to `A`; they may themselves be `X`-complete.  The resulting path
avoids `X` altogether and has no `X`-complete vertex in its interior. -/
theorem exists_path_interior_avoiding_of_connected {X : Set V} {u v : V}
    (hconn : ConnectedSet G (X ∪ {z : V | VertexComplete G z X})ᶜ)
    (hu : u ∉ X) (hv : v ∉ X)
    (hua : u ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ∨
      ∃ a ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, G.Adj u a)
    (hvb : v ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ∨
      ∃ b ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, G.Adj v b) :
    ∃ p : List V, IsPathFrom G p u v ∧ (∀ w ∈ p, w ∉ X) ∧
      (∀ w ∈ SPGT.interior p, ¬ VertexComplete G w X) := by
  obtain ⟨p, hp, hmem, hint⟩ := exists_path_of_connected_attach hconn hua hvb
  refine ⟨p, hp, ?_, fun w hw => (mem_compl_separator_iff.mp (hint w hw)).2⟩
  intro w hw
  rcases hmem w hw with h | h | h
  · exact (mem_compl_separator_iff.mp h).1
  · rw [h]; exact hu
  · rw [h]; exact hv

/-! ### The headline lemmas -/

/-- **Headline, strong form.**  In a graph admitting no skew partition, if the separator
`X ∪ {X-complete vertices}` is not anticonnected (e.g. by
`not_anticonnectedSet_separator_of_nonempty`), then any two vertices avoiding `X` and not
`X`-complete are joined by an induced path *every* vertex of which avoids `X` and is not
`X`-complete. -/
theorem exists_path_avoiding_of_no_skew_partition {X : Set V} {u v : V}
    (hno : ¬ AdmitsSkewPartition G)
    (hB : ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}))
    (hu : u ∉ X) (hu' : ¬ VertexComplete G u X)
    (hv : v ∉ X) (hv' : ¬ VertexComplete G v X) :
    ∃ p : List V, IsPathFrom G p u v ∧ ∀ z ∈ p, z ∉ X ∧ ¬ VertexComplete G z X :=
  exists_path_avoiding_of_connected (connectedSet_compl_separator hno hB) hu hu' hv hv'

/-- **Headline, the form the paper uses.**  In a graph admitting no skew partition, if the
separator `X ∪ {X-complete vertices}` is not anticonnected, then any two vertices that avoid
`X` and are attached to `A := (X ∪ {X-complete vertices})ᶜ` are joined by an induced path
disjoint from `X` and containing no `X`-complete vertex **in its interior**.

This is the *"Since `G` admits no skew partition, there is a path `P` from … to …, disjoint
from `X` and containing no `X`-complete vertex in its interior"* of 23.2 and 23.4.  A caller
whose endpoints lie in `A` passes `Or.inl`; a caller whose endpoint is `X`-complete gets the
`Or.inr` disjunct from `exists_adj_compl_separator_of_no_skew_partition`. -/
theorem exists_path_interior_avoiding_of_no_skew_partition {X : Set V} {u v : V}
    (hno : ¬ AdmitsSkewPartition G)
    (hB : ¬ AnticonnectedSet G (X ∪ {z : V | VertexComplete G z X}))
    (hu : u ∉ X) (hv : v ∉ X)
    (hua : u ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ∨
      ∃ a ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, G.Adj u a)
    (hvb : v ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ ∨
      ∃ b ∈ (X ∪ {z : V | VertexComplete G z X})ᶜ, G.Adj v b) :
    ∃ p : List V, IsPathFrom G p u v ∧ (∀ w ∈ p, w ∉ X) ∧
      (∀ w ∈ SPGT.interior p, ¬ VertexComplete G w X) :=
  exists_path_interior_avoiding_of_connected (connectedSet_compl_separator hno hB) hu hv hua hvb

end Workspace.ProofLemmas.SkewPartitionFromSeparator
