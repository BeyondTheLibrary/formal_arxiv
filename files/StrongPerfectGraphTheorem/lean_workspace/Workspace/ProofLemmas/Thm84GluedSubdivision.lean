import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Gluing the chosen rungs into a subdivision of `J`

PAPER (printed p. 39, the prose immediately following the proof of 8.1): *"For each edge `uv` of
`J`, choose a `uv`-rung `R_uv`.  It follows from 8.1 and the final axiom above that the subgraph
of `G` induced on the union of the vertex sets of these rungs is a line graph of a bipartite
subdivision `H` of `J`."*

The paper discharges this sentence in one line and prints **no** argument, so the object it
asserts has to be built by hand.  This module supplies the *carrier*: a graph `Hs` on an
explicit vertex type together with the family of tracks realising `IsSubdivision J Hs`.
`Thm84GluedBipartite` then supplies bipartiteness, `Thm84GluedLineGraphIso` the isomorphism
`L(Hs) ≅ G|K`, and `Thm84GluedTransport` moves the whole package onto `Fin n`.

## The vertex model

Write `k = pathLength (R u v)`, so `R u v = [x₀, …, x_k]` has `k + 1` entries.  The track of
`Hs` along the edge `uv` is

```
[inl u, inr x₁, inr x₂, …, inr x_k, inl v]
```

— `k + 2` vertices and `k + 1` edges, the edge between the `i`-th and `(i+1)`-st vertices
corresponding to the rung vertex `x_i`.  So the **interior** vertices of the track along `uv` are
exactly the members of `V(R u v)` other than the head of `R u v`, and the vertex type of `Hs` is

```
GluedVertex J R  =  U ⊕ {x : V // x ∈ rungUnion J R ∧ ¬ IsChosenHead J R x}
```

## Why the orientation is not optional

Each edge `uv` of `J` contributes `|R u v| + 1` track-vertices, two of which (`inl u` and
`inl v`) are branch-vertices shared with the other tracks at `u` and at `v`.  Hence exactly
**one** end of each rung has to be dropped from the interior, and which one depends on a choice
of direction along the edge — the `T v u = (T u v).reverse` clause of `IsSubdivision` forbids
dropping the head in both directions at once.  `Orient` is the usual edge-orientation device
(already used by `Thm82RungFamily.exists_symmetric_rung_family`): totally order `U` through
`Fintype.equivFin`, and orient every edge from its smaller to its larger end.  `IsChosenHead x`
then says that `x` is the head of the rung on some edge *taken in its chosen direction*, and
those are precisely the `|E(J)|` vertices of `K` that must not be duplicated.

## What is exported

The existential below lists, for the specific injection `ι := Sum.inl`, all eight conjuncts of
`Tracks.IsSubdivision J Hs`, and then three further facts that the downstream modules consume:

* the track along `uv` has one more vertex than the rung `R u v`;
* run in its chosen direction, the track is literally the list displayed above (tested after
  the projection `Sum.map id Subtype.val` back into `U ⊕ V`, which is injective, so this pins
  the track down completely);
* the *edge dictionary* `ρ`: the edge of the track between its `i`-th and `(i+1)`-st vertices is
  sent by `ρ` to the `i`-th vertex of the rung `R u v`.  This is the map that
  `Thm84GluedLineGraphIso` turns into the bijection `E(Hs) ≃ K`.

**Status: this module is a work item — the statement below is stated but not yet proved.**
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84GluedSubdivision

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **"The union of the vertex sets of these rungs"** (printed p. 39).

This is the set `K` on which `StripSystems.FormsLineGraph` induces its appearance of `J`. -/
def rungUnion {U : Type*} (J : SimpleGraph U) (R : U → U → List V) : Set V :=
  ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}

/-- The chosen direction of an edge of `J`: from the smaller to the larger end in the arbitrary
total order that `Fintype.equivFin` puts on `U`.  For `u ≠ v` exactly one of `Orient u v` and
`Orient v u` holds. -/
def Orient {U : Type*} [Fintype U] (u v : U) : Prop :=
  ((Fintype.equivFin U u : Fin (Fintype.card U)) : ℕ)
    ≤ ((Fintype.equivFin U v : Fin (Fintype.card U)) : ℕ)

noncomputable instance {U : Type*} [Fintype U] : DecidableRel (Orient (U := U)) := fun u v =>
  inferInstanceAs (Decidable (((Fintype.equivFin U u : Fin (Fintype.card U)) : ℕ) ≤ _))

/-- `x` is the head of the rung sitting on some edge of `J`, that edge being taken in its
chosen direction.  These are exactly the vertices of `K` that get identified with a
branch-vertex of the glued subdivision rather than becoming an interior vertex of a track. -/
def IsChosenHead {U : Type*} [Fintype U] (J : SimpleGraph U) (R : U → U → List V) (x : V) :
    Prop :=
  ∃ u v : U, J.Adj u v ∧ Orient u v ∧ (R u v).head? = some x

/-- The vertex type of the glued subdivision: one vertex for each vertex of `J` (the
branch-vertices), and one for each vertex of `K` that is not a chosen rung head (the interior
vertices of the tracks). -/
abbrev GluedVertex {U : Type*} [Fintype U] (J : SimpleGraph U) (R : U → U → List V) : Type _ :=
  U ⊕ {x : V // x ∈ rungUnion J R ∧ ¬ IsChosenHead J R x}

/-! ## The construction -/

namespace Glue

variable {U : Type*} [Fintype U]

/-! ### Small list facts -/

theorem reverse_dropLast' {α : Type*} (l : List α) : l.reverse.dropLast = l.tail.reverse := by
  cases l with
  | nil => simp
  | cons a t => simp

theorem reverse_tail' {α : Type*} (l : List α) : l.reverse.tail = l.dropLast.reverse := by
  have h := reverse_dropLast' l.reverse
  rw [List.reverse_reverse] at h
  rw [h, List.reverse_reverse]

theorem head_notMem_tail {α : Type*} {l : List α} (hnd : l.Nodup) {x : α}
    (hh : l.head? = some x) : x ∉ l.tail := by
  cases l with
  | nil => simp at hh
  | cons a t =>
    simp only [List.head?_cons, Option.some_inj] at hh
    subst hh
    simpa using (List.nodup_cons.mp hnd).1

theorem getLast?_concat' {α : Type*} (l : List α) (a : α) : (l ++ [a]).getLast? = some a := by
  rw [List.getLast?_append_cons]
  rfl

theorem getLast_notMem_dropLast {α : Type*} {l : List α} (hnd : l.Nodup) {x : α}
    (hh : l.getLast? = some x) : x ∉ l.dropLast := by
  have hne : l ≠ [] := by rintro rfl; simp at hh
  have hx : l.getLast hne = x := by
    rw [List.getLast?_eq_getLast hne] at hh
    exact Option.some_injective _ hh
  have heq : l.dropLast ++ [l.getLast hne] = l := List.dropLast_append_getLast hne
  rw [hx] at heq
  intro hmem
  rw [← heq, List.nodup_append] at hnd
  exact hnd.2.2 x hmem x (by simp) rfl

theorem mem_tail_of_ne {α : Type*} {l : List α} {x y : α} (hx : x ∈ l)
    (hh : l.head? = some y) (hne : x ≠ y) : x ∈ l.tail := by
  cases l with
  | nil => simp at hh
  | cons a t =>
    simp only [List.head?_cons, Option.some_inj] at hh
    rcases List.mem_cons.mp hx with h | h
    · exact absurd (h.trans hh) hne
    · exact h

theorem mem_dropLast_of_ne {α : Type*} {l : List α} {x y : α} (hx : x ∈ l)
    (hh : l.getLast? = some y) (hne : x ≠ y) : x ∈ l.dropLast := by
  have hne' : l ≠ [] := by rintro rfl; simp at hh
  have hy : l.getLast hne' = y := by
    rw [List.getLast?_eq_getLast hne'] at hh
    exact Option.some_injective _ hh
  have heq : l.dropLast ++ [l.getLast hne'] = l := List.dropLast_append_getLast hne'
  rw [hy] at heq
  rw [← heq] at hx
  rcases List.mem_append.mp hx with h | h
  · exact h
  · exact absurd (List.mem_singleton.mp h) hne

/-! ### Orientation -/

theorem orient_total (u v : U) : Orient u v ∨ Orient v u := le_total _ _

theorem orient_antisymm {u v : U} (h1 : Orient u v) (h2 : Orient v u) : u = v :=
  (Fintype.equivFin U).injective (Fin.ext (le_antisymm h1 h2))

/-! ### The defining data -/

/-- Embedding a vertex of `K` into the glued vertex type, with a junk value `Sum.inl u₀`
for vertices that are not interior vertices of any track. -/
noncomputable def emb (J : SimpleGraph U) (R : U → U → List V) (u₀ : U) (x : V) :
    GluedVertex J R :=
  @dite (GluedVertex J R) (x ∈ rungUnion J R ∧ ¬ IsChosenHead J R x) (Classical.dec _)
    (fun h => Sum.inr ⟨x, h⟩) (fun _ => Sum.inl u₀)

/-- The rung vertices that become interior vertices of the track along `uv`, listed in the
order in which the track (run from `u` to `v`) meets them. -/
noncomputable def interiorRung (R : U → U → List V) (u v : U) : List V :=
  if Orient u v then (R u v).tail else (R u v).dropLast

/-- The track of the glued graph along the edge `uv`, run from `u` to `v`. -/
noncomputable def gluedTrack (J : SimpleGraph U) (R : U → U → List V) (u₀ u v : U) :
    List (GluedVertex J R) :=
  Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])

/-- The glued graph: its edges are exactly the edges of the tracks. -/
noncomputable def gluedGraph (J : SimpleGraph U) (R : U → U → List V) (u₀ : U) :
    SimpleGraph (GluedVertex J R) :=
  SimpleGraph.fromEdgeSet
    (⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (gluedTrack J R u₀ u v))

/-- `x` is the rung vertex corresponding to the edge `e` of the glued graph. -/
def DictPred (J : SimpleGraph U) (R : U → U → List V) (u₀ : U)
    (e : Sym2 (GluedVertex J R)) (x : V) : Prop :=
  ∃ (u v : U) (i : ℕ) (a b : GluedVertex J R), J.Adj u v ∧ Orient u v ∧
    (gluedTrack J R u₀ u v)[i]? = some a ∧ (gluedTrack J R u₀ u v)[i + 1]? = some b ∧
    (R u v)[i]? = some x ∧ e = s(a, b)

/-- The edge dictionary. -/
noncomputable def gluedDict (J : SimpleGraph U) (R : U → U → List V) (u₀ : U) (x₀ : V)
    (e : Sym2 (GluedVertex J R)) : V :=
  @dite V (∃ x : V, DictPred J R u₀ e x) (Classical.dec _)
    (fun h => h.choose) (fun _ => x₀)

/-! ### Basic properties -/

variable {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {R : U → U → List V} {u₀ : U}

theorem mem_rungUnion {u v : U} (huv : J.Adj u v) {x : V} (hx : x ∈ R u v) :
    x ∈ rungUnion J R := by
  simp only [rungUnion, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨u, v, huv, hx⟩

theorem rungUnion_elim {x : V} (hx : x ∈ rungUnion J R) : ∃ u v : U, J.Adj u v ∧ x ∈ R u v := by
  simp only [rungUnion, Set.mem_iUnion, Set.mem_setOf_eq] at hx
  obtain ⟨a, b, hab, hxab⟩ := hx
  exact ⟨a, b, hab, hxab⟩

theorem rung_ne_nil (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) : R u v ≠ [] := by
  obtain ⟨s, t, hp, -, -⟩ := StripSystemBasics.rung_isPath (hR u v huv)
  exact hp.1.1

theorem rung_nodup (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) : (R u v).Nodup := by
  obtain ⟨s, t, hp, -, -⟩ := StripSystemBasics.rung_isPath (hR u v huv)
  exact hp.1.2.1

theorem rung_length_pos (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) : 0 < (R u v).length :=
  List.length_pos_of_ne_nil (rung_ne_nil hR huv)

theorem emb_eq_inr {x : V} (h : x ∈ rungUnion J R ∧ ¬ IsChosenHead J R x) :
    emb J R u₀ x = Sum.inr ⟨x, h⟩ := dif_pos h

theorem interiorRung_pos {u v : U} (hor : Orient u v) :
    interiorRung R u v = (R u v).tail := if_pos hor

theorem interiorRung_neg {u v : U} (hor : ¬ Orient u v) :
    interiorRung R u v = (R u v).dropLast := if_neg hor

theorem interiorRung_subset {u v : U} {x : V} (hx : x ∈ interiorRung R u v) : x ∈ R u v := by
  by_cases hor : Orient (U := U) u v
  · rw [interiorRung_pos hor] at hx
    exact List.mem_of_mem_tail hx
  · rw [interiorRung_neg hor] at hx
    exact List.dropLast_subset _ hx

theorem interiorRung_nodup (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) : (interiorRung R u v).Nodup := by
  by_cases hor : Orient (U := U) u v
  · rw [interiorRung_pos hor]
    exact (rung_nodup hR huv).tail
  · rw [interiorRung_neg hor]
    exact List.Sublist.nodup (List.dropLast_sublist _) (rung_nodup hR huv)

theorem interiorRung_length (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) : (interiorRung R u v).length = (R u v).length - 1 := by
  by_cases hor : Orient (U := U) u v
  · rw [interiorRung_pos hor, List.length_tail]
  · rw [interiorRung_neg hor, List.length_dropLast]

/-- The key membership fact: every vertex that the track along `uv` uses in its interior really
is a legitimate interior vertex, i.e. it lies in the rung union and is not a chosen head. -/
theorem interiorRung_mem_ok (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) {x : V} (hx : x ∈ interiorRung R u v) :
    x ∈ rungUnion J R ∧ ¬ IsChosenHead J R x := by
  have hxR : x ∈ R u v := interiorRung_subset hx
  refine ⟨mem_rungUnion huv hxR, ?_⟩
  rintro ⟨u', v', hu'v', hor', hhead⟩
  have hxR' : x ∈ R u' v' := List.mem_of_mem_head? hhead
  have h1 : x ∈ S u v := StripSystemBasics.rung_subset_strip (hR u v huv) x hxR
  have h2 : x ∈ S u' v' := StripSystemBasics.rung_subset_strip (hR u' v' hu'v') x hxR'
  have hedge : s(u, v) = s(u', v') := by
    by_contra hne
    exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN huv hu'v' hne) h1 h2
  rcases Sym2.eq_iff.mp hedge with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · subst hu; subst hv
    rw [interiorRung_pos hor'] at hx
    exact head_notMem_tail (rung_nodup hR huv) hhead hx
  · subst hu; subst hv
    -- here `hor' : Orient v u`
    have hnor : ¬ Orient (U := U) u v := by
      intro hc
      exact huv.ne (orient_antisymm hc hor')
    rw [interiorRung_neg hnor] at hx
    have hhead' : (R u v).getLast? = some x := by
      rw [hRsymm u v huv, List.head?_reverse] at hhead
      exact hhead
    exact getLast_notMem_dropLast (rung_nodup hR huv) hhead' hx

/-- Conversely: a vertex of a rung which is not a chosen head really is an interior vertex of
the track along that edge. -/
theorem mem_interiorRung_of_not_chosenHead
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) {x : V} (hx : x ∈ R u v)
    (hnot : ¬ IsChosenHead J R x) : x ∈ interiorRung R u v := by
  by_cases hor : Orient (U := U) u v
  · rw [interiorRung_pos hor]
    obtain ⟨y, hy⟩ : ∃ y, (R u v).head? = some y := by
      rcases hl : R u v with _ | ⟨a, t⟩
      · exact absurd hl (rung_ne_nil hR huv)
      · exact ⟨a, rfl⟩
    refine mem_tail_of_ne hx hy ?_
    rintro rfl
    exact hnot ⟨u, v, huv, hor, hy⟩
  · have hor' : Orient (U := U) v u := (orient_total u v).resolve_left hor
    rw [interiorRung_neg hor]
    obtain ⟨y, hy⟩ : ∃ y, (R u v).getLast? = some y :=
      ⟨(R u v).getLast (rung_ne_nil hR huv), List.getLast?_eq_getLast _⟩
    refine mem_dropLast_of_ne hx hy ?_
    rintro rfl
    refine hnot ⟨v, u, huv.symm, hor', ?_⟩
    rw [hRsymm u v huv, List.head?_reverse]
    exact hy

theorem emb_mem_interior (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) {x : V} (hx : x ∈ interiorRung R u v) :
    emb J R u₀ x = Sum.inr ⟨x, interiorRung_mem_ok hSN hR hRsymm huv hx⟩ :=
  emb_eq_inr _

/-! ### Structure of the tracks -/

theorem gluedTrack_head (J : SimpleGraph U) (R : U → U → List V) (u₀ u v : U) :
    (gluedTrack J R u₀ u v).head? = some (Sum.inl u) := rfl

theorem gluedTrack_getLast (J : SimpleGraph U) (R : U → U → List V) (u₀ u v : U) :
    (gluedTrack J R u₀ u v).getLast? = some (Sum.inl v) := by
  show (Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])).getLast? = _
  rw [← List.cons_append]
  exact getLast?_concat' _ _

theorem gluedTrack_interior (J : SimpleGraph U) (R : U → U → List V) (u₀ u v : U) :
    trackInterior (gluedTrack J R u₀ u v) = (interiorRung R u v).map (emb J R u₀) := by
  show ((Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])).tail).dropLast = _
  simp

theorem gluedTrack_length (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    {u v : U} (huv : J.Adj u v) :
    (gluedTrack J R u₀ u v).length = (R u v).length + 1 := by
  have h1 : (interiorRung R u v).length = (R u v).length - 1 := interiorRung_length hR huv
  have h2 : 0 < (R u v).length := rung_length_pos hR huv
  show (Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])).length = _
  simp only [List.length_cons, List.length_append, List.length_map, List.length_nil]
  omega

theorem gluedTrack_nodup (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) : (gluedTrack J R u₀ u v).Nodup := by
  have hmapinr : ∀ x ∈ interiorRung R u v, ∃ y : {z : V // z ∈ rungUnion J R ∧
      ¬ IsChosenHead J R z}, emb J R u₀ x = Sum.inr y := by
    intro x hx
    exact ⟨⟨x, interiorRung_mem_ok hSN hR hRsymm huv hx⟩, emb_mem_interior hSN hR hRsymm huv hx⟩
  have hmapnodup : ((interiorRung R u v).map (emb J R u₀)).Nodup := by
    refine List.Nodup.map_on ?_ (interiorRung_nodup hR huv)
    intro a ha b hb hab
    rw [emb_mem_interior hSN hR hRsymm huv ha, emb_mem_interior hSN hR hRsymm huv hb] at hab
    have := Sum.inr_injective hab
    exact congrArg Subtype.val this
  show (Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])).Nodup
  rw [List.nodup_cons]
  constructor
  · intro hmem
    rcases List.mem_append.mp hmem with h | h
    · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
      rw [emb_mem_interior hSN hR hRsymm huv hx] at hxe
      exact absurd hxe (by simp)
    · rw [List.mem_singleton] at h
      exact huv.ne (Sum.inl_injective h)
  · rw [List.nodup_append]
    refine ⟨hmapnodup, by simp, ?_⟩
    intro a ha b hb
    rw [List.mem_singleton] at hb
    subst hb
    obtain ⟨x, hx, hxe⟩ := List.mem_map.mp ha
    rw [emb_mem_interior hSN hR hRsymm huv hx] at hxe
    rw [← hxe]
    simp

theorem interiorRung_reverse
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) :
    interiorRung R v u = (interiorRung R u v).reverse := by
  by_cases hor : Orient (U := U) u v
  · have hnor : ¬ Orient (U := U) v u := by
      intro hc; exact huv.ne (orient_antisymm hor hc)
    rw [interiorRung_neg hnor, interiorRung_pos hor, hRsymm u v huv, reverse_dropLast']
  · have hor' : Orient (U := U) v u := (orient_total u v).resolve_left hor
    rw [interiorRung_pos hor', interiorRung_neg hor, hRsymm u v huv, reverse_tail']

theorem gluedTrack_reverse
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) :
    gluedTrack J R u₀ v u = (gluedTrack J R u₀ u v).reverse := by
  show Sum.inl v :: ((interiorRung R v u).map (emb J R u₀) ++ [Sum.inl u])
      = (Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v])).reverse
  rw [interiorRung_reverse hRsymm huv]
  simp

/-! ### The glued graph -/

theorem mem_union_of_trackEdge {u v : U} (huv : J.Adj u v)
    {e : Sym2 (GluedVertex J R)} (he : e ∈ trackEdges (gluedTrack J R u₀ u v)) :
    e ∈ ⋃ (a : U) (b : U) (_ : J.Adj a b), trackEdges (gluedTrack J R u₀ a b) := by
  simp only [Set.mem_iUnion]
  exact ⟨u, v, huv, he⟩

theorem gluedGraph_adj_of_trackEdge (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) (i : ℕ) (hi : i + 1 < (gluedTrack J R u₀ u v).length) :
    (gluedGraph J R u₀).Adj ((gluedTrack J R u₀ u v)[i]'(by omega))
      ((gluedTrack J R u₀ u v)[i + 1]'hi) := by
  rw [gluedGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨mem_union_of_trackEdge huv ⟨i, hi, rfl⟩, ?_⟩
  intro hcon
  have := (List.Nodup.getElem_inj_iff (gluedTrack_nodup hSN hR hRsymm huv)).mp hcon
  omega

theorem gluedTrack_isTrackFrom (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) :
    IsTrackFrom (gluedGraph J R u₀) (gluedTrack J R u₀ u v) (Sum.inl u) (Sum.inl v) := by
  refine ⟨⟨?_, gluedTrack_nodup hSN hR hRsymm huv, ?_⟩, gluedTrack_head J R u₀ u v,
    gluedTrack_getLast J R u₀ u v⟩
  · show Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v]) ≠ []
    simp
  · intro i hi
    exact gluedGraph_adj_of_trackEdge hSN hR hRsymm huv i hi

/-! ### Tracks on distinct edges of `J` meet only at their ends -/

theorem trackInterior_mem_elim {u v : U} {w : GluedVertex J R}
    (hw : w ∈ trackInterior (gluedTrack J R u₀ u v)) :
    ∃ x ∈ interiorRung R u v, emb J R u₀ x = w := by
  rw [gluedTrack_interior] at hw
  exact List.mem_map.mp hw

theorem gluedTrack_mem_elim {u v : U} {w : GluedVertex J R}
    (hw : w ∈ gluedTrack J R u₀ u v) :
    w = Sum.inl u ∨ w = Sum.inl v ∨ ∃ x ∈ interiorRung R u v, emb J R u₀ x = w := by
  have hw' : w ∈ Sum.inl u :: ((interiorRung R u v).map (emb J R u₀) ++ [Sum.inl v]) := hw
  rcases List.mem_cons.mp hw' with h | h
  · exact Or.inl h
  · rcases List.mem_append.mp h with h' | h'
    · exact Or.inr (Or.inr (List.mem_map.mp h'))
    · exact Or.inr (Or.inl (List.mem_singleton.mp h'))

theorem gluedTrack_disjoint (hSN : IsJStripSystem G J S N)
    (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (u v u' v' : U) (huv : J.Adj u v) (hu'v' : J.Adj u' v') (hne : s(u, v) ≠ s(u', v'))
    (w : GluedVertex J R) (hw : w ∈ trackInterior (gluedTrack J R u₀ u v)) :
    w ∉ gluedTrack J R u₀ u' v' := by
  obtain ⟨x, hx, hxe⟩ := trackInterior_mem_elim hw
  intro hmem
  rcases gluedTrack_mem_elim hmem with h | h | ⟨y, hy, hye⟩
  · rw [← hxe, emb_mem_interior hSN hR hRsymm huv hx] at h
    exact absurd h (by simp)
  · rw [← hxe, emb_mem_interior hSN hR hRsymm huv hx] at h
    exact absurd h (by simp)
  · rw [← hxe, emb_mem_interior hSN hR hRsymm huv hx,
      emb_mem_interior hSN hR hRsymm hu'v' hy] at hye
    have hxy : y = x := by
      have h' := Sum.inr_injective hye
      simpa using h'
    subst hxy
    have h1 : y ∈ S u v := StripSystemBasics.rung_subset_strip (hR u v huv) y
      (interiorRung_subset hx)
    have h2 : y ∈ S u' v' := StripSystemBasics.rung_subset_strip (hR u' v' hu'v') y
      (interiorRung_subset hy)
    exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN huv hu'v' hne) h1 h2

/-! ### The edge dictionary -/

theorem gluedDict_spec {x₀ : V} {e : Sym2 (GluedVertex J R)}
    (h : ∃ x : V, DictPred J R u₀ e x) : DictPred J R u₀ e (gluedDict J R u₀ x₀ e) := by
  have hd : gluedDict J R u₀ x₀ e = h.choose := dif_pos h
  rw [hd]
  exact h.choose_spec

theorem dictPred_of (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    {u v : U} (huv : J.Adj u v) (i : ℕ) (a b : GluedVertex J R) (x : V)
    (ha : (gluedTrack J R u₀ u v)[i]? = some a)
    (hb : (gluedTrack J R u₀ u v)[i + 1]? = some b)
    (hx : (R u v)[i]? = some x) : DictPred J R u₀ s(a, b) x := by
  by_cases hor : Orient (U := U) u v
  · exact ⟨u, v, i, a, b, huv, hor, ha, hb, hx, rfl⟩
  · have hor' : Orient (U := U) v u := (orient_total u v).resolve_left hor
    obtain ⟨hia, hqa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hib, hqb⟩ := List.getElem?_eq_some_iff.mp hb
    set m := (R u v).length with hm
    have hqlen : (gluedTrack J R u₀ u v).length = m + 1 := gluedTrack_length hR huv
    have hrvu : R v u = (R u v).reverse := hRsymm u v huv
    have hq'len : (gluedTrack J R u₀ v u).length = m + 1 := by
      rw [gluedTrack_length hR huv.symm, hrvu, List.length_reverse]
    have hq : gluedTrack J R u₀ v u = (gluedTrack J R u₀ u v).reverse :=
      gluedTrack_reverse hRsymm huv
    have him : i < m := by omega
    refine ⟨v, u, m - 1 - i, b, a, huv.symm, hor', ?_, ?_, ?_, Sym2.eq_swap⟩
    · refine List.getElem?_eq_some_iff.mpr ⟨by omega, ?_⟩
      have e1 : (gluedTrack J R u₀ v u)[m - 1 - i]'(by omega)
          = ((gluedTrack J R u₀ u v).reverse)[m - 1 - i]'(by simp; omega) :=
        List.getElem_of_eq hq _
      rw [e1, List.getElem_reverse]
      rw [SubdivisionCounting.getElem_eq_of_index_eq (gluedTrack J R u₀ u v)
        (show (gluedTrack J R u₀ u v).length - 1 - (m - 1 - i) = i + 1 by omega) _ hib]
      exact hqb
    · refine List.getElem?_eq_some_iff.mpr ⟨by omega, ?_⟩
      have e1 : (gluedTrack J R u₀ v u)[m - 1 - i + 1]'(by omega)
          = ((gluedTrack J R u₀ u v).reverse)[m - 1 - i + 1]'(by simp; omega) :=
        List.getElem_of_eq hq _
      rw [e1, List.getElem_reverse]
      rw [SubdivisionCounting.getElem_eq_of_index_eq (gluedTrack J R u₀ u v)
        (show (gluedTrack J R u₀ u v).length - 1 - (m - 1 - i + 1) = i by omega) _ hia]
      exact hqa
    · obtain ⟨hix, hrx⟩ := List.getElem?_eq_some_iff.mp hx
      refine List.getElem?_eq_some_iff.mpr ⟨by rw [hrvu, List.length_reverse]; omega, ?_⟩
      have e1 : (R v u)[m - 1 - i]'(by rw [hrvu, List.length_reverse]; omega)
          = ((R u v).reverse)[m - 1 - i]'(by simp; omega) := List.getElem_of_eq hrvu _
      rw [e1, List.getElem_reverse]
      rw [SubdivisionCounting.getElem_eq_of_index_eq (R u v)
        (show (R u v).length - 1 - (m - 1 - i) = i by omega) _ hix]
      exact hrx

end Glue

/-- **The glued graph is a subdivision of `J`.**

Given a `J`-strip system `(S,N)` in a Berge graph `G` with `J` 3-connected, and an edge-indexed
choice of rungs `R`, the tracks

```
T u v = [inl u, inr x₁, …, inr x_k, inl v]      (R u v = [x₀, …, x_k])
```

glue into a graph `Hs` on `GluedVertex J R` which is a subdivision of `J` with `ι = Sum.inl`.
All eight conjuncts of `Tracks.IsSubdivision J Hs` are listed explicitly, so that the witnesses
`Hs`, `T` — and the edge dictionary `ρ` sending the `i`-th edge of `T u v` to the `i`-th vertex
of `R u v` — are available to the companion modules.

Disjointness of the tracks is the strip-system axiom *"the sets `S_uv` (`uv ∈ E(J)`) are
pairwise disjoint"* (`StripSystemBasics.strip_disjoint`) together with `V(R u v) ⊆ S_uv`; that
each track is a track of `Hs` is immediate from the construction, since `Hs` is *defined* by its
edge set being the union of the `trackEdges (T u v)`. -/
theorem exists_glued_subdivision {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (R : U → U → List V) (hR : ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v))
    (hRsymm : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse) :
    ∃ (Hs : SimpleGraph (GluedVertex J R)) (T : U → U → List (GluedVertex J R))
      (ρ : Sym2 (GluedVertex J R) → V),
      -- (1) `ι = Sum.inl` embeds `V(J)` into `V(Hs)`
      Function.Injective (Sum.inl : U → GluedVertex J R) ∧
      -- (2) each `T u v` is a track of `Hs` from `inl u` to `inl v`
      (∀ u v : U, J.Adj u v → IsTrackFrom Hs (T u v) (Sum.inl u) (Sum.inl v)) ∧
      -- (3) each track has at least one edge
      (∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v)) ∧
      -- (4) the family is edge-indexed
      (∀ u v : U, J.Adj u v → T v u = (T u v).reverse) ∧
      -- (5) distinct edges of `J` carry vertex-disjoint tracks, except at their ends
      (∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
        ∀ w ∈ trackInterior (T u v), w ∉ T u' v') ∧
      -- (6) interior vertices of a track are new
      (∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v),
        w ∉ Set.range (Sum.inl : U → GluedVertex J R)) ∧
      -- (7) `Hs` has no other vertices
      (∀ w : GluedVertex J R, (∃ u : U, w = Sum.inl u) ∨
        ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v)) ∧
      -- (8) `Hs` has no other edges
      (Hs.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v)) ∧
      -- the track along `uv` has one vertex more than the rung `R u v`
      (∀ u v : U, J.Adj u v → (T u v).length = (R u v).length + 1) ∧
      -- run in its chosen direction, the track is `[inl u, inr x₁, …, inr x_k, inl v]`
      (∀ u v : U, J.Adj u v → Orient u v →
        (T u v).map (Sum.map id Subtype.val)
          = (Sum.inl u : U ⊕ V) :: ((R u v).tail.map (Sum.inr : V → U ⊕ V)
              ++ [(Sum.inl v : U ⊕ V)])) ∧
      -- the edge dictionary: the `i`-th edge of `T u v` is the `i`-th vertex of `R u v`
      (∀ u v : U, J.Adj u v → ∀ (i : ℕ) (hi : i + 1 < (T u v).length),
        (R u v)[i]? = some (ρ s((T u v)[i]'(by omega), (T u v)[i + 1]'hi))) := by
  classical
  have hcard : 3 < Fintype.card U := hJ.1
  obtain ⟨u₀⟩ : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨v₀, hv₀⟩ := SubdivisionCounting.exists_adj_of_three_connected J hJ u₀
  obtain ⟨x₀, -⟩ := List.exists_mem_of_ne_nil _ (Glue.rung_ne_nil hR hv₀)
  -- (1)
  have h1 : Function.Injective (Sum.inl : U → GluedVertex J R) := Sum.inl_injective
  -- (2)
  have h2 : ∀ u v : U, J.Adj u v → IsTrackFrom (Glue.gluedGraph J R u₀)
      (Glue.gluedTrack J R u₀ u v) (Sum.inl u) (Sum.inl v) :=
    fun u v huv => Glue.gluedTrack_isTrackFrom hSN hR hRsymm huv
  -- (9)
  have h9 : ∀ u v : U, J.Adj u v →
      (Glue.gluedTrack J R u₀ u v).length = (R u v).length + 1 :=
    fun u v huv => Glue.gluedTrack_length hR huv
  -- (3)
  have h3 : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (Glue.gluedTrack J R u₀ u v) := by
    intro u v huv
    have ha := h9 u v huv
    have hb := Glue.rung_length_pos hR huv
    simp only [trackLength]
    omega
  -- (4)
  have h4 : ∀ u v : U, J.Adj u v →
      Glue.gluedTrack J R u₀ v u = (Glue.gluedTrack J R u₀ u v).reverse :=
    fun u v huv => Glue.gluedTrack_reverse hRsymm huv
  -- (5)
  have h5 : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (Glue.gluedTrack J R u₀ u v), w ∉ Glue.gluedTrack J R u₀ u' v' :=
    fun u v u' v' huv hu'v' hne w hw =>
      Glue.gluedTrack_disjoint hSN hR hRsymm u v u' v' huv hu'v' hne w hw
  -- (6)
  have h6 : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (Glue.gluedTrack J R u₀ u v),
      w ∉ Set.range (Sum.inl : U → GluedVertex J R) := by
    intro u v huv w hw
    obtain ⟨x, hx, hxe⟩ := Glue.trackInterior_mem_elim hw
    rw [Glue.emb_mem_interior hSN hR hRsymm huv hx] at hxe
    rintro ⟨a, ha⟩
    rw [← hxe] at ha
    exact absurd ha (by simp)
  -- (7)
  have h7 : ∀ w : GluedVertex J R, (∃ u : U, w = Sum.inl u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (Glue.gluedTrack J R u₀ u v) := by
    intro w
    cases w with
    | inl a => exact Or.inl ⟨a, rfl⟩
    | inr y =>
      obtain ⟨u, v, huv, hmem⟩ := Glue.rungUnion_elim y.2.1
      refine Or.inr ⟨u, v, huv, ?_⟩
      have hyI : (y : V) ∈ Glue.interiorRung R u v :=
        Glue.mem_interiorRung_of_not_chosenHead hR hRsymm huv hmem y.2.2
      rw [Glue.gluedTrack_interior]
      refine List.mem_map.mpr ⟨(y : V), hyI, ?_⟩
      rw [Glue.emb_eq_inr y.2]
  -- (8)
  have h8 : (Glue.gluedGraph J R u₀).edgeSet
      = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (Glue.gluedTrack J R u₀ u v) := by
    rw [Glue.gluedGraph, SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Set.mem_setOf_eq]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    simp only [Set.mem_iUnion] at h
    obtain ⟨u, v, huv, i, hi, rfl⟩ := h
    intro hdiag
    simp only [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] at hdiag
    have := (List.Nodup.getElem_inj_iff (Glue.gluedTrack_nodup hSN hR hRsymm huv)).mp hdiag
    omega
  -- (10)
  have h10 : ∀ u v : U, J.Adj u v → Orient u v →
      (Glue.gluedTrack J R u₀ u v).map (Sum.map id Subtype.val)
        = (Sum.inl u : U ⊕ V) :: ((R u v).tail.map (Sum.inr : V → U ⊕ V)
            ++ [(Sum.inl v : U ⊕ V)]) := by
    intro u v huv hor
    have key : (Glue.interiorRung R u v).map
        ((Sum.map id Subtype.val : GluedVertex J R → U ⊕ V) ∘ (Glue.emb J R u₀))
        = (R u v).tail.map (Sum.inr : V → U ⊕ V) := by
      rw [Glue.interiorRung_pos hor]
      refine List.map_congr_left ?_
      intro x hx
      have hxI : x ∈ Glue.interiorRung R u v := by rw [Glue.interiorRung_pos hor]; exact hx
      show Sum.map id Subtype.val (Glue.emb J R u₀ x) = _
      rw [Glue.emb_mem_interior hSN hR hRsymm huv hxI]
      rfl
    show ((Sum.inl u :: ((Glue.interiorRung R u v).map (Glue.emb J R u₀) ++ [Sum.inl v])).map
      (Sum.map id Subtype.val)) = _
    rw [List.map_cons, List.map_append, List.map_map, List.map_singleton, key]
    rfl
  -- (11)
  have hedgedisj : ∀ (u v u' v' : U), J.Adj u v → J.Adj u' v' →
      ∀ f : Sym2 (GluedVertex J R), f ∈ trackEdges (Glue.gluedTrack J R u₀ u v) →
        f ∈ trackEdges (Glue.gluedTrack J R u₀ u' v') → s(u, v) = s(u', v') :=
    fun u v u' v' huv hu'v' f hf1 hf2 =>
      SubdivisionCounting.trackEdges_disjoint h1 h2 h3 h5 u v u' v' huv hu'v' f hf1 hf2
  have huniq : ∀ (e : Sym2 (GluedVertex J R)) (x y : V),
      Glue.DictPred J R u₀ e x → Glue.DictPred J R u₀ e y → x = y := by
    rintro e x y ⟨u, v, i, a, b, huv, hor, ha, hb, hx, rfl⟩
      ⟨u', v', i', a', b', hu'v', hor', ha', hb', hy, he⟩
    obtain ⟨hia, hqa⟩ := List.getElem?_eq_some_iff.mp ha
    obtain ⟨hib, hqb⟩ := List.getElem?_eq_some_iff.mp hb
    obtain ⟨hia', hqa'⟩ := List.getElem?_eq_some_iff.mp ha'
    obtain ⟨hib', hqb'⟩ := List.getElem?_eq_some_iff.mp hb'
    have hf1 : s(a, b) ∈ trackEdges (Glue.gluedTrack J R u₀ u v) := ⟨i, hib, by rw [hqa, hqb]⟩
    have hf2 : s(a, b) ∈ trackEdges (Glue.gluedTrack J R u₀ u' v') :=
      ⟨i', hib', by rw [hqa', hqb', ← he]⟩
    have hedge := hedgedisj u v u' v' huv hu'v' _ hf1 hf2
    have huu : u = u' ∧ v = v' := by
      rcases Sym2.eq_iff.mp hedge with h | h
      · exact h
      · exfalso
        obtain ⟨h1', h2'⟩ := h
        subst h1'; subst h2'
        exact huv.ne (Glue.orient_antisymm hor hor')
    obtain ⟨hu, hv⟩ := huu
    subst hu; subst hv
    have hnd := Glue.gluedTrack_nodup hSN hR hRsymm huv (u₀ := u₀)
    have hii : i = i' := by
      rw [← hqa, ← hqb, ← hqa', ← hqb'] at he
      rcases Sym2.eq_iff.mp he with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact (List.Nodup.getElem_inj_iff hnd).mp e1
      · have j1 := (List.Nodup.getElem_inj_iff hnd).mp e1
        have j2 := (List.Nodup.getElem_inj_iff hnd).mp e2
        omega
    subst hii
    rw [hx] at hy
    exact Option.some_injective _ hy
  have h11 : ∀ u v : U, J.Adj u v → ∀ (i : ℕ)
      (hi : i + 1 < (Glue.gluedTrack J R u₀ u v).length),
      (R u v)[i]? = some (Glue.gluedDict J R u₀ x₀
        s((Glue.gluedTrack J R u₀ u v)[i]'(by omega),
          (Glue.gluedTrack J R u₀ u v)[i + 1]'hi)) := by
    intro u v huv i hi
    have hlt : i < (R u v).length := by have := h9 u v huv; omega
    have hx : (R u v)[i]? = some ((R u v)[i]'hlt) := List.getElem?_eq_getElem hlt
    have hp : Glue.DictPred J R u₀
        s((Glue.gluedTrack J R u₀ u v)[i]'(by omega),
          (Glue.gluedTrack J R u₀ u v)[i + 1]'hi) ((R u v)[i]'hlt) :=
      Glue.dictPred_of hR hRsymm huv i _ _ _ (List.getElem?_eq_getElem (by omega))
        (List.getElem?_eq_getElem hi) hx
    have hex : ∃ z : V, Glue.DictPred J R u₀
        s((Glue.gluedTrack J R u₀ u v)[i]'(by omega),
          (Glue.gluedTrack J R u₀ u v)[i + 1]'hi) z := ⟨_, hp⟩
    have := huniq _ _ _ hp (Glue.gluedDict_spec (x₀ := x₀) hex)
    rw [hx, this]
  exact ⟨Glue.gluedGraph J R u₀, Glue.gluedTrack J R u₀, Glue.gluedDict J R u₀ x₀,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

end Workspace.ProofLemmas.Thm84GluedSubdivision
