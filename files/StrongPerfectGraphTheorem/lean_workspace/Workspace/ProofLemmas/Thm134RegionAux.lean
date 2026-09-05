import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics

set_option autoImplicit false

/-!
# Auxiliary facts for the region analysis of 13.4

The proof of claim (1) of 13.4 (printed p. 84) uses, without comment, three
routine facts about the strip `S = (A, C, B)` and about components:

* *"since `B ∪ C` is connected"* — `stripFarSideConnected`;
* *"and all vertices in `A` have neighbours in it"* — `stripVertexHasFarNeighbour`;
* *"`F` is a component of `V(G) \ (A ∪ A₀ ∪ N)`"* — which needs that no vertex of
  `H` outside the component `F` has a neighbour in `F`
  (`component_no_outside_neighbour`).

`connectedSet_of_isPathList` (the vertex set of a path is connected) is the tool
all of them are built from.
-/

namespace Workspace.ProofLemmas.Thm134RegionAux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- A singleton is connected. -/
theorem connectedSet_singleton (G : SimpleGraph V) (v : V) :
    ConnectedSet G ({v} : Set V) := by
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

/-- The vertex set of a path is connected. -/
theorem connectedSet_of_isPathList :
    ∀ p : List V, IsPathList G p → ConnectedSet G {v : V | v ∈ p} := by
  intro p
  induction p with
  | nil => intro h; exact absurd rfl h.1
  | cons a q ih =>
    intro h
    rcases eq_or_ne q [] with rfl | hq
    · have he : {v : V | v ∈ [a]} = ({a} : Set V) := by ext x; simp
      rw [he]
      exact connectedSet_singleton G a
    · have hqlen : 0 < q.length := List.length_pos_of_ne_nil hq
      have hq' : IsPathList G q := by
        have hd := PathBasics.isPathList_drop h (k := 1) (by simp; omega)
        simpa using hd
      have hadj : G.Adj a (q[0]'hqlen) := by
        have := PathBasics.path_adj_succ h (i := 0) (by simp; omega)
        simpa using this
      have he : {v : V | v ∈ a :: q} = {v : V | v ∈ q} ∪ ({a} : Set V) := by
        ext x; simp only [Set.mem_setOf_eq, List.mem_cons, Set.mem_union,
          Set.mem_singleton_iff]; tauto
      rw [he]
      exact ConnectedSetUnionAttach.connectedSet_union_singleton (ih hq')
        ⟨q[0]'hqlen, List.getElem_mem hqlen, hadj⟩

/-- A walk of `G|X` lifts to `G|Y` whenever `X ⊆ Y`. -/
theorem reachable_mono {X Y : Set V} (hXY : X ⊆ Y) {x y : V} (hx : x ∈ X) (hy : y ∈ X)
    (hr : (G.induce X).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce Y).Reachable ⟨x, hXY hx⟩ ⟨y, hXY hy⟩ := by
  obtain ⟨w⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hXY z.2⟩, fun {_ _} hab => hab⟩ : (G.induce X) →g (G.induce Y)) w⟩

/-- The head of a repetition-free list does not occur in its tail. -/
private theorem head_not_mem_tail {p : List V} (hnd : p.Nodup) (hne : p ≠ [])
    {a : V} (ha : p.head? = some a) : a ∉ p.tail := by
  have hh : p.head hne = a := by
    have := List.head?_eq_head hne
    rw [ha] at this
    exact (Option.some_injective _ this).symm
  have hcons : p.head hne :: p.tail = p := List.cons_head_tail hne
  rw [← hcons] at hnd
  have := (List.nodup_cons.mp hnd).1
  rwa [hh] at this

/-- The tail of a rung `a`-`P`-`b` lies in `B ∪ C` and is connected. -/
theorem rung_tail {A C B : Set V} {a b : V} {P : List V}
    (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hr : IsRungOfStrip G A C B a P b) :
    (∀ w ∈ P.tail, w ∈ B ∪ C) ∧ ConnectedSet G {v : V | v ∈ P.tail} ∧
      b ∈ P.tail ∧ (∀ w ∈ P, w ≠ a → w ∈ P.tail) := by
  obtain ⟨hP, haA, hbB, hAonly, hBonly, hCint⟩ := hr
  have hne : P ≠ [] := hP.1.1
  have hnd : P.Nodup := hP.1.2.1
  have hanot : a ∉ P.tail := head_not_mem_tail hnd hne hP.2.1
  have hmemP : ∀ w, w ∈ P.tail → w ∈ P := fun w hw => (List.tail_sublist P).subset hw
  have hsplit : ∀ w ∈ P, w ≠ a → w ∈ P.tail := by
    intro w hw hwa
    have hcons : P.head hne :: P.tail = P := List.cons_head_tail hne
    have hh : P.head hne = a := by
      have := List.head?_eq_head hne
      rw [hP.2.1] at this
      exact (Option.some_injective _ this).symm
    rw [← hcons, hh] at hw
    rcases List.mem_cons.mp hw with h | h
    · exact absurd h hwa
    · exact h
  have hbtail : b ∈ P.tail := by
    refine hsplit b (PathBasics.getLast_mem hP.2.2) ?_
    intro hba
    exact (Set.disjoint_left.mp hAB haA) (hba ▸ hbB)
  have hsub : ∀ w ∈ P.tail, w ∈ B ∪ C := by
    intro w hw
    by_cases hwb : w = b
    · exact Or.inl (hwb ▸ hbB)
    · refine Or.inr (hCint w ?_)
      refine (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hmemP w hw, ?_, hwb⟩
      intro h; exact hanot (h ▸ hw)
  refine ⟨hsub, ?_, hbtail, hsplit⟩
  -- the tail of a path is a path
  have htail : IsPathList G P.tail := by
    have hd := PathBasics.isPathList_drop hP.1 (k := 1) ?_
    · simpa using hd
    · have := PathBasics.path_length_pos hP.1
      by_contra hcon
      push_neg at hcon
      have hlen1 : P.length = 1 := by omega
      obtain ⟨x, hxe⟩ := List.length_eq_one_iff.mp hlen1
      rw [hxe] at hbtail
      simp at hbtail
  exact connectedSet_of_isPathList P.tail htail

/-- Every vertex of `A` has a neighbour in `B ∪ C`: the rung through it is a path
from it to `B` whose interior lies in `C`. -/
theorem stripVertexHasFarNeighbour {A C B : Set V} (h : StepConnected G A C B) :
    ∀ a ∈ A, ∃ x ∈ B ∪ C, G.Adj a x := by
  obtain ⟨⟨hAB, hAC, hBC⟩, -, hrung, -, -⟩ := h
  intro a ha
  obtain ⟨a', P, b', hr, hmem⟩ := hrung a (Or.inl (Or.inl ha))
  have haa : a = a' := hr.2.2.2.1 a hmem ha
  subst haa
  obtain ⟨hsub, -, hbtail, -⟩ := rung_tail hAB hAC hr
  have hP := hr.1
  have hlen : 2 ≤ P.length := by
    by_contra hcon
    push_neg at hcon
    have hpos := PathBasics.path_length_pos hP.1
    have hlen1 : P.length = 1 := by omega
    obtain ⟨x, hxe⟩ := List.length_eq_one_iff.mp hlen1
    rw [hxe] at hbtail
    simp at hbtail
  have hadj : G.Adj (P[0]'(by omega)) (P[1]'(by omega)) :=
    PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
  have h0 : P[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  refine ⟨P[1]'(by omega), hsub _ ?_, by rw [← h0]; exact hadj⟩
  -- `P[1]` lies in the tail
  refine hr.2.2.2.2.2 |> fun _ => ?_
  have hmem1 : (P[1]'(by omega)) ∈ P := List.getElem_mem (by omega)
  refine (rung_tail hAB hAC hr).2.2.2 _ hmem1 ?_
  intro hcon
  have := PathBasics.path_ne_of_ne_index hP.1 (i := 1) (j := 0) (by omega) (by omega)
    (by omega)
  exact this (by rw [hcon, h0])

/-- **`B ∪ C` is connected** (used without comment in the proof of 13.4(1)).

Every vertex of `C` lies on a rung, and the tail of that rung is a connected
subset of `B ∪ C` reaching `B`; and `B` itself is connected inside `B ∪ C`
because of the second step-connectedness condition — for the partition of `B`
into "reaches `b₀`" and "does not", a step would supply an edge across it. -/
theorem stripFarSideConnected {A C B : Set V} (h : StepConnected G A C B) :
    ConnectedSet G (B ∪ C) := by
  obtain ⟨⟨hAB, hAC, hBC⟩, ⟨hAne, hBne⟩, hrung, hstep, hpart⟩ := h
  obtain ⟨b0, hb0⟩ := hBne
  have hb0S : b0 ∈ B ∪ C := Or.inl hb0
  -- (a) every vertex of `B` reaches `b0` inside `B ∪ C`
  have hBreach : ∀ (b : V) (hb : b ∈ B),
      (G.induce (B ∪ C)).Reachable ⟨b, Or.inl hb⟩ ⟨b0, hb0S⟩ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨b1, hb1B, hb1n⟩ := hcon
    set X : Set V := {x : V | x ∈ B ∧ ∀ hx : x ∈ B ∪ C,
      (G.induce (B ∪ C)).Reachable ⟨x, hx⟩ ⟨b0, hb0S⟩} with hXdef
    have hXB : X ⊆ B := fun x hx => hx.1
    have hb0X : b0 ∈ X := ⟨hb0, fun _ => SimpleGraph.Reachable.refl _⟩
    have hb1Y : b1 ∈ B \ X := ⟨hb1B, fun hc => hb1n (hc.2 (Or.inl hb1B))⟩
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, h1, h2⟩ :=
      hpart X (B \ X) (Or.inr (Set.union_diff_cancel hXB))
        (Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx) ⟨b0, hb0X⟩ ⟨b1, hb1Y⟩
    obtain ⟨hr1, hr2, -, hadjst⟩ := hs
    have ha₁A : a₁ ∈ A := hr1.2.1
    have hb₁B : b₁ ∈ B := hr1.2.2.1
    have ha₂A : a₂ ∈ A := hr2.2.1
    have hb₂B : b₂ ∈ B := hr2.2.2.1
    have hb₁X : b₁ ∈ X := by
      rcases h1 with hh | hh
      · exact absurd (hXB hh) (Set.disjoint_left.mp hAB ha₁A)
      · exact hh
    have hb₂Y : b₂ ∈ B \ X := by
      rcases h2 with hh | hh
      · exact absurd hh.1 (Set.disjoint_left.mp hAB ha₂A)
      · exact hh
    have hb₁mem : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
    have hb₂mem : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
    have hedge : G.Adj b₁ b₂ := (hadjst b₁ hb₁mem b₂ hb₂mem).mpr (Or.inr ⟨rfl, rfl⟩)
    refine hb₂Y.2 ⟨hb₂B, fun hx => ?_⟩
    have hstep' : (G.induce (B ∪ C)).Adj ⟨b₂, hx⟩ ⟨b₁, Or.inl hb₁B⟩ := hedge.symm
    exact hstep'.reachable.trans (hb₁X.2 (Or.inl hb₁B))
  -- (b) every vertex of `B ∪ C` reaches `b0`
  have key : ∀ (x : V) (hx : x ∈ B ∪ C),
      (G.induce (B ∪ C)).Reachable ⟨x, hx⟩ ⟨b0, hb0S⟩ := by
    intro x hx
    rcases hx with hxB | hxC
    · exact hBreach x hxB
    · obtain ⟨a', P, b', hr, hmem⟩ := hrung x (Or.inr hxC)
      obtain ⟨hsub, hconn, hbtail, hsplit⟩ := rung_tail hAB hAC hr
      have hxa : x ≠ a' := by
        intro hh
        exact (Set.disjoint_left.mp hAC hr.2.1) (hh ▸ hxC)
      have hxtail : x ∈ P.tail := hsplit x hmem hxa
      have hreach : (G.induce {v : V | v ∈ P.tail}).Reachable ⟨x, hxtail⟩ ⟨b', hbtail⟩ :=
        hconn ⟨x, hxtail⟩ ⟨b', hbtail⟩
      have hmono := reachable_mono (G := G) (X := {v : V | v ∈ P.tail}) (Y := B ∪ C)
        (fun w hw => hsub w hw) hxtail hbtail hreach
      exact hmono.trans (hBreach b' hr.2.2.1)
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  exact (key u hu).trans (key v hv).symm

/-- No vertex of `S` outside a component `F` of `S` has a neighbour in `F`. -/
theorem component_no_outside_neighbour [Fintype V] {S F : Set V}
    (hF : IsComponent G S F) {v : V} (hvS : v ∈ S) (hvF : v ∉ F) :
    ∀ f ∈ F, ¬ G.Adj v f := by
  intro f hf hadj
  have hconn : ConnectedSet G (F ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hf, hadj⟩
  have := hF.2.2 (F ∪ {v}) Set.subset_union_left
    (Set.union_subset hF.1 (Set.singleton_subset_iff.mpr hvS)) hconn
  exact hvF (this ▸ (Or.inr rfl : v ∈ F ∪ {v}))

end Workspace.ProofLemmas.Thm134RegionAux
