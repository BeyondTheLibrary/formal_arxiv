import Mathlib

/-!
# Orientations of a multigraph

An *orientation* of a multigraph `G : Graph α β` chooses, for each edge `e`, which of its two
ends is the **tail** and which is the **head**. `Orientation G` bundles total functions
`tail head : β → α` with the single axiom `G.IsLink e (tail e) (head e)` for every `e ∈ E(G)`,
so `tail e`, `head e` are the two ends of `e` in some order (equal on a loop). Values on
non-edges are junk and must never be observed. Every multigraph over a nonempty vertex type
admits an orientation (`Orientation.ofGraph`; the hypothesis is necessary, see `nonempty_iff`).
-/

open Graph
open scoped Graph

namespace Workspace.Types.Orientation

variable {α β : Type*} {G H : Graph α β} {e : β} {x y : α}

/-- An **orientation** of the multigraph `G`: each edge `e` of `G` is assigned a `tail` and a
`head`, which are required to be the two ends of `e`. The values of `tail`/`head` outside of
`E(G)` are arbitrary junk and carry no meaning. -/
@[ext]
structure Orientation (G : Graph α β) where
  /-- The vertex an edge is directed *out of*. Meaningful only on `E(G)`. -/
  tail : β → α
  /-- The vertex an edge is directed *into*. Meaningful only on `E(G)`. -/
  head : β → α
  /-- For every edge of `G`, its tail and head are its two ends. -/
  isLink_tail_head : ∀ ⦃e⦄, e ∈ E(G) → G.IsLink e (tail e) (head e)

namespace Orientation

variable (O : Orientation G)

/-! ### Basic incidence facts -/

/-- The tail of an edge is an end of that edge. -/
lemma isLink_head_tail (he : e ∈ E(G)) : G.IsLink e (O.head e) (O.tail e) :=
  (O.isLink_tail_head he).symm

/-- The tail of an edge of `G` is incident to it. -/
lemma inc_tail (he : e ∈ E(G)) : G.Inc e (O.tail e) :=
  (O.isLink_tail_head he).inc_left

/-- The head of an edge of `G` is incident to it. -/
lemma inc_head (he : e ∈ E(G)) : G.Inc e (O.head e) :=
  (O.isLink_tail_head he).inc_right

/-- The tail of an edge of `G` is a vertex of `G`. -/
lemma tail_mem (he : e ∈ E(G)) : O.tail e ∈ V(G) :=
  (O.isLink_tail_head he).left_mem

/-- The head of an edge of `G` is a vertex of `G`. -/
lemma head_mem (he : e ∈ E(G)) : O.head e ∈ V(G) :=
  (O.isLink_tail_head he).right_mem

/-- The ends of an edge, as seen by an orientation, are the ends of that edge in some order. -/
lemma eq_and_eq_or_eq_and_eq (h : G.IsLink e x y) :
    (O.tail e = x ∧ O.head e = y) ∨ (O.tail e = y ∧ O.head e = x) :=
  (O.isLink_tail_head h.edge_mem).eq_and_eq_or_eq_and_eq h

/-- An orientation recovers the link relation: for an edge of `G`, the ends of `e` are exactly
`tail e` and `head e`, up to swapping. -/
lemma isLink_iff (he : e ∈ E(G)) :
    G.IsLink e x y ↔ (O.tail e = x ∧ O.head e = y) ∨ (O.tail e = y ∧ O.head e = x) :=
  (O.isLink_tail_head he).isLink_iff

/-- A vertex is incident to an edge of `G` exactly when it is its tail or its head. -/
lemma inc_iff (he : e ∈ E(G)) : G.Inc e x ↔ x = O.tail e ∨ x = O.head e :=
  ⟨fun h ↦ h.eq_or_eq_of_isLink (O.isLink_tail_head he), by
    rintro (rfl | rfl)
    · exact O.inc_tail he
    · exact O.inc_head he⟩

/-! ### Loops -/

/-- On a loop, the tail is the loop's vertex. -/
lemma tail_eq_of_isLoopAt (h : G.IsLoopAt e x) : O.tail e = x :=
  (h.eq_of_inc (O.inc_tail h.edge_mem)).symm

/-- On a loop, the head is the loop's vertex. -/
lemma head_eq_of_isLoopAt (h : G.IsLoopAt e x) : O.head e = x :=
  (h.eq_of_inc (O.inc_head h.edge_mem)).symm

/-- On a loop, tail and head coincide (with the loop's vertex). -/
lemma tail_eq_head_of_isLoopAt (h : G.IsLoopAt e x) : O.tail e = O.head e := by
  rw [O.tail_eq_of_isLoopAt h, O.head_eq_of_isLoopAt h]

/-- An edge of `G` is a loop exactly when its tail and head agree. -/
lemma isLoopAt_tail_iff_tail_eq_head (he : e ∈ E(G)) :
    G.IsLoopAt e (O.tail e) ↔ O.tail e = O.head e := by
  refine ⟨fun h ↦ O.tail_eq_head_of_isLoopAt h, fun h ↦ ?_⟩
  have := O.isLink_tail_head he
  rwa [← h] at this

/-! ### Reversal -/

/-- Reversing an orientation: swap tails and heads. -/
@[simps]
def reverse (O : Orientation G) : Orientation G where
  tail := O.head
  head := O.tail
  isLink_tail_head _ he := (O.isLink_tail_head he).symm

@[simp]
lemma reverse_reverse (O : Orientation G) : O.reverse.reverse = O := rfl

lemma reverse_injective : Function.Injective (reverse (G := G)) :=
  Function.LeftInverse.injective reverse_reverse

/-! ### Restriction to a subgraph -/

/-- An orientation of `G` restricts to an orientation of any subgraph `H ≤ G`: since `H` and `G`
agree on the ends of every edge of `H`, the same `tail`/`head` functions work. -/
@[simps]
def restrict (O : Orientation G) (hHG : H ≤ G) : Orientation H where
  tail := O.tail
  head := O.head
  isLink_tail_head _ he := (hHG.isLink_iff he).2 (O.isLink_tail_head (hHG.edgeSet_mono he))

/-! ### Existence -/

open Classical in
/-- Every multigraph over a nonempty vertex type has an orientation: pick, for each edge, some
pair of ends via choice (and an arbitrary junk value on non-edges). -/
noncomputable def ofGraph [Nonempty α] (G : Graph α β) : Orientation G where
  tail e := if he : e ∈ E(G) then (G.exists_isLink_of_mem_edgeSet he).choose
            else Classical.arbitrary α
  head e := if he : e ∈ E(G) then (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose
            else Classical.arbitrary α
  isLink_tail_head e he := by
    simp only [dif_pos he]
    exact (G.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec

/-- **Existence of orientations**: every multigraph with a nonempty vertex type can be oriented. -/
theorem exists_orientation [Nonempty α] (G : Graph α β) : Nonempty (Orientation G) :=
  ⟨ofGraph G⟩

instance [Nonempty α] : Nonempty (Orientation G) := exists_orientation G

/-- If `G` has at least one edge, it has an orientation (its vertex type is then automatically
nonempty). -/
theorem nonempty_of_edgeSet_nonempty (h : E(G).Nonempty) : Nonempty (Orientation G) := by
  obtain ⟨e, he⟩ := h
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  have : Nonempty α := ⟨x⟩
  exact exists_orientation G

/-- A graph admits an orientation iff there is somewhere for `tail`/`head` to send edges: either
the edge type is empty (so the junk data is vacuous) or the vertex type is nonempty. This makes
precise that the `Nonempty α` hypothesis in `exists_orientation` is honest and unavoidable. -/
theorem nonempty_iff : Nonempty (Orientation G) ↔ (IsEmpty β ∨ Nonempty α) := by
  constructor
  · rintro ⟨O⟩
    rcases isEmpty_or_nonempty β with hβ | ⟨⟨e⟩⟩
    · exact Or.inl hβ
    · exact Or.inr ⟨O.tail e⟩
  · rintro (hβ | hα)
    · exact ⟨⟨fun e ↦ (hβ.false e).elim, fun e ↦ (hβ.false e).elim,
        fun e _ ↦ (hβ.false e).elim⟩⟩
    · exact exists_orientation G

end Orientation

end Workspace.Types.Orientation
