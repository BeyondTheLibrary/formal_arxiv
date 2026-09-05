import Mathlib
import Workspace.Types.Core

/-!
# Adding one new vertex with a prescribed neighbourhood, and transport along `Sum.inl`

§1 of the proof of 1.5 reads:

> *"Let `G'` be the graph obtained from `G` by adding a new vertex `z` with
> neighbour set `B₁`."*

This module introduces that graph as `addPendantVertex G S` (notation `G +ᵥ S`), on
the vertex type `V ⊕ Unit`, with the new vertex `z := Sum.inr ()`; the paper's `G'`
is `G +ᵥ B₁`.

It is **not** an instance of `Workspace.Types.Replication.replicateVertex`: the new
vertex is not a twin of an old one (it is adjacent to all of `S` and to nothing
else, whereas a replicated vertex is adjacent to a chosen vertex as well as to that
vertex's neighbourhood).  So the definition really is new, and — because every
downstream node of the 1.5 proof depends on its exact shape — it is deliberately
kept in the same module as its transport clauses, so that no second, incompatible
copy of the definition can appear.

Everything is stated at the `List.map Sum.inl` level rather than through subtypes
and `SimpleGraph.induce`.  That is what lets §3 of the proof avoid an "ambient list
all of whose vertices lie in `S` comes from an induced list" lemma: a hole of `G'`
avoiding `z` *is literally* `c.map Sum.inl` for a list `c` over `V`
(`exists_eq_map_inl`), and the transport clauses then move it to `G` and back.

None of these lemmas has a counterpart in the paper; they are bookkeeping.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.AddPendantVertexTransport

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V W : Type*}

/-! ### The definition -/

/-- PAPER (§1 of the proof of 1.5): *"Let `G'` be the graph obtained from `G` by
adding a new vertex `z` with neighbour set `B₁`."*

`addPendantVertex G S` is the graph on `V ⊕ Unit` whose restriction to the copy
`Sum.inl '' V` of `V` is `G`, and whose new vertex `z = Sum.inr ()` is adjacent
exactly to the vertices `Sum.inl a` with `a ∈ S`. -/
def addPendantVertex (G : SimpleGraph V) (S : Set V) : SimpleGraph (V ⊕ Unit) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => G.Adj a b
    | Sum.inl a, Sum.inr _ => a ∈ S
    | Sum.inr _, Sum.inl b => b ∈ S
    | Sum.inr _, Sum.inr _ => False
  symm := by
    rintro (a | u) (b | v) h
    · exact (h : G.Adj a b).symm
    · exact (h : a ∈ S)
    · exact (h : b ∈ S)
    · exact (h : False)
  loopless := by
    constructor
    rintro (a | u) h
    · exact G.loopless.irrefl a (h : G.Adj a a)
    · exact (h : False)

@[inherit_doc] scoped infixl:65 " +ᵥ " => addPendantVertex

/-! ### (a) The four defining adjacency equations -/

/-- Two old vertices are adjacent in `G +ᵥ S` exactly when they are adjacent in `G`. -/
theorem adj_inl_inl (G : SimpleGraph V) (S : Set V) (a b : V) :
    (G +ᵥ S).Adj (Sum.inl a) (Sum.inl b) ↔ G.Adj a b := by
  exact Iff.rfl

/-- The new vertex is adjacent to exactly the old vertices lying in `S`. -/
theorem adj_inl_inr (G : SimpleGraph V) (S : Set V) (a : V) (u : Unit) :
    (G +ᵥ S).Adj (Sum.inl a) (Sum.inr u) ↔ a ∈ S := by
  exact Iff.rfl

/-- The new vertex is adjacent to exactly the old vertices lying in `S`. -/
theorem adj_inr_inl (G : SimpleGraph V) (S : Set V) (b : V) (u : Unit) :
    (G +ᵥ S).Adj (Sum.inr u) (Sum.inl b) ↔ b ∈ S := by
  exact Iff.rfl

/-- There is only one new vertex, and no loop at it. -/
theorem not_adj_inr_inr (G : SimpleGraph V) (S : Set V) (u v : Unit) :
    ¬ (G +ᵥ S).Adj (Sum.inr u) (Sum.inr v) := by
  exact id

/-! ### (b) The complement -/

/-- Complementation commutes with the inclusion of the old vertices. -/
theorem compl_adj_inl_inl (G : SimpleGraph V) (S : Set V) (a b : V) :
    ((G +ᵥ S)ᶜ).Adj (Sum.inl a) (Sum.inl b) ↔ Gᶜ.Adj a b := by
  constructor
  · rintro ⟨hne, hadj⟩
    exact ⟨fun h => hne (by rw [h]), hadj⟩
  · rintro ⟨hne, hadj⟩
    exact ⟨fun h => hne (Sum.inl_injective h), hadj⟩

/-- In the complement, the new vertex is adjacent to exactly the old vertices
*outside* `S`. -/
theorem compl_adj_inl_inr (G : SimpleGraph V) (S : Set V) (a : V) (u : Unit) :
    ((G +ᵥ S)ᶜ).Adj (Sum.inl a) (Sum.inr u) ↔ a ∉ S := by
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨Sum.inl_ne_inr, h⟩

/-! ### (c) Transport of paths and holes along `Sum.inl` -/

/-- Generic transport of `IsPathList` along an injection that reflects adjacency. -/
private theorem isPathList_map_gen {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b : V, H.Adj (f a) (f b) ↔ G.Adj a b) (p : List V) :
    IsPathList G p ↔ IsPathList H (p.map f) := by
  constructor
  · rintro ⟨hne, hnd, hp⟩
    refine ⟨by simpa using hne, hnd.map hf, ?_⟩
    intro i j hi hj
    simp only [List.getElem_map]
    rw [hadj]
    exact hp i j (by simpa using hi) (by simpa using hj)
  · rintro ⟨hne, hnd, hp⟩
    refine ⟨by simpa using hne, hnd.of_map, ?_⟩
    intro i j hi hj
    have hh := hp i j (by simpa using hi) (by simpa using hj)
    simp only [List.getElem_map] at hh
    rw [hadj] at hh
    exact hh

/-- Generic transport of `IsHoleList` along an injection that reflects adjacency. -/
private theorem isHoleList_map_gen {G : SimpleGraph V} {H : SimpleGraph W}
    (f : V → W) (hf : Function.Injective f)
    (hadj : ∀ a b : V, H.Adj (f a) (f b) ↔ G.Adj a b) (c : List V) :
    IsHoleList G c ↔ IsHoleList H (c.map f) := by
  constructor
  · rintro ⟨h4, hnd, hc⟩
    refine ⟨by simpa using h4, hnd.map hf, ?_⟩
    intro i j hi hj
    simp only [List.getElem_map, List.length_map]
    rw [hadj]
    exact hc i j (by simpa using hi) (by simpa using hj)
  · rintro ⟨h4, hnd, hc⟩
    refine ⟨by simpa using h4, hnd.of_map, ?_⟩
    intro i j hi hj
    have hh := hc i j (by simpa using hi) (by simpa using hj)
    simp only [List.getElem_map, List.length_map] at hh
    rw [hadj] at hh
    exact hh

/-- `head?` transports along an injection. -/
private theorem head?_map_iff {f : V → W} (hf : Function.Injective f) (p : List V) (u : V) :
    p.head? = some u ↔ (p.map f).head? = some (f u) := by
  rw [List.head?_map]
  rcases p with _ | ⟨a, t⟩
  · simp
  · simp only [List.head?_cons, Option.map_some, Option.some.injEq]
    exact ⟨fun h => by rw [h], fun h => hf h⟩

/-- `getLast?` transports along an injection. -/
private theorem getLast?_map_iff {f : V → W} (hf : Function.Injective f) (p : List V) (v : V) :
    p.getLast? = some v ↔ (p.map f).getLast? = some (f v) := by
  rw [List.getLast?_map]
  rcases h : p.getLast? with _ | a
  · simp
  · simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun hh => by rw [hh], fun hh => hf hh⟩

/-- Paths of `G` are exactly the paths of `G +ᵥ S` avoiding the new vertex. -/
theorem isPathList_map_inl (G : SimpleGraph V) (S : Set V) (p : List V) :
    IsPathList G p ↔ IsPathList (G +ᵥ S) (p.map Sum.inl) := by
  exact isPathList_map_gen Sum.inl Sum.inl_injective (fun a b => adj_inl_inl G S a b) p

/-- Holes of `G` are exactly the holes of `G +ᵥ S` avoiding the new vertex. -/
theorem isHoleList_map_inl (G : SimpleGraph V) (S : Set V) (c : List V) :
    IsHoleList G c ↔ IsHoleList (G +ᵥ S) (c.map Sum.inl) := by
  exact isHoleList_map_gen Sum.inl Sum.inl_injective (fun a b => adj_inl_inl G S a b) c

/-- The complement version of `isPathList_map_inl` (antipaths). -/
theorem isPathList_compl_map_inl (G : SimpleGraph V) (S : Set V) (p : List V) :
    IsPathList Gᶜ p ↔ IsPathList ((G +ᵥ S)ᶜ) (p.map Sum.inl) := by
  exact isPathList_map_gen Sum.inl Sum.inl_injective (fun a b => compl_adj_inl_inl G S a b) p

/-- The complement version of `isHoleList_map_inl` (antiholes). -/
theorem isHoleList_compl_map_inl (G : SimpleGraph V) (S : Set V) (c : List V) :
    IsHoleList Gᶜ c ↔ IsHoleList ((G +ᵥ S)ᶜ) (c.map Sum.inl) := by
  exact isHoleList_map_gen Sum.inl Sum.inl_injective (fun a b => compl_adj_inl_inl G S a b) c

/-- Transport of a path with named ends. -/
theorem isPathFrom_map_inl (G : SimpleGraph V) (S : Set V) (p : List V) (u v : V) :
    IsPathFrom G p u v ↔
      IsPathFrom (G +ᵥ S) (p.map Sum.inl) (Sum.inl u) (Sum.inl v) := by
  exact and_congr (isPathList_map_inl G S p)
    (and_congr (head?_map_iff Sum.inl_injective p u) (getLast?_map_iff Sum.inl_injective p v))

/-- Transport of an antipath with named ends. -/
theorem isPathFrom_compl_map_inl (G : SimpleGraph V) (S : Set V) (p : List V) (u v : V) :
    IsPathFrom Gᶜ p u v ↔
      IsPathFrom ((G +ᵥ S)ᶜ) (p.map Sum.inl) (Sum.inl u) (Sum.inl v) := by
  exact and_congr (isPathList_compl_map_inl G S p)
    (and_congr (head?_map_iff Sum.inl_injective p u) (getLast?_map_iff Sum.inl_injective p v))

/-! ### (d) The numerical and structural data are `List.map`-invariant -/

/-- `pathLength` only sees the length of the list. -/
theorem pathLength_map (f : V → W) (p : List V) :
    pathLength (p.map f) = pathLength p := by
  simp [pathLength]

/-- `holeLength` only sees the length of the list. -/
theorem holeLength_map (f : V → W) (c : List V) :
    holeLength (c.map f) = holeLength c := by
  simp [holeLength]

/-- The interior of a mapped list is the mapped interior.  (Mathlib's names here are
`List.map_tail` and `List.map_dropLast`; there is no `List.tail_map` nor
`List.dropLast_map`.) -/
theorem interior_map (f : V → W) (p : List V) :
    SPGT.interior (p.map f) = (SPGT.interior p).map f := by
  simp only [SPGT.interior, List.map_tail, List.map_dropLast]

/-! ### (e) Lists over `V ⊕ Unit` avoiding the new vertex come from `V` -/

/-- A list over `V ⊕ Unit` with no entry equal to the new vertex is the image of a
list over `V` of the same length.  (Take `ℓ₀ := ℓ.filterMap Sum.getLeft?`.) -/
theorem exists_eq_map_inl {ℓ : List (V ⊕ Unit)} (h : ∀ x ∈ ℓ, x ≠ Sum.inr ()) :
    ∃ ℓ₀ : List V, ℓ = ℓ₀.map Sum.inl ∧ ℓ₀.length = ℓ.length := by
  induction ℓ with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons x t ih =>
      obtain ⟨t₀, ht, htlen⟩ := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
      rcases x with a | u
      · exact ⟨a :: t₀, by rw [List.map_cons, ← ht], by simp [htlen]⟩
      · exact absurd (by cases u; rfl) (h (Sum.inr u) (by simp))

/-- The list `ℓ₀` of `exists_eq_map_inl` is unique. -/
theorem map_inl_injective :
    Function.Injective (fun ℓ₀ : List V => ℓ₀.map (Sum.inl : V → V ⊕ Unit)) := by
  exact fun _ _ h => List.map_injective_iff.mpr Sum.inl_injective h

end Workspace.ProofLemmas.AddPendantVertexTransport
