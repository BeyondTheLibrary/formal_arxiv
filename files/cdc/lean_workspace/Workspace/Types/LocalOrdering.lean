import Mathlib
import Workspace.Types.MultigraphBasic

/-!
# Local orderings of the incident edges of a multigraph

Formalises the paper's "at each vertex `v`, locally order the incident edges as `a`, `b`, `c`".
The ordering is *data*: `LocalOrdering G` carries a function `edge : α → Fin 3 → β` with axioms
saying that, at every `v ∈ V(G)`, the list `edge v 0, edge v 1, edge v 2` enumerates the edges
incident to `v` without repetition (`inc_edge`, `injective`, `exists_index`); equivalently
(`range_edge`) `edge v` maps `Fin 3` bijectively onto `G.incidenceSet v`.

Values at `v ∉ V(G)` are junk and must never be observed. Looplessness/cubicness are not baked
in but are hypotheses of the existence theorem `exists_localOrdering`, whose `[Nonempty β]` only
supplies that junk value and is automatic once `G` has a vertex.
-/

open Set

open scoped Graph

namespace Workspace.Types.LocalOrdering

open Workspace.Types.LocalOrdering

variable {α β : Type*} {G : Graph α β} {e : β} {u v : α} {i j : Fin 3}

/-- A **local ordering** of a multigraph `G`: at each vertex `v` of `G` it names the three
incident edges `edge v 0`, `edge v 1`, `edge v 2` (the paper's `a`, `b`, `c`).

The axioms say precisely that, for `v ∈ V(G)`, the map `edge v : Fin 3 → β` enumerates
`G.incidenceSet v` without repetition. For `v ∉ V(G)` the value of `edge v` is unconstrained
junk and carries no meaning. -/
structure LocalOrdering (G : Graph α β) where
  /-- `edge v i` is the `i`-th of the three edges at `v`. -/
  edge : α → Fin 3 → β
  /-- Every listed edge is incident to `v`. -/
  inc_edge : ∀ v ∈ V(G), ∀ i, G.Inc (edge v i) v
  /-- The listed edges are pairwise distinct: no edge at `v` is listed twice. -/
  injective : ∀ v ∈ V(G), Function.Injective (edge v)
  /-- Every edge incident to `v` is listed. -/
  exists_index : ∀ v ∈ V(G), ∀ e, G.Inc e v → ∃ i, edge v i = e

namespace LocalOrdering

variable (o : LocalOrdering G)

/-! ## Basic lemmas -/

/-- Each of the three edges listed at a vertex `v` of `G` is incident to `v`. -/
lemma inc (hv : v ∈ V(G)) (i : Fin 3) : G.Inc (o.edge v i) v := o.inc_edge v hv i

/-- Each of the three edges listed at a vertex `v` of `G` lies in `G.incidenceSet v`. -/
lemma edge_mem_incidenceSet (hv : v ∈ V(G)) (i : Fin 3) : o.edge v i ∈ G.incidenceSet v :=
  o.inc hv i

/-- Each of the three edges listed at a vertex `v` of `G` is an edge of `G`. -/
lemma edge_mem_edgeSet (hv : v ∈ V(G)) (i : Fin 3) : o.edge v i ∈ E(G) := (o.inc hv i).edge_mem

/-- The three edges listed at a vertex `v` of `G` are pairwise distinct. -/
lemma edge_ne_edge (hv : v ∈ V(G)) (hij : i ≠ j) : o.edge v i ≠ o.edge v j :=
  fun h ↦ hij (o.injective v hv h)

/-- At a vertex `v` of `G`, the local ordering enumerates exactly the edges incident to `v`. -/
lemma range_edge (hv : v ∈ V(G)) : Set.range (o.edge v) = G.incidenceSet v := by
  ext e
  refine ⟨?_, fun he ↦ ?_⟩
  · rintro ⟨i, rfl⟩
    exact o.edge_mem_incidenceSet hv i
  · obtain ⟨i, hi⟩ := o.exists_index v hv e he
    exact ⟨i, hi⟩

/-- An edge `e` is incident to `v ∈ V(G)` if and only if it is one of the three listed edges. -/
lemma inc_iff_exists_index (hv : v ∈ V(G)) : G.Inc e v ↔ ∃ i, o.edge v i = e :=
  ⟨o.exists_index v hv e, by rintro ⟨i, rfl⟩; exact o.inc hv i⟩

end LocalOrdering

/-! ## Existence

Every loopless cubic multigraph (over a nonempty edge type) admits a local ordering. -/

/-- A cubic graph with at least one vertex has at least one edge; in particular its edge type
is nonempty. This makes the `[Nonempty β]` hypothesis of `exists_localOrdering` harmless. -/
lemma nonempty_edgeType_of_isCubic (hcubic : G.IsCubic) (hv : v ∈ V(G)) : Nonempty β := by
  by_contra h
  rw [not_nonempty_iff] at h
  have : G.degree v = 0 := by
    have h1 : G.incidenceSet v = ∅ := Set.eq_empty_of_isEmpty _
    have h2 : G.loopSet v = ∅ := Set.eq_empty_of_isEmpty _
    simp [Graph.degree_def, h1, h2]
  rw [hcubic v hv] at this
  exact absurd this (by norm_num)

/-- In a loopless cubic multigraph, every vertex is incident to exactly three edges. -/
lemma ncard_incidenceSet_eq_three (hloopless : G.IsLoopless) (hcubic : G.IsCubic)
    (hv : v ∈ V(G)) : (G.incidenceSet v).ncard = 3 := by
  rw [← hloopless.degree_eq_ncard_incidenceSet v]
  exact hcubic v hv

/-- **Existence of local orderings.** Every loopless cubic multigraph admits a local ordering
of the edges at each of its vertices. The `[Nonempty β]` hypothesis only supplies the
never-observed junk value of `edge v` at vertices `v ∉ V(G)`. -/
theorem exists_localOrdering [Nonempty β] (hloopless : G.IsLoopless) (hcubic : G.IsCubic) :
    Nonempty (LocalOrdering G) := by
  classical
  -- Choose, for each vertex `v`, an enumeration of the edges at `v` (junk off `V(G)`).
  have key : ∀ v : α, ∃ f : Fin 3 → β, v ∈ V(G) →
      (∀ i, G.Inc (f i) v) ∧ Function.Injective f ∧ ∀ e, G.Inc e v → ∃ i, f i = e := by
    intro v
    by_cases hv : v ∈ V(G)
    · obtain ⟨a, b, c, hab, hac, hbc, hset⟩ :=
        Set.ncard_eq_three.1 (ncard_incidenceSet_eq_three hloopless hcubic hv)
      have hmem : ∀ x ∈ ({a, b, c} : Set β), G.Inc x v := by
        intro x hx
        rw [← hset] at hx
        exact hx
      refine ⟨![a, b, c], fun _ ↦ ⟨?_, ?_, ?_⟩⟩
      · intro i
        fin_cases i
        · exact hmem a (by simp)
        · exact hmem b (by simp)
        · exact hmem c (by simp)
      · intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all
      · intro e he
        have : e ∈ ({a, b, c} : Set β) := by rw [← hset]; exact he
        rcases this with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · exact ⟨1, by simp⟩
        · exact ⟨2, by simp⟩
    · exact ⟨fun _ ↦ Classical.arbitrary β, fun h ↦ absurd h hv⟩
  choose f hf using key
  exact ⟨{ edge := f
           inc_edge := fun v hv i ↦ (hf v hv).1 i
           injective := fun v hv ↦ (hf v hv).2.1
           exists_index := fun v hv e he ↦ (hf v hv).2.2 e he }⟩

end Workspace.Types.LocalOrdering
