import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity

/-!
# Cycles of a multigraph

A **cycle** of a multigraph `G : Graph α β` is a subgraph `C ≤ G` that is connected and in
which every vertex has degree exactly `2` (computed inside `C`, with the multigraph
convention that a loop contributes two edge-ends). Because Mathlib's `Graph α β` uses the
embedded-set design, a subgraph is again a `Graph α β`, so a cycle is a graph, not a walk.

With this convention a single loop is a cycle and a pair of parallel edges is a cycle, while
a single non-loop edge and an isolated vertex are not; the empty graph is excluded via the
`V(C).Nonempty` conjunct hidden in `Graph.Connected`.

* `Graph.IsCycle G C` — `C ≤ G ∧ C.Connected ∧ C.IsTwoRegular`.
-/

open Set

open scoped Graph

variable {α β : Type*} {G H C : Graph α β} {e e₁ e₂ : β} {u v : α}

namespace Graph

/-! ## The definition -/

/-- `G.IsCycle C` means the multigraph `C` is a **cycle of `G`**: a subgraph of `G` that is
connected and every one of whose vertices has degree exactly `2` in `C`. Consequently a
single loop is a cycle, and so is a pair of parallel edges. -/
def IsCycle (G C : Graph α β) : Prop :=
  C ≤ G ∧ C.Connected ∧ C.IsTwoRegular

/-- The definition of `Graph.IsCycle`, with `Graph.IsTwoRegular` spelled out. -/
theorem isCycle_def :
    G.IsCycle C ↔ C ≤ G ∧ C.Connected ∧ ∀ v ∈ V(C), C.degree v = 2 := Iff.rfl

theorem IsCycle.mk (hle : C ≤ G) (hconn : C.Connected)
    (hdeg : ∀ v ∈ V(C), C.degree v = 2) : G.IsCycle C := ⟨hle, hconn, hdeg⟩

/-! ## Basic API -/

/-- A cycle of `G` is a subgraph of `G`. -/
theorem IsCycle.le (h : G.IsCycle C) : C ≤ G := h.1

/-- A cycle is connected. -/
theorem IsCycle.connected (h : G.IsCycle C) : C.Connected := h.2.1

/-- A cycle is two-regular. -/
theorem IsCycle.isTwoRegular (h : G.IsCycle C) : C.IsTwoRegular := h.2.2

/-- Every vertex of a cycle has degree `2` in the cycle. -/
theorem IsCycle.degree_eq (h : G.IsCycle C) (hv : v ∈ V(C)) : C.degree v = 2 :=
  h.2.2 v hv

/-- A cycle has at least one vertex; in particular the empty graph is never a cycle. -/
theorem IsCycle.vertexSet_nonempty (h : G.IsCycle C) : V(C).Nonempty :=
  h.connected.nonempty

/-- A cycle has at least one edge. -/
theorem IsCycle.edgeSet_nonempty (h : G.IsCycle C) : E(C).Nonempty := by
  obtain ⟨v, hv⟩ := h.vertexSet_nonempty
  have hdeg : C.degree v = 2 := h.degree_eq hv
  have hne : (C.incidenceSet v).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hempty
    have hloop : C.loopSet v = ∅ :=
      Set.subset_empty_iff.1 <| (C.loopSet_subset_incidenceSet v).trans hempty.subset
    rw [Graph.degree_def, hempty, hloop] at hdeg
    simp at hdeg
  obtain ⟨e, he⟩ := hne
  exact ⟨e, ((C.mem_incidenceSet v e).1 he).edge_mem⟩

/-- Being a cycle is monotone in the ambient graph. -/
theorem IsCycle.mono (h : G.IsCycle C) (hGH : G ≤ H) : H.IsCycle C :=
  ⟨h.le.trans hGH, h.connected, h.isTwoRegular⟩

/-- A cycle of `G` is a cycle of itself. -/
theorem IsCycle.self (h : G.IsCycle C) : C.IsCycle C :=
  ⟨le_rfl, h.connected, h.isTwoRegular⟩

/-- Anything that is a cycle of itself and a subgraph of `G` is a cycle of `G`. -/
theorem IsCycle.of_self (h : C.IsCycle C) (hle : C ≤ G) : G.IsCycle C :=
  ⟨hle, h.connected, h.isTwoRegular⟩

end Graph

namespace Workspace.Types.Cycle

/-! ## Sanity checks against the intended conventions -/

/-- **A single loop is a cycle.** -/
theorem isCycle_bouquet_singleton (v : α) (e : β) :
    (Graph.bouquet v {e}).IsCycle (Graph.bouquet v ({e} : Set β)) := by
  refine ⟨le_rfl, ?_, ?_⟩
  · exact Graph.connected_of_forall_reachable (x := v) (by simp) <| by
      intro y hy
      simp only [Graph.vertexSet_bouquet, Set.mem_singleton_iff] at hy
      subst hy
      exact Graph.Reachable.rfl
  · intro x hx
    simp only [Graph.vertexSet_bouquet, Set.mem_singleton_iff] at hx
    subst hx
    rw [Graph.degree_bouquet, Set.ncard_singleton]

end Workspace.Types.Cycle
