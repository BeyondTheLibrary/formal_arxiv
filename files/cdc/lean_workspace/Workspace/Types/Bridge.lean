import Mathlib
import Workspace.Types.Connectivity

/-!
# Bridges of a multigraph

An edge `e` of a multigraph `G : Graph α β` is a **bridge** (a cut edge) when deleting it —
keeping all vertices — disconnects its two ends. `G` is **bridgeless** when none of its
edges is a bridge.

* `Graph.IsBridge G e` — `∃ x y, G.IsLink e x y ∧ ¬ (G.deleteEdges {e}).Reachable x y`.
* `Graph.Bridgeless G` — `∀ e ∈ E(G), ¬ G.IsBridge e`.
-/

open Set

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {e f : β} {x y : α}

/-- `G.IsBridge e` means that `e` is an edge of `G` whose ends lie in different components
of `G - e`, the multigraph obtained by deleting `e` and keeping every vertex. -/
def IsBridge (G : Graph α β) (e : β) : Prop :=
  ∃ x y, G.IsLink e x y ∧ ¬ (G.deleteEdges {e}).Reachable x y

/-- `G.Bridgeless` means that no edge of `G` is a bridge. -/
def Bridgeless (G : Graph α β) : Prop :=
  ∀ e ∈ E(G), ¬ G.IsBridge e

/-! ### Basic API -/

theorem isBridge_def :
    G.IsBridge e ↔ ∃ x y, G.IsLink e x y ∧ ¬ (G.deleteEdges {e}).Reachable x y := Iff.rfl

theorem bridgeless_def : G.Bridgeless ↔ ∀ e ∈ E(G), ¬ G.IsBridge e := Iff.rfl

/-- A bridge is an edge. -/
theorem IsBridge.edge_mem (h : G.IsBridge e) : e ∈ E(G) := by
  obtain ⟨x, y, hxy, -⟩ := h
  exact hxy.edge_mem

/-- The ends of a bridge are separated in `G - e`, for either ordering of the ends. -/
theorem IsBridge.not_reachable (h : G.IsBridge e) (hxy : G.IsLink e x y) :
    ¬ (G.deleteEdges {e}).Reachable x y := by
  obtain ⟨a, b, hab, hr⟩ := h
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hab.eq_and_eq_or_eq_and_eq hxy
  · exact hr
  · exact fun hc => hr hc.symm

/-- The existential and universal formulations of `IsBridge` agree. -/
theorem isBridge_iff_forall :
    G.IsBridge e ↔ e ∈ E(G) ∧ ∀ x y, G.IsLink e x y → ¬ (G.deleteEdges {e}).Reachable x y := by
  refine ⟨fun h => ⟨h.edge_mem, fun _ _ hxy => h.not_reachable hxy⟩, fun ⟨he, h⟩ => ?_⟩
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
  exact ⟨x, y, hxy, h x y hxy⟩

/-- The ends of a bridge are distinct; equivalently, a bridge is not a loop. -/
theorem IsBridge.ne_of_isLink (h : G.IsBridge e) (hxy : G.IsLink e x y) : x ≠ y := by
  rintro rfl
  exact h.not_reachable hxy Graph.Reachable.rfl

/-- A loop is never a bridge: deleting it leaves its (unique) end reachable from itself. -/
theorem IsLoopAt.not_isBridge (h : G.IsLoopAt e x) : ¬ G.IsBridge e :=
  fun hb => hb.ne_of_isLink h rfl

/-- A bridge is a nonloop edge at each of its ends. -/
theorem IsBridge.isNonloopAt (h : G.IsBridge e) (hxy : G.IsLink e x y) :
    G.IsNonloopAt e x :=
  ⟨y, (h.ne_of_isLink hxy).symm, hxy⟩

/-- To show a graph bridgeless it suffices to reconnect the ends of every edge after
deleting it. -/
theorem bridgeless_of_forall_reachable
    (h : ∀ e ∈ E(G), ∀ x y, G.IsLink e x y → (G.deleteEdges {e}).Reachable x y) :
    G.Bridgeless :=
  fun e he hb => (hb.not_reachable (Graph.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec)
    (h e he _ _ (Graph.exists_isLink_of_mem_edgeSet he).choose_spec.choose_spec)

/-- A bridgeless graph has no bridges at all. -/
theorem Bridgeless.not_isBridge (h : G.Bridgeless) (e : β) : ¬ G.IsBridge e :=
  fun hb => h e hb.edge_mem hb

/-! ### Sanity checks -/

/-- A loop is never a bridge. -/
example (v : α) (e : β) : ¬ (Graph.bouquet v ({e} : Set β)).IsBridge e := by
  refine Graph.IsLoopAt.not_isBridge (x := v) ?_
  simp [Graph.bouquet]

/-- Neither of two parallel edges is a bridge: deleting one leaves the other joining the
same pair of vertices. -/
example (u v : α) (e₁ e₂ : β) (_huv : u ≠ v) (he : e₁ ≠ e₂) :
    ¬ (Graph.banana u v ({e₁, e₂} : Set β)).IsBridge e₁ := by
  set G : Graph α β := Graph.banana u v ({e₁, e₂} : Set β) with hG
  intro hb
  have h₂ : (G.deleteEdges {e₁}).IsLink e₂ u v := by
    simp [hG, Graph.deleteEdges_isLink, Ne.symm he]
  exact hb.not_reachable (x := u) (y := v) (by simp [hG]) h₂.reachable

/-- A lone cut edge is a bridge. -/
example (u v : α) (e : β) (huv : u ≠ v) : (Graph.banana u v ({e} : Set β)).IsBridge e := by
  set G : Graph α β := Graph.banana u v ({e} : Set β) with hG
  refine ⟨u, v, by simp [hG], fun hr => huv ?_⟩
  have hadj : ∀ b, ¬ (G.deleteEdges ({e} : Set β)).Adj u b := by
    rintro b ⟨f, hf⟩
    rw [Graph.deleteEdges_isLink, hG] at hf
    simp at hf
    exact hf.2 hf.1.1
  rw [Graph.reachable_def, Relation.reflTransGen_iff_eq hadj] at hr
  exact hr.symm

end Graph
