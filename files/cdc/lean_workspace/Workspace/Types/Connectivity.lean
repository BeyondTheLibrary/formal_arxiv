import Mathlib

/-!
# Connectivity for multigraphs

Reachability and connectedness for Mathlib's multigraph type `Graph α β` (parallel edges
and loops allowed).

* `Graph.Reachable G x y` — `x` and `y` are joined by a walk in `G`, i.e. the
  reflexive-transitive closure of the adjacency relation `Graph.Adj`.
* `Graph.Connected G` — `G` has at least one vertex, and any two of its vertices are
  reachable from each other.
-/

open Set

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {x y z : α}

/-- `G.Reachable x y` means that `x` and `y` are joined by a walk in the multigraph `G`;
equivalently, the reflexive-transitive closure of `G.Adj`. Note that `G.Reachable x x`
holds for every `x : α`, even for `x ∉ V(G)`. -/
def Reachable (G : Graph α β) (x y : α) : Prop :=
  Relation.ReflTransGen G.Adj x y

/-- `G.Connected` means the multigraph `G` has at least one vertex and every two of its
vertices are reachable from each other. The nonemptiness requirement rules out the empty
graph. -/
def Connected (G : Graph α β) : Prop :=
  V(G).Nonempty ∧ ∀ x ∈ V(G), ∀ y ∈ V(G), G.Reachable x y

/-! ### Basic API for `Graph.Reachable` -/

theorem reachable_def : G.Reachable x y ↔ Relation.ReflTransGen G.Adj x y := Iff.rfl

/-- Reachability is reflexive. -/
@[refl]
protected theorem Reachable.refl (G : Graph α β) (x : α) : G.Reachable x x :=
  Relation.ReflTransGen.refl

protected theorem Reachable.rfl : G.Reachable x x :=
  Relation.ReflTransGen.refl

/-- Adjacent vertices are reachable from one another. -/
theorem Adj.reachable (h : G.Adj x y) : G.Reachable x y :=
  Relation.ReflTransGen.single h

/-- If `e` is an edge of `G` with ends `x` and `y`, then `x` and `y` are reachable. -/
theorem IsLink.reachable {e : β} (h : G.IsLink e x y) : G.Reachable x y :=
  (Graph.Adj.reachable ⟨e, h⟩)

/-- Reachability is symmetric. -/
@[symm]
protected theorem Reachable.symm (h : G.Reachable x y) : G.Reachable y x :=
  Relation.ReflTransGen.symmetric (fun _ _ hxy => hxy.symm) h

theorem reachable_comm : G.Reachable x y ↔ G.Reachable y x :=
  ⟨Graph.Reachable.symm, Graph.Reachable.symm⟩

/-- Reachability is transitive. -/
@[trans]
protected theorem Reachable.trans (hxy : G.Reachable x y) (hyz : G.Reachable y z) :
    G.Reachable x z :=
  Relation.ReflTransGen.trans hxy hyz

/-- Prepend an adjacency to a walk. -/
theorem Reachable.head (hxy : G.Adj x y) (hyz : G.Reachable y z) : G.Reachable x z :=
  Relation.ReflTransGen.head hxy hyz

/-- Append an adjacency to a walk. -/
theorem Reachable.tail (hxy : G.Reachable x y) (hyz : G.Adj y z) : G.Reachable x z :=
  Relation.ReflTransGen.tail hxy hyz

/-- Reachability is monotone in the graph: a walk in a subgraph is a walk in the
ambient graph. -/
protected theorem Reachable.mono (hHG : H ≤ G) (h : H.Reachable x y) :
    G.Reachable x y :=
  Relation.ReflTransGen.mono (fun _ _ hxy => hxy.mono hHG) h

/-- Reachability is an equivalence relation on the ambient vertex type `α`. -/
theorem reachable_equivalence (G : Graph α β) : Equivalence G.Reachable :=
  ⟨fun x => Graph.Reachable.refl G x, Graph.Reachable.symm, Graph.Reachable.trans⟩

/-- A vertex reachable from `x` by a *nontrivial* walk certifies that `x ∈ V(G)`. -/
theorem Reachable.left_mem_of_ne (h : G.Reachable x y) (hne : x ≠ y) : x ∈ V(G) := by
  obtain (rfl | ⟨c, hac, -⟩) := h.cases_head
  · exact absurd rfl hne
  · exact hac.left_mem

theorem Reachable.right_mem_of_ne (h : G.Reachable x y) (hne : x ≠ y) : y ∈ V(G) :=
  h.symm.left_mem_of_ne hne.symm

/-! ### Basic API for `Graph.Connected` -/

theorem connected_def :
    G.Connected ↔ V(G).Nonempty ∧ ∀ x ∈ V(G), ∀ y ∈ V(G), G.Reachable x y := Iff.rfl

/-- A connected graph has a vertex. -/
theorem Connected.nonempty (h : G.Connected) : V(G).Nonempty := h.1

/-- Any two vertices of a connected graph are reachable from each other. -/
theorem Connected.reachable (h : G.Connected) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Reachable x y :=
  h.2 x hx y hy

/-- To prove a graph connected it suffices to exhibit a vertex of `G` from which every
vertex of `G` is reachable. -/
theorem connected_of_forall_reachable (hx : x ∈ V(G))
    (h : ∀ y ∈ V(G), G.Reachable x y) : G.Connected :=
  ⟨⟨x, hx⟩, fun _ ha _ hb => (h _ ha).symm.trans (h _ hb)⟩

end Graph
