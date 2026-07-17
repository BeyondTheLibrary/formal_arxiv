import Mathlib

/-!
# Basic vertex-degree invariants of a multigraph

Elementary degree theory for Mathlib's multigraph type `Graph α β` (parallel edges and
loops allowed). The **degree** of a vertex `v` counts edge-ends at `v`: a non-loop edge
incident to `v` contributes one end, a loop at `v` contributes two. On top of `degree`
we define the predicates `IsLoopless`, `IsCubic` (3-regular) and `IsTwoRegular`.
-/

open Set

open scoped Graph

namespace Graph

variable {α β : Type*} {G : Graph α β} {e : β} {u v : α}

/-! ## Degree -/

/-- The **degree** of a vertex `v` of a multigraph `G`: the number of edge-ends at `v`.
A non-loop edge incident to `v` contributes one end; a loop at `v` contributes two. -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ :=
  (G.incidenceSet v).ncard + (G.loopSet v).ncard

lemma degree_def (G : Graph α β) (v : α) :
    G.degree v = (G.incidenceSet v).ncard + (G.loopSet v).ncard := rfl

/-- The set of non-loop edges at `v`: the edges contributing exactly one end at `v`. -/
def nonloopSet (G : Graph α β) (v : α) : Set β := {e | G.IsNonloopAt e v}

@[simp]
lemma mem_nonloopSet : e ∈ G.nonloopSet v ↔ G.IsNonloopAt e v := Iff.rfl

lemma nonloopSet_subset_incidenceSet (G : Graph α β) (v : α) :
    G.nonloopSet v ⊆ G.incidenceSet v := fun _ he ↦ he.inc

/-- The edges incident to `v` split into the non-loops at `v` and the loops at `v`. -/
lemma nonloopSet_union_loopSet (G : Graph α β) (v : α) :
    G.nonloopSet v ∪ G.loopSet v = G.incidenceSet v := by
  ext e
  simp only [Set.mem_union, Graph.mem_nonloopSet, Graph.mem_loopSet, Graph.mem_incidenceSet]
  exact ⟨fun h ↦ h.elim Graph.IsNonloopAt.inc Graph.IsLoopAt.inc,
    fun h ↦ h.isLoopAt_or_isNonloopAt.symm⟩

lemma disjoint_nonloopSet_loopSet (G : Graph α β) (v : α) :
    Disjoint (G.nonloopSet v) (G.loopSet v) := by
  rw [Set.disjoint_left]
  exact fun e he he' ↦ he.not_isLoopAt v he'

/-- Each loop at `v` counts twice in the degree; each non-loop edge incident to `v` counts once. -/
lemma degree_eq_ncard_nonloopSet_add_two_mul_ncard_loopSet
    (hfin : (G.incidenceSet v).Finite) :
    G.degree v = (G.nonloopSet v).ncard + 2 * (G.loopSet v).ncard := by
  have hn : (G.nonloopSet v).Finite := hfin.subset (G.nonloopSet_subset_incidenceSet v)
  have hl : (G.loopSet v).Finite := hfin.subset (G.loopSet_subset_incidenceSet v)
  have hsplit : (G.incidenceSet v).ncard = (G.nonloopSet v).ncard + (G.loopSet v).ncard := by
    rw [← G.nonloopSet_union_loopSet v, Set.ncard_union_eq (G.disjoint_nonloopSet_loopSet v) hn hl]
  rw [Graph.degree_def, hsplit]
  omega

/-- A vertex outside the graph has no incident edges. -/
lemma incidenceSet_eq_empty_of_notMem (hv : v ∉ V(G)) : G.incidenceSet v = ∅ := by
  ext e
  simp only [Graph.mem_incidenceSet, Set.mem_empty_iff_false, iff_false]
  exact fun h ↦ hv h.vertex_mem

lemma loopSet_eq_empty_of_notMem (hv : v ∉ V(G)) : G.loopSet v = ∅ :=
  Set.subset_empty_iff.1 <|
    (G.loopSet_subset_incidenceSet v).trans (Graph.incidenceSet_eq_empty_of_notMem hv).subset

lemma degree_eq_zero_of_notMem (hv : v ∉ V(G)) : G.degree v = 0 := by
  simp [Graph.degree_def, Graph.incidenceSet_eq_empty_of_notMem hv,
    Graph.loopSet_eq_empty_of_notMem hv]

/-! ## Looplessness -/

/-- A multigraph is **loopless** if it has no loop at all. -/
def IsLoopless (G : Graph α β) : Prop := ∀ e x, ¬ G.IsLoopAt e x

lemma IsLoopless.loopSet_eq_empty (h : G.IsLoopless) (v : α) : G.loopSet v = ∅ := by
  ext e
  simpa using h e v

/-- In a loopless graph the degree of `v` is the number of edges incident to `v`. -/
lemma IsLoopless.degree_eq_ncard_incidenceSet (h : G.IsLoopless) (v : α) :
    G.degree v = (G.incidenceSet v).ncard := by
  simp [Graph.degree_def, h.loopSet_eq_empty v]

lemma IsLoopless.isNonloopAt_of_inc (h : G.IsLoopless) (hi : G.Inc e v) :
    G.IsNonloopAt e v :=
  hi.isLoopAt_or_isNonloopAt.resolve_left (h e v)

lemma isLoopless_iff_forall_isLink_ne :
    G.IsLoopless ↔ ∀ e x y, G.IsLink e x y → x ≠ y := by
  constructor
  · intro h e x y hl hxy
    subst hxy
    exact h e x hl
  · intro h e x hl
    exact h e x x hl rfl

/-! ## Regularity predicates -/

/-- A multigraph is **cubic** (3-regular) if every one of its vertices has degree `3`. -/
def IsCubic (G : Graph α β) : Prop := ∀ v ∈ V(G), G.degree v = 3

/-- A multigraph is **two-regular** if every one of its vertices has degree `2`.
With the loops-count-twice convention, a single loop and a pair of parallel edges are
both two-regular. -/
def IsTwoRegular (G : Graph α β) : Prop := ∀ v ∈ V(G), G.degree v = 2

lemma IsCubic.degree_eq (h : G.IsCubic) (hv : v ∈ V(G)) : G.degree v = 3 := h v hv

lemma IsTwoRegular.degree_eq (h : G.IsTwoRegular) (hv : v ∈ V(G)) :
    G.degree v = 2 := h v hv

/-! ## Basic examples -/

@[simp]
lemma incidenceSet_banana_left (u v : α) (F : Set β) :
    (Graph.banana u v F).incidenceSet u = F := by
  ext e; simp

@[simp]
lemma incidenceSet_banana_right (u v : α) (F : Set β) :
    (Graph.banana u v F).incidenceSet v = F := by
  ext e; simp

lemma loopSet_banana_left_of_ne (h : u ≠ v) (F : Set β) :
    (Graph.banana u v F).loopSet u = ∅ := by
  ext e; simp [h]

/-- In a `banana` on two distinct vertices, each endpoint has degree equal to the number
of edges. In particular two parallel edges give both endpoints degree `2`. -/
lemma degree_banana_left_of_ne (h : u ≠ v) (F : Set β) :
    (Graph.banana u v F).degree u = F.ncard := by
  simp [Graph.degree_def, Graph.loopSet_banana_left_of_ne h]

/-- The single vertex of a `bouquet` has degree twice the number of loops. In particular a
single loop gives degree `2`. -/
lemma degree_bouquet (v : α) (F : Set β) :
    (Graph.bouquet v F).degree v = 2 * F.ncard := by
  have hl : (Graph.bouquet v F).loopSet v = F := by ext e; simp
  rw [Graph.degree_def, hl, Graph.incidenceSet_banana_left, two_mul]

end Graph
