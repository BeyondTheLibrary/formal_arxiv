import Mathlib
import Workspace.Types.Cycle

/-!
# Cycle double covers

The paper's central object: a **cycle double cover** of a graph is a multiset of cycles in
which every edge occurs exactly twice.

* `Multiset.edgeMultiplicity D e` — the number of members of `D`, counted with multiplicity,
  whose edge set contains `e`.
* `Graph.IsCycleDoubleCover G D` — every member of `D` is a cycle of `G`, and every edge of
  `G` has multiplicity exactly `2` in `D`.
* `Graph.HasCycleDoubleCover G` — `∃ D, G.IsCycleDoubleCover D`; the conclusion of the main
  theorem.

A `Multiset` (not a `Set`) is essential: the same cycle may legitimately be used twice.
-/

open Set

open scoped Graph

variable {α β : Type*} {G C : Graph α β} {D : Multiset (Graph α β)} {e : β} {u v : α}

namespace Multiset

/-! ## Counting the members of a multiset of graphs that use a given edge -/

open scoped Classical in
/-- `D.edgeMultiplicity e` is the number of graphs in the multiset `D`, counted with
multiplicity, whose edge set contains `e`. -/
noncomputable def edgeMultiplicity (D : Multiset (Graph α β)) (e : β) : ℕ :=
  D.countP (fun C ↦ e ∈ E(C))

open scoped Classical in
theorem edgeMultiplicity_def (D : Multiset (Graph α β)) (e : β) :
    D.edgeMultiplicity e = D.countP (fun C ↦ e ∈ E(C)) := by
  rw [Multiset.edgeMultiplicity]

@[simp]
theorem edgeMultiplicity_zero (e : β) :
    (0 : Multiset (Graph α β)).edgeMultiplicity e = 0 := by
  classical
  rw [Multiset.edgeMultiplicity_def, Multiset.countP_zero]

/-- Consing on a graph that uses `e` increases the multiplicity of `e` by one. -/
theorem edgeMultiplicity_cons_of_mem (D : Multiset (Graph α β))
    (h : e ∈ E(C)) : (C ::ₘ D).edgeMultiplicity e = D.edgeMultiplicity e + 1 := by
  classical
  rw [Multiset.edgeMultiplicity_def, Multiset.edgeMultiplicity_def,
    Multiset.countP_cons_of_pos (p := fun C ↦ e ∈ E(C)) D h]

/-- Consing on a graph that does not use `e` leaves the multiplicity of `e` unchanged. -/
theorem edgeMultiplicity_cons_of_notMem (D : Multiset (Graph α β))
    (h : e ∉ E(C)) : (C ::ₘ D).edgeMultiplicity e = D.edgeMultiplicity e := by
  classical
  rw [Multiset.edgeMultiplicity_def, Multiset.edgeMultiplicity_def,
    Multiset.countP_cons_of_neg (p := fun C ↦ e ∈ E(C)) D h]

/-- An edge has positive multiplicity exactly when some member of the multiset uses it. -/
theorem edgeMultiplicity_pos_iff :
    0 < D.edgeMultiplicity e ↔ ∃ C ∈ D, e ∈ E(C) := by
  classical
  rw [Multiset.edgeMultiplicity_def]
  exact Multiset.countP_pos

/-- An edge has multiplicity zero exactly when no member of the multiset uses it. -/
theorem edgeMultiplicity_eq_zero_iff :
    D.edgeMultiplicity e = 0 ↔ ∀ C ∈ D, e ∉ E(C) := by
  classical
  rw [Multiset.edgeMultiplicity_def]
  exact Multiset.countP_eq_zero

end Multiset

namespace Graph

/-! ## The definition -/

/-- `G.IsCycleDoubleCover D` means the multiset of graphs `D` is a **cycle double cover** of
`G`: every member of `D` is a cycle of `G`, and every edge of `G` occurs in exactly two
members of `D`, counted with multiplicity. -/
def IsCycleDoubleCover (G : Graph α β) (D : Multiset (Graph α β)) : Prop :=
  (∀ C ∈ D, G.IsCycle C) ∧ ∀ e ∈ E(G), D.edgeMultiplicity e = 2

theorem isCycleDoubleCover_def :
    G.IsCycleDoubleCover D ↔
      (∀ C ∈ D, G.IsCycle C) ∧ ∀ e ∈ E(G), D.edgeMultiplicity e = 2 := Iff.rfl

theorem IsCycleDoubleCover.mk (hcyc : ∀ C ∈ D, G.IsCycle C)
    (hcount : ∀ e ∈ E(G), D.edgeMultiplicity e = 2) : G.IsCycleDoubleCover D := ⟨hcyc, hcount⟩

/-- `G` **has a cycle double cover** if some multiset of graphs is a cycle double cover of
`G`. This is the conclusion of the cycle double cover theorem. -/
def HasCycleDoubleCover (G : Graph α β) : Prop :=
  ∃ D : Multiset (Graph α β), G.IsCycleDoubleCover D

theorem IsCycleDoubleCover.hasCycleDoubleCover (h : G.IsCycleDoubleCover D) :
    G.HasCycleDoubleCover := ⟨D, h⟩

theorem hasCycleDoubleCover_def :
    G.HasCycleDoubleCover ↔ ∃ D : Multiset (Graph α β), G.IsCycleDoubleCover D := Iff.rfl

/-! ## Basic API -/

/-- Every member of a cycle double cover of `G` is a cycle of `G`. -/
theorem IsCycleDoubleCover.isCycle_of_mem (h : G.IsCycleDoubleCover D)
    (hC : C ∈ D) : G.IsCycle C := h.1 C hC

/-- Every edge of `G` occurs exactly twice in a cycle double cover of `G`. -/
theorem IsCycleDoubleCover.edgeMultiplicity_eq (h : G.IsCycleDoubleCover D)
    (he : e ∈ E(G)) : D.edgeMultiplicity e = 2 := h.2 e he

/-- Every member of a cycle double cover of `G` is a subgraph of `G`. -/
theorem IsCycleDoubleCover.le_of_mem (h : G.IsCycleDoubleCover D) (hC : C ∈ D) :
    C ≤ G := (h.isCycle_of_mem hC).le

/-- No member of a cycle double cover of `G` uses an edge outside `E(G)`. -/
theorem IsCycleDoubleCover.edgeSet_subset_of_mem (h : G.IsCycleDoubleCover D)
    (hC : C ∈ D) : E(C) ⊆ E(G) :=
  Graph.IsSubgraph.edgeSet_mono (h.le_of_mem hC)

/-- Every edge of `G` is used by at least one member of a cycle double cover. -/
theorem IsCycleDoubleCover.exists_mem_of_mem_edgeSet (h : G.IsCycleDoubleCover D)
    (he : e ∈ E(G)) : ∃ C ∈ D, e ∈ E(C) := by
  refine Multiset.edgeMultiplicity_pos_iff.1 ?_
  rw [h.edgeMultiplicity_eq he]
  norm_num

/-- Every edge of `G` lies on a cycle of `G`, if `G` has a cycle double cover. -/
theorem IsCycleDoubleCover.exists_isCycle_mem_edgeSet (h : G.IsCycleDoubleCover D)
    (he : e ∈ E(G)) : ∃ C, G.IsCycle C ∧ e ∈ E(C) := by
  obtain ⟨C, hCD, heC⟩ := h.exists_mem_of_mem_edgeSet he
  exact ⟨C, h.isCycle_of_mem hCD, heC⟩

/-- **The obstruction lemma.** If some edge of `G` lies on no cycle of `G`, then `G` has no
cycle double cover. This is what rules out bridges. -/
theorem not_hasCycleDoubleCover_of_forall_isCycle_notMem (he : e ∈ E(G))
    (h : ∀ C, G.IsCycle C → e ∉ E(C)) : ¬ G.HasCycleDoubleCover := by
  rintro ⟨D, hD⟩
  obtain ⟨C, hC, heC⟩ := hD.exists_isCycle_mem_edgeSet he
  exact h C hC heC

/-- The empty multiset is a cycle double cover of `G` exactly when `G` has no edges. -/
theorem isCycleDoubleCover_zero_iff :
    G.IsCycleDoubleCover 0 ↔ E(G) = ∅ := by
  constructor
  · intro h
    refine Set.eq_empty_iff_forall_notMem.2 fun e he ↦ ?_
    have := h.edgeMultiplicity_eq he
    rw [Multiset.edgeMultiplicity_zero] at this
    exact absurd this (by norm_num)
  · intro h
    refine ⟨fun C hC ↦ absurd hC (Multiset.notMem_zero C), fun e he ↦ ?_⟩
    rw [h] at he
    exact absurd he (Set.notMem_empty e)

end Graph

namespace Workspace.Types.CycleDoubleCover

/-! ## Sanity checks against the intended meaning -/

/-- **A cycle is doubly covered by itself taken twice.** If `G` is a cycle of itself, then
`{G, G}` — containing `G` with multiplicity `2` — is a cycle double cover of `G`. This is
exactly the statement that fails if one uses a `Set` of cycles instead of a multiset. -/
theorem isCycleDoubleCover_pair_self (h : G.IsCycle G) :
    G.IsCycleDoubleCover {G, G} := by
  have hpair : ({G, G} : Multiset (Graph α β)) = G ::ₘ G ::ₘ 0 := rfl
  refine ⟨fun C hC ↦ ?_, fun e he ↦ ?_⟩
  · rw [hpair] at hC
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hC
    obtain rfl | rfl := hC <;> exact h
  · rw [hpair, Multiset.edgeMultiplicity_cons_of_mem _ he,
      Multiset.edgeMultiplicity_cons_of_mem _ he, Multiset.edgeMultiplicity_zero]

/-- **No cycle of a single non-loop edge contains that edge**: its ends would have degree
`1`, not `2`. -/
theorem notMem_edgeSet_of_isCycle_banana_singleton (huv : u ≠ v) (e : β) (C : Graph α β)
    (hC : (Graph.banana u v ({e} : Set β)).IsCycle C) : e ∉ E(C) := by
  have key : ∀ (x y : α), x ≠ y → ∀ C : Graph α β, (Graph.banana x y ({e} : Set β)).IsCycle C →
      x ∉ V(C) := by
    intro x y hxy C hC hxC
    have hinc : C.incidenceSet x ⊆ ({e} : Set β) := by
      intro f hf
      have hb : (Graph.banana x y ({e} : Set β)).Inc f x :=
        Graph.Inc.mono hC.le ((C.mem_incidenceSet x f).1 hf)
      rw [Graph.banana_inc] at hb
      exact hb.1
    have hloop : C.loopSet x = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun f hf ↦ ?_
      have hb : (Graph.banana x y ({e} : Set β)).IsLoopAt f x :=
        Graph.IsLoopAt.mono hC.le ((C.mem_loopSet x f).1 hf)
      rw [Graph.banana_isLoopAt] at hb
      exact hxy hb.2.2
    have hcard : (C.incidenceSet x).ncard ≤ 1 := by
      simpa using Set.ncard_le_ncard hinc (Set.finite_singleton e)
    have hdeg : C.degree x = 2 := hC.degree_eq hxC
    rw [Graph.degree_def, hloop, Set.ncard_empty] at hdeg
    omega
  intro heC
  obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet heC
  have hb : (Graph.banana u v ({e} : Set β)).IsLink e x y := Graph.IsLink.mono hC.le hxy
  rw [Graph.banana_isLink] at hb
  obtain ⟨-, ⟨hx, -⟩ | ⟨hx, -⟩⟩ := hb
  · exact key u v huv C hC (hx ▸ hxy.left_mem)
  · exact key v u huv.symm C (by rwa [Graph.banana_comm]) (hx ▸ hxy.left_mem)

/-- **A single non-loop edge — i.e. a bridge — has no cycle double cover.** -/
theorem not_hasCycleDoubleCover_banana_singleton (huv : u ≠ v) (e : β) :
    ¬ (Graph.banana u v ({e} : Set β)).HasCycleDoubleCover :=
  Graph.not_hasCycleDoubleCover_of_forall_isCycle_notMem (e := e) (by simp)
    (notMem_edgeSet_of_isCycle_banana_singleton huv e)

end Workspace.Types.CycleDoubleCover
