import Mathlib
import Workspace.Types.MultigraphBasic

/-!
# Proper 3-edge-colourings of a multigraph

A **proper 3-edge-colouring** of a multigraph `G : Graph α β` is a map `c : β → Fin 3` such
that any two *distinct* edges meeting at a common vertex get distinct colours:

  `G.IsProper3EdgeColouring c ↔ ∀ v ∈ V(G), Set.InjOn c (G.incidenceSet v)`.

On a loopless cubic graph this is equivalent to "the three edges at each vertex receive all
three colours" (`Graph.IsProper3EdgeColouring.image_incidenceSet_eq_univ`). Cubicness,
looplessness and surjectivity are hypotheses of the statements that use this predicate, not
part of the predicate itself.
-/

open Set

open scoped Graph

namespace Graph

variable {α β : Type*} {G H : Graph α β} {c : β → Fin 3} {e e₁ e₂ : β} {u v : α}

/-! ## The definition -/

/-- A map `c : β → Fin 3` is a **proper 3-edge-colouring** of `G` if, at every vertex, any
two distinct edges incident to that vertex receive distinct colours. -/
def IsProper3EdgeColouring (G : Graph α β) (c : β → Fin 3) : Prop :=
  ∀ v ∈ V(G), ∀ e₁, G.Inc e₁ v → ∀ e₂, G.Inc e₂ v → e₁ ≠ e₂ → c e₁ ≠ c e₂

/-! ## Basic reformulations -/

/-- The defining property in applied form: two distinct edges meeting at a vertex have
different colours. -/
lemma IsProper3EdgeColouring.ne_of_inc (h : G.IsProper3EdgeColouring c)
    (hv : v ∈ V(G)) (h₁ : G.Inc e₁ v) (h₂ : G.Inc e₂ v) (hne : e₁ ≠ e₂) : c e₁ ≠ c e₂ :=
  h v hv e₁ h₁ e₂ h₂ hne

/-- A proper 3-edge-colouring is **injective on the edges incident to any vertex**. -/
lemma IsProper3EdgeColouring.injOn (h : G.IsProper3EdgeColouring c) (hv : v ∈ V(G)) :
    Set.InjOn c (G.incidenceSet v) := by
  intro e₁ h₁ e₂ h₂ hcol
  by_contra hne
  exact h v hv e₁ ((G.mem_incidenceSet v e₁).1 h₁) e₂ ((G.mem_incidenceSet v e₂).1 h₂) hne hcol

/-- Being a proper 3-edge-colouring is exactly injectivity on every incidence set. -/
lemma isProper3EdgeColouring_iff_injOn :
    G.IsProper3EdgeColouring c ↔ ∀ v ∈ V(G), Set.InjOn c (G.incidenceSet v) :=
  ⟨fun h _v hv ↦ h.injOn hv,
    fun h v hv e₁ h₁ e₂ h₂ hne hcol ↦
      hne (h v hv ((G.mem_incidenceSet v e₁).2 h₁) ((G.mem_incidenceSet v e₂).2 h₂) hcol)⟩

/-! ## Behaviour under passing to a subgraph -/

/-- Properness is inherited by subgraphs. -/
lemma IsProper3EdgeColouring.mono (h : G.IsProper3EdgeColouring c) (hHG : H ≤ G) :
    H.IsProper3EdgeColouring c :=
  fun v hv e₁ h₁ e₂ h₂ hne ↦
    h v (Graph.IsSubgraph.vertexSet_mono hHG hv) e₁ (h₁.mono hHG) e₂ (h₂.mono hHG) hne

/-! ## The loopless cubic case

On a loopless cubic graph the injectivity formulation is equivalent to "all three colours
appear at each vertex". -/

/-- At a degree-`3` vertex of a loopless graph, a proper 3-edge-colouring hits **every**
colour. -/
lemma IsProper3EdgeColouring.image_incidenceSet_eq_univ
    (h : G.IsProper3EdgeColouring c) (hloop : G.IsLoopless) (hv : v ∈ V(G))
    (hdeg : G.degree v = 3) : c '' G.incidenceSet v = (Set.univ : Set (Fin 3)) := by
  have hcard : (G.incidenceSet v).ncard = 3 := by
    rw [← hloop.degree_eq_ncard_incidenceSet v, hdeg]
  have himg : (c '' G.incidenceSet v).ncard = 3 := by
    rw [(h.injOn hv).ncard_image, hcard]
  have hle : (Set.univ : Set (Fin 3)).ncard ≤ (c '' G.incidenceSet v).ncard := by
    rw [himg, Set.ncard_univ]
    simp
  exact Set.eq_of_subset_of_ncard_le (Set.subset_univ _) hle (Set.finite_univ)

/-- At a degree-`3` vertex of a loopless graph, each of the three colours is realised by an
edge at `v`. -/
lemma IsProper3EdgeColouring.exists_inc_colour
    (h : G.IsProper3EdgeColouring c) (hloop : G.IsLoopless) (hv : v ∈ V(G))
    (hdeg : G.degree v = 3) (i : Fin 3) : ∃ e, G.Inc e v ∧ c e = i := by
  have := h.image_incidenceSet_eq_univ hloop hv hdeg
  have hi : i ∈ c '' G.incidenceSet v := by rw [this]; trivial
  obtain ⟨e, he, hce⟩ := hi
  exact ⟨e, (G.mem_incidenceSet v e).1 he, hce⟩

end Graph
