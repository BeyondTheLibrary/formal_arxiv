import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Maps

set_option autoImplicit false

namespace Workspace.ProofLemmas

/-- The spanning graph obtained by retaining exactly the `H`-edges selected by `X`. -/
def retainedEdgeGraph {W : Type*} (H : SimpleGraph W) (X : Set H.edgeSet) : SimpleGraph W :=
  SimpleGraph.fromEdgeSet {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (⟨e, he⟩ : H.edgeSet) ∈ X}

/-- An induced subgraph of a line graph is the line graph of the corresponding
spanning retained-edge graph. -/
theorem RetainedEdgeLineGraphIso
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (X : Set H.edgeSet) :
    retainedEdgeGraph H X ≤ H ∧
      ∃ φ : (H.lineGraph).induce X ≃g (retainedEdgeGraph H X).lineGraph,
        (∀ e : X, (φ e).val = e.val.val) ∧
          (H.IsBipartite → (retainedEdgeGraph H X).IsBipartite) := by
  let S : Set (Sym2 W) :=
    {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (⟨e, he⟩ : H.edgeSet) ∈ X}
  have hret : retainedEdgeGraph H X = SimpleGraph.fromEdgeSet S := rfl
  have hmem (e : Sym2 W) :
      e ∈ (retainedEdgeGraph H X).edgeSet ↔
        ∃ he : e ∈ H.edgeSet, (⟨e, he⟩ : H.edgeSet) ∈ X := by
    rw [hret, SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · exact fun he => he.1
    · intro h
      obtain ⟨he, _⟩ := h
      refine ⟨⟨he, by assumption⟩, ?_⟩
      simpa only [Sym2.mem_diagSet] using H.not_isDiag_of_mem_edgeSet he
  have hle : retainedEdgeGraph H X ≤ H := by
    rw [← SimpleGraph.edgeSet_subset_edgeSet]
    intro e he
    exact (hmem e).mp he |>.choose
  let toRetained : X → (retainedEdgeGraph H X).edgeSet := fun e =>
    ⟨e.val.val, (hmem e.val.val).mpr ⟨e.val.property, e.property⟩⟩
  let fromRetained : (retainedEdgeGraph H X).edgeSet → X := fun e =>
    ⟨⟨e.val, ((hmem e.val).mp e.property).choose⟩,
      ((hmem e.val).mp e.property).choose_spec⟩
  let φ : (H.lineGraph).induce X ≃g (retainedEdgeGraph H X).lineGraph :=
    { toFun := toRetained
      invFun := fromRetained
      left_inv := by
        intro e
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro e
        apply Subtype.ext
        rfl
      map_rel_iff' := by
        intro e f
        simp only [SimpleGraph.comap_adj, Function.Embedding.coe_subtype]
        change
          (toRetained e ≠ toRetained f ∧
              ((toRetained e).val ∩ (toRetained f).val : Set W).Nonempty) ↔
            (e.val ≠ f.val ∧ ((e.val.val ∩ f.val.val : Set W).Nonempty))
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨fun hef => h1 ?_, h2⟩
          exact Subtype.ext (congrArg (fun z : H.edgeSet => (z : Sym2 W)) hef)
        · rintro ⟨h1, h2⟩
          refine ⟨fun hef => h1 ?_, h2⟩
          exact Subtype.ext (congrArg (fun z : (retainedEdgeGraph H X).edgeSet =>
            (z : Sym2 W)) hef) }
  refine ⟨hle, φ, ?_, fun h => SimpleGraph.Colorable.mono_left hle h⟩
  intro e
  rfl

end Workspace.ProofLemmas
