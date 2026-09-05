import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# Ingredients for 5.3's closing construction

Two pieces of `Workspace.ProofLemmas.K33SubgraphYieldsTheorem.ComponentYieldsNondegenerate`
that are independent of the still-`private` internals of
`Workspace.ProofLemmas.SubdivisionDatumRealize`:

* `transferSubgraph` — a subgraph of a smaller graph, read as a subgraph of a larger one.  This
  is what lets the closing construction be carried out in an explicitly-built
  `D : SimpleGraph W` (adjacency = the union of the six tracks' edges, so that the branch
  vertices are *computable*) and then moved back into `H`.  The two `coe`s are literally equal,
  so every `IsSubdivision`/appearance statement transports by `rfl`.

* `exists_k33_vertices` — the paper's *"It is helpful now to change the notation.  Let `J` have
  vertex set `{a₁,a₂,a₃,b₁,b₂,b₃}`, where `a₁,a₂,a₃` are adjacent to `b₁,b₂,b₃`."*  This turns
  the opaque hypothesis `Nonempty (J.coe ≃g K₃,₃)` into six named vertices of `H` with the nine
  edges, their pairwise distinctness, and the fact that they exhaust `J.verts`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K33ComponentConstruction

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*}

/-! ### Reading a subgraph of `D` as a subgraph of `H` -/

/-- If `D ≤ H` then any subgraph of `D` is a subgraph of `H`, with the same vertex set and the
same adjacency — and hence, by `transferSubgraph_coe`, literally the same `coe` graph. -/
def transferSubgraph {D H : SimpleGraph W} (hle : D ≤ H) (S : D.Subgraph) : H.Subgraph where
  verts := S.verts
  Adj := S.Adj
  adj_sub := fun h => hle (S.adj_sub h)
  edge_vert := fun h => S.edge_vert h
  symm := S.symm

@[simp] theorem transferSubgraph_verts {D H : SimpleGraph W} (hle : D ≤ H) (S : D.Subgraph) :
    (transferSubgraph hle S).verts = S.verts := rfl

@[simp] theorem transferSubgraph_adj {D H : SimpleGraph W} (hle : D ≤ H) (S : D.Subgraph)
    (x y : W) : (transferSubgraph hle S).Adj x y ↔ S.Adj x y := Iff.rfl

/-- The transferred subgraph has the *same* coerced graph, so any property of `S.coe` — in
particular `IsSubdivision` and `NondegenerateAppearance` — transports without any work. -/
theorem transferSubgraph_coe {D H : SimpleGraph W} (hle : D ≤ H) (S : D.Subgraph) :
    (transferSubgraph hle S).coe = S.coe := rfl

/-! ### Naming the six vertices of a `K₃,₃` subgraph -/

/-- **5.3, "it is helpful now to change the notation".**  A subgraph isomorphic to `K₃,₃` is
given by six vertices `a 0, a 1, a 2, b 0, b 1, b 2` of `H`, pairwise distinct, with every
`a i` adjacent in `H` to every `b j`, and with `J.verts` exactly the set of the six. -/
theorem exists_k33_vertices {H : SimpleGraph W} (J : H.Subgraph)
    (hJ : Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3))) :
    ∃ a b : Fin 3 → W,
      (∀ i, a i ∈ J.verts) ∧ (∀ j, b j ∈ J.verts) ∧
      Function.Injective a ∧ Function.Injective b ∧
      (∀ i j, a i ≠ b j) ∧
      (∀ i j, H.Adj (a i) (b j)) ∧
      (∀ w ∈ J.verts, (∃ i, w = a i) ∨ (∃ j, w = b j)) := by
  obtain ⟨φ⟩ := hJ
  have hinj : Function.Injective (fun s : Fin 3 ⊕ Fin 3 => ((φ.symm s : ↥J.verts) : W)) := by
    intro s t hst
    exact EquivLike.injective φ.symm (Subtype.val_injective hst)
  refine ⟨fun i => ((φ.symm (Sum.inl i) : ↥J.verts) : W),
    fun j => ((φ.symm (Sum.inr j) : ↥J.verts) : W), fun i => (φ.symm (Sum.inl i)).2,
    fun j => (φ.symm (Sum.inr j)).2, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j h
    exact Sum.inl_injective (hinj h)
  · intro i j h
    exact Sum.inr_injective (hinj h)
  · intro i j h
    exact Sum.inl_ne_inr (hinj h)
  · intro i j
    have hK : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (Sum.inl i) (Sum.inr j) := by
      simp [_root_.completeBipartiteGraph_adj]
    have h : J.coe.Adj (φ.symm (Sum.inl i)) (φ.symm (Sum.inr j)) :=
      φ.symm.map_adj_iff.mpr hK
    exact J.adj_sub h
  · intro w hw
    have hback : ((φ.symm (φ ⟨w, hw⟩) : ↥J.verts) : W) = w := by
      rw [φ.symm_apply_apply]
    cases hcase : φ ⟨w, hw⟩ with
    | inl i =>
        refine Or.inl ⟨i, ?_⟩
        rw [← hback, hcase]
    | inr j =>
        refine Or.inr ⟨j, ?_⟩
        rw [← hback, hcase]

end Workspace.ProofLemmas.K33ComponentConstruction
