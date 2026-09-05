import Mathlib

/-!
# A spanning `K₃,₃` subgraph of a bipartite graph is the whole graph

This is the **last sentence** of the printed proof of 5.3 (published page 19):

> *"So we may assume there is no such `F`.  **Since `H` is bipartite, it follows that
> `H = J = K₃,₃`**, and so the theorem holds."*

The step the paper compresses into *"since `H` is bipartite"* is this: `J ≅ K₃,₃` is already
*complete* bipartite, so any edge of `H` that is not an edge of `J` joins two vertices on the
same side of `J`'s bipartition; but those two have a common neighbour on the other side (each
side of `K₃,₃` has three vertices, and every cross pair is adjacent), and the three of them
would form a triangle in the bipartite `H`.

Hence `H` has no edges beyond `J`'s, and as `V(J) = V(H)` the inclusion `J.coe → H` is an
isomorphism.

This is stated separately from `Workspace.ProofLemmas.Thm53Assembly` because it is the one
piece of 5.3's closing paragraph that does not need the component/attachment analysis; whoever
proves `Thm53Assembly.K33SubgraphYieldsTheorem` can use it directly for the *"no such `F`"*
branch.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K33SubgraphSpanning

/-- Two vertices of `K₃,₃` that are non-adjacent lie on the same side, and therefore have a
common neighbour on the other side. -/
private theorem exists_common_nbr (a b : Fin 3 ⊕ Fin 3)
    (h : ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b) :
    ∃ z, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a z ∧
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj b z := by
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          exact ⟨Sum.inr 0, by simp [_root_.completeBipartiteGraph_adj],
            by simp [_root_.completeBipartiteGraph_adj]⟩
      | inr j => exact absurd (by simp [_root_.completeBipartiteGraph_adj]) h
  | inr i =>
      cases b with
      | inl j => exact absurd (by simp [_root_.completeBipartiteGraph_adj]) h
      | inr j =>
          exact ⟨Sum.inl 0, by simp [_root_.completeBipartiteGraph_adj],
            by simp [_root_.completeBipartiteGraph_adj]⟩

/-- A bipartite graph has no triangle. -/
private theorem no_triangle {W : Type*} {H : SimpleGraph W} (hbip : H.IsBipartite) {x y z : W}
    (h1 : H.Adj x y) (h2 : H.Adj x z) (h3 : H.Adj y z) : False := by
  obtain ⟨col⟩ := hbip
  have v1 := (col x).isLt
  have v2 := (col y).isLt
  have v3 := (col z).isLt
  have n1 : ((col x : ℕ)) ≠ ((col y : ℕ)) := fun h => col.valid h1 (Fin.val_injective h)
  have n2 : ((col x : ℕ)) ≠ ((col z : ℕ)) := fun h => col.valid h2 (Fin.val_injective h)
  have n3 : ((col y : ℕ)) ≠ ((col z : ℕ)) := fun h => col.valid h3 (Fin.val_injective h)
  omega

/-- **5.3, closing sentence.**  If `H` is bipartite and has a *spanning* subgraph isomorphic to
`K₃,₃`, then `H` itself is isomorphic to `K₃,₃`. -/
theorem iso_k33_of_spanning {W : Type*} {H : SimpleGraph W} (hbip : H.IsBipartite)
    (J : H.Subgraph)
    (hJ : Nonempty (J.coe ≃g completeBipartiteGraph (Fin 3) (Fin 3)))
    (hverts : J.verts = Set.univ) :
    Nonempty (H ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  obtain ⟨φ⟩ := hJ
  -- `H` has no edge beyond those of `J`.
  have hfull : ∀ x y : ↥J.verts, H.Adj ↑x ↑y → J.coe.Adj x y := by
    intro x y hxy
    by_contra hnadj
    have hφ : ¬ (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (φ x) (φ y) := by
      rw [φ.map_adj_iff]; exact hnadj
    obtain ⟨z, hz1, hz2⟩ := exists_common_nbr (φ x) (φ y) hφ
    have hxz : J.coe.Adj x (φ.symm z) := by rw [← φ.map_adj_iff]; simpa using hz1
    have hyz : J.coe.Adj y (φ.symm z) := by rw [← φ.map_adj_iff]; simpa using hz2
    exact no_triangle hbip hxy (J.adj_sub hxz) (J.adj_sub hyz)
  -- and it has all of `J`'s vertices, so the inclusion is an isomorphism.
  have einc : H ≃g J.coe := by
    refine ⟨⟨fun w => ⟨w, by rw [hverts]; trivial⟩, Subtype.val, fun _ => rfl, fun _ => rfl⟩, ?_⟩
    intro a b
    exact ⟨fun h => J.adj_sub h, fun h => hfull _ _ h⟩
  exact ⟨einc.trans φ⟩

end Workspace.ProofLemmas.K33SubgraphSpanning
