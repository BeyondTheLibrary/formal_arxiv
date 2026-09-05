import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Types.Appearances

/-! The exceptional skeleton in the enlargement assertion, printed pp. 42–43. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.EnlargementFromNonlocalK33

open Workspace.Types.Tracks.SPGT Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

local instance : DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj :=
  fun a b => by rw [completeBipartiteGraph_adj]; infer_instance

private theorem k33_neighbor_delete_card (a b : Fin 3 ⊕ Fin 3)
    (hab : (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b) :
    ((completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet a \ {b}).ncard = 2 := by
  let s : Finset (Fin 3 ⊕ Fin 3) := Finset.univ.filter fun z =>
    (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a z ∧ z ≠ b
  have hs : (↑s : Set (Fin 3 ⊕ Fin 3)) =
      (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet a \ {b} := by
    ext z
    simp [s, SimpleGraph.neighborSet]
  rw [← hs, Set.ncard_coe_finset]
  revert hab
  change (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b →
    (Finset.univ.filter fun z =>
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a z ∧ z ≠ b).card = 2
  clear hs s
  revert a b
  decide

/-- A proper subgraph of a graph without isolated vertices misses an edge. -/
private theorem missing_edge {X : Type*} {A : SimpleGraph X}
    (hnbr : ∀ x, ∃ y, A.Adj x y) (S : A.Subgraph) (hS : S ≠ ⊤) :
    ∃ x y, A.Adj x y ∧ ¬ S.Adj x y := by
  by_contra h
  have hall : ∀ x y, A.Adj x y → S.Adj x y := by
    intro x y hxy
    by_contra hn
    exact h ⟨x, y, hxy, hn⟩
  apply hS
  apply SimpleGraph.Subgraph.ext
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨y, hxy⟩ := hnbr x
    exact S.edge_vert (hall x y hxy)
  · funext x y
    exact propext ⟨S.adj_sub, hall x y⟩

/-- PAPER (printed p. 43): "Moreover, if `J' = K₃,₃` then `J = K₄`."
The assertion holds for every `J`-enlargement isomorphic to `K₃,₃`. A missing edge
leaves its two ends with degree at most two in the proper subgraph. Thus at most
four vertices can be images of vertices of the 3-connected graph `J`. -/
theorem old_is_k4 {U X : Type*} [Fintype U] [Fintype X]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (A : SimpleGraph X)
    (henl : IsJEnlargement J A)
    (h33 : Nonempty (A ≃g completeBipartiteGraph (Fin 3) (Fin 3))) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
  classical
  obtain ⟨e⟩ := h33
  obtain ⟨hA, S, hS, n, B, hsub, ⟨φ⟩⟩ := henl
  obtain ⟨x, y, hxy, hmiss⟩ := missing_edge
    (exists_adj_of_three_connected A hA) S hS
  let f : Fin n → Fin 3 ⊕ Fin 3 := fun v => e (φ.symm v : X)
  have hf : Function.Injective f := e.injective.comp
    (Subtype.val_injective.comp φ.symm.injective)
  have hmap : ∀ u v, B.Adj u v →
      (completeBipartiteGraph (Fin 3) (Fin 3)).Adj (f u) (f v) := by
    intro u v huv
    exact e.map_rel_iff.mpr (S.adj_sub (φ.symm.map_rel_iff.mpr huv))
  have hnot : ∀ u v, f u = e x → f v = e y → ¬ B.Adj u v := by
    intro u v hu hv huv
    have hu' : (φ.symm u : X) = x := e.injective hu
    have hv' : (φ.symm v : X) = y := e.injective hv
    have hs : S.Adj (φ.symm u : X) (φ.symm v : X) := φ.symm.map_rel_iff.mpr huv
    exact hmiss (hu' ▸ hv' ▸ hs)
  have avoid : ∀ u ∈ branchVertices B, f u ≠ e x ∧ f u ≠ e y := by
    intro u hu
    have bound : ∀ a b, (completeBipartiteGraph (Fin 3) (Fin 3)).Adj a b →
        f u = a → (∀ v, B.Adj u v → f v ≠ b) → False := by
      intro a b hab hua hn
      have hsub : f '' B.neighborSet u ⊆
          (completeBipartiteGraph (Fin 3) (Fin 3)).neighborSet a \ {b} := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨hua ▸ hmap u v hv, hn v hv⟩
      have hcard := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_image_of_injective _ hf, k33_neighbor_delete_card a b hab] at hcard
      change 3 ≤ (B.neighborSet u).ncard at hu
      omega
    constructor
    · intro hx
      exact bound (e x) (e y) (e.map_rel_iff.mpr hxy) hx
        (fun v huv hy => hnot u v hx hy huv)
    · intro hy
      exact bound (e y) (e x) (e.map_rel_iff.mpr hxy.symm) hy
        (fun v huv hx => hnot v u hx hy huv.symm)
  obtain ⟨ι, T, hι, htrack, hlen, _, hdisj, hnew, _, _⟩ := hsub
  have hb : Set.range ι ⊆ branchVertices B :=
    range_subset_branchVertices hι htrack hlen hdisj hnew
      (three_le_degree_of_three_connected J hJ)
  have hsmall : Set.range (f ∘ ι) ⊆ ({e x, e y} : Set (Fin 3 ⊕ Fin 3))ᶜ := by
    rintro _ ⟨u, rfl⟩
    have h := avoid (ι u) (hb ⟨u, rfl⟩)
    simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
      not_or, Function.comp_apply] using h
  have hle := Set.ncard_le_ncard hsmall (Set.toFinite _)
  rw [Set.ncard_range_of_injective (hf.comp hι), Set.ncard_compl,
    Set.ncard_pair (e.injective.ne hxy.ne)] at hle
  simp only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] at hle
  have hcard : Fintype.card U = 4 := by have := hJ.1; omega
  have hcomplete : ∀ u v, u ≠ v → J.Adj u v := by
    intro u v huv
    have hdeg := three_le_degree_of_three_connected J hJ u
    have hsub : J.neighborSet u ⊆ ({u} : Set U)ᶜ := by
      intro w hw heq
      exact hw.ne heq.symm
    have hsize : (({u} : Set U)ᶜ).ncard = 3 := by
      rw [Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, hcard]
    have heq := Set.eq_of_subset_of_ncard_le hsub
      (show (({u} : Set U)ᶜ).ncard ≤ (J.neighborSet u).ncard by omega) (Set.toFinite _)
    change v ∈ J.neighborSet u
    rw [heq]
    exact huv.symm
  refine ⟨{ toEquiv := Fintype.equivFinOfCardEq hcard, map_rel_iff' := ?_ }⟩
  intro u v
  simp only [SimpleGraph.top_adj, ne_eq, Equiv.apply_eq_iff_eq]
  exact ⟨hcomplete u v, SimpleGraph.Adj.ne⟩

end Workspace.ProofLemmas.EnlargementFromNonlocalK33
