import Workspace.ProofLemmas.Thm58StarBranchBasics
import Workspace.ProofLemmas.Thm101LinkOntoTriangle
import Workspace.Types.RousselRubio

/-!
# Three tracks through one vertex give a linkable triangle in the line graph

PAPER (proof of 5.8 (6), printed p. 28): *"Hence in `L(H)` there are three vertex-disjoint
paths, from `N_{v₁}`, `N_{v₂}`, `N_u` respectively to `N_w`, and there are no edges between
them except in the triangle `T` formed by their ends in `N_w`."*

The graph-theoretic content of that sentence is elementary once the three tracks of `H` are
given: three tracks that all start at `w` and meet nowhere else have pairwise disjoint edge
sets, their edges at `w` are pairwise adjacent in `L(H)`, and two edges lying on different
tracks are adjacent in `L(H)` only when both are the edge at `w`.  This file proves that
dictionary and packages it into the `2.4`-ready form
`VertexCanBeLinkedOntoTriangle`, allowing each of the three paths to be extended by an
extra region (the part of a rung, or the path through `F`) which is anticomplete to
everything outside its own sector.

Nothing here is specific to 5.8; only the statement of the gap that uses it is.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchStarTracks

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Thm58StarBranchBasics ThreeTracksLineGraphPrism TrackToRungPath

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
  {φ : H.lineGraph ≃g G.induce K}

section Tracks

variable {p q : List (Fin n)} {a bp bq : Fin n}

/-- Two tracks starting at `a` and meeting only there have different first edges. -/
theorem first_edges_ne (hp : IsTrackFrom H p a bp) (hq : IsTrackFrom H q a bq)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a) :
    firstTrackEdge p hp2 ≠ firstTrackEdge q hq2 := by
  intro heq
  have hp0 : p[0]'(by omega) = a := by
    have := hp.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < p.length)] at this
    exact Option.some_injective _ this
  have hq0 : q[0]'(by omega) = a := by
    have := hq.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < q.length)] at this
    exact Option.some_injective _ this
  rw [firstTrackEdge, firstTrackEdge, hp0, hq0, Sym2.congr_right] at heq
  have hmem : p[1]'(by omega) ∈ q := heq ▸ List.getElem_mem (by omega)
  have hpa : p[1]'(by omega) = a := hmeet _ (List.getElem_mem (by omega)) hmem
  have : (1 : ℕ) = 0 := hp.1.2.1.getElem_inj_iff.mp (by rw [hp0, hpa])
  omega

/-- Edges on two tracks that meet only at their common first vertex are distinct. -/
theorem trackEdges_disjoint (hp : IsTrackFrom H p a bp) (hq : IsTrackFrom H q a bq)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a) {e : Sym2 (Fin n)}
    (hep : e ∈ trackEdges p) (heq : e ∈ trackEdges q) : False := by
  obtain ⟨i, hi, rfl⟩ := hep
  have h1 : p[i]'(by omega) ∈ q := by
    obtain ⟨j, hj, hj'⟩ := heq
    have : p[i]'(by omega) = q[j]'(by omega) ∨ p[i]'(by omega) = q[j + 1]'hj := by
      have : p[i]'(by omega) ∈ s(q[j]'(by omega), q[j + 1]'hj) := by
        rw [← hj']; exact Sym2.mem_mk_left _ _
      simpa using this
    rcases this with h | h <;> rw [h] <;> exact List.getElem_mem _
  have h2 : p[i + 1]'hi ∈ q := by
    obtain ⟨j, hj, hj'⟩ := heq
    have : p[i + 1]'hi = q[j]'(by omega) ∨ p[i + 1]'hi = q[j + 1]'hj := by
      have : p[i + 1]'hi ∈ s(q[j]'(by omega), q[j + 1]'hj) := by
        rw [← hj']; exact Sym2.mem_mk_right _ _
      simpa using this
    rcases this with h | h <;> rw [h] <;> exact List.getElem_mem _
  have e1 : p[i]'(by omega) = a := hmeet _ (List.getElem_mem _) h1
  have e2 : p[i + 1]'hi = a := hmeet _ (List.getElem_mem _) h2
  have : i = i + 1 := hp.1.2.1.getElem_inj_iff.mp (by rw [e1, e2])
  omega

/-- Two rungs of tracks meeting only at `a` are disjoint sets of vertices of `G`. -/
theorem edgeImage_disjoint (hp : IsTrackFrom H p a bp) (hq : IsTrackFrom H q a bq)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a) :
    ∀ x ∈ edgeImage φ (trackEdges p), x ∉ edgeImage φ (trackEdges q) := by
  rintro x ⟨e, he, hep, rfl⟩ ⟨f, hf, hfq, hxf⟩
  have hef : e = f := congrArg Subtype.val (φ.injective (Subtype.ext hxf))
  exact trackEdges_disjoint hp hq hmeet hep (hef ▸ hfq)

/-- The two edges at `a` are adjacent in the line graph, hence in `G`. -/
theorem firstRungVertex_adj (hp : IsTrackFrom H p a bp) (hq : IsTrackFrom H q a bq)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a) :
    G.Adj (firstRungVertex φ p hp.1 hp2) (firstRungVertex φ q hq.1 hq2) := by
  apply φ.map_rel_iff.mpr
  refine ⟨fun hh => first_edges_ne hp hq hp2 hq2 hmeet (congrArg Subtype.val hh), a, ?_, ?_⟩
  · exact firstTrackEdge_contains hp hp2
  · exact firstTrackEdge_contains hq hq2

/-- The only `G`-edge between two such rungs joins the two edges at `a`. -/
theorem edgeImage_cross (hp : IsTrackFrom H p a bp) (hq : IsTrackFrom H q a bq)
    (hp2 : 2 ≤ p.length) (hq2 : 2 ≤ q.length)
    (hmeet : ∀ z ∈ p, z ∈ q → z = a) :
    ∀ x ∈ edgeImage φ (trackEdges p), ∀ y ∈ edgeImage φ (trackEdges q), G.Adj x y →
      x = firstRungVertex φ p hp.1 hp2 ∧ y = firstRungVertex φ q hq.1 hq2 := by
  rintro x ⟨e, he, hep, rfl⟩ y ⟨f, hf, hfq, rfl⟩ hadj
  obtain ⟨hne, z, hze, hzf⟩ :=
    SimpleGraph.lineGraph_adj_iff_exists.mp (φ.map_rel_iff.mp hadj)
  have hzp : z ∈ p := by
    obtain ⟨i, hi, rfl⟩ := hep
    rcases Sym2.mem_iff.mp hze with h | h <;> rw [h] <;> exact List.getElem_mem _
  have hzq : z ∈ q := by
    obtain ⟨j, hj, rfl⟩ := hfq
    rcases Sym2.mem_iff.mp hzf with h | h <;> rw [h] <;> exact List.getElem_mem _
  have hza : z = a := hmeet z hzp hzq
  subst hza
  constructor
  · exact congrArg (fun t : H.edgeSet => (φ t : V))
      (Subtype.ext (edge_eq_firstTrackEdge hp hp2 hep hze))
  · exact congrArg (fun t : H.edgeSet => (φ t : V))
      (Subtype.ext (edge_eq_firstTrackEdge hq hq2 hfq hzf))

end Tracks

/-- The `2.4`-ready packaging of the three-track configuration.

`S i` are three tracks of `H` starting at `w` and meeting only there.  `T i` is the actual
path used for the link: it starts at the edge of `S i` at `w` and runs inside a part `Rg i` of
the rung of `S i` together with an extra region `E i`, which is required to be disjoint from
and anticomplete to everything outside sector `i`.  The triangle is the set of the three edges of
`H` at `w`. -/
theorem canBeLinked_of_star_tracks (v : V) {w : Fin n} {b : Fin 3 → Fin n}
    {S : Fin 3 → List (Fin n)} (hS : ∀ i, IsTrackFrom H (S i) w (b i))
    (hlen : ∀ i, 2 ≤ (S i).length)
    (hmeet : ∀ i j : Fin 3, i ≠ j → ∀ z ∈ S i, z ∈ S j → z = w)
    {Rg E : Fin 3 → Set V}
    (hRg : ∀ i, Rg i ⊆ edgeImage φ (trackEdges (S i)))
    (hEd : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, x ∉ E j)
    (hEr : ∀ i j : Fin 3, ∀ x ∈ E i, x ∉ Rg j)
    (hEE : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, ∀ y ∈ E j, ¬ G.Adj x y)
    (hErc : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ E i, ∀ y ∈ Rg j, ¬ G.Adj x y)
    {T : Fin 3 → List V} (hT : ∀ i, IsPathList G (T i))
    (hThead : ∀ i, (T i).head? = some (firstRungVertex φ (S i) (hS i).1 (hlen i)))
    (hTsub : ∀ i, ∀ x ∈ T i, x ∈ Rg i ∪ E i)
    (hnbr : ∀ i, ∃ x ∈ T i, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v
      (firstRungVertex φ (S 0) (hS 0).1 (hlen 0))
      (firstRungVertex φ (S 1) (hS 1).1 (hlen 1))
      (firstRungVertex φ (S 2) (hS 2).1 (hlen 2)) := by
  classical
  refine Thm101LinkOntoTriangle.canBeLinkedOntoTriangle_of_sectors G v
    (fun i => firstRungVertex φ (S i) (hS i).1 (hlen i)) T
    (fun i => Rg i ∪ E i) ?_ hT (fun i => Or.inl (hThead i))
    hTsub ?_ ?_ hnbr
  · intro i j hij
    exact firstRungVertex_adj (hS i) (hS j) (hlen i) (hlen j) (hmeet i j hij)
  · rintro i j hij x (hx | hx) (hx' | hx')
    · exact edgeImage_disjoint (hS i) (hS j) (hmeet i j hij) x (hRg i hx) (hRg j hx')
    · exact hEr j i x hx' hx
    · exact hEr i j x hx hx'
    · exact hEd i j hij x hx hx'
  · rintro i j hij x (hx | hx) y (hy | hy) hadj
    · exact edgeImage_cross (hS i) (hS j) (hlen i) (hlen j) (hmeet i j hij)
        x (hRg i hx) y (hRg j hy) hadj
    · exact absurd hadj.symm (hErc j i hij.symm y hy x hx)
    · exact absurd hadj (hErc i j hij x hx y hy)
    · exact absurd hadj (hEE i j hij x hx y hy)

end Workspace.ProofLemmas.Thm58StarBranchStarTracks
