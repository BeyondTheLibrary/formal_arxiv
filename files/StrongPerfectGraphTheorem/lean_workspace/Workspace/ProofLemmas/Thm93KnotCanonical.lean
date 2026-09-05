import Workspace.ProofLemmas.Thm93KnotModel
import Workspace.ProofLemmas.Thm93KnotDictionary
import Workspace.ProofLemmas.Thm93KnotTransportW
import Workspace.Statements.S09.Thm_9_1

/-! Reduce the appearance construction to two even chains with four cross edges. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93KnotCanonical
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93KnotModel
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm93KnotHost
open Workspace.ProofLemmas.Thm93KnotSubdivision
open Workspace.ProofLemmas.Thm93KnotHostIso
open Workspace.ProofLemmas.Thm93KnotDictionary

/-- **Remaining construction gap.**
PAPER (9.3, printed p. 48): *"Then `K` is a degenerate appearance of `K₄` in `G`,
say `K=L(H)`."*

Here all vertices and adjacencies are fixed by the two numbers `m,n`. The intended `H`
consists of disjoint chains with `m,n` edges, joined by all four edges between their ends.
The even chain lengths give a bipartite graph. The four cross edges form the degenerate
four-cycle, and the chain edges give `leftPath` and `rightPath` in the line graph. -/
theorem canonical_appearance_gap (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hem : Even m) (hen : Even n) :
    KnotAppearanceData (graph m n) (leftPath m n) (rightPath m n)
      (.inl ⟨0, by omega⟩) (.inl ⟨m - 1, by omega⟩)
      (.inr (.inl ⟨0, by omega⟩)) (.inr (.inl ⟨n - 1, by omega⟩))
      (cross 0) (cross 2) (cross 1) (cross 3) Set.univ := by
  have hmm : 0 < m := by omega
  have hnn : 0 < n := by omega
  refine Thm93KnotTransportW.transportW (phi hm hn) (leftPath m n) (rightPath m n)
    (.inl ⟨0, by omega⟩) (.inl ⟨m - 1, by omega⟩)
    (.inr (.inl ⟨0, by omega⟩)) (.inr (.inl ⟨n - 1, by omega⟩))
    (cross 0) (cross 2) (cross 1) (cross 3)
    (c1 m n) (c2 m n) (c3 m n) (c4 m n)
    (fun c => {u : Vertex m n | edgeOf m n u ∈ incidentEdges (host m n) c})
    ⟨host_isSubdivision hm hn, host_bipartite hem hen⟩ (host_degenerate hm hn)
    (fun c => (phiSet_eq hm hn _).symm) (corners_nodup hm hn)
    (by simp [c1, c2]) (by simp [c2, c3, Fin.val_last]) (by simp [c3, c4, Fin.val_last])
    (by simp [c4, c1, Fin.val_last]) (branchVertices_eq hm hn)
    ⟨edgeOf_mem_edgeSet hmm hnn (cross 0), phi_edgeOf hm hn (cross 0) _⟩ ?_
    ⟨edgeOf_mem_edgeSet hmm hnn (cross 2), phi_edgeOf hm hn (cross 2) _⟩ ?_
    ?_ ?_ ?_ ?_ ?_ ?_
  · -- the edge `c₂c₃` is `y₂ = cross 3`
    have hmem : s(c2 m n, c3 m n) ∈ (host m n).edgeSet := by
      simp [c2, c3, Fin.val_last]
    refine ⟨hmem, ?_⟩
    have hswap : (⟨s(c2 m n, c3 m n), hmem⟩ : (host m n).edgeSet)
        = ⟨edgeOf m n (cross 3), edgeOf_mem_edgeSet hmm hnn (cross 3)⟩ :=
      Subtype.ext (Sym2.eq_swap)
    rw [hswap, phi_edgeOf hm hn (cross 3)]
  · -- the edge `c₄c₁` is `x₂ = cross 1`
    have hmem : s(c4 m n, c1 m n) ∈ (host m n).edgeSet := by
      simp [c4, c1, Fin.val_last]
    refine ⟨hmem, ?_⟩
    have hswap : (⟨s(c4 m n, c1 m n), hmem⟩ : (host m n).edgeSet)
        = ⟨edgeOf m n (cross 1), edgeOf_mem_edgeSet hmm hnn (cross 1)⟩ :=
      Subtype.ext (Sym2.eq_swap)
    rw [hswap, phi_edgeOf hm hn (cross 1)]
  · ext u
    simp only [Set.mem_setOf_eq, mem_incidentEdges_iff hm hn, c1_mem_edgeOf hm hn,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · ext u
    simp only [Set.mem_setOf_eq, mem_incidentEdges_iff hm hn, c2_mem_edgeOf hm hn,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · ext u
    simp only [Set.mem_setOf_eq, mem_incidentEdges_iff hm hn, c3_mem_edgeOf hm hn,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · ext u
    simp only [Set.mem_setOf_eq, mem_incidentEdges_iff hm hn, c4_mem_edgeOf hm hn,
      Set.mem_insert_iff, Set.mem_singleton_iff]
  · refine ⟨chainA m n, chainA_isBranch hm hn, chainA_isTrackFrom, ?_⟩
    rw [phiSet_eq hm hn]
    ext u
    simp only [Set.mem_setOf_eq, edgeOf_mem_trackEdges_chainA hm hn, leftPath,
      List.mem_ofFn, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩
  · refine ⟨chainB m n, chainB_isBranch hm hn, chainB_isTrackFrom, ?_⟩
    rw [phiSet_eq hm hn]
    ext u
    simp only [Set.mem_setOf_eq, edgeOf_mem_trackEdges_chainB hm hn, rightPath,
      List.mem_ofFn, Set.mem_range]
    exact ⟨fun ⟨i, hi⟩ => ⟨i, hi.symm⟩, fun ⟨i, hi⟩ => ⟨i, hi.symm⟩⟩

/-- Apply the indexed construction to the two paths of a knot. The label map is injective,
covers `K`, and preserves adjacency by `label_spec`. -/
theorem appearance_data {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hlen₁ : pathLength Q₁ = 1) (hlen₂ : pathLength Q₂ = 1) :
    KnotAppearanceData G P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K := by
  obtain ⟨ho₁, ho₂, _, _⟩ := (Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot).1
  have hp₁ : 0 < P₁.length := List.length_pos_of_ne_nil hP₁.1.1
  have hp₂ : 0 < P₂.length := List.length_pos_of_ne_nil hP₂.1.1
  have hl₁ : 2 ≤ P₁.length := by obtain ⟨k, hk⟩ := ho₁; unfold pathLength at hk; omega
  have hl₂ : 2 ≤ P₂.length := by obtain ⟨k, hk⟩ := ho₂; unfold pathLength at hk; omega
  have he₁ : Even P₁.length := by
    obtain ⟨k, hk⟩ := ho₁
    exact ⟨k + 1, by unfold pathLength at hk; omega⟩
  have he₂ : Even P₂.length := by
    obtain ⟨k, hk⟩ := ho₂
    exact ⟨k + 1, by unfold pathLength at hk; omega⟩
  obtain ⟨hi, hcover, ha⟩ := label_spec G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂
    hknot hP₁ hP₂ hQ₁ hQ₂ hlen₁ hlen₂ K hK
  have h := Thm93KnotTransport.transport (graph P₁.length P₂.length) G
    (label P₁ P₂ x₁ x₂ y₁ y₂) hi ha K hcover _ _ _ _ _ _ _ _ _ _
    (canonical_appearance_gap P₁.length P₂.length hl₁ hl₂ he₁ he₂)
  simpa only [leftPath_map_label, rightPath_map_label, label, cross,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    PathBasics.getElem_zero_of_head? hP₁.2.1 hp₁,
    PathBasics.getElem_last_of_getLast? hP₁.2.2 hp₁,
    PathBasics.getElem_zero_of_head? hP₂.2.1 hp₂,
    PathBasics.getElem_last_of_getLast? hP₂.2.2 hp₂] using h

end Workspace.ProofLemmas.Thm93KnotCanonical
