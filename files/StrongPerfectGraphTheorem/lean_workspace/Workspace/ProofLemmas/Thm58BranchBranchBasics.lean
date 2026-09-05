import Workspace.ProofLemmas.Thm58Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.Thm58SingletonCase

/-!
# The two branches in 5.8 (5) and (7)

The attachment union is not local, so the two branches are different. Distinct
branches share no edge. Thus only the ends of the outside path can have neighbors
in the appearance, and each end has a neighbor in its own branch.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranch

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- Attachments read back as edges of `H`, as in printed p. 26. -/
def edgeAttachments (φ : H.lineGraph ≃g G.induce K) (F : Set V) : Set (Sym2 (Fin n)) :=
  {e | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K}

/-- The hypotheses on the path permit either choice of its first end. -/
theorem ready_reverse (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂) :
    Thm58Setup.Ready G m J n H K φ N F P.reverse p₂ p₁ := by
  rcases h with ⟨hG, hJ, hsub, hN, hFK, hnonlocal, hP, hPF, hcard⟩
  refine ⟨hG, hJ, hsub, hN, hFK, hnonlocal, PathBasics.isPathFrom_reverse hP, ?_, hcard⟩
  simpa only [List.mem_reverse] using hPF

/-- The two ends differ because the path has at least two vertices. -/
theorem ends_ne (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂) : p₁ ≠ p₂ := by
  rcases h with ⟨_, _, _, _, _, _, hP, hPF, hcard⟩
  have hlen : 2 ≤ P.length := by
    by_contra hshort
    have hpos := PathBasics.path_length_pos hP.1
    have hone : P.length = 1 := by omega
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hone
    have hF : F = {a} := by rw [← hPF, ha]; ext x; simp
    simp [hF] at hcard
  exact PathBasics.isPathFrom_ends_ne hP (by unfold pathLength; omega)

/-- An edge common to two branches identifies their edge sets. This is the
branch part of claim (5), using the subdivision's disjoint interiors. -/
theorem branch_edges_eq_of_common (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q r : List (Fin n)} (hq : IsBranch H q) (hr : IsBranch H r)
    {e : Sym2 (Fin n)} (heq : e ∈ trackEdges q) (her : e ∈ trackEdges r) :
    trackEdges q = trackEdges r := by
  obtain ⟨ι, T, hι, ht, hl, hrev, hd, hnew, hcover, he⟩ := hsub
  have hdeg := SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hq2 : 2 ≤ q.length := by obtain ⟨i, hi, _⟩ := heq; omega
  have hr2 : 2 ≤ r.length := by obtain ⟨i, hi, _⟩ := her; omega
  obtain ⟨u, v, huv, hqT⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
    hι ht hl hrev hd hnew hcover he hdeg hq hq2
  obtain ⟨a, b, hab, hrT⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
    hι ht hl hrev hd hnew hcover he hdeg hr hr2
  have heqT : e ∈ trackEdges (T u v) := hqT ▸ heq
  have herT : e ∈ trackEdges (T a b) := hrT ▸ her
  have heqends := SubdivisionCounting.trackEdges_disjoint hι ht hl hd
    u v a b huv hab e heqT herT
  rw [hqT, hrT]
  rcases Sym2.eq_iff.mp heqends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [hrev _ _ hab, SubdivisionCounting.trackEdges_reverse]

/-- Any branch through an internal vertex of another branch has the same edges. -/
theorem branch_edges_eq_of_internal (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    {q r : List (Fin n)} (hq : IsBranch H q) (hr : IsBranch H r)
    {c : Fin n} (hcq : c ∈ trackInterior q) (hcr : c ∈ r) :
    trackEdges q = trackEdges r := by
  obtain ⟨k, hk, hkc⟩ := (SubdivisionCounting.mem_trackInterior_iff q c).mp hcq
  have hinc : incidentEdges H c ⊆ trackEdges q := by
    rw [← hkc]
    exact Thm57Claim2Structure.incidentEdges_internal_subset hq (by omega) (by omega)
  by_cases hr2 : 2 ≤ r.length
  · obtain ⟨i, hi, hc⟩ := BranchClassification.exists_edge_of_mem hr2 hcr
    have he : s(r[i]'(by omega), r[i + 1]'hi) ∈ trackEdges r := ⟨i, hi, rfl⟩
    apply branch_edges_eq_of_common hJ hsub hq hr (hinc ⟨hr.1.2.2 i hi, ?_⟩) he
    rcases hc with h | h <;> simp [h]
  · have hlen : r.length = 1 := by
      have hpos := List.length_pos_of_ne_nil hr.1.1
      omega
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hac : a = c := (List.mem_singleton.mp hcr).symm
    subst a
    have heq := hr.2.2 q hq.1 hq.2.1
      (by rintro e ⟨i, hi, _⟩; simp at hi)
      (by intro w hw; have hwc := List.mem_singleton.mp hw; rw [hwc, ← hkc]; exact List.getElem_mem _)
    have hmem : s(q[k]'(by omega), q[k + 1]'(by omega)) ∈ trackEdges [c] :=
      heq ▸ (show s(q[k]'(by omega), q[k + 1]'(by omega)) ∈ trackEdges q from ⟨k, by omega, rfl⟩)
    obtain ⟨i, hi, _⟩ := hmem
    simp at hi

/-- Every attachment of `F` lies in one of the two sets obtained by deleting an end. -/
theorem attachments_union (hne : p₁ ≠ p₂) :
    edgeAttachments φ F =
      edgeAttachments φ (F \ {p₂}) ∪ edgeAttachments φ (F \ {p₁}) := by
  ext e
  constructor
  · rintro ⟨he, hyK, x, hxF, hyx⟩
    by_cases hx : x = p₂
    · exact Or.inr ⟨he, hyK, x, ⟨hxF, by simpa [hx] using hne.symm⟩, hyx⟩
    · exact Or.inl ⟨he, hyK, x, ⟨hxF, hx⟩, hyx⟩
  · rintro (⟨he, hyK, x, hxF, hyx⟩ | ⟨he, hyK, x, hxF, hyx⟩)
    · exact ⟨he, hyK, x, hxF.1, hyx⟩
    · exact ⟨he, hyK, x, hxF.1, hyx⟩

/-- PAPER (7): "the edges `u₁v₁` and `u₂v₂` are different". -/
theorem branches_ne (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂) :
    trackEdges q₁ ≠ trackEdges q₂ := by
  intro heq
  apply h.2.2.2.2.2.1
  refine Or.inr ⟨q₁, hq₁, ?_⟩
  change edgeAttachments φ F ⊆ trackEdges q₁
  rw [attachments_union (φ := φ) (ends_ne h)]
  exact Set.union_subset hX₁ (heq.symm ▸ hX₂)

/-- The branch attachments are disjoint, including the intersection in claim (5). -/
theorem branches_disjoint (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂) :
    Disjoint (trackEdges q₁) (trackEdges q₂) := by
  apply Set.disjoint_left.mpr
  intro e he₁ he₂
  exact branches_ne h hq₁ hX₁ hX₂
    (branch_edges_eq_of_common h.2.1 h.2.2.1.1 hq₁ hq₂ he₁ he₂)

/-- Only the two path ends can have neighbors in the appearance. -/
theorem adjacent_vertex_is_end (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {x y : V} (hx : x ∈ F) (hy : y ∈ K) (hxy : G.Adj x y) :
    x = p₁ ∨ x = p₂ := by
  by_contra hends
  have hne₁ : x ≠ p₁ := fun heq => hends (Or.inl heq)
  have hne₂ : x ≠ p₂ := fun heq => hends (Or.inr heq)
  let e := φ.symm ⟨y, hy⟩
  have he : (↑(φ e) : V) = y := congrArg Subtype.val (φ.apply_symm_apply ⟨y, hy⟩)
  have he₁ : e.1 ∈ edgeAttachments φ (F \ {p₂}) :=
    ⟨e.2, he.symm ▸ hy, x, ⟨hx, hne₂⟩, he.symm ▸ hxy.symm⟩
  have he₂ : e.1 ∈ edgeAttachments φ (F \ {p₁}) :=
    ⟨e.2, he.symm ▸ hy, x, ⟨hx, hne₁⟩, he.symm ▸ hxy.symm⟩
  exact Set.disjoint_left.mp (branches_disjoint h hq₁ hq₂ hX₁ hX₂) (hX₁ he₁) (hX₂ he₂)

/-- Nonlocality forces each path end to have a neighbor in `K`. -/
theorem first_end_has_neighbor (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₂ : List (Fin n)} (hq₂ : IsBranch H q₂)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂) :
    ∃ y ∈ K, G.Adj p₁ y := by
  by_contra hnone
  apply h.2.2.2.2.2.1
  refine Or.inr ⟨q₂, hq₂, ?_⟩
  rintro e ⟨he, hyK, x, hxF, hyx⟩
  apply hX₂
  refine ⟨he, hyK, x, ⟨hxF, ?_⟩, hyx⟩
  intro hxp
  exact hnone ⟨_, hyK, hxp ▸ hyx.symm⟩

end Workspace.ProofLemmas.Thm58BranchBranch
