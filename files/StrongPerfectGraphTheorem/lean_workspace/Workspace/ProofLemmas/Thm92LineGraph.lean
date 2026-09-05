import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm92Intrinsic
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-!
# The line-graph side of 9.2

For a bipartite subdivision of `K₄`, the triangles of the line graph are exactly the three
edges at branch vertices.  Its flat components are exactly its six branches.  This identifies
the two definitions from `Appearances` with the intrinsic definitions used by 9.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm92LineGraph

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm92Intrinsic

variable {W : Type*} [Fintype W] [DecidableEq W]

def edgeSubtypeSet (H : SimpleGraph W) (X : Set (Sym2 W)) : Set H.edgeSet :=
  {e | (e : Sym2 W) ∈ X}

theorem k4_neighbor_ncard (u : Fin 4) :
    ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard = 3 := by
  have heq : (⊤ : SimpleGraph (Fin 4)).neighborSet u = ({u} : Set (Fin 4))ᶜ := by
    ext v
    simp [SimpleGraph.top_adj, ne_comm]
  rw [heq]
  have hsum := Set.ncard_add_ncard_compl ({u} : Set (Fin 4))
  rw [Set.ncard_singleton, Nat.card_eq_fintype_card, Fintype.card_fin] at hsum
  omega

section Setup

variable {H : SimpleGraph W} {ι : Fin 4 → W} {T : Fin 4 → Fin 4 → List W}
  (hι : Function.Injective ι)
  (htrack : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
    IsTrackFrom H (T u v) (ι u) (ι v))
  (hlen : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
    1 ≤ trackLength (T u v))
  (hrev : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
    T v u = (T u v).reverse)
  (hdisj : ∀ u v u' v' : Fin 4,
    (⊤ : SimpleGraph (Fin 4)).Adj u v → (⊤ : SimpleGraph (Fin 4)).Adj u' v' →
    s(u, v) ≠ s(u', v') → ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
  (hnew : ∀ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v →
    ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
  (hcover : ∀ w : W, (∃ u : Fin 4, w = ι u) ∨
    ∃ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v ∧ w ∈ trackInterior (T u v))
  (hedges : H.edgeSet = ⋃ (u : Fin 4) (v : Fin 4)
    (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v), trackEdges (T u v))

include hι htrack hlen hrev hdisj hnew hcover hedges in
theorem branchVertices_eq_range : branchVertices H = Set.range ι := by
  apply Set.Subset.antisymm
  · exact SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  · exact SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew
      (fun u => by rw [k4_neighbor_ncard])

include hι htrack hlen hrev hdisj hnew hcover hedges in
theorem branch_degree_eq_three (u : Fin 4) :
    (H.neighborSet (ι u)).ncard = 3 := by
  apply le_antisymm
  · calc
      (H.neighborSet (ι u)).ncard ≤
          ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
        Thm84RungEndDictionary.degree_branch_le hι htrack hlen hrev hnew hedges u
      _ = 3 := k4_neighbor_ncard u
  · have hrange : ι u ∈ branchVertices H := by
      rw [branchVertices_eq_range hι htrack hlen hrev hdisj hnew hcover hedges]
      exact ⟨u, rfl⟩
    exact hrange

include hι htrack hlen hrev hdisj hnew hcover hedges in
theorem incidentEdges_ncard_eq_three {w : W} (hw : w ∈ branchVertices H) :
    (incidentEdges H w).ncard = 3 := by
  rw [branchVertices_eq_range hι htrack hlen hrev hdisj hnew hcover hedges] at hw
  obtain ⟨u, rfl⟩ := hw
  rw [Thm84RungEndDictionary.incidentEdges_ncard,
    branch_degree_eq_three hι htrack hlen hrev hdisj hnew hcover hedges]

include hι htrack hlen hrev hdisj hnew hcover hedges in
theorem subdividingTrack_isBranch {u v : Fin 4}
    (huv : (⊤ : SimpleGraph (Fin 4)).Adj u v) : IsBranch H (T u v) := by
  have hbv : branchVertices H = Set.range ι :=
    branchVertices_eq_range hι htrack hlen hrev hdisj hnew hcover hedges
  refine Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
    (fun h => huv.ne (hι h)) ?_ ?_ ?_
  · intro w hw hwb
    exact hnew u v huv w hw (by rw [← hbv]; exact hwb)
  · rw [hbv]; exact ⟨u, rfl⟩
  · rw [hbv]; exact ⟨v, rfl⟩

include hedges in
theorem edge_mem_some_track {e : Sym2 W} (he : e ∈ H.edgeSet) :
    ∃ u v : Fin 4, ∃ huv : (⊤ : SimpleGraph (Fin 4)).Adj u v,
      e ∈ trackEdges (T u v) := by
  rw [hedges] at he
  simp only [Set.mem_iUnion] at he
  exact he

/-- A triangle of `L(H)` is the star of a branch vertex. -/
theorem lineTriangle_common (hbip : H.IsBipartite) {e₁ e₂ e₃ : H.edgeSet}
    (h12 : H.lineGraph.Adj e₁ e₂) (h23 : H.lineGraph.Adj e₂ e₃)
    (h31 : H.lineGraph.Adj e₃ e₁) :
    ∃ w ∈ branchVertices H,
      (e₁ : Sym2 W) ∈ incidentEdges H w ∧ (e₂ : Sym2 W) ∈ incidentEdges H w ∧
        (e₃ : Sym2 W) ∈ incidentEdges H w := by
  obtain ⟨hne12, a, ha1, ha2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp h12
  obtain ⟨hne23, b, hb2, hb3⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp h23
  obtain ⟨hne31, c, hc3, hc1⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp h31
  have ne12 : (e₁ : Sym2 W) ≠ (e₂ : Sym2 W) := fun h => hne12 (Subtype.ext h)
  have ne23 : (e₂ : Sym2 W) ≠ (e₃ : Sym2 W) := fun h => hne23 (Subtype.ext h)
  have ne13 : (e₁ : Sym2 W) ≠ (e₃ : Sym2 W) := fun h => hne31 (Subtype.ext h.symm)
  obtain ⟨w, hw1, hw2, hw3⟩ := Thm84RungEndDictionary.exists_common_of_three hbip
    e₁.2 e₂.2 e₃.2 ne12 ne13 ne23 ⟨a, ha1, ha2⟩ ⟨c, hc1, hc3⟩ ⟨b, hb2, hb3⟩
  have hthree : ({(e₁ : Sym2 W), (e₂ : Sym2 W), (e₃ : Sym2 W)} : Set (Sym2 W)) ⊆
      incidentEdges H w := by
    rintro e (rfl | rfl | rfl)
    · exact ⟨e₁.2, hw1⟩
    · exact ⟨e₂.2, hw2⟩
    · exact ⟨e₃.2, hw3⟩
  have hcard : 3 ≤ (incidentEdges H w).ncard := by
    have hsetcard : ({(e₁ : Sym2 W), (e₂ : Sym2 W), (e₃ : Sym2 W)} : Set (Sym2 W)).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨_, _, _, ne12, ne13, ne23, rfl⟩
    rw [← hsetcard]
    exact Set.ncard_le_ncard hthree (Set.toFinite _)
  have hwb : w ∈ branchVertices H := by
    change 3 ≤ (H.neighborSet w).ncard
    rw [← Thm84RungEndDictionary.incidentEdges_ncard]
    exact hcard
  exact ⟨w, hwb, ⟨e₁.2, hw1⟩, ⟨e₂.2, hw2⟩, ⟨e₃.2, hw3⟩⟩

/-- Two line-graph vertices meeting at a non-branch vertex form a flat edge. -/
theorem flatAdj_of_common_nonbranch (hbip : H.IsBipartite) {e f : H.edgeSet} {w : W}
    (hef : e ≠ f) (hwe : w ∈ (e : Sym2 W)) (hwf : w ∈ (f : Sym2 W))
    (hwb : w ∉ branchVertices H) : FlatAdj H.lineGraph e f := by
  refine ⟨(SimpleGraph.lineGraph_adj_iff_exists).mpr ⟨hef, w, hwe, hwf⟩, ?_⟩
  rintro ⟨g, heg, hfg⟩
  obtain ⟨hneeg, a, hae, hag⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp heg
  obtain ⟨hnefg, b, hbf, hbg⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hfg
  have neef : (e : Sym2 W) ≠ (f : Sym2 W) := fun h => hef (Subtype.ext h)
  have neeg : (e : Sym2 W) ≠ (g : Sym2 W) := fun h => hneeg (Subtype.ext h)
  have nefg : (f : Sym2 W) ≠ (g : Sym2 W) := fun h => hnefg (Subtype.ext h)
  obtain ⟨z, hze, hzf, hzg⟩ := Thm84RungEndDictionary.exists_common_of_three hbip
    e.2 f.2 g.2 neef neeg nefg ⟨w, hwe, hwf⟩ ⟨a, hae, hag⟩ ⟨b, hbf, hbg⟩
  have hzw : z = w := Thm84RungEndDictionary.subsingleton_inter_of_ne neef hze hzf hwe hwf
  apply hwb
  change 3 ≤ (H.neighborSet w).ncard
  rw [← Thm84RungEndDictionary.incidentEdges_ncard]
  have hsub : ({(e : Sym2 W), (f : Sym2 W), (g : Sym2 W)} : Set (Sym2 W)) ⊆
      incidentEdges H w := by
    rintro x (rfl | rfl | rfl)
    · exact ⟨e.2, hwe⟩
    · exact ⟨f.2, hwf⟩
    · exact ⟨g.2, hzw ▸ hzg⟩
  have hc : ({(e : Sym2 W), (f : Sym2 W), (g : Sym2 W)} : Set (Sym2 W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨_, _, _, neef, neeg, nefg, rfl⟩
  rw [← hc]
  exact Set.ncard_le_ncard hsub (Set.toFinite _)

include hι htrack hlen hrev hdisj hnew hcover hedges in
/-- A flat step cannot leave one subdividing track. -/
theorem flatAdj_closed_track (hbip : H.IsBipartite) {u v : Fin 4}
    (huv : (⊤ : SimpleGraph (Fin 4)).Adj u v) {e f : H.edgeSet}
    (heT : (e : Sym2 W) ∈ trackEdges (T u v)) (hef : FlatAdj H.lineGraph e f) :
    (f : Sym2 W) ∈ trackEdges (T u v) := by
  obtain ⟨hne, w, hwe, hwf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hef.1
  have hwb : w ∉ branchVertices H := by
    intro hbranch
    have hcard : 3 ≤ (incidentEdges H w).ncard := by
      rw [Thm84RungEndDictionary.incidentEdges_ncard]
      exact hbranch
    have heI : (e : Sym2 W) ∈ incidentEdges H w := ⟨e.2, hwe⟩
    have hfI : (f : Sym2 W) ∈ incidentEdges H w := ⟨f.2, hwf⟩
    have hdiffcard : (incidentEdges H w \ {(e : Sym2 W)}).ncard =
        (incidentEdges H w).ncard - 1 := Set.ncard_diff_singleton_of_mem heI
    have hdiffgt : 1 < (incidentEdges H w \ {(e : Sym2 W)}).ncard := by omega
    obtain ⟨g, hg, hgf⟩ :=
      Set.exists_ne_of_one_lt_ncard hdiffgt (f : Sym2 W)
    have hgI : g ∈ incidentEdges H w := hg.1
    have hge : g ≠ (e : Sym2 W) := by
      intro h
      exact hg.2 (by simpa using h)
    let g' : H.edgeSet := ⟨g, hgI.1⟩
    apply hef.2
    refine ⟨g', ?_, ?_⟩
    · exact (SimpleGraph.lineGraph_adj_iff_exists).mpr
        ⟨fun h => hge (congrArg Subtype.val h).symm, w, hwe, hgI.2⟩
    · exact (SimpleGraph.lineGraph_adj_iff_exists).mpr
        ⟨fun h => hgf (congrArg Subtype.val h).symm, w, hwf, hgI.2⟩
  have hwT : w ∈ T u v := by
    obtain ⟨i, hi, hei⟩ := heT
    rw [hei, Sym2.mem_iff] at hwe
    rcases hwe with h | h
    · exact h ▸ List.getElem_mem _
    · exact h ▸ List.getElem_mem _
  have hwTint : w ∈ trackInterior (T u v) := by
    have hnotrange : w ∉ Set.range ι := by
      rw [← branchVertices_eq_range hι htrack hlen hrev hdisj hnew hcover hedges]
      exact hwb
    have hpos : 0 < (T u v).length := by
      have := hlen u v huv
      simp only [trackLength] at this
      omega
    by_contra hnotint
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hwT hnotint hpos with h | h
    · rw [h, SubdivisionCounting.track_head (htrack u v huv) hpos] at hnotrange
      exact absurd ⟨u, rfl⟩ hnotrange
    · rw [h, DegenerateK4Tracks.track_getLast (htrack u v huv) hpos] at hnotrange
      exact absurd ⟨v, rfl⟩ hnotrange
  obtain ⟨p, q, hpq, hfT⟩ := edge_mem_some_track hedges f.2
  have hwT' : w ∈ T p q := by
    obtain ⟨i, hi, hfi⟩ := hfT
    rw [hfi, Sym2.mem_iff] at hwf
    rcases hwf with h | h
    · exact h ▸ List.getElem_mem _
    · exact h ▸ List.getElem_mem _
  by_cases hs : s(u, v) = s(p, q)
  · rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hfT
    · rw [hrev u v huv, SubdivisionCounting.trackEdges_reverse] at hfT
      exact hfT
  · exact absurd hwT' (hdisj u v p q huv hpq hs w hwTint)

include hι htrack hlen hrev hdisj hnew hcover hedges in
/-- All edges of one subdividing track lie in one flat component of the line graph. -/
theorem trackEdges_flat_reachable (hbip : H.IsBipartite) {u v : Fin 4}
    (huv : (⊤ : SimpleGraph (Fin 4)).Adj u v) {e f : H.edgeSet}
    (he : (e : Sym2 W) ∈ trackEdges (T u v))
    (hf : (f : Sym2 W) ∈ trackEdges (T u v)) :
    Relation.ReflTransGen (FlatAdj H.lineGraph) e f := by
  let q := T u v
  have hq : IsTrackFrom H q (ι u) (ι v) := htrack u v huv
  have hq2 : 2 ≤ q.length := by
    have := hlen u v huv
    change 1 ≤ q.length - 1 at this
    omega
  let edgeAt : ∀ k : ℕ, k + 1 < q.length → H.edgeSet := fun k hk =>
    ⟨s(q[k]'(by omega), q[k + 1]'hk), hq.1.2.2 k hk⟩
  have hstep : ∀ k (hk : k + 2 < q.length),
      FlatAdj H.lineGraph (edgeAt k (by omega)) (edgeAt (k + 1) (by omega)) := by
    intro k hk
    have hnd := hq.1.2.1
    have hne : edgeAt k (by omega) ≠ edgeAt (k + 1) (by omega) := by
      intro h
      have hv := congrArg Subtype.val h
      change s(q[k]'(by omega), q[k + 1]'(by omega)) =
        s(q[k + 1]'(by omega), q[k + 2]'(by omega)) at hv
      rcases Sym2.eq_iff.mp hv with hp | hp
      · have := hnd.getElem_inj_iff.mp hp.1
        omega
      · have := hnd.getElem_inj_iff.mp hp.1
        omega
    have hmid : q[k + 1]'(by omega) ∈ trackInterior q :=
      SubdivisionCounting.mem_trackInterior_getElem q k hk
    have hnotbranch : q[k + 1]'(by omega) ∉ branchVertices H := by
      intro hb
      have hrange : q[k + 1]'(by omega) ∈ Set.range ι := by
        rw [← branchVertices_eq_range hι htrack hlen hrev hdisj hnew hcover hedges]
        exact hb
      exact hnew u v huv _ hmid hrange
    exact flatAdj_of_common_nonbranch hbip hne (by simp [edgeAt]) (by simp [edgeAt]) hnotbranch
  have hreach0 : ∀ k (hk : k + 1 < q.length),
      Relation.ReflTransGen (FlatAdj H.lineGraph) (edgeAt 0 (by omega)) (edgeAt k hk) := by
    intro k
    induction k with
    | zero =>
        intro hk
        have heq : edgeAt 0 (by omega) = edgeAt 0 hk := Subtype.ext rfl
        rw [heq]
    | succ k ih =>
        intro hk
        exact Relation.ReflTransGen.tail (ih (by omega)) (hstep k (by omega))
  obtain ⟨i, hi, hei⟩ := he
  obtain ⟨j, hj, hfj⟩ := hf
  have heq : e = edgeAt i hi := Subtype.ext hei
  have hfeq : f = edgeAt j hj := Subtype.ext hfj
  rw [heq, hfeq]
  have hir := hreach0 i hi
  have hjr := hreach0 j hj
  exact (Relation.ReflTransGen.symmetric (fun _ _ => flatAdj_symm) hir).trans hjr

end Setup

/-! ### The two intrinsic dictionaries -/

theorem localForLineGraph_iff_intrinsic {H : SimpleGraph W}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) (hX : X ⊆ H.edgeSet) :
    LocalForLineGraph H X ↔ IntrinsicLocal H.lineGraph (edgeSubtypeSet H X) := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    fun u => by rw [k4_neighbor_ncard]
  constructor
  · rintro (⟨w, hwb, hsubX⟩ | ⟨q, hqB, hsubX⟩)
    · have hc := incidentEdges_ncard_eq_three hι htrack hlen hrev hdisj hnew hcover hedges hwb
      obtain ⟨e₁, e₂, e₃, h12, h13, h23, hstar⟩ := Set.ncard_eq_three.mp hc
      have he₁ : e₁ ∈ H.edgeSet := by
        have : e₁ ∈ incidentEdges H w := by rw [hstar]; simp
        exact this.1
      have he₂ : e₂ ∈ H.edgeSet := by
        have : e₂ ∈ incidentEdges H w := by rw [hstar]; simp
        exact this.1
      have he₃ : e₃ ∈ H.edgeSet := by
        have : e₃ ∈ incidentEdges H w := by rw [hstar]; simp
        exact this.1
      let E₁ : H.edgeSet := ⟨e₁, he₁⟩
      let E₂ : H.edgeSet := ⟨e₂, he₂⟩
      let E₃ : H.edgeSet := ⟨e₃, he₃⟩
      have hadj12 : H.lineGraph.Adj E₁ E₂ :=
        (SimpleGraph.lineGraph_adj_iff_exists).mpr
          ⟨fun h => h12 (congrArg Subtype.val h), w,
            (by have hh : e₁ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₁ : Sym2 W); exact hh.2),
            (by have hh : e₂ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₂ : Sym2 W); exact hh.2)⟩
      have hadj23 : H.lineGraph.Adj E₂ E₃ :=
        (SimpleGraph.lineGraph_adj_iff_exists).mpr
          ⟨fun h => h23 (congrArg Subtype.val h), w,
            (by have hh : e₂ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₂ : Sym2 W); exact hh.2),
            (by have hh : e₃ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₃ : Sym2 W); exact hh.2)⟩
      have hadj31 : H.lineGraph.Adj E₃ E₁ :=
        (SimpleGraph.lineGraph_adj_iff_exists).mpr
          ⟨fun h => h13 (congrArg Subtype.val h).symm, w,
            (by have hh : e₃ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₃ : Sym2 W); exact hh.2),
            (by have hh : e₁ ∈ incidentEdges H w := by rw [hstar]; simp
                show w ∈ (E₁ : Sym2 W); exact hh.2)⟩
      refine Or.inl ⟨E₁, E₂, E₃, hadj12, hadj23, hadj31, ?_⟩
      intro e heX
      have heI := hsubX heX
      rw [hstar] at heI
      rcases heI with he | he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Or.inl (Subtype.ext he))
      · have heq : e = E₃ := Subtype.ext (by simpa using he)
        exact Or.inr (Or.inr (by simpa using heq))
    · refine Or.inr ?_
      by_cases hsmall : q.length < 2
      · left
        ext e
        constructor
        · intro he
          obtain ⟨i, hi, -⟩ := hsubX he
          omega
        · simp
      · have hq2 : 2 ≤ q.length := by omega
        obtain ⟨u, v, huv, hEq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
          hι htrack hlen hrev hdisj hnew hcover hedges hdeg hqB hq2
        by_cases hempty : edgeSubtypeSet H X = ∅
        · exact Or.inl hempty
        · right
          obtain ⟨e, he⟩ := Set.nonempty_iff_ne_empty.mpr hempty
          refine ⟨e, he, ?_⟩
          intro f hf
          apply trackEdges_flat_reachable hι htrack hlen hrev hdisj hnew hcover hedges hbip huv
          · rw [← hEq]
            exact hsubX he
          · rw [← hEq]
            exact hsubX hf
  · rintro (⟨e₁, e₂, e₃, h12, h23, h31, hsubX⟩ | hflat)
    · obtain ⟨w, hwb, he₁, he₂, he₃⟩ := lineTriangle_common hbip h12 h23 h31
      exact Or.inl ⟨w, hwb, fun e he => by
        have he' : (⟨e, hX he⟩ : H.edgeSet) ∈ edgeSubtypeSet H X := he
        rcases hsubX he' with h | h | h
        · have hev : e = (e₁ : Sym2 W) := congrArg Subtype.val h
          rw [hev]
          exact he₁
        · have hev : e = (e₂ : Sym2 W) := congrArg Subtype.val h
          rw [hev]
          exact he₂
        · have h3 : (⟨e, hX he⟩ : H.edgeSet) = e₃ := by simpa using h
          have hev : e = (e₃ : Sym2 W) := congrArg Subtype.val h3
          rw [hev]
          exact he₃⟩
    · rcases hflat with hempty | ⟨e, heX, hreach⟩
      · have hXempty : X = ∅ := by
          ext x
          constructor
          · intro hx
            have : (⟨x, hX hx⟩ : H.edgeSet) ∈ edgeSubtypeSet H X := hx
            rw [hempty] at this
            exact this.elim
          · simp
        have huv : (⊤ : SimpleGraph (Fin 4)).Adj (0 : Fin 4) 1 := by simp
        exact Or.inr ⟨T 0 1,
          subdividingTrack_isBranch hι htrack hlen hrev hdisj hnew hcover hedges huv,
          by rw [hXempty]; exact Set.empty_subset _⟩
      · obtain ⟨u, v, huv, heT⟩ := edge_mem_some_track hedges e.2
        refine Or.inr ⟨T u v,
          subdividingTrack_isBranch hι htrack hlen hrev hdisj hnew hcover hedges huv, ?_⟩
        intro x hx
        have hx' : (⟨x, hX hx⟩ : H.edgeSet) ∈ edgeSubtypeSet H X := hx
        have hr := hreach ⟨x, hX hx⟩ hx'
        have hclosed : ∀ f : H.edgeSet, Relation.ReflTransGen (FlatAdj H.lineGraph) e f →
            (f : Sym2 W) ∈ trackEdges (T u v) := by
          intro f hreach'
          induction hreach' with
          | refl => exact heT
          | tail hprev hstep ih =>
              exact flatAdj_closed_track hι htrack hlen hrev hdisj hnew hcover hedges hbip
                huv ih hstep
        exact hclosed _ hr

theorem saturatesLineGraph_iff_intrinsic {H : SimpleGraph W}
    (hsub : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) :
    SaturatesLineGraph H X ↔ IntrinsicSaturates H.lineGraph (edgeSubtypeSet H X) := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  constructor
  · intro hsat e₁ e₂ e₃ h12 h23 h31 x hx y hy
    obtain ⟨w, hwb, he₁, he₂, he₃⟩ := lineTriangle_common hbip h12 h23 h31
    apply Subtype.ext
    apply hsat w hwb
    · refine ⟨?_, ?_⟩
      · rcases hx.1 with h | h | h
        · exact (show (x : Sym2 W) ∈ incidentEdges H w by simpa [h] using he₁)
        · exact (show (x : Sym2 W) ∈ incidentEdges H w by simpa [h] using he₂)
        · have hx3 : x = e₃ := by simpa using h
          exact hx3 ▸ he₃
      · exact hx.2
    · refine ⟨?_, ?_⟩
      · rcases hy.1 with h | h | h
        · exact (show (y : Sym2 W) ∈ incidentEdges H w by simpa [h] using he₁)
        · exact (show (y : Sym2 W) ∈ incidentEdges H w by simpa [h] using he₂)
        · have hy3 : y = e₃ := by simpa using h
          exact hy3 ▸ he₃
      · exact hy.2
  · intro hint w hwb
    have hc := incidentEdges_ncard_eq_three hι htrack hlen hrev hdisj hnew hcover hedges hwb
    obtain ⟨e₁, e₂, e₃, h12, h13, h23, hstar⟩ := Set.ncard_eq_three.mp hc
    have he₁ : e₁ ∈ H.edgeSet := (show e₁ ∈ incidentEdges H w by rw [hstar]; simp).1
    have he₂ : e₂ ∈ H.edgeSet := (show e₂ ∈ incidentEdges H w by rw [hstar]; simp).1
    have he₃ : e₃ ∈ H.edgeSet := (show e₃ ∈ incidentEdges H w by rw [hstar]; simp).1
    let E₁ : H.edgeSet := ⟨e₁, he₁⟩
    let E₂ : H.edgeSet := ⟨e₂, he₂⟩
    let E₃ : H.edgeSet := ⟨e₃, he₃⟩
    have hw₁ : w ∈ e₁ := (show e₁ ∈ incidentEdges H w by rw [hstar]; simp).2
    have hw₂ : w ∈ e₂ := (show e₂ ∈ incidentEdges H w by rw [hstar]; simp).2
    have hw₃ : w ∈ e₃ := (show e₃ ∈ incidentEdges H w by rw [hstar]; simp).2
    have hs := hint E₁ E₂ E₃
      ((SimpleGraph.lineGraph_adj_iff_exists).mpr
        ⟨fun h => h12 (congrArg Subtype.val h), w, hw₁, hw₂⟩)
      ((SimpleGraph.lineGraph_adj_iff_exists).mpr
        ⟨fun h => h23 (congrArg Subtype.val h), w, hw₂, hw₃⟩)
      ((SimpleGraph.lineGraph_adj_iff_exists).mpr
        ⟨fun h => h13 (congrArg Subtype.val h).symm, w, hw₃, hw₁⟩)
    intro e he f hf
    have heEdge : e ∈ H.edgeSet := he.1.1
    have hfEdge : f ∈ H.edgeSet := hf.1.1
    exact congrArg Subtype.val (hs (x := ⟨e, heEdge⟩) (y := ⟨f, hfEdge⟩) (by
      refine ⟨?_, he.2⟩
      rw [hstar] at he
      rcases he.1 with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (by
          have : (⟨e, heEdge⟩ : H.edgeSet) = E₃ := Subtype.ext (by simpa using h)
          simpa using this))) (by
      refine ⟨?_, hf.2⟩
      rw [hstar] at hf
      rcases hf.1 with h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (by
          have : (⟨f, hfEdge⟩ : H.edgeSet) = E₃ := Subtype.ext (by simpa using h)
          simpa using this))))

end Workspace.ProofLemmas.Thm92LineGraph
