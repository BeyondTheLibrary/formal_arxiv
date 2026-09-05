import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim1Helpers
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.HPrimeTracks

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenEndgameHelpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary
open Workspace.ProofLemmas.BranchClassification

theorem bool_eq_of_ne_ne (a b c : Bool) (hab : a ≠ b) (hac : a ≠ c) : b = c := by
  cases a <;> cases b <;> cases c <;> simp_all

/-- A major vertex witnesses overshadowing as soon as an odd long branch is present. -/
theorem overshadowed_of_major_branch {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} {K : Set V} (φ : H.lineGraph ≃g G.induce K)
    {B : List W} {a b : W} (hB : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    (hodd : Odd (trackLength B)) (hlong : 3 ≤ trackLength B)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H)
    {y : V} (hy : MajorForLineGraph G H K φ y) :
    IsOvershadowedAppearance G H K φ := by
  exact ⟨B, a, b, hB, hfrom, hodd, hlong, y, hy.2 a ha, hy.2 b hb⟩

/-- An edge occurring on a track forces that track to have positive length. -/
theorem one_le_trackLength_of_mem {W : Type*} {B : List W} {e : Sym2 W}
    (he : e ∈ trackEdges B) : 1 ≤ trackLength B := by
  obtain ⟨i, hi, -⟩ := he
  simp only [trackLength]
  omega

/-- The named ends of a nontrivial track are distinct. -/
theorem track_ends_ne {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W}
    (hB : IsTrackFrom H B a b) (hlen : 1 ≤ trackLength B) : a ≠ b := by
  have hlen' : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
  intro hab
  have h0 : B[0]'(by omega) = a := head_getElem hB.2.1 (by omega)
  have hl : B[B.length - 1]'(by omega) = b := last_getElem hB.2.2 (by omega)
  have hi : (0 : ℕ) = B.length - 1 :=
    hB.1.2.1.getElem_inj_iff.mp (by rw [h0, hl, hab])
  omega

/-- A meeting of two finite edges has a witnessing common end. -/
theorem exists_common_end {W : Type*} {e f : Sym2 W} (h : MeetEdges e f) :
    ∃ w : W, w ∈ e ∧ w ∈ f := by
  simpa only [MeetEdges, DisjointEdges, not_forall, not_not] using h

/-- If an edge `e` misses `v`, at most one edge at `v` can meet `e` in a bipartite graph. -/
theorem meeting_edges_at_vertex_subsingleton {W : Type*} {H : SimpleGraph W}
    (hbip : H.IsBipartite) {v : W} {e : Sym2 W} (heE : e ∈ H.edgeSet) (hve : v ∉ e) :
    ({f : Sym2 W | f ∈ incidentEdges H v ∧ MeetEdges f e}).Subsingleton := by
  intro f hf g hg
  by_contra hfg
  have hfe : f ≠ e := by
    rintro rfl
    exact hve hf.1.2
  have hge : g ≠ e := by
    rintro rfl
    exact hve hg.1.2
  have hmef : ∃ w, w ∈ e ∧ w ∈ f := by
    obtain ⟨w, hwf, hwe⟩ := exists_common_end hf.2
    exact ⟨w, hwe, hwf⟩
  have hmeg : ∃ w, w ∈ e ∧ w ∈ g := by
    obtain ⟨w, hwg, hwe⟩ := exists_common_end hg.2
    exact ⟨w, hwe, hwg⟩
  obtain ⟨w, hwe, hwf, hwg⟩ := exists_common_of_three hbip heE hf.1.1 hg.1.1
    hfe.symm hge.symm hfg hmef hmeg
    ⟨v, hf.1.2, hg.1.2⟩
  have hvw : v = w := subsingleton_inter_of_ne hfg hf.1.2 hg.1.2 hwf hwg
  exact hve (hvw ▸ hwe)

/-- Every branch-vertex in the minimal setup has an incident `Y`-complete edge. -/
theorem exists_complete_incident
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (v : Fin n) (hv : v ∈ branchVertices H) :
    ∃ e : Sym2 (Fin n), e ∈ incidentEdges H v ∧ e ∈ completeEdges G H K φ Y := by
  classical
  by_cases htri : (incidentEdges H v ∩ completeEdges G H K φ Y).Subsingleton
  · obtain ⟨-, hX, -, -⟩ :=
      triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy v ⟨hv, htri⟩
    obtain ⟨e, he, -⟩ := hX
    exact ⟨e, he.1, he.2⟩
  · rw [Set.not_subsingleton_iff] at htri
    obtain ⟨e, he, -, -, -⟩ := htri
    exact ⟨e, he.1, he.2⟩

/-- Two distinct complete edges at a branch-vertex allow one avoiding a fixed edge which does
not contain that branch-vertex. -/
theorem exists_complete_not_meeting_of_nontrivial
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (hbip : H.IsBipartite)
    {v : W} {e : Sym2 W} (heE : e ∈ H.edgeSet) (hve : v ∉ e)
    (hnt : ¬ (incidentEdges H v ∩ completeEdges G H K φ Y).Subsingleton) :
    ∃ f ∈ completeEdges G H K φ Y, v ∈ f ∧ ¬ MeetEdges f e := by
  classical
  rw [Set.not_subsingleton_iff] at hnt
  obtain ⟨f, hf, g, hg, hfg⟩ := hnt
  by_cases hfm : MeetEdges f e
  · have hgm : ¬ MeetEdges g e := by
      intro hgm
      exact hfg (meeting_edges_at_vertex_subsingleton hbip heE hve
        ⟨hf.1, hfm⟩ ⟨hg.1, hgm⟩)
    exact ⟨g, hg.2, hg.1.2, hgm⟩
  · exact ⟨f, hf.2, hf.1.2, hfm⟩

/-- An edge outside a branch cannot meet it at an internal vertex: that would make the
internal vertex have degree at least three. -/
theorem external_edge_meets_branch_only_at_ends
    {W : Type*} [Finite W] {H : SimpleGraph W} {B : List W} {a b w : W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    {e f : Sym2 W} (heB : e ∈ trackEdges B) (hfE : f ∈ H.edgeSet)
    (hfout : f ∉ trackEdges B) (hwf : w ∈ f) (hwe : w ∈ e) : w = a ∨ w = b := by
  have hwB : w ∈ B := by
    obtain ⟨i, hi, hie⟩ := heB
    rw [hie] at hwe
    rcases Sym2.mem_iff.mp hwe with h | h
    · rw [h]
      exact List.getElem_mem _
    · rw [h]
      exact List.getElem_mem _
  by_contra hends
  simp only [not_or] at hends
  have hwint : w ∈ trackInterior B := by
    by_contra hnint
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
        hfrom.2.1 hfrom.2.2 hwB hnint with h | h
    · exact hends.1 h
    · exact hends.2 h
  apply hbranch.2.1 w hwint
  obtain ⟨j, hj, hjw⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff B w).mp hwint
  let d₁ : Sym2 W := s(B[j]'(by omega), B[j + 1]'(by omega))
  let d₂ : Sym2 W := s(B[j + 1]'(by omega), B[j + 2]'(by omega))
  have hd₁B : d₁ ∈ trackEdges B := ⟨j, by omega, rfl⟩
  have hd₂B : d₂ ∈ trackEdges B := ⟨j + 1, by omega, rfl⟩
  have hd₁E : d₁ ∈ H.edgeSet := hfrom.1.2.2 j (by omega)
  have hd₂E : d₂ ∈ H.edgeSet := hfrom.1.2.2 (j + 1) (by omega)
  have hwd₁ : w ∈ d₁ := by
    change w ∈ s(B[j]'(by omega), B[j + 1]'(by omega))
    rw [← hjw]
    simp
  have hwd₂ : w ∈ d₂ := by
    change w ∈ s(B[j + 1]'(by omega), B[j + 2]'(by omega))
    rw [← hjw]
    simp
  have hd₁d₂ : d₁ ≠ d₂ := by
    intro h
    dsimp [d₁, d₂] at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h, -⟩ | ⟨h, -⟩
    · have := hfrom.1.2.1.getElem_inj_iff.mp h
      omega
    · have := hfrom.1.2.1.getElem_inj_iff.mp h
      omega
  have hd₁f : d₁ ≠ f := fun h => hfout (h ▸ hd₁B)
  have hd₂f : d₂ ≠ f := fun h => hfout (h ▸ hd₂B)
  have hsub : ({d₁, d₂, f} : Set (Sym2 W)) ⊆ incidentEdges H w := by
    intro d hd
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
    rcases hd with rfl | rfl | rfl
    · exact ⟨hd₁E, hwd₁⟩
    · exact ⟨hd₂E, hwd₂⟩
    · exact ⟨hfE, hwf⟩
  have hcard : ({d₁, d₂, f} : Set (Sym2 W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨d₁, d₂, f, hd₁d₂, hd₁f, hd₂f, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, incidentEdges_ncard] at hle
  exact hle

/-- A convenient vertex version of `external_edge_meets_branch_only_at_ends`: every
intersection of an external edge with a nontrivial branch is one of the named ends. -/
theorem external_edge_inter_branch_only_at_ends
    {W : Type*} [Finite W] {H : SimpleGraph W} {B : List W} {a b w : W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    (hpos : 1 ≤ trackLength B) {f : Sym2 W} (hfE : f ∈ H.edgeSet)
    (hfout : f ∉ trackEdges B) (hwB : w ∈ B) (hwf : w ∈ f) :
    w = a ∨ w = b := by
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  obtain ⟨i, hi, hiw⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_edge_of_mem hB2 hwB
  let e : Sym2 W := s(B[i]'(by omega), B[i + 1]'hi)
  have heB : e ∈ trackEdges B := ⟨i, hi, rfl⟩
  have hwe : w ∈ e := by
    dsimp [e]
    rcases hiw with h | h
    · rw [h]; simp
    · rw [h]; simp
  exact external_edge_meets_branch_only_at_ends hbranch hfrom heB hfE hfout hwf hwe

/-- The two-vertex list associated with an edge at `a`, with the edge itself remembered. -/
theorem edge_track_from_incident {W : Type*} {H : SimpleGraph W} {a : W}
    {e : Sym2 W} (he : e ∈ incidentEdges H a) :
    ∃ z : W, IsTrackFrom H [a, z] a z ∧ e = s(a, z) := by
  obtain ⟨z, heq⟩ := Sym2.mem_iff_exists.mp he.2
  refine ⟨z, Workspace.ProofLemmas.HPrimeTracks.isTrackFrom_pair ?_, heq⟩
  apply H.mem_edgeSet.mp
  rw [← heq]
  exact he.1

/-- The endpoint, length, and distinctness facts used throughout the endgame. -/
theorem branchChoice_basic
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n))
    (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃) :
    1 ≤ trackLength B₁ ∧ 1 ≤ trackLength B₂ ∧ 1 ≤ trackLength B₃ ∧
    b ∈ branchVertices H ∧ b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
    b₃ ∈ branchVertices H ∧ b ≠ b₁ ∧ b ≠ b₂ ∧ b ≠ b₃ ∧
    b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ := by
  classical
  rcases hbc with ⟨hb, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have hlen₁ := one_le_trackLength_of_mem he₁B₁
  have hlen₂ := one_le_trackLength_of_mem he₂B₂
  have hlen₃ := one_le_trackLength_of_mem he₃B₃
  have hlist₁ : 2 ≤ B₁.length := by simp only [trackLength] at hlen₁; omega
  have hlist₂ : 2 ≤ B₂.length := by simp only [trackLength] at hlen₂; omega
  have hlist₃ : 2 ≤ B₃.length := by simp only [trackLength] at hlen₃; omega
  have hends₁ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₁ b b₁ hB₁ hfrom₁ hlen₁
  have hends₂ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₂ b b₂ hB₂ hfrom₂ hlen₂
  have hends₃ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ hlen₃
  have hbb₁ := track_ends_ne hfrom₁ hlen₁
  have hbb₂ := track_ends_ne hfrom₂ hlen₂
  have hbb₃ := track_ends_ne hfrom₃ hlen₃
  obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
  have hdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have far_ne : ∀ (B B' : List (Fin n)) (c c' : Fin n) (e e' : Sym2 (Fin n)),
      IsBranch H B → IsTrackFrom H B b c → 2 ≤ B.length → c ∈ branchVertices H →
      IsBranch H B' → IsTrackFrom H B' b c' → 2 ≤ B'.length →
      e ∈ trackEdges B → e ∈ incidentEdges H b →
      e' ∈ trackEdges B' → e' ∈ incidentEdges H b → e ≠ e' → c ≠ c' := by
    intro B B' c c' e e' hBr hFr hL hc hBr' hFr' hL' heB heI heB' heI' hee' hcc'
    have hEq : trackEdges B = trackEdges B' :=
      trackEdges_eq_of_same_ends hι htrack hTlen hrev hdisj hnew hcover hedges hdeg
        hBr hL hFr hBr' hL' hFr' hb hc (Or.inl ⟨rfl, hcc'.symm⟩)
    have heB'' : e ∈ trackEdges B' := hEq ▸ heB
    have heFirst := trackEdge_at_head hFr' hL' heB'' heI.2
    have heFirst' := trackEdge_at_head hFr' hL' heB' heI'.2
    exact hee' (heFirst.trans heFirst'.symm)
  obtain ⟨-, -, -, -, -, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁e₂ : e₁ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ he₁X₁) (h ▸ he₂X₂)
  have hb₁b₂ := far_ne B₁ B₂ b₁ b₂ e₁ e₂ hB₁ hfrom₁ hlist₁ hends₁.2
    hB₂ hfrom₂ hlist₂ he₁B₁ he₁inc he₂B₂ he₂inc he₁e₂
  have hb₁b₃ := far_ne B₁ B₃ b₁ b₃ e₁ e₃ hB₁ hfrom₁ hlist₁ hends₁.2
    hB₃ hfrom₃ hlist₃ he₁B₁ he₁inc he₃B₃ he₃inc he₃e₁.symm
  have hb₂b₃ := far_ne B₂ B₃ b₂ b₃ e₂ e₃ hB₂ hfrom₂ hlist₂ hends₂.2
    hB₃ hfrom₃ hlist₃ he₂B₂ he₂inc he₃B₃ he₃inc he₃e₂.symm
  exact ⟨hlen₁, hlen₂, hlen₃, hb, hends₁.2, hends₂.2, hends₃.2,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩

/-- A branch edge avoids every branch-vertex other than the two ends of the branch. -/
theorem branch_edge_avoids_other_branchVertex
    {W : Type*} {H : SimpleGraph W} {B : List W} {a b c : W} {e : Sym2 W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B a b) (heB : e ∈ trackEdges B)
    (hc : c ∈ branchVertices H) (hca : c ≠ a) (hcb : c ≠ b) : c ∉ e := by
  intro hce
  have hcB : c ∈ B := by
    obtain ⟨i, hi, hie⟩ := heB
    rw [hie] at hce
    rcases Sym2.mem_iff.mp hce with h | h
    · rw [h]
      exact List.getElem_mem _
    · rw [h]
      exact List.getElem_mem _
  have hcint : c ∉ trackInterior B := fun hint => hbranch.2.1 c hint hc
  rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      hfrom.2.1 hfrom.2.2 hcB hcint with h | h
  · exact hca h
  · exact hcb h

/-- Adjacent ends force a branch of a subdivision of a 3-connected graph to have one edge. -/
theorem branch_length_one_of_adj
    {U W : Type*} [Fintype U] [Fintype W] (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (hsub : IsSubdivision J H) {B : List W} {a b : W}
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    (hpos : 1 ≤ trackLength B) (hab : H.Adj a b) : trackLength B = 1 := by
  rcases Nat.eq_or_lt_of_le hpos with h | h
  · exact h.symm
  · exact False.elim
      ((Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub B a b hbranch hfrom h).2.2.2 hab)

/-- A one-edge track named from `a` to `b` has precisely the edge `ab`. -/
theorem trackEdges_eq_singleton_of_length_one
    {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W}
    (hfrom : IsTrackFrom H B a b) (hlen : trackLength B = 1) :
    trackEdges B = {s(a, b)} := by
  have hlen' : B.length = 2 := by simp only [trackLength] at hlen; omega
  exact trackEdges_of_len_two hfrom hlen'

/-- If the end-edges of a nontrivial track meet, the track has at most two edges. -/
theorem trackLength_le_two_of_end_edges_meet
    {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W} {e f : Sym2 W}
    (hfrom : IsTrackFrom H B a b) (hpos : 1 ≤ trackLength B)
    (he : e ∈ trackEdges B) (hea : a ∈ e)
    (hf : f ∈ trackEdges B) (hfb : b ∈ f) (hm : MeetEdges e f) :
    trackLength B ≤ 2 := by
  have hB2 : 2 ≤ B.length := by
    have h := hpos
    simp only [trackLength] at h
    omega
  have heq := trackEdge_at_head hfrom hB2 he hea
  have hfeq := trackEdge_at_last hfrom hB2 hf hfb
  obtain ⟨w, hwe, hwf⟩ := exists_common_end hm
  rw [heq] at hwe
  rw [hfeq] at hwf
  rcases Sym2.mem_iff.mp hwe with hw0 | hw1 <;>
    rcases Sym2.mem_iff.mp hwf with hwl | hwr
  · have hi := hfrom.1.2.1.getElem_inj_iff.mp (hw0.symm.trans hwl)
    simp only [trackLength]
    omega
  · have hi := hfrom.1.2.1.getElem_inj_iff.mp (hw0.symm.trans hwr)
    simp only [trackLength]
    omega
  · have hi := hfrom.1.2.1.getElem_inj_iff.mp (hw1.symm.trans hwl)
    simp only [trackLength]
    omega
  · have hi := hfrom.1.2.1.getElem_inj_iff.mp (hw1.symm.trans hwr)
    simp only [trackLength]
    omega

/-- Suppose that `d₁,d₂` are the two displayed edges at `v`, joining it respectively to
`b₁,b₂`, while `b-b₂-v` is a two-edge path.  If every further edge at `v` meets the first
edge `e₃` of a branch from `b` to `b₃`, then there is at most one such further edge.

This is the elementary bipartite/branch-theoretic content of the sentence in (12) saying
that all further edges at `v` are incident with `b₃`. -/
theorem other_incident_edges_subsingleton
    {W : Type*} [Finite W] {H : SimpleGraph W} (hbip : H.IsBipartite)
    {B : List W} {b b₂ b₃ v : W} {e₃ d₁ d₂ : Sym2 W}
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B b b₃)
    (hpos : 1 ≤ trackLength B) (he₃B : e₃ ∈ trackEdges B) (hbe₃ : b ∈ e₃)
    (hbb₂ : H.Adj b b₂) (hb₂v : H.Adj b₂ v)
    (hd₁v : d₁ ∈ incidentEdges H v) (hd₂v : d₂ ∈ incidentEdges H v)
    (hd₁d₂ : d₁ ≠ d₂) (hvb : v ≠ b)
    (hmeet : ∀ g ∈ incidentEdges H v, g ≠ d₁ → g ≠ d₂ → MeetEdges g e₃) :
    (incidentEdges H v \ ({d₁, d₂} : Set (Sym2 W))).Subsingleton := by
  classical
  have hvnot_e₃ : v ∉ e₃ := by
    intro hve₃
    have heq : e₃ = s(b, v) := eq_sym2_of_mem_mem hvb.symm hbe₃ hve₃
    have hbvadj : H.Adj b v := by
      apply H.mem_edgeSet.mp
      rw [← heq]
      obtain ⟨i, hi, hie⟩ := he₃B
      rw [hie]
      exact hfrom.1.2.2 i hi
    exact no_triangle_of_bipartite hbip hbb₂ hb₂v hbvadj
  have classify : ∀ g ∈ incidentEdges H v, g ≠ d₁ → g ≠ d₂ →
      g ∈ trackEdges B ∨ g = s(v, b₃) := by
    intro g hg hg₁ hg₂
    by_cases hgB : g ∈ trackEdges B
    · exact Or.inl hgB
    · right
      obtain ⟨w, hwg, hwe₃⟩ := exists_common_end (hmeet g hg hg₁ hg₂)
      rcases external_edge_meets_branch_only_at_ends hB hfrom he₃B hg.1 hgB hwg hwe₃ with
        hwb | hwb₃
      · have hgvb : g = s(v, b) := eq_sym2_of_mem_mem hvb hg.2 (hwb ▸ hwg)
        have hvbadj : H.Adj v b := by
          apply H.mem_edgeSet.mp
          rw [← hgvb]
          exact hg.1
        exact False.elim (no_triangle_of_bipartite hbip hb₂v.symm hbb₂.symm hvbadj)
      · exact eq_sym2_of_mem_mem
          (fun h => hvnot_e₃ (h.symm ▸ (hwb₃ ▸ hwe₃))) hg.2 (hwb₃ ▸ hwg)
  intro g hg h hh
  have hg₁ : g ≠ d₁ := by
    intro hgd
    exact hg.2 (by simp [hgd])
  have hg₂ : g ≠ d₂ := by
    intro hgd
    exact hg.2 (by simp [hgd])
  have hh₁ : h ≠ d₁ := by
    intro hhd
    exact hh.2 (by simp [hhd])
  have hh₂ : h ≠ d₂ := by
    intro hhd
    exact hh.2 (by simp [hhd])
  rcases classify g hg.1 hg₁ hg₂ with hgB | hgeq
  · rcases classify h hh.1 hh₁ hh₂ with hhB | hheq
    · have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
      have hvbranch : v ∈ branchVertices H := by
        have hsub : ({d₁, d₂, g} : Set (Sym2 W)) ⊆ incidentEdges H v := by
          intro e he
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
          rcases he with rfl | rfl | rfl
          · exact hd₁v
          · exact hd₂v
          · exact hg.1
        have hc : ({d₁, d₂, g} : Set (Sym2 W)).ncard = 3 :=
          Set.ncard_eq_three.mpr ⟨d₁, d₂, g, hd₁d₂, hg₁.symm, hg₂.symm, rfl⟩
        have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hc, incidentEdges_ncard] at hle
        exact hle
      have hvb₃ : v = b₃ := by
        have hv_in_B' : v ∈ B := by
          obtain ⟨i, hi, hie⟩ := hgB
          rw [hie] at hg
          rcases Sym2.mem_iff.mp hg.1.2 with hv | hv
          · rw [hv]
            exact List.getElem_mem _
          · rw [hv]
            exact List.getElem_mem _
        have hvnotint : v ∉ trackInterior B := fun hint => hB.2.1 v hint hvbranch
        rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
            hfrom.2.1 hfrom.2.2 hv_in_B' hvnotint with hvb' | hvb₃'
        · exact False.elim (hvb hvb')
        · exact hvb₃'
      have hlastg := trackEdge_at_last hfrom hB2 hgB (by rw [← hvb₃]; exact hg.1.2)
      have hlasth := trackEdge_at_last hfrom hB2 hhB (by rw [← hvb₃]; exact hh.1.2)
      exact hlastg.trans hlasth.symm
    · have hvb₃ : v = b₃ := by
        have hv_in_B : v ∈ B := by
          obtain ⟨i, hi, hie⟩ := hgB
          rw [hie] at hg
          rcases Sym2.mem_iff.mp hg.1.2 with hv | hv
          · rw [hv]; exact List.getElem_mem _
          · rw [hv]; exact List.getElem_mem _
        have hvbranch : v ∈ branchVertices H := by
          have hsub : ({d₁, d₂, g} : Set (Sym2 W)) ⊆ incidentEdges H v := by
            intro e he
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
            rcases he with rfl | rfl | rfl
            · exact hd₁v
            · exact hd₂v
            · exact hg.1
          have hc : ({d₁, d₂, g} : Set (Sym2 W)).ncard = 3 :=
            Set.ncard_eq_three.mpr ⟨d₁, d₂, g, hd₁d₂, hg₁.symm, hg₂.symm, rfl⟩
          have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [hc, incidentEdges_ncard] at hle
          exact hle
        have hvnotint : v ∉ trackInterior B := fun hint => hB.2.1 v hint hvbranch
        rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
            hfrom.2.1 hfrom.2.2 hv_in_B hvnotint with hvb' | hvb₃'
        · exact False.elim (hvb hvb')
        · exact hvb₃'
      have : s(v, b₃) ∉ H.edgeSet := by
        rw [hvb₃]
        simpa using H.loopless.irrefl b₃
      exact False.elim (this (hheq ▸ hh.1.1))
  · rcases classify h hh.1 hh₁ hh₂ with hhB | hheq
    · exact (by
        have : h = g := by
          -- Apply the preceding branch/external case with the two edges interchanged.
          have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
          have hvbranch : v ∈ branchVertices H := by
            have hsub : ({d₁, d₂, h} : Set (Sym2 W)) ⊆ incidentEdges H v := by
              intro e he
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
              rcases he with rfl | rfl | rfl
              · exact hd₁v
              · exact hd₂v
              · exact hh.1
            have hc : ({d₁, d₂, h} : Set (Sym2 W)).ncard = 3 :=
              Set.ncard_eq_three.mpr ⟨d₁, d₂, h, hd₁d₂, hh₁.symm, hh₂.symm, rfl⟩
            have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
            rw [hc, incidentEdges_ncard] at hle
            exact hle
          have hv_in_B : v ∈ B := by
            obtain ⟨i, hi, hie⟩ := hhB
            rw [hie] at hh
            rcases Sym2.mem_iff.mp hh.1.2 with hv | hv
            · rw [hv]; exact List.getElem_mem _
            · rw [hv]; exact List.getElem_mem _
          have hvnotint : v ∉ trackInterior B := fun hint => hB.2.1 v hint hvbranch
          have hvb₃ : v = b₃ := by
            rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
                hfrom.2.1 hfrom.2.2 hv_in_B hvnotint with hvb' | hvb₃'
            · exact False.elim (hvb hvb')
            · exact hvb₃'
          have : s(v, b₃) ∉ H.edgeSet := by
            rw [hvb₃]
            simpa using H.loopless.irrefl b₃
          exact False.elim (this (hgeq ▸ hg.1.1))
        exact this.symm)
    · exact hgeq.trans hheq.symm
/-- The basic branch-identification move used in (11): an edge at the far end of one branch
which meets the first edge of another branch must join the two far ends, and the latter branch
has length one. -/
theorem identify_cross_meeting
    {U W : Type*} [Fintype U] [Fintype W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H)
    {B D : List W} {a z c : W} {e d f : Sym2 W}
    (hB : IsBranch H B) (hBfrom : IsTrackFrom H B a z)
    (hD : IsBranch H D) (hDfrom : IsTrackFrom H D a c)
    (hBpos : 1 ≤ trackLength B) (hDpos : 1 ≤ trackLength D)
    (hc : c ∈ branchVertices H) (hca : c ≠ a) (hcz : c ≠ z)
    (heB : e ∈ trackEdges B) (hea : a ∈ e)
    (hdD : d ∈ trackEdges D) (hda : a ∈ d)
    (hfE : f ∈ H.edgeSet) (hfc : c ∈ f) (hfd : f ≠ d)
    (hmeet : MeetEdges f e) :
    trackLength B = 1 ∧ e = s(a, z) ∧ f = s(c, z) := by
  have hfout : f ∉ trackEdges B := by
    intro hfB
    exact branch_edge_avoids_other_branchVertex hB hBfrom hfB hc hca hcz hfc
  obtain ⟨w, hwf, hwe⟩ := exists_common_end hmeet
  rcases external_edge_meets_branch_only_at_ends hB hBfrom heB hfE hfout hwf hwe with
    hwa | hwz
  · have hfac : f = s(c, a) := eq_sym2_of_mem_mem hca hfc (hwa ▸ hwf)
    have hac : H.Adj a c := by
      apply (SimpleGraph.mem_edgeSet H).mp
      rw [hfac] at hfE
      rw [Sym2.eq_swap]
      exact hfE
    have hDlen : trackLength D = 1 :=
      branch_length_one_of_adj J hJ H hsub hD hDfrom hDpos hac
    have hDE := trackEdges_eq_singleton_of_length_one hDfrom hDlen
    have hdeq : d = s(a, c) := by
      rw [hDE] at hdD
      exact Set.mem_singleton_iff.mp hdD
    exfalso
    apply hfd
    rw [hfac, hdeq, Sym2.eq_swap]
  · have heq : e = s(a, z) := eq_sym2_of_mem_mem
        (track_ends_ne hBfrom hBpos) hea (hwz ▸ hwe)
    have haz : H.Adj a z := by
      apply (SimpleGraph.mem_edgeSet H).mp
      rw [← heq]
      obtain ⟨i, hi, hie⟩ := heB
      rw [hie]
      exact hBfrom.1.2.2 i hi
    have hBlen : trackLength B = 1 :=
      branch_length_one_of_adj J hJ H hsub hB hBfrom hBpos haz
    have hfeq : f = s(c, z) := eq_sym2_of_mem_mem hcz hfc (hwz ▸ hwf)
    exact ⟨hBlen, heq, hfeq⟩

/-- If the first half of (11) failed, the unique complete edge at `b₁` would be `b₁b₃`,
`B₃` would have length one, and `B₁` would have length at least two.  This is the first
paragraph of the printed proof of (11), before it invokes maximality. -/
theorem claim11_failure_shape
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n))
    (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hfail : ∀ f : Sym2 (Fin n), f ∈ completeEdges G H K φ Y → b₁ ∈ f →
      MeetEdges f e₃) :
    ∃ f : Sym2 (Fin n),
      f ∈ completeEdges G H K φ Y ∧ f ∈ incidentEdges H b₁ ∧
      f = s(b₁, b₃) ∧ Triad G H K φ Y b₁ ∧
      trackLength B₃ = 1 ∧ e₃ = s(b, b₃) ∧ 2 ≤ trackLength B₁ := by
  classical
  rcases hbc with ⟨hb, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbasic := branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
    ⟨hb, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  rcases hbasic with ⟨hlen₁, hlen₂, hlen₃, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩
  have hb₁e₃ : b₁ ∉ e₃ :=
    branch_edge_avoids_other_branchVertex hB₃ hfrom₃ he₃B₃ hb₁V hbb₁.symm hb₁b₃
  have hsubsingle : (incidentEdges H b₁ ∩ completeEdges G H K φ Y).Subsingleton := by
    intro f hf g hg
    exact meeting_edges_at_vertex_subsingleton hsub.2 he₃inc.1 hb₁e₃
      ⟨hf.1, hfail f hf.2 hf.1.2⟩ ⟨hg.1, hfail g hg.2 hg.1.2⟩
  have htri : Triad G H K φ Y b₁ := ⟨hb₁V, hsubsingle⟩
  obtain ⟨f, hfinc, hfX⟩ :=
    exists_complete_incident G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ hb₁V
  obtain ⟨hXE, -, -, hXX₁, -, -, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hfe₁ : f ≠ e₁ := by
    intro h
    exact (Set.disjoint_left.mp hXX₁ hfX) (h ▸ he₁X₁)
  have hshape := identify_cross_meeting J hJ H hsub.1 hB₃ hfrom₃ hB₁ hfrom₁
    hlen₃ hlen₁ hb₁V hbb₁.symm hb₁b₃ he₃B₃ he₃inc.2 he₁B₁
    he₁inc.2 hfX.1 hfinc.2 hfe₁ (hfail f hfX hfinc.2)
  rcases hshape with ⟨hlen₃one, he₃eq, hfeq⟩
  have hlen₁long : 2 ≤ trackLength B₁ := by
    rcases Nat.eq_or_lt_of_le hlen₁ with hone | hlong
    · have hB₁E := trackEdges_eq_singleton_of_length_one hfrom₁ hone.symm
      have he₁eq : e₁ = s(b, b₁) := by
        rw [hB₁E] at he₁B₁
        exact Set.mem_singleton_iff.mp he₁B₁
      have h01 : H.Adj b b₁ := by
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [← he₁eq]
        exact he₁inc.1
      have h13 : H.Adj b₁ b₃ := by
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [← hfeq]
        exact hfX.1
      have h03 : H.Adj b b₃ := by
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [← he₃eq]
        exact he₃inc.1
      exact False.elim (no_triangle_of_bipartite hsub.2 h01 h13 h03)
    · exact hlong
  exact ⟨f, hfX, hfinc, hfeq, htri, hlen₃one, he₃eq, hlen₁long⟩

/-- At the centre of a branch choice, every incident edge other than the distinguished
`X₁`- and `X₂`-edges is in `X`. -/
theorem other_incident_is_complete
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V)
    {b : W} {e₁ e₂ e : Sym2 W}
    (hb : b ∈ branchVertices H)
    (he₁inc : e₁ ∈ incidentEdges H b) (he₁X₁ : e₁ ∈ extraEdges G H K φ Y y₁)
    (he₂inc : e₂ ∈ incidentEdges H b) (he₂X₂ : e₂ ∈ extraEdges G H K φ Y y₂)
    (heinc : e ∈ incidentEdges H b) (hene₁ : e ≠ e₁) (hene₂ : e ≠ e₂)
    (hXX₁ : Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₁))
    (hXX₂ : Disjoint (completeEdges G H K φ Y) (extraEdges G H K φ Y y₂))
    (hX₁X₂ : Disjoint (extraEdges G H K φ Y y₁) (extraEdges G H K φ Y y₂))
    (hsat₁ : SaturatesLineGraph H
      (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁))
    (hsat₂ : SaturatesLineGraph H
      (completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂)) :
    e ∈ completeEdges G H K φ Y := by
  have he₂out : e₂ ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    simp only [Set.mem_union, not_or]
    exact ⟨Set.disjoint_right.mp hXX₂ he₂X₂,
      Set.disjoint_right.mp hX₁X₂ he₂X₂⟩
  have he₁out : e₁ ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
    simp only [Set.mem_union, not_or]
    exact ⟨Set.disjoint_right.mp hXX₁ he₁X₁,
      Set.disjoint_left.mp hX₁X₂ he₁X₁⟩
  have heU₁ : e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    by_contra heout
    exact hene₂ (hsat₁ b hb ⟨heinc, heout⟩ ⟨he₂inc, he₂out⟩)
  have heU₂ : e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
    by_contra heout
    exact hene₁ (hsat₂ b hb ⟨heinc, heout⟩ ⟨he₁inc, he₁out⟩)
  rcases heU₁ with heX | heX₁
  · exact heX
  rcases heU₂ with heX | heX₂
  · exact heX
  exact False.elim ((Set.disjoint_left.mp hX₁X₂ heX₁) heX₂)

/-- Subdivision preserves the degree of an old vertex in the direction needed by the §6.1
endgame: distinct neighbours in the original graph yield distinct first neighbours on the
subdividing tracks. -/
theorem original_degree_le_subdivision_degree
    {U W : Type*} [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hdisj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (u : U) : (J.neighborSet u).ncard ≤ (H.neighborSet (ι u)).ncard := by
  classical
  have hlen2 : ∀ v : U, J.Adj u v → 2 ≤ (T u v).length := by
    intro v hv
    have h := hlen u v hv
    simp only [trackLength] at h
    omega
  let F : U → W := fun v => (T u v).getD 1 (ι u)
  have hmaps : ∀ v ∈ J.neighborSet u, F v ∈ H.neighborSet (ι u) := by
    intro v hv
    have hv' : J.Adj u v := hv
    have hadj := (htrack u v hv').1.2.2 0 (by have := hlen2 v hv'; omega)
    rw [Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v hv') (by
      have := hlen2 v hv'; omega)] at hadj
    change H.Adj (ι u) (F v)
    dsimp [F]
    rw [List.getD_eq_getElem _ _ (by have := hlen2 v hv'; omega)]
    exact hadj
  have hinj : Set.InjOn F (J.neighborSet u) := by
    intro v₁ hv₁ v₂ hv₂ heq
    have hv₁' : J.Adj u v₁ := hv₁
    have hv₂' : J.Adj u v₂ := hv₂
    by_contra hne
    have hs : s(u, v₁) ≠ s(u, v₂) := by
      intro h
      rcases Sym2.eq_iff.mp h with ⟨-, h⟩ | ⟨-, h⟩
      · exact hne h
      · exact absurd hv₁' (by rw [h]; exact J.loopless.irrefl u)
    have hget₁ : F v₁ = (T u v₁)[1]'(by have := hlen2 v₁ hv₁'; omega) := by
      dsimp [F]
      exact List.getD_eq_getElem _ _ (by have := hlen2 v₁ hv₁'; omega)
    have hget₂ : F v₂ = (T u v₂)[1]'(by have := hlen2 v₂ hv₂'; omega) := by
      dsimp [F]
      exact List.getD_eq_getElem _ _ (by have := hlen2 v₂ hv₂'; omega)
    have heq' : (T u v₁)[1]'(by have := hlen2 v₁ hv₁'; omega) =
        (T u v₂)[1]'(by have := hlen2 v₂ hv₂'; omega) := by
      rw [← hget₁, ← hget₂]
      exact heq
    by_cases hl₁ : 3 ≤ (T u v₁).length
    · have hm : (T u v₁)[1]'(by omega) ∈ trackInterior (T u v₁) :=
        Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem _ 0 (by omega)
      exact hdisj u v₁ u v₂ hv₁' hv₂' hs _ hm
        (by rw [heq']; exact List.getElem_mem _)
    · have hl₁' : (T u v₁).length = 2 := by have := hlen2 v₁ hv₁'; omega
      have hx₁ : (T u v₁)[1]'(by omega) = ι v₁ :=
        Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v₁ hv₁') hl₁'
      by_cases hl₂ : 3 ≤ (T u v₂).length
      · have hm : (T u v₂)[1]'(by omega) ∈ trackInterior (T u v₂) :=
          Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem _ 0 (by omega)
        exact hnew u v₂ hv₂' _ hm ⟨v₁, by rw [← heq', hx₁]⟩
      · have hl₂' : (T u v₂).length = 2 := by have := hlen2 v₂ hv₂'; omega
        have hx₂ : (T u v₂)[1]'(by omega) = ι v₂ :=
          Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v₂ hv₂') hl₂'
        exact hne (hι (by rw [← hx₁, ← hx₂]; exact heq'))
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.toFinite _)

/-- Two old vertices which are adjacent in a subdivision were adjacent before subdivision. -/
theorem original_adj_of_subdivision_adj
    {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    {p q : U} (hadj : H.Adj (ι p) (ι q)) : J.Adj p q := by
  have hmem : s(ι p, ι q) ∈ H.edgeSet := hadj
  rw [hedges] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨u, v, huv, i, hi, heq⟩ := hmem
  have hrng : (T u v)[i]'(by omega) ∈ Set.range ι ∧
      (T u v)[i + 1]'hi ∈ Set.range ι := by
    rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨⟨p, h₁⟩, ⟨q, h₂⟩⟩
    · exact ⟨⟨q, h₂⟩, ⟨p, h₁⟩⟩
  have hlen2 : (T u v).length = 2 :=
    Workspace.ProofLemmas.SubdivisionCounting.track_edge_len_two (T u v) i hi
      (fun hc => hnew u v huv _ hc hrng.1) (fun hc => hnew u v huv _ hc hrng.2)
  have hieq : i = 0 := by omega
  have hA : (T u v)[i]'(by omega) = ι u :=
    (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (T u v) hieq (by omega) (by omega)).trans
      (Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v huv) (by omega))
  have hB : (T u v)[i + 1]'hi = ι v :=
    (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (T u v) (show i + 1 = 1 by omega) hi (by omega)).trans
      (Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v huv) hlen2)
  have heq2 : s(ι p, ι q) = s(ι u, ι v) := by rw [heq, hA, hB]
  rcases Sym2.eq_iff.mp heq2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · rw [hι h₁, hι h₂]
    exact huv
  · rw [hι h₁, hι h₂]
    exact huv.symm

/-- The old vertices corresponding to the two ends of a branch are adjacent in the graph
being subdivided. -/
theorem original_adj_of_branch_ends
    {U W : Type*} [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard)
    {B : List W} {a b : W} {p q : U}
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    (hpos : 1 ≤ trackLength B) (ha : a = ι p) (hb : b = ι q) : J.Adj p q := by
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hι htrack hlen hdisj hnew hdeg
  have haV : a ∈ branchVertices H := by rw [ha]; exact hrange ⟨p, rfl⟩
  have hbV : b ∈ branchVertices H := by rw [hb]; exact hrange ⟨q, rfl⟩
  obtain ⟨u, v, huv, -, hends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlen hrev hdisj hnew hcover hedges hdeg hB
      (by simp only [trackLength] at hpos; omega) hfrom haV hbV
  rcases hends with ⟨hau, hbv⟩ | ⟨hav, hbu⟩
  · have hpu : p = u := hι (ha.symm.trans hau)
    have hqv : q = v := hι (hb.symm.trans hbv)
    rwa [hpu, hqv]
  · have hpv : p = v := hι (ha.symm.trans hav)
    have hqu : q = u := hι (hb.symm.trans hbu)
    rw [hpv, hqu]
    exact huv.symm

/-- A vertex of degree three with three named distinct neighbours has no other neighbour. -/
theorem neighbor_of_degree_three
    {U : Type*} [Finite U] {J : SimpleGraph U} {u a b c x : U}
    (hdeg : (J.neighborSet u).ncard = 3)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hua : J.Adj u a) (hub : J.Adj u b) (huc : J.Adj u c)
    (hux : J.Adj u x) : x = a ∨ x = b ∨ x = c := by
  by_contra h
  simp only [not_or] at h
  have hsub : ({a, b, c, x} : Set U) ⊆ J.neighborSet u := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl <;> assumption
  have hcard : ({a, b, c, x} : Set U).ncard = 4 := by
    apply Set.ncard_eq_four.mpr
    exact ⟨a, b, c, x, hab, hac, (fun hax => h.1 hax.symm), hbc,
      (fun hbx => h.2.1 hbx.symm), (fun hcx => h.2.2 hcx.symm), rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard, hdeg] at hle
  omega

/-- In a 3-connected graph, adjacent degree-three vertices with the same other two neighbours
exhaust the graph.  Deleting those two neighbours would otherwise separate their edge from an
additional vertex. -/
theorem four_vertices_of_two_degree_three
    {U : Type*} [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {u₀ u₁ u₂ u₃ : U}
    (h01 : J.Adj u₀ u₁) (h02 : J.Adj u₀ u₂) (h03 : J.Adj u₀ u₃)
    (h12 : J.Adj u₁ u₂) (h13 : J.Adj u₁ u₃)
    (h23ne : u₂ ≠ u₃)
    (hdeg0 : (J.neighborSet u₀).ncard = 3)
    (hdeg1 : (J.neighborSet u₁).ncard = 3) :
    ∀ x : U, x = u₀ ∨ x = u₁ ∨ x = u₂ ∨ x = u₃ := by
  classical
  have h01ne : u₀ ≠ u₁ := h01.ne
  have h02ne : u₀ ≠ u₂ := h02.ne
  have h03ne : u₀ ≠ u₃ := h03.ne
  have h12ne : u₁ ≠ u₂ := h12.ne
  have h13ne : u₁ ≠ u₃ := h13.ne
  have hN0 : ∀ {x : U}, J.Adj u₀ x → x = u₁ ∨ x = u₂ ∨ x = u₃ := by
    intro x hx
    exact neighbor_of_degree_three hdeg0 h12ne h13ne h23ne h01 h02 h03 hx
  have hN1 : ∀ {x : U}, J.Adj u₁ x → x = u₀ ∨ x = u₂ ∨ x = u₃ := by
    intro x hx
    exact neighbor_of_degree_three hdeg1 h02ne h03ne h23ne h01.symm h12 h13 hx
  intro x
  by_cases hx0 : x = u₀
  · exact Or.inl hx0
  by_cases hx1 : x = u₁
  · exact Or.inr (Or.inl hx1)
  by_cases hx2 : x = u₂
  · exact Or.inr (Or.inr (Or.inl hx2))
  by_cases hx3 : x = u₃
  · exact Or.inr (Or.inr (Or.inr hx3))
  let S : Set U := {u₂, u₃}
  have hScard : S.ncard < 3 := by
    dsimp [S]
    rw [Set.ncard_pair h23ne]
    omega
  have hconn := (hJ.2 S hScard).preconnected
  have hu0S : u₀ ∈ Sᶜ := by simp [S, h02ne, h03ne]
  have hxS : x ∈ Sᶜ := by simp [S, hx2, hx3]
  obtain ⟨w⟩ := hconn ⟨u₀, hu0S⟩ ⟨x, hxS⟩
  have stay : ∀ {a b : ↑Sᶜ}, (J.induce Sᶜ).Walk a b →
      ((a : U) = u₀ ∨ (a : U) = u₁) → ((b : U) = u₀ ∨ (b : U) = u₁) := by
    intro a b p
    induction p with
    | nil => exact fun h => h
    | @cons a b c hab p ih =>
        intro ha
        apply ih
        have habJ : J.Adj (a : U) (b : U) := hab
        rcases ha with ha | ha
        · rcases hN0 (ha ▸ habJ) with hb | hb | hb
          · exact Or.inr hb
          · exact False.elim (b.2 (by simp [S, hb]))
          · exact False.elim (b.2 (by simp [S, hb]))
        · rcases hN1 (ha ▸ habJ) with hb | hb | hb
          · exact Or.inl hb
          · exact False.elim (b.2 (by simp [S, hb]))
          · exact False.elim (b.2 (by simp [S, hb]))
  rcases stay w (Or.inl rfl) with hx | hx
  · exact False.elim (hx0 hx)
  · exact False.elim (hx1 hx)

/-- If two old vertices are adjacent already in the subdivision, their subdividing track has
one edge. -/
theorem subdivision_track_length_two_of_adj
    {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    {p q : U} (hadj : H.Adj (ι p) (ι q)) : (T p q).length = 2 := by
  have hmem : s(ι p, ι q) ∈ H.edgeSet := hadj
  rw [hedges] at hmem
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨u, v, huv, i, hi, heq⟩ := hmem
  have hrng : (T u v)[i]'(by omega) ∈ Set.range ι ∧
      (T u v)[i + 1]'hi ∈ Set.range ι := by
    rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact ⟨⟨p, h₁⟩, ⟨q, h₂⟩⟩
    · exact ⟨⟨q, h₂⟩, ⟨p, h₁⟩⟩
  have hlen2 : (T u v).length = 2 :=
    Workspace.ProofLemmas.SubdivisionCounting.track_edge_len_two (T u v) i hi
      (fun hc => hnew u v huv _ hc hrng.1) (fun hc => hnew u v huv _ hc hrng.2)
  have hieq : i = 0 := by omega
  have hA : (T u v)[i]'(by omega) = ι u :=
    (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (T u v) hieq (by omega) (by omega)).trans
      (Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v huv) (by omega))
  have hB : (T u v)[i + 1]'hi = ι v :=
    (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
      (T u v) (show i + 1 = 1 by omega) hi (by omega)).trans
      (Workspace.ProofLemmas.SubdivisionCounting.track_last (htrack u v huv) hlen2)
  have heq2 : s(ι p, ι q) = s(ι u, ι v) := by rw [heq, hA, hB]
  rcases Sym2.eq_iff.mp heq2 with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨rfl, rfl⟩ : p = u ∧ q = v := ⟨hι h₁, hι h₂⟩
    exact hlen2
  · obtain ⟨rfl, rfl⟩ : p = v ∧ q = u := ⟨hι h₁, hι h₂⟩
    rw [hrev q p huv, List.length_reverse]
    exact hlen2

/-- Every named subdividing track is a branch when the original graph has minimum degree
three. -/
theorem subdivision_track_isBranch
    {U W : Type*} [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hcover : ∀ w : W, (∃ u : U, w = ι u) ∨
      ∃ u v : U, J.Adj u v ∧ w ∈ trackInterior (T u v))
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard)
    {u v : U} (huv : J.Adj u v) : IsBranch H (T u v) := by
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hι htrack hlen hdisj hnew hdeg
  have hbrsub : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  exact Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
    (htrack u v huv) (fun h => huv.ne (hι h))
    (fun w hw hbranch => hnew u v huv w hw (hbrsub hbranch))
    (hrange ⟨u, rfl⟩) (hrange ⟨v, rfl⟩)

/-- Reversing a branch only changes its orientation. -/
theorem isBranch_reverse {W : Type*} {H : SimpleGraph W} {q : List W}
    (hq : IsBranch H q) : IsBranch H q.reverse := by
  refine ⟨Workspace.ProofLemmas.TrackSlice.isTrackList_reverse hq.1, ?_, ?_⟩
  · intro v hv
    exact hq.2.1 v (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mp hv)
  · intro q' hq' hq'int hsub hverts
    have hsub' : trackEdges q ⊆ trackEdges q' := by
      simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using hsub
    have hverts' : ∀ v ∈ q, v ∈ q' := by
      intro v hv
      exact hverts v (by simpa using hv)
    have heq := hq.2.2 q' hq' hq'int hsub' hverts'
    simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using heq

/-- A degree-two vertex between two branch vertices is the unique internal vertex of a branch. -/
theorem three_vertex_branch_of_degree_two
    {W : Type*} [Finite W] {H : SimpleGraph W} {a x b : W}
    (hax : H.Adj a x) (hxb : H.Adj x b)
    (haxne : a ≠ x) (hab : a ≠ b) (hxbne : x ≠ b)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H)
    (hdegx : (H.neighborSet x).ncard = 2) : IsBranch H [a, x, b] := by
  have htrack : IsTrackFrom H [a, x, b] a b := by
    refine ⟨⟨by simp, by simp [haxne, hab, hxbne], ?_⟩, rfl, rfl⟩
    intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    have hc : i = 0 ∨ i = 1 := by omega
    rcases hc with rfl | rfl
    · simpa using hax
    · simpa using hxb
  apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch htrack hab
  · intro w hw
    have hwx : w = x := by simpa [trackInterior] using hw
    rw [hwx]
    show ¬ 3 ≤ (H.neighborSet x).ncard
    omega
  · exact ha
  · exact hb

/-- Four explicitly listed vertices which exhaust a graph and are pairwise adjacent identify
that graph with `K₄`. -/
theorem iso_top_of_four_vertices
    {U : Type*} [Fintype U] {J : SimpleGraph U} {a b c d : U}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hall : ∀ x : U, x = a ∨ x = b ∨ x = c ∨ x = d)
    (hAB : J.Adj a b) (hAC : J.Adj a c) (hAD : J.Adj a d)
    (hBC : J.Adj b c) (hBD : J.Adj b d) (hCD : J.Adj c d) :
    Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := by
  let f : Fin 4 → U := fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c else d
  have hf0 : f 0 = a := by simp [f]
  have hf1 : f 1 = b := by norm_num [f]
  have hf2 : f 2 = c := by
    simp [f, show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
  have hf3 : f 3 = d := by
    simp [f, show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide,
      show (3 : Fin 4) ≠ 2 by decide]
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp only [hf0, hf1, hf2, hf3] at hij ⊢ <;> simp_all
  have hfsurj : Function.Surjective f := by
    intro x
    rcases hall x with rfl | rfl | rfl | rfl
    · exact ⟨0, hf0⟩
    · exact ⟨1, hf1⟩
    · exact ⟨2, hf2⟩
    · exact ⟨3, hf3⟩
  let e : Fin 4 ≃ U := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let ψ : (⊤ : SimpleGraph (Fin 4)) ≃g J :=
    { toEquiv := e
      map_rel_iff' := by
        intro i j
        change J.Adj (f i) (f j) ↔ i ≠ j
        fin_cases i <;> fin_cases j <;>
          simp only [hf0, hf1, hf2, hf3] <;>
          simp_all [J.adj_comm] }
  exact ⟨ψ.symm⟩

/-- Four degree-three vertices forming a cycle, whose third neighbours alternate between two
vertices, exhaust a 3-connected graph.  Deleting the two alternating neighbours leaves the
four-cycle as a closed connected component, so there can be no further vertex. -/
theorem six_vertices_of_alternating_degree_three_cycle
    {U : Type*} [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {a b c d p q : U}
    (hab : J.Adj a b) (hbc : J.Adj b c) (hcd : J.Adj c d) (hda : J.Adj d a)
    (hap : J.Adj a p) (hcp : J.Adj c p)
    (hbq : J.Adj b q) (hdq : J.Adj d q)
    (habne : a ≠ b) (hacne : a ≠ c) (hadne : a ≠ d)
    (hapne : a ≠ p) (haqne : a ≠ q)
    (hbcne : b ≠ c) (hbdne : b ≠ d) (hbpne : b ≠ p) (hbqne : b ≠ q)
    (hcdne : c ≠ d) (hcpne : c ≠ p) (hcqne : c ≠ q)
    (hdpne : d ≠ p) (hdqne : d ≠ q) (hpq : p ≠ q)
    (hdega : (J.neighborSet a).ncard = 3)
    (hdegb : (J.neighborSet b).ncard = 3)
    (hdegc : (J.neighborSet c).ncard = 3)
    (hdegd : (J.neighborSet d).ncard = 3) :
    ∀ x : U, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = p ∨ x = q := by
  classical
  have hNa : ∀ {x : U}, J.Adj a x → x = b ∨ x = d ∨ x = p := by
    intro x hx
    exact neighbor_of_degree_three hdega hbdne hbpne hdpne hab hda.symm hap hx
  have hNb : ∀ {x : U}, J.Adj b x → x = a ∨ x = c ∨ x = q := by
    intro x hx
    exact neighbor_of_degree_three hdegb hacne haqne hcqne hab.symm hbc hbq hx
  have hNc : ∀ {x : U}, J.Adj c x → x = b ∨ x = d ∨ x = p := by
    intro x hx
    exact neighbor_of_degree_three hdegc hbdne hbpne hdpne hbc.symm hcd hcp hx
  have hNd : ∀ {x : U}, J.Adj d x → x = a ∨ x = c ∨ x = q := by
    intro x hx
    exact neighbor_of_degree_three hdegd hacne haqne hcqne hda hcd.symm hdq hx
  intro x
  by_cases hxa : x = a
  · exact Or.inl hxa
  by_cases hxb : x = b
  · exact Or.inr (Or.inl hxb)
  by_cases hxc : x = c
  · exact Or.inr (Or.inr (Or.inl hxc))
  by_cases hxd : x = d
  · exact Or.inr (Or.inr (Or.inr (Or.inl hxd)))
  by_cases hxp : x = p
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hxp))))
  by_cases hxq : x = q
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hxq))))
  let S : Set U := {p, q}
  have hScard : S.ncard < 3 := by
    dsimp [S]
    rw [Set.ncard_pair hpq]
    omega
  have hconn := (hJ.2 S hScard).preconnected
  have haS : a ∈ Sᶜ := by simp [S, hapne, haqne]
  have hxS : x ∈ Sᶜ := by simp [S, hxp, hxq]
  obtain ⟨w⟩ := hconn ⟨a, haS⟩ ⟨x, hxS⟩
  have stay : ∀ {r s : ↑Sᶜ}, (J.induce Sᶜ).Walk r s →
      ((r : U) = a ∨ (r : U) = b ∨ (r : U) = c ∨ (r : U) = d) →
      ((s : U) = a ∨ (s : U) = b ∨ (s : U) = c ∨ (s : U) = d) := by
    intro r s w
    induction w with
    | nil => exact fun h => h
    | @cons r t s hrt w ih =>
        intro hr
        apply ih
        have hAdj : J.Adj (r : U) (t : U) := hrt
        rcases hr with hr | hr | hr | hr
        · rcases hNa (hr ▸ hAdj) with ht | ht | ht
          · exact Or.inr (Or.inl ht)
          · exact Or.inr (Or.inr (Or.inr ht))
          · exact False.elim (t.2 (by simp [S, ht]))
        · rcases hNb (hr ▸ hAdj) with ht | ht | ht
          · exact Or.inl ht
          · exact Or.inr (Or.inr (Or.inl ht))
          · exact False.elim (t.2 (by simp [S, ht]))
        · rcases hNc (hr ▸ hAdj) with ht | ht | ht
          · exact Or.inr (Or.inl ht)
          · exact Or.inr (Or.inr (Or.inr ht))
          · exact False.elim (t.2 (by simp [S, ht]))
        · rcases hNd (hr ▸ hAdj) with ht | ht | ht
          · exact Or.inl ht
          · exact Or.inr (Or.inr (Or.inl ht))
          · exact False.elim (t.2 (by simp [S, ht]))
  rcases stay w (Or.inl rfl) with hx | hx | hx | hx
  · exact False.elim (hxa hx)
  · exact False.elim (hxb hx)
  · exact False.elim (hxc hx)
  · exact False.elim (hxd hx)

/-- An exhaustive labelled bipartition with all and only the cross edges identifies a graph
with `K₃,₃`. -/
theorem iso_completeBipartite_three_three
    {U : Type*} [Fintype U] {J : SimpleGraph U}
    (a b : Fin 3 → U) (ha : Function.Injective a) (hb : Function.Injective b)
    (habne : ∀ i j, a i ≠ b j)
    (hall : ∀ x : U, (∃ i, x = a i) ∨ ∃ j, x = b j)
    (hcross : ∀ i j, J.Adj (a i) (b j))
    (hleft : ∀ i j, ¬ J.Adj (a i) (a j))
    (hright : ∀ i j, ¬ J.Adj (b i) (b j)) :
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  let f : Fin 3 ⊕ Fin 3 → U
    | Sum.inl i => a i
    | Sum.inr j => b j
  have hfinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j => exact congrArg Sum.inl (ha hxy)
        | inr j => exact False.elim (habne i j hxy)
    | inr i =>
        cases y with
        | inl j => exact False.elim (habne j i hxy.symm)
        | inr j => exact congrArg Sum.inr (hb hxy)
  have hfsurj : Function.Surjective f := by
    intro x
    rcases hall x with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact ⟨Sum.inl i, hi.symm⟩
    · exact ⟨Sum.inr j, hj.symm⟩
  let e : (Fin 3 ⊕ Fin 3) ≃ U := Equiv.ofBijective f ⟨hfinj, hfsurj⟩
  let ψ : completeBipartiteGraph (Fin 3) (Fin 3) ≃g J :=
    { toEquiv := e
      map_rel_iff' := by
        intro x y
        change J.Adj (f x) (f y) ↔ _
        cases x with
        | inl i =>
            cases y with
            | inl j => simp [f, completeBipartiteGraph_adj, hleft i j]
            | inr j => simp [f, completeBipartiteGraph_adj, hcross i j]
        | inr i =>
            cases y with
            | inl j => simp [f, completeBipartiteGraph_adj, (hcross j i).symm]
            | inr j => simp [f, completeBipartiteGraph_adj, hright i j] }
  exact ⟨ψ.symm⟩

/-- Two distinct branches issuing from the same branch-vertex meet only at that vertex. -/
theorem branches_from_common_end_meet_only
    {U W : Type*} [Fintype U] [Finite W]
    {J : SimpleGraph U} (hJ : IsKConnected J 3) {H : SimpleGraph W}
    (hsub : IsSubdivision J H)
    {B C : List W} {a b c : W}
    (hB : IsBranch H B) (hBfrom : IsTrackFrom H B a b)
    (hC : IsBranch H C) (hCfrom : IsTrackFrom H C a c)
    (hBpos : 1 ≤ trackLength B) (hCpos : 1 ≤ trackLength C)
    (ha : a ∈ branchVertices H) (hb : b ∈ branchVertices H)
    (hc : c ∈ branchVertices H) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∀ w ∈ B, w ∈ C → w = a := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hBpos; omega
  have hC2 : 2 ≤ C.length := by simp only [trackLength] at hCpos; omega
  obtain ⟨u, v, huv, hBE, hBends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlen hrev hdisj hnew hcover hedges hdeg hB hB2 hBfrom ha hb
  obtain ⟨x, y, hxy, hCE, hCends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlen hrev hdisj hnew hcover hedges hdeg hC hC2 hCfrom ha hc
  have hedge : s(u, v) ≠ s(x, y) := by
    intro heq
    have hpairB : s(a, b) = Sym2.map ι s(u, v) := by
      rcases hBends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [Sym2.map_pair_eq]
      · rw [Sym2.eq_swap]
        simp [Sym2.map_pair_eq]
    have hpairC : s(a, c) = Sym2.map ι s(x, y) := by
      rcases hCends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp [Sym2.map_pair_eq]
      · rw [Sym2.eq_swap]
        simp [Sym2.map_pair_eq]
    have hp : s(a, b) = s(a, c) := hpairB.trans ((congrArg (Sym2.map ι) heq).trans hpairC.symm)
    rcases Sym2.eq_iff.mp hp with ⟨-, h⟩ | ⟨h, -⟩
    · exact hbc h
    · exact hac h
  intro w hwB hwC
  have mem_track_of_mem_branch : ∀ {D : List W} {p q : U}, 2 ≤ D.length →
      trackEdges D = trackEdges (T p q) → w ∈ D → w ∈ T p q := by
    intro D p q hD2 hDE hw
    obtain ⟨i, hi, hiw⟩ :=
      Workspace.ProofLemmas.BranchClassification.exists_edge_of_mem hD2 hw
    have he : s(D[i]'(by omega), D[i + 1]'hi) ∈ trackEdges (T p q) := by
      rw [← hDE]
      exact ⟨i, hi, rfl⟩
    have hm := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges he
    rcases hiw with h | h
    · exact h ▸ hm.1
    · exact h ▸ hm.2
  have hwT : w ∈ T u v := mem_track_of_mem_branch hB2 hBE hwB
  have hwS : w ∈ T x y := mem_track_of_mem_branch hC2 hCE hwC
  have hnint : w ∉ trackInterior (T u v) := fun hi => hdisj u v x y huv hxy hedge w hi hwS
  have hTpos : 0 < (T u v).length := by
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
      hwT hnint hTpos with hw0 | hw1
  · have hwιu : w = ι u := by
      rw [hw0]
      exact Workspace.ProofLemmas.SubdivisionCounting.track_head (htrack u v huv) hTpos
    rcases hBends with ⟨hau, -⟩ | ⟨-, hau⟩
    · exact hwιu.trans hau.symm
    · exfalso
      have hwb : w = b := hwιu.trans hau.symm
      have hnotintC : w ∉ trackInterior C := fun hi => hC.2.1 w hi (hwb ▸ hb)
      have hbcases : w = a ∨ w = c :=
        Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          hCfrom.2.1 hCfrom.2.2 hwC hnotintC
      rcases hbcases with hwa | hwc
      · exact False.elim (hab (hwa.symm.trans hwb))
      · exact False.elim (hbc (hwb.symm.trans hwc))
  · have hwιv : w = ι v := by
      rw [hw1]
      exact Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast (htrack u v huv) hTpos
    rcases hBends with ⟨-, hbv⟩ | ⟨hbv, -⟩
    · exfalso
      have hwb : w = b := hwιv.trans hbv.symm
      have hnotintC : w ∉ trackInterior C := fun hi => hC.2.1 w hi (by rw [hwb]; exact hb)
      rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          hCfrom.2.1 hCfrom.2.2 hwC hnotintC with hwa | hwc
      · exact False.elim (hab (hwa.symm.trans hwb))
      · exact False.elim (hbc (hwb.symm.trans hwc))
    · exact hwιv.trans hbv.symm

/-- Extend a branch through an edge at its far end, unless that edge already belongs to it. -/
theorem extend_branch_through_incident_edge {W : Type*} [Finite W]
    {H : SimpleGraph W} {B : List W} {a b : W} {f : Sym2 W}
    (hB : IsBranch H B) (hfrom : IsTrackFrom H B a b)
    (hpos : 1 ≤ trackLength B) (hf : f ∈ incidentEdges H b) (haf : a ∉ f) :
    ∃ (P : List W) (z : W), IsTrackFrom H P a z ∧ 2 ≤ P.length ∧
      f ∈ trackEdges P ∧ (∀ w ∈ P, w ∈ B ∨ w ∈ f) ∧
      ∀ _hP2 : 2 ≤ P.length,
        s(P[0]'(by omega), P[1]'(by omega)) ∈ trackEdges B := by
  classical
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  by_cases hfB : f ∈ trackEdges B
  · refine ⟨B, b, hfrom, hB2, hfB, ?_, ?_⟩
    · intro w hw
      exact Or.inl hw
    · intro _
      exact ⟨0, by omega, rfl⟩
  · obtain ⟨z, hfz⟩ := Sym2.mem_iff_exists.mp hf.2
    have hab : a ≠ b := track_ends_ne hfrom hpos
    have hbz : b ≠ z := by
      have hadj : H.Adj b z := by
        apply H.mem_edgeSet.mp
        rw [← hfz]
        exact hf.1
      exact hadj.ne
    have haz : a ≠ z := by
      intro h
      apply haf
      rw [hfz, ← h]
      simp
    have hzB : z ∉ B := by
      intro hzB
      obtain ⟨i, hi, hiz⟩ :=
        Workspace.ProofLemmas.BranchClassification.exists_edge_of_mem hB2 hzB
      let e : Sym2 W := s(B[i]'(by omega), B[i + 1]'hi)
      have heB : e ∈ trackEdges B := ⟨i, hi, rfl⟩
      have hze : z ∈ e := by
        dsimp [e]
        rcases hiz with h | h
        · rw [h]; simp
        · rw [h]; simp
      have hzf : z ∈ f := by rw [hfz]; simp
      rcases external_edge_meets_branch_only_at_ends hB hfrom heB hf.1 hfB hzf hze with
        hza | hzb
      · exact haz hza.symm
      · exact hbz hzb.symm
    have hbzAdj : H.Adj b z := by
      apply H.mem_edgeSet.mp
      rw [← hfz]
      exact hf.1
    let P := B ++ [z]
    have hP : IsTrackFrom H P a z :=
      Workspace.ProofLemmas.TrackSlice.isTrackFrom_concat hfrom hbzAdj hzB
    refine ⟨P, z, hP, ?_, ?_, ?_, ?_⟩
    · simp [P]; omega
    · have hlast : B[B.length - 1]'(by omega) = b :=
        Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hfrom (by omega)
      refine ⟨B.length - 1, ?_, ?_⟩
      · simp [P]; omega
      · dsimp [P]
        have hleft : (B ++ [z])[B.length - 1]'(by simp) = b := by
          rw [List.getElem_append_left (by omega)]
          exact hlast
        have hidx : B.length - 1 + 1 = B.length := by omega
        have hright0 : (B ++ [z])[B.length]'(by simp) = z := by
          rw [List.getElem_append_right (show B.length ≤ B.length by omega)]
          simp
        have hright : (B ++ [z])[B.length - 1 + 1]'(by
            simp only [List.length_append, List.length_singleton]
            omega) = z :=
          (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq
            (B ++ [z]) hidx (by
              simp only [List.length_append, List.length_singleton]
              omega) (by simp)).trans hright0
        rw [hleft, hright]
        exact hfz
    · intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · exact Or.inl hw
      · right
        have hwz : w = z := List.eq_of_mem_singleton hw
        rw [hwz, hfz]
        simp
    · intro hP2
      refine ⟨0, by omega, ?_⟩
      simp only [P]
      rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]

end Workspace.ProofLemmas.Thm61EvenEndgameHelpers
