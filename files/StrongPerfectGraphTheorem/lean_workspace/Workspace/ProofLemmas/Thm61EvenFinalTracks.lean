import Workspace.ProofLemmas.Thm61EvenEndgameHelpers
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.BipartiteClosedWalkEven

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenFinalTracks

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-- Claim (9) applied to the track obtained by adding one complete edge at each end
of an even track with no complete edges. Its penultimate vertices are the original ends. -/
theorem complete_edge_hits_ends
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V} {y₁ y₂ : V}
    (h9 : Claim9 G H K φ Y y₁ y₂)
    {B : List (Fin n)} {a b u v : Fin n}
    (hB : IsTrackFrom H B a b) (hpos : 1 ≤ trackLength B)
    (heven : Even (trackLength B))
    (hua : H.Adj u a) (hbv : H.Adj b v)
    (huB : u ∉ B) (hvB : v ∉ B) (huv : u ≠ v)
    (hfirst : s(u, a) ∈ completeEdges G H K φ Y)
    (hlast : s(b, v) ∈ completeEdges G H K φ Y)
    (hno : Disjoint (trackEdges B) (completeEdges G H K φ Y)) :
    ∀ f ∈ completeEdges G H K φ Y, a ∈ f ∨ b ∈ f := by
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hpos; omega
  let P := u :: (B ++ [v])
  obtain ⟨hP, hlen, hget, -, -⟩ := hang_track hB hB2 hua hbv huB hvB huv
  have hP5 : 5 ≤ P.length := by
    obtain ⟨k, hk⟩ := heven
    simp only [trackLength] at hk hpos
    change 5 ≤ (u :: (B ++ [v])).length
    omega
  have hPeven : Even (trackLength P) := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k + 1, ?_⟩
    change P.length - 1 = _
    simp only [trackLength] at hk
    change (u :: (B ++ [v])).length - 1 = _
    omega
  have hedges := hang_edges hB hB2 (u := u) (v := v)
  have hint : ∀ i : ℕ, 1 ≤ i → ∀ hi : i + 2 < P.length,
      s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y := by
    intro i hi hi' hc
    have hiB : i < B.length := by change i + 2 < (u :: (B ++ [v])).length at hi'; omega
    have heq := hedges.2.2 i hi hi'
    have hm : s(B[i - 1]'(by omega), B[i]'hiB) ∈ trackEdges B := by
      refine ⟨i - 1, by omega, ?_⟩
      congr 1
      exact geq B (by omega) (by omega) (by omega)
    exact Set.disjoint_left.mp hno hm (heq ▸ hc)
  have hpa : P[1]'(by omega) = a := by
    exact (hget 0 (by omega) (by omega)).trans (head_getElem hB.2.1 (by omega))
  have hpb : P[P.length - 2]'(by omega) = b := by
    have heq : P.length - 2 = (B.length - 1) + 1 := by
      change (u :: (B ++ [v])).length - 2 = _
      omega
    exact (geq P heq (by omega) (by
      change (B.length - 1) + 1 < (u :: (B ++ [v])).length
      omega)).trans ((hget (B.length - 1) (by omega) (by omega)).trans
        (last_getElem hB.2.2 (by omega)))
  intro f hf
  have hc := h9 Y (Or.inl rfl) P hP.1 hP5 hPeven
    (hedges.1.symm ▸ hfirst) (hedges.2.1.symm ▸ hlast) hint f hf
  simpa only [hpa, hpb] using hc

/-- The last use of (9): an even branch whose end-edges are complete and whose internal
edges are not has length two if a complete edge misses all its internal vertices. -/
theorem length_two_of_claim9
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V} {y₁ y₂ : V}
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (Y' : Set V) (hY' : Y' = Y ∨ Y' = Y \ {y₁} ∨ Y' = Y \ {y₂})
    {B : List (Fin n)} (hB : IsTrackList H B) (hB2 : 2 ≤ B.length)
    (heven : Even (trackLength B))
    (hfirst : s(B[0]'(by omega), B[1]'(by omega)) ∈ completeEdges G H K φ Y')
    (hlast : s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) ∈
      completeEdges G H K φ Y')
    (hint : ∀ i : ℕ, 1 ≤ i → ∀ hi : i + 2 < B.length,
      s(B[i]'(by omega), B[i + 1]'(by omega)) ∉ completeEdges G H K φ Y')
    {e : Sym2 (Fin n)} (he : e ∈ completeEdges G H K φ Y')
    (hmiss : ∀ w ∈ trackInterior B, w ∉ e) : trackLength B = 2 := by
  have hlt : B.length < 5 := by
    by_contra h
    have h5 : 5 ≤ B.length := by omega
    rcases h9 Y' hY' B hB h5 heven hfirst hlast hint e he with h | h
    · exact hmiss _ (SubdivisionCounting.mem_trackInterior_getElem B 0 (by omega)) h
    · have hi : B[B.length - 2]'(by omega) ∈ trackInterior B := by
        have hm := SubdivisionCounting.mem_trackInterior_getElem B (B.length - 3) (by omega)
        rwa [geq B (show B.length - 3 + 1 = B.length - 2 by omega)
          (by omega) (by omega)] at hm
      exact hmiss _ hi h
  obtain ⟨k, hk⟩ := heven
  simp only [trackLength] at hk ⊢
  omega

/-- The last parity assertion of (13): `b` and `b₁` have the same color, and both `b₂`
and `b₃` have the opposite color. Thus every track from `b₂` to `b₃` is even. -/
theorem fourth_branch_even
    {W : Type*} {H : SimpleGraph W} (hbip : H.IsBipartite)
    {B₁ B₄ : List W} {b b₁ b₂ b₃ : W}
    (hfrom₁ : IsTrackFrom H B₁ b b₁) (heven : Even (trackLength B₁))
    (h12 : H.Adj b₁ b₂) (h03 : H.Adj b b₃)
    (hfrom₄ : IsTrackFrom H B₄ b₂ b₃) : Even (trackLength B₄) := by
  obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  have h01 := (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp heven
  apply (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₄).mpr
  exact bool_eq_of_ne_ne (col b) (col b₂) (col b₃)
    (h01.symm ▸ col.valid h12) (col.valid h03)

/-- Every edge incident with a branch-vertex belongs to a branch oriented from that vertex.
This is the choice "Let `B₄` be the branch of `H` containing `e₄`." -/
theorem branch_from_incident
    {m n : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {H : SimpleGraph (Fin n)} (hsub : IsSubdivision J H)
    {b : Fin n} (hb : b ∈ branchVertices H)
    {e : Sym2 (Fin n)} (he : e ∈ incidentEdges H b) :
    ∃ (B : List (Fin n)) (b' : Fin n),
      IsBranch H B ∧ e ∈ trackEdges B ∧ IsTrackFrom H B b b' := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdegJ : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard := fun u =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdegJ
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hTint : ∀ u v : Fin m, J.Adj u v → ∀ w ∈ trackInterior (T u v),
      w ∉ branchVertices H := fun u v huv w hw hbw => hnew u v huv w hw (hbv₂ hbw)
  have hTbranch : ∀ u v : Fin m, J.Adj u v → IsBranch H (T u v) := by
    intro u v huv
    exact Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
      (fun huvEq => huv.ne (hι huvEq)) (hTint u v huv)
      (hbv₁ ⟨u, rfl⟩) (hbv₁ ⟨v, rfl⟩)
  have hbranchFor : ∀ e : Sym2 (Fin n), e ∈ incidentEdges H b →
      ∃ (B : List (Fin n)) (b' : Fin n),
        IsBranch H B ∧ e ∈ trackEdges B ∧ IsTrackFrom H B b b' := by
    intro e he
    have heE : e ∈ H.edgeSet := he.1
    rw [hedges] at heE
    simp only [Set.mem_iUnion] at heE
    obtain ⟨u, v, huv, heT⟩ := heE
    have hbT : b ∈ T u v :=
      NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges heT he.2
    have hbnotint : b ∉ trackInterior (T u v) := fun hbint => hTint u v huv b hbint hb
    have hbends := SubdivisionCompose.mem_ends_of_mem
      (htrack u v huv).2.1 (htrack u v huv).2.2 hbT hbnotint
    rcases hbends with hbU | hbV
    · refine ⟨T u v, ι v, hTbranch u v huv, heT, ?_⟩
      rw [hbU]
      exact htrack u v huv
    · refine ⟨T v u, ι u, hTbranch v u huv.symm, ?_, ?_⟩
      · rw [hrev u v huv, SubdivisionCounting.trackEdges_reverse]
        exact heT
      · rw [hbV]
        exact htrack v u huv.symm
  exact hbranchFor e he

end Workspace.ProofLemmas.Thm61EvenFinalTracks
