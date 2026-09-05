import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
import Workspace.ProofLemmas.EnlargementFromNonlocalLongTrack
import Workspace.ProofLemmas.EnlargementFromNonlocalColoring
import Workspace.ProofLemmas.EnlargementFromNonlocalParity
import Workspace.ProofLemmas.EnlargementFromNonlocalPromotion
import Workspace.ProofLemmas.EnlargementFromNonlocalConnectivity
import Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision
import Workspace.ProofLemmas.EnlargementFromNonlocalK33
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm85Five8Transported
import Workspace.ProofLemmas.SixVertexBipartiteK4SubdivisionDegenerate
import Workspace.ProofLemmas.TrackSlice
import Workspace.PriorWork.DiracK4Subdivision

/-!
# Structural facts for a non-local chord of a subdivision

Two vertices on no common branch are distinct and nonadjacent. The added host is bipartite
because an old track and the new track give a hole in its line graph. The promoted skeleton
is 3-connected, contains a proper subdivision of the old skeleton, and satisfies the exceptional
`K₃,₃` clause. Only splitting old tracks at internal attachment vertices remains open, in
`EnlargementFromNonlocalPromotion.split_internal_tracks_gap`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.EnlargementFromNonlocalStructure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack

variable {V U W Z : Type*}

private theorem list_eq_nil_of_not_ne_nil {A : Type*} (l : List A)
    (h : ¬ l ≠ []) : l = [] := by
  by_cases heq : l = []
  · exact heq
  · exact (h heq).elim

private theorem exists_mem_of_ne_nil {A : Type*} {l : List A} (h : l ≠ []) :
    ∃ a, a ∈ l := by
  cases l with
  | nil => exact (h rfl).elim
  | cons a l => exact ⟨a, by simp⟩

private theorem finTwo_not_three_pairwise (a b c : Fin 2) :
    ¬ (a ≠ b ∧ b ≠ c ∧ c ≠ a) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

/-- Two vertices of a subdivision that lie on no common branch are distinct and nonadjacent. -/
theorem ne_and_not_adj_of_no_common_branch [Fintype U] [Finite W]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    c₁ ≠ c₂ ∧ ¬ H.Adj c₁ c₂ := by
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hbvLower : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hι htrack hlen hdisj hnew hdeg
  have hbvUpper : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  have hbranch : ∀ u v : U, (huv : J.Adj u v) → IsBranch H (T u v) := by
    intro u v huv
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch
      (htrack u v huv) (fun h => huv.ne (hι h))
    · intro w hw hwb
      exact hnew u v huv w hw (hbvUpper hwb)
    · exact hbvLower ⟨u, rfl⟩
    · exact hbvLower ⟨v, rfl⟩
  have hc₁ne : c₁ ≠ c₂ := by
    intro heq
    subst c₂
    rcases hcover c₁ with ⟨u, hu⟩ | ⟨u, v, huv, hc⟩
    · obtain ⟨v, huv⟩ :=
        Workspace.ProofLemmas.SubdivisionCounting.exists_adj_of_three_connected J hJ u
      apply hnb
      refine ⟨T u v, hbranch u v huv, ?_, ?_⟩
      · rw [hu]
        exact List.mem_of_mem_head? (htrack u v huv).2.1
      · rw [hu]
        exact List.mem_of_mem_head? (htrack u v huv).2.1
    · apply hnb
      refine ⟨T u v, hbranch u v huv, ?_, ?_⟩
      · exact Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hc
      · exact Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hc
  refine ⟨hc₁ne, ?_⟩
  intro hc₁c₂
  have hedge : s(c₁, c₂) ∈ H.edgeSet :=
    (SimpleGraph.mem_edgeSet H).mpr hc₁c₂
  rw [hedges] at hedge
  simp only [Set.mem_iUnion] at hedge
  obtain ⟨u, v, huv, heT⟩ := hedge
  have hends := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges heT
  exact hnb ⟨T u v, hbranch u v huv, hends.1, hends.2⟩

/-- **Promoting two non-local attachment vertices produces the enlarged skeleton.**

PAPER (printed p. 26): *"Then there is an appearance `L(H')` in `G` of some
`J`-enlargement `J'`, with `L(H)` an induced subgraph of `L(H')`.  Moreover, if
`J' = K₃,₃` then `J = K₄`."*

This is the purely topological part of that sentence.  Split the two old subdividing tracks at
`c₁,c₂` when the attachment vertex is internal, promote the split points to skeleton vertices,
and add the new skeleton edge between them. -/
theorem promotedChordEnlargement [Fintype U] [Fintype W] [Fintype Z]
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (D : SimpleGraph Z) (rho : W → Z) (p : List Z)
    (hext : IsBranchExtension H c₁ c₂ D rho p) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement J J' ∧ IsSubdivision J' D ∧
        (Nonempty (J' ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
          Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4)))) := by
  classical
  have hc := ne_and_not_adj_of_no_common_branch J hJ H hsub c₁ c₂ hnb
  obtain ⟨m, B, a, b, ι, T, hJB, hs, ha, hb, hcover, hnbB⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalPromotion.promote_vertices
      J hJ H hsub c₁ c₂ hc.1 hnb
  have hab := ne_and_not_adj_of_no_common_branch J hJ B hJB a b hnbB
  have hcyclic : CyclicallyThreeConnected B :=
    ⟨Fintype.card U, J.overFin rfl,
      Workspace.ProofLemmas.SubdivisionCounting.isKConnected_of_iso (J.overFinIso rfl) hJ,
      Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso
        (J.overFinIso rfl) hJB⟩
  let J' := B ⊔ SimpleGraph.edge a b
  have hJ' : IsKConnected J' 3 :=
    Workspace.ProofLemmas.EnlargementFromNonlocalConnectivity.three_connected
      B hcyclic a b hab.1 hcover hnbB
  have henl : IsJEnlargement J J' := by
    refine ⟨hJ', ?_⟩
    let S : J'.Subgraph := SimpleGraph.toSubgraph B (show B ≤ J' from le_sup_left)
    refine ⟨S, ?_, m, B, hJB, ?_⟩
    · intro htop
      have hadj : S.Adj a b := by
        rw [htop]
        exact Or.inr (by simp [SimpleGraph.edge_adj, hab.1])
      exact hab.2 hadj
    · exact ⟨(SimpleGraph.toSubgraph B (show B ≤ J' from le_sup_left)).spanningCoeEquivCoeOfSpanning
        (SimpleGraph.toSubgraph.isSpanning B (show B ≤ J' from le_sup_left)) |>.symm⟩
  have hext' : IsBranchExtension H (ι a) (ι b) D rho p := by
    rwa [ha, hb]
  refine ⟨m, J', henl, ?_, ?_⟩
  · exact Workspace.ProofLemmas.EnlargementFromNonlocalSubdivision.add_edge
      B H ι T hs a b hab.1 hab.2 D rho p hext'
  · exact Workspace.ProofLemmas.EnlargementFromNonlocalK33.old_is_k4 J hJ J' henl

/-- **The new subdivision is bipartite.**

PAPER (printed p. 26): *"Then there is an appearance `L(H')` in `G` of some
`J`-enlargement `J'`."*  The word "appearance" includes that `H'` is bipartite.  If the new
track has the wrong parity, the two old attachment branches and 3-connectivity supply an odd
cycle of length at least five; its line graph is an odd hole in the induced Berge subgraph. -/
theorem branchExtensionBipartite [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W] [Fintype Z]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsBipartiteSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (D : SimpleGraph Z) (rho : W → Z) (p : List Z)
    (hext : IsBranchExtension H c₁ c₂ D rho p)
    (K' : Set V) (psi : D.lineGraph ≃g G.induce K') :
    D.IsBipartite := by
  classical
  have hc := ne_and_not_adj_of_no_common_branch J hJ H hsub.1 c₁ c₂ hnb
  have hcyclic : CyclicallyThreeConnected H :=
    ⟨Fintype.card U, J.overFin rfl,
      Workspace.ProofLemmas.SubdivisionCounting.isKConnected_of_iso (J.overFinIso rfl) hJ,
      Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso
        (J.overFinIso rfl) hsub.1⟩
  obtain ⟨r, hr, hrlen⟩ :=
    Workspace.ProofLemmas.EnlargementFromNonlocalLongTrack.exists_long_track
      hcyclic c₁ c₂ hc.1 hc.2 hnb
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
  exact Workspace.ProofLemmas.EnlargementFromNonlocalColoring.bipartite_of_parity hext col
    (Workspace.ProofLemmas.EnlargementFromNonlocalParity.extension_parity
      hG hext hc.2 hr hrlen psi col)

/-- A proper enlargement of a 3-connected graph cannot itself be `K₄`. -/
theorem enlargementNotK4 [Fintype U] {m : ℕ} (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (J' : SimpleGraph (Fin m))
    (henl : IsJEnlargement J J') :
    ¬ Nonempty (J' ≃g (⊤ : SimpleGraph (Fin 4))) := by
  classical
  intro hJ'4
  obtain ⟨isoJ'4⟩ := hJ'4
  obtain ⟨hJ'3, S, hSne, nD, Dg, hDsub, ⟨φD⟩⟩ := henl
  have hcardU : 3 < Fintype.card U := hJ.1
  haveI : Nonempty U := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨R, hRsub⟩ :=
    _root_.Workspace.PriorWork.DiracK4Subdivision.exists_k4_subdivision_subgraph_of_min_degree_three
      J (Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ)
  have hmapinj : Function.Injective
      (Sym2.map (Subtype.val : R.verts → U)) :=
    Sym2.map.injective Subtype.val_injective
  have himage : Sym2.map (Subtype.val : R.verts → U) '' R.coe.edgeSet ⊆ J.edgeSet := by
    rintro e ⟨f, hf, rfl⟩
    induction f using Sym2.ind with
    | _ a b =>
      rw [Sym2.map_mk]
      exact (SimpleGraph.mem_edgeSet J).mpr
        (R.adj_sub ((SimpleGraph.mem_edgeSet R.coe).mp hf))
  have hRle : R.coe.edgeSet.ncard ≤ J.edgeSet.ncard := by
    calc
      R.coe.edgeSet.ncard =
          (Sym2.map (Subtype.val : R.verts → U) '' R.coe.edgeSet).ncard :=
        (Set.ncard_image_of_injective _ hmapinj).symm
      _ ≤ J.edgeSet.ncard := Set.ncard_le_ncard himage (Set.toFinite _)
  have h0 : (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard ≤ R.coe.edgeSet.ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.edgeSet_ncard_le_of_isSubdivision
      (⊤ : SimpleGraph (Fin 4)) R.coe hRsub
  have h1 : J.edgeSet.ncard ≤ Dg.edgeSet.ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.edgeSet_ncard_le_of_isSubdivision J Dg hDsub
  have h2 : Dg.edgeSet.ncard < J'.edgeSet.ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.edgeSet_ncard_lt_of_ne_top
      J' hJ'3 S hSne Dg φD
  have h3 : J'.edgeSet.ncard = (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_congr isoJ'4.mapEdgeSet
  omega

/-- A bipartite subdivision of `K₄` has at least six vertices. -/
theorem six_le_card_of_bipartite_k4_subdivision [Fintype U] [Fintype W]
    (J : SimpleGraph U) (H : SimpleGraph W)
    (hJ4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hH : IsBipartiteSubdivision J H) : 6 ≤ Fintype.card W := by
  classical
  obtain ⟨e⟩ := hJ4
  have hsub4 : IsSubdivision (⊤ : SimpleGraph (Fin 4)) H :=
    Workspace.ProofLemmas.Thm85Five8Transported.isSubdivision_of_iso e hH.1
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub4
  have htop : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v huv
    simpa using huv
  have hrangeCard : (Set.range ι).ncard = 4 := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ hι, Set.ncard_univ]
    simp
  by_contra hcard
  have hcardLe : Fintype.card W ≤ 5 := by omega
  have noTwoInteriors : ∀ (u v a b : Fin 4), u ≠ v → a ≠ b →
      s(u, v) ≠ s(a, b) → trackInterior (T u v) ≠ [] →
        trackInterior (T a b) ≠ [] → False := by
    intro u v a b huv hab hpairs huvi habi
    obtain ⟨w, hw⟩ := exists_mem_of_ne_nil huvi
    obtain ⟨z, hz⟩ := exists_mem_of_ne_nil habi
    have hwnew : w ∉ Set.range ι := hnew u v (htop u v huv) w hw
    have hznew : z ∉ Set.range ι := hnew a b (htop a b hab) z hz
    have hzT : z ∈ T a b :=
      Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hz
    have hwz : w ≠ z := by
      intro hwzeq
      exact hdisj u v a b (htop u v huv) (htop a b hab) hpairs w hw (hwzeq ▸ hzT)
    have hwinsert : w ∉ (insert z (Set.range ι) : Set W) := by
      intro hmem
      change w = z ∨ w ∈ Set.range ι at hmem
      exact hmem.elim hwz hwnew
    have hsetCard : (insert w (insert z (Set.range ι)) : Set W).ncard = 6 := by
      rw [Set.ncard_insert_of_notMem hwinsert (Set.toFinite _),
        Set.ncard_insert_of_notMem hznew (Set.toFinite _), hrangeCard]
    have hle := Set.ncard_le_ncard
      (Set.subset_univ (insert w (insert z (Set.range ι)) : Set W)) (Set.toFinite _)
    rw [hsetCard, Set.ncard_univ, Nat.card_eq_fintype_card] at hle
    omega
  have emptyOther : ∀ (u v a b : Fin 4), u ≠ v → a ≠ b →
      s(u, v) ≠ s(a, b) → trackInterior (T u v) ≠ [] →
        trackInterior (T a b) = [] := by
    intro u v a b huv hab hpairs hint
    apply list_eq_nil_of_not_ne_nil
    intro hint'
    exact noTwoInteriors u v a b huv hab hpairs hint hint'
  have directAdj : ∀ (u v : Fin 4), u ≠ v → trackInterior (T u v) = [] →
      H.Adj (ι u) (ι v) := by
    intro u v huv hinter
    have ht := htrack u v (htop u v huv)
    have htwo : 2 ≤ (T u v).length := by
      have := hlen u v (htop u v huv)
      simp only [trackLength] at this
      omega
    have hinterLen : (trackInterior (T u v)).length = 0 := by simp [hinter]
    have hlenTwo : (T u v).length = 2 := by
      simp only [trackInterior, List.length_dropLast, List.length_tail] at hinterLen
      omega
    have hadj := ht.1.2.2 0 (by omega)
    have hfirst : (T u v)[0]'(by omega) = ι u :=
      Workspace.ProofLemmas.SubdivisionCounting.track_head ht (by omega)
    have hlast : (T u v)[1]'(by omega) = ι v := by
      have h := Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast ht (by omega)
      simpa [hlenTwo] using h
    rwa [hfirst, hlast] at hadj
  obtain ⟨color, hcolor⟩ := hH.2
  have noTriangle : ∀ a b c : Fin 4,
      H.Adj (ι a) (ι b) → H.Adj (ι b) (ι c) → H.Adj (ι c) (ι a) → False := by
    intro a b c hab hbc hca
    exact finTwo_not_three_pairwise (color (ι a)) (color (ι b)) (color (ι c))
      ⟨hcolor hab, hcolor hbc, hcolor hca⟩
  by_cases h01 : trackInterior (T 0 1) ≠ []
  · have h02 := emptyOther 0 1 0 2 (by decide) (by decide) (by decide) h01
    have h23 := emptyOther 0 1 2 3 (by decide) (by decide) (by decide) h01
    have h30 := emptyOther 0 1 3 0 (by decide) (by decide) (by decide) h01
    exact noTriangle 0 2 3
      (directAdj 0 2 (by decide) h02)
      (directAdj 2 3 (by decide) h23)
      (directAdj 3 0 (by decide) h30)
  · have he01 := list_eq_nil_of_not_ne_nil _ h01
    by_cases h02 : trackInterior (T 0 2) ≠ []
    · have h13 := emptyOther 0 2 1 3 (by decide) (by decide) (by decide) h02
      have h30 := emptyOther 0 2 3 0 (by decide) (by decide) (by decide) h02
      exact noTriangle 0 1 3
        (directAdj 0 1 (by decide) he01)
        (directAdj 1 3 (by decide) h13)
        (directAdj 3 0 (by decide) h30)
    · have he02 := list_eq_nil_of_not_ne_nil _ h02
      by_cases h12 : trackInterior (T 1 2) ≠ []
      · have h13 := emptyOther 1 2 1 3 (by decide) (by decide) (by decide) h12
        have h30 := emptyOther 1 2 3 0 (by decide) (by decide) (by decide) h12
        exact noTriangle 0 1 3
          (directAdj 0 1 (by decide) he01)
          (directAdj 1 3 (by decide) h13)
          (directAdj 3 0 (by decide) h30)
      · have he12 := list_eq_nil_of_not_ne_nil _ h12
        exact noTriangle 0 1 2
          (directAdj 0 1 (by decide) he01)
          (directAdj 1 2 (by decide) he12)
          (directAdj 2 0 (by decide) (by
            rw [hrev 0 2 (htop 0 2 (by decide))]
            simpa [Workspace.ProofLemmas.TrackSlice.trackInterior_reverse]
              using he02))

/-- **Deleting the added branch from a `K₃,₃` extension leaves a degenerate `K₄`
subdivision.**

PAPER (printed p. 26): *"Moreover, if `J' = K₃,₃` then `J = K₄`, and so `L(H)` is
nondegenerate and therefore so is `L(H')`."*  The contrapositive used here is the finite
six-vertex part hidden in "therefore": if the enlarged subdivision itself is `K₃,₃`, its old
`K₄` subdivision is the graph obtained by deleting the new branch and is degenerate. -/
theorem k33ExtensionForcesOldDegenerate [Fintype U] [Fintype W] [Fintype Z]
    (J : SimpleGraph U) (H : SimpleGraph W) (hsub : IsBipartiteSubdivision J H)
    (c₁ c₂ : W) (D : SimpleGraph Z) (rho : W → Z) (p : List Z)
    (hext : IsBranchExtension H c₁ c₂ D rho p)
    (hJ4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hD33 : Nonempty (D ≃g completeBipartiteGraph (Fin 3) (Fin 3))) :
    DegenerateAppearance J H := by
  obtain ⟨isoD33⟩ := hD33
  have hZcard : Fintype.card Z = 6 := by
    have h := Fintype.card_congr isoD33.toEquiv
    simpa using h
  have hWle : Fintype.card W ≤ 6 := by
    have h := Fintype.card_le_of_injective rho hext.inj
    omega
  have hWge : 6 ≤ Fintype.card W :=
    six_le_card_of_bipartite_k4_subdivision J H hJ4 hsub
  have hWcard : Fintype.card W = 6 := by omega
  exact Workspace.ProofLemmas.SixVertexBipartiteK4SubdivisionDegenerate
    J H hJ4 hsub hWcard

/-- **The enlarged appearance is nondegenerate.**

PAPER (printed p. 26): *"Moreover, if `J' = K₃,₃` then `J = K₄`, and so `L(H)` is
nondegenerate and therefore so is `L(H')`."*  The `K₄` alternative cannot occur for a proper
3-connected enlargement.  In the `K₃,₃` alternative, deleting the added branch leaves a
degenerate `K₄` subdivision unless the enlarged appearance is nondegenerate. -/
theorem branchExtensionNondegenerate [Fintype U] [Fintype W] [Fintype Z] {m : ℕ}
    (J : SimpleGraph U) (hJ : IsKConnected J 3) (H : SimpleGraph W)
    (hsub : IsSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (D : SimpleGraph Z) (rho : W → Z) (p : List Z)
    (hext : IsBranchExtension H c₁ c₂ D rho p)
    (J' : SimpleGraph (Fin m)) (henl : IsJEnlargement J J')
    (hDsub : IsSubdivision J' D)
    (hclass : Nonempty (J' ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
      Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateAppearance J H) :
    NondegenerateAppearance J' D := by
  intro hdeg
  rcases hdeg with h4 | h33
  · exact enlargementNotK4 J hJ J' henl h4.1
  · have hJ4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) := hclass h33.2.1
    exact hnd hJ4
      (k33ExtensionForcesOldDegenerate J H ⟨hsub,
        SimpleGraph.Colorable.of_hom
          ({ toFun := rho, map_rel' := by
              intro a b hab
              exact hext.oldAdj a b hab } : H →g D)
          (by
            obtain ⟨isoD33⟩ := h33.2.2
            exact SimpleGraph.Colorable.of_hom isoD33.toHom
              Workspace.ProofLemmas.SubdivisionCounting.k33_bipartite)⟩
        c₁ c₂ D rho p hext hJ4 h33.2.2)

end Workspace.ProofLemmas.EnlargementFromNonlocalStructure
