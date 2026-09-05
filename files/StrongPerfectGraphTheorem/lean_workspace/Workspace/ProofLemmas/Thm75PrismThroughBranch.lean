import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionTrackExpansion
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.Statements.S07.Thm_7_1

/-!
# 7.5, claim (1): the prism through the branch `Bc₁c₂`

PAPER (proof of 7.5, claim (1), printed p. 35): *"By 7.1, there are two paths `Q₁, Q₂` of `H`
between `c₁` and `c₂`, such that `Q₁, Q₂, Bc₁c₂` are vertex-disjoint except for their ends, and
for `i = 1, 2`, `aᵢ` is the first edge of `Qᵢ`.  Let `bᵢ` be the other end-edge of `Qᵢ`.  Both
`Q₁` and `Q₂` have odd length, since `Bc₁c₂` is odd and `H` is bipartite; and they have length
`≥ 3` since `c₁, c₂` are nonadjacent (for they are the ends of a branch of length `> 1`.)  Hence
there are two paths `P₁, P₂` of `L(H)` from `Nc₁` to `Nc₂`, such that `P₁, P₂, Rc₁c₂` are
vertex-disjoint and form a prism, and `Pᵢ` is from `aᵢ` to `bᵢ`.  Now `Bc₁c₂` is odd and
therefore `Rc₁c₂` is even, and similarly `P₁` and `P₂` are even."*

This module packages that whole sentence: for the fixed branch `Bc₁c₂` it names its rung's ends
`r₁ ∈ Nc₁`, `r₂ ∈ Nc₂`, and says that any two distinct `a₁, a₂ ∈ Nc₁ \ {r₁}` are the `Nc₁`-ends
of a prism of `G` whose third path is the rung `Rc₁c₂`, all three paths being even of length
`≥ 2` and contained in `V(L(H))`.

It is the composite of three things the printed proof chains together:

* **7.1** applied to the 3-connected `J`, giving three tracks of `J` from `c₁` to `c₂` that are
  disjoint except at their ends, one of them the edge `c₁c₂` and the other two with prescribed
  first edges;
* the expansion of those `J`-tracks into `H`-tracks along the subdivision
  (`SubdivisionCompose.expandTracks`), and the parity computation "`Qᵢ` odd since `Bc₁c₂` is odd
  and `H` is bipartite";
* the track/path dictionary of printed p. 19 — *"the edge-set of a track becomes the vertex-set
  of a path"* — turning three `H`-tracks that pairwise meet only at `c₁, c₂` into three paths of
  `L(H)` forming a prism, with `pathLength Pᵢ = trackLength Qᵢ - 1`.

**Status: statement only — this module is a work item.**  It is the last place in the proof of
7.5 where 7.1 is needed for claim (1).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75PrismThroughBranch

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.SubdivisionTrackExpansion

/-- **7.5, claim (1), the geometric input.**  The rung `Rc₁c₂` has ends `r₁ ∈ Nc₁`, `r₂ ∈ Nc₂`,
and any two distinct `a₁, a₂ ∈ Nc₁ \ {r₁}` extend to a prism `P₁, P₂, Rc₁c₂` of `G` with
triangles `{a₁, a₂, r₁}` and `{b₁, b₂, r₂}`, all three paths even of length `≥ 2` and inside
`V(L(H)) = K`. -/
theorem thm75PrismThroughBranch {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B) :
    ∃ r₁ r₂ : V, r₁ ∈ NSet G H K φ c₁ ∧ r₂ ∈ NSet G H K φ c₂ ∧
      r₁ ∈ trackRung φ B hfrom.1 ∧ r₂ ∈ trackRung φ B hfrom.1 ∧
      ∀ a₁ a₂ : V, a₁ ∈ NSet G H K φ c₁ → a₂ ∈ NSet G H K φ c₁ →
        a₁ ≠ r₁ → a₂ ≠ r₁ → a₁ ≠ a₂ →
        ∃ (b₁ b₂ : V) (P₁ P₂ R : List V),
          b₁ ∈ NSet G H K φ c₂ ∧ b₂ ∈ NSet G H K φ c₂ ∧
          FormPrism G ![a₁, a₂, r₁] ![b₁, b₂, r₂] P₁ P₂ R ∧
          Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength R) ∧
          2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧ 2 ≤ pathLength R ∧
          (∀ v ∈ P₁, v ∈ K) ∧ (∀ v ∈ P₂, v ∈ K) ∧ (∀ v ∈ R, v ∈ K) := by
  classical
  have hsub : IsSubdivision J H := happ.1.1
  have hbip : H.IsBipartite := happ.1.2
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  let hS : SubdivWitness J H ι T := ⟨hι, htrack, hlenT, hrev, hdisj, hnew⟩
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hBtwo : 2 ≤ B.length := by
    simp only [trackLength] at hlen
    omega
  have hBtwoEdges : 2 ≤ trackLength B := by omega
  obtain ⟨hcne, hc₁branch, hc₂branch, hcnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂
      hbranch hfrom hBtwoEdges
  obtain ⟨u₀, v₀, hu₀v₀, hBedges, hends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlenT hrev hdisj hnew hcover hedges hdeg hbranch hBtwo hfrom
      hc₁branch hc₂branch
  obtain ⟨u, v, huv, huc₁, hvc₂, hBT⟩ :
      ∃ u v : U, J.Adj u v ∧ ι u = c₁ ∧ ι v = c₂ ∧ B = T u v := by
    rcases hends with ⟨hc₁u, hc₂v⟩ | ⟨hc₁v, hc₂u⟩
    · have hTfrom : IsTrackFrom H (T u₀ v₀) c₁ c₂ := by
        simpa [hc₁u, hc₂v] using htrack u₀ v₀ hu₀v₀
      have hEq : B = T u₀ v₀ :=
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          hfrom.1.2.1 hTfrom.1.2.1 hfrom.2.1 hTfrom.2.1 hfrom.2.2 hTfrom.2.2
          (by rw [hBedges])
      exact ⟨u₀, v₀, hu₀v₀, hc₁u.symm, hc₂v.symm, hEq⟩
    · have hTfrom : IsTrackFrom H (T v₀ u₀) c₁ c₂ := by
        simpa [hc₁v, hc₂u] using htrack v₀ u₀ hu₀v₀.symm
      have hBedges' : trackEdges B = trackEdges (T v₀ u₀) := by
        rw [hrev u₀ v₀ hu₀v₀,
          Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
        exact hBedges
      have hEq : B = T v₀ u₀ :=
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          hfrom.1.2.1 hTfrom.1.2.1 hfrom.2.1 hTfrom.2.1 hfrom.2.2 hTfrom.2.2
          (by rw [hBedges'])
      exact ⟨v₀, u₀, hu₀v₀.symm, hc₁v.symm, hc₂u.symm, hEq⟩
  have hbase : IsTrackFrom J [u, v] u v := by
    refine ⟨⟨by simp, by simp [huv.ne], ?_⟩, rfl, rfl⟩
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst i
    simpa using huv
  have hExpandBase : expandTracks ι T [u, v] = B := by
    have hEq := expandTracks_cons_cons_full hS u v [] huv (by simp)
    have hEq' : expandTracks ι T [u, v] = T u v := by simpa using hEq
    exact hEq'.trans hBT.symm
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  have hcolne : col c₁ ≠ col c₂ := by
    intro heq
    have heven : Even (trackLength B) :=
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom).2 heq
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  let r₁ : V := firstRungVertex φ B hfrom.1 hBtwo
  let r₂ : V := lastRungVertex φ B hfrom.1 hBtwo
  have hr₁ : r₁ ∈ NSet G H K φ c₁ := by
    refine ⟨firstTrackEdge B hBtwo, firstTrackEdge_mem hfrom.1 hBtwo, ?_, rfl⟩
    exact ⟨firstTrackEdge_mem hfrom.1 hBtwo, firstTrackEdge_contains hfrom hBtwo⟩
  have hr₂ : r₂ ∈ NSet G H K φ c₂ := by
    refine ⟨lastTrackEdge B hBtwo, lastTrackEdge_mem hfrom.1 hBtwo, ?_, rfl⟩
    exact ⟨lastTrackEdge_mem hfrom.1 hBtwo, lastTrackEdge_contains hfrom hBtwo⟩
  refine ⟨r₁, r₂, hr₁, hr₂,
    firstRungVertex_mem φ hfrom.1 hBtwo, lastRungVertex_mem φ hfrom.1 hBtwo, ?_⟩
  intro a₁ a₂ ha₁ ha₂ ha₁r ha₂r ha₁₂
  obtain ⟨e₁, he₁E, he₁inc, ha₁eq⟩ := ha₁
  obtain ⟨e₂, he₂E, he₂inc, ha₂eq⟩ := ha₂
  have hu₁ : ι u ∈ e₁ := by rw [huc₁]; exact he₁inc.2
  have hu₂ : ι u ∈ e₂ := by rw [huc₁]; exact he₂inc.2
  obtain ⟨x₁, hux₁, he₁T⟩ := edge_at_embedded_vertex hS hedges he₁E hu₁
  obtain ⟨x₂, hux₂, he₂T⟩ := edge_at_embedded_vertex hS hedges he₂E hu₂
  have hx₁v : x₁ ≠ v := by
    intro hx
    subst x₁
    have he₁B : e₁ ∈ trackEdges B := by rw [hBT]; exact he₁T
    have heq := edge_eq_firstTrackEdge hfrom hBtwo he₁B he₁inc.2
    apply ha₁r
    rw [ha₁eq]
    dsimp [r₁, firstRungVertex]
    apply congrArg (fun z : H.edgeSet => (φ z : V))
    exact Subtype.ext heq
  have hx₂v : x₂ ≠ v := by
    intro hx
    subst x₂
    have he₂B : e₂ ∈ trackEdges B := by rw [hBT]; exact he₂T
    have heq := edge_eq_firstTrackEdge hfrom hBtwo he₂B he₂inc.2
    apply ha₂r
    rw [ha₂eq]
    dsimp [r₁, firstRungVertex]
    apply congrArg (fun z : H.edgeSet => (φ z : V))
    exact Subtype.ext heq
  have hx₁₂ : x₁ ≠ x₂ := by
    intro hx
    subst x₂
    have hTtwo : 2 ≤ (T u x₁).length := two_le_track_length hS hux₁
    have heq₁ := edge_eq_firstTrackEdge (htrack u x₁ hux₁) hTtwo he₁T hu₁
    have heq₂ := edge_eq_firstTrackEdge (htrack u x₁ hux₁) hTtwo he₂T hu₂
    have heq : e₁ = e₂ := heq₁.trans heq₂.symm
    apply ha₁₂
    rw [ha₁eq, ha₂eq]
    apply congrArg (fun z : H.edgeSet => (φ z : V))
    exact Subtype.ext heq
  have hec₁ : s(u, x₁) ≠ s(u, v) := by
    intro heq
    exact hx₁v (Sym2.congr_right.mp heq)
  have hec₂ : s(u, x₂) ≠ s(u, v) := by
    intro heq
    exact hx₂v (Sym2.congr_right.mp heq)
  have he₁₂ : s(u, x₁) ≠ s(u, x₂) := by
    intro heq
    exact hx₁₂ (Sym2.congr_right.mp heq)
  obtain ⟨Qbase, Q₁, Q₂, hQbase, hQ₁, hQ₂, hdBase₁, hdBase₂, hd₁₂,
      hfirstBase, hfirst₁, hfirst₂⟩ :=
    Workspace.Statements.S07.SPGT.thm_7_1 J hJ u v huv (s(u, x₁)) (s(u, x₂))
      hux₁ hux₂ (by simp) (by simp) hec₁ hec₂ he₁₂
  obtain ⟨w₁, rest₁, hQ₁shape, hw₁⟩ := hfirst₁
  obtain ⟨w₂, rest₂, hQ₂shape, hw₂⟩ := hfirst₂
  have hw₁x : w₁ = x₁ := Sym2.congr_right.mp hw₁
  have hw₂x : w₂ = x₂ := Sym2.congr_right.mp hw₂
  subst w₁
  subst w₂
  have hQ₁two : 2 ≤ Q₁.length := by rw [hQ₁shape]; simp
  have hQ₂two : 2 ≤ Q₂.length := by rw [hQ₂shape]; simp
  have havoid₁ : s(u, v) ∉ trackEdges Q₁ := by
    intro he
    have heq := edge_eq_firstTrackEdge hQ₁ hQ₁two he (by simp)
    have hfirst : firstTrackEdge Q₁ hQ₁two = s(u, x₁) := by
      simp [firstTrackEdge, hQ₁shape]
    exact hx₁v (Sym2.congr_right.mp (heq.trans hfirst)).symm
  have havoid₂ : s(u, v) ∉ trackEdges Q₂ := by
    intro he
    have heq := edge_eq_firstTrackEdge hQ₂ hQ₂two he (by simp)
    have hfirst : firstTrackEdge Q₂ hQ₂two = s(u, x₂) := by
      simp [firstTrackEdge, hQ₂shape]
    exact hx₂v (Sym2.congr_right.mp (heq.trans hfirst)).symm
  let P₁ : List W := expandTracks ι T Q₁
  let P₂ : List W := expandTracks ι T Q₂
  have hP₁ : IsTrackFrom H P₁ c₁ c₂ := by
    have ht := expandTracks_isTrackFrom hS hQ₁
    simpa [P₁, huc₁, hvc₂] using ht
  have hP₂ : IsTrackFrom H P₂ c₁ c₂ := by
    have ht := expandTracks_isTrackFrom hS hQ₂
    simpa [P₂, huc₁, hvc₂] using ht
  have hQ₁chain : List.IsChain J.Adj Q₁ := List.isChain_iff_getElem.mpr hQ₁.1.2.2
  have hQ₂chain : List.IsChain J.Adj Q₂ := List.isChain_iff_getElem.mpr hQ₂.1.2.2
  have hP₁two : 2 ≤ P₁.length := by
    dsimp [P₁]
    exact two_le_expandTracks_length hS hQ₁chain hQ₁two
  have hP₂two : 2 ≤ P₂.length := by
    dsimp [P₂]
    exact two_le_expandTracks_length hS hQ₂chain hQ₂two
  have hQ₁tail : List.IsChain J.Adj (x₁ :: rest₁) := by
    rw [hQ₁shape] at hQ₁chain
    exact hQ₁chain.tail
  have hQ₂tail : List.IsChain J.Adj (x₂ :: rest₂) := by
    rw [hQ₂shape] at hQ₂chain
    exact hQ₂chain.tail
  have he₁P₁ : e₁ ∈ trackEdges P₁ := by
    dsimp [P₁]
    rw [hQ₁shape]
    exact trackEdges_expandTracks_prefix hS hux₁ hQ₁tail he₁T
  have he₂P₂ : e₂ ∈ trackEdges P₂ := by
    dsimp [P₂]
    rw [hQ₂shape]
    exact trackEdges_expandTracks_prefix hS hux₂ hQ₂tail he₂T
  have ha₁first : firstRungVertex φ P₁ hP₁.1 hP₁two = a₁ := by
    have heq := edge_eq_firstTrackEdge hP₁ hP₁two he₁P₁ he₁inc.2
    rw [ha₁eq]
    dsimp [firstRungVertex]
    apply congrArg (fun z : H.edgeSet => (φ z : V))
    exact Subtype.ext heq.symm
  have ha₂first : firstRungVertex φ P₂ hP₂.1 hP₂two = a₂ := by
    have heq := edge_eq_firstTrackEdge hP₂ hP₂two he₂P₂ he₂inc.2
    rw [ha₂eq]
    dsimp [firstRungVertex]
    apply congrArg (fun z : H.edgeSet => (φ z : V))
    exact Subtype.ext heq.symm
  have htriv₁ : ∀ z ∈ [u, v], z ∈ Q₁ → z = u ∨ z = v := by
    intro z hz _
    simpa using hz
  have htriv₂ : ∀ z ∈ [u, v], z ∈ Q₂ → z = u ∨ z = v := by
    intro z hz _
    simpa using hz
  have hdExpBase₁ := expandTracks_meet_only_ends hS hbase hQ₁ htriv₁ (Or.inr havoid₁)
  have hdExpBase₂ := expandTracks_meet_only_ends hS hbase hQ₂ htriv₂ (Or.inr havoid₂)
  have hdExp₁₂ := expandTracks_meet_only_ends hS hQ₁ hQ₂ hd₁₂ (Or.inl havoid₁)
  have hdB₁ : ∀ z ∈ B, z ∈ P₁ → z = c₁ ∨ z = c₂ := by
    intro z hzB hzP
    have hz := hdExpBase₁ z (by rw [hExpandBase]; exact hzB) (by simpa [P₁] using hzP)
    simpa [huc₁, hvc₂] using hz
  have hdB₂ : ∀ z ∈ B, z ∈ P₂ → z = c₁ ∨ z = c₂ := by
    intro z hzB hzP
    have hz := hdExpBase₂ z (by rw [hExpandBase]; exact hzB) (by simpa [P₂] using hzP)
    simpa [huc₁, hvc₂] using hz
  have hdP₁P₂ : ∀ z ∈ P₁, z ∈ P₂ → z = c₁ ∨ z = c₂ := by
    intro z hz₁ hz₂
    have hz := hdExp₁₂ z (by simpa [P₁] using hz₁) (by simpa [P₂] using hz₂)
    simpa [huc₁, hvc₂] using hz
  have hP₁odd : Odd (trackLength P₁) := Nat.not_even_iff_odd.mp (by
    intro heven
    exact hcolne ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hP₁).1 heven))
  have hP₂odd : Odd (trackLength P₂) := Nat.not_even_iff_odd.mp (by
    intro heven
    exact hcolne ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hP₂).1 heven))
  have hP₁three := three_le_trackLength_of_odd_of_nonadj hP₁ hP₁odd hcnadj
  have hP₂three := three_le_trackLength_of_odd_of_nonadj hP₂ hP₂odd hcnadj
  let b₁ : V := lastRungVertex φ P₁ hP₁.1 hP₁two
  let b₂ : V := lastRungVertex φ P₂ hP₂.1 hP₂two
  have hb₁ : b₁ ∈ NSet G H K φ c₂ := by
    refine ⟨lastTrackEdge P₁ hP₁two, lastTrackEdge_mem hP₁.1 hP₁two, ?_, rfl⟩
    exact ⟨lastTrackEdge_mem hP₁.1 hP₁two, lastTrackEdge_contains hP₁ hP₁two⟩
  have hb₂ : b₂ ∈ NSet G H K φ c₂ := by
    refine ⟨lastTrackEdge P₂ hP₂two, lastTrackEdge_mem hP₂.1 hP₂two, ?_, rfl⟩
    exact ⟨lastTrackEdge_mem hP₂.1 hP₂two, lastTrackEdge_contains hP₂ hP₂two⟩
  have hform := threeTracksLineGraphPrism φ hP₁ hP₂ hfrom hP₁two hP₂two hBtwo
    hcne hcnadj hdP₁P₂ (fun z hz₁ hzB => hdB₁ z hzB hz₁)
      (fun z hz₂ hzB => hdB₂ z hzB hz₂)
  rw [ha₁first, ha₂first] at hform
  have hP₁even : Even (pathLength (trackRung φ P₁ hP₁.1)) := by
    obtain ⟨k, hk⟩ := hP₁odd
    refine ⟨k, ?_⟩
    rw [trackRung_pathLength]
    omega
  have hP₂even : Even (pathLength (trackRung φ P₂ hP₂.1)) := by
    obtain ⟨k, hk⟩ := hP₂odd
    refine ⟨k, ?_⟩
    rw [trackRung_pathLength]
    omega
  have hReven : Even (pathLength (trackRung φ B hfrom.1)) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k, ?_⟩
    rw [trackRung_pathLength]
    omega
  refine ⟨b₁, b₂, trackRung φ P₁ hP₁.1, trackRung φ P₂ hP₂.1,
    trackRung φ B hfrom.1, hb₁, hb₂, ?_, hP₁even, hP₂even, hReven, ?_, ?_, ?_,
    trackRung_subset_K φ P₁ hP₁.1, trackRung_subset_K φ P₂ hP₂.1,
    trackRung_subset_K φ B hfrom.1⟩
  · simpa [r₁, r₂, b₁, b₂] using hform
  · rw [trackRung_pathLength]
    omega
  · rw [trackRung_pathLength]
    omega
  · rw [trackRung_pathLength]
    omega

end Workspace.ProofLemmas.Thm75PrismThroughBranch
