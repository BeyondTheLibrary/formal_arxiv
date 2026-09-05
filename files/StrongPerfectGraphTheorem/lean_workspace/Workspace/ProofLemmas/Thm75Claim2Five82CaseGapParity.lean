import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionTrackExpansion
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S07.Thm_7_1

/-!
# The return track of a branch, and the one hole that fixes the case-1 parity

PAPER (proof of 7.5, claim (2), printed p. 37): *"So if in `L(H)` we replace `Rb₁b₂` by `R′` we
obtain another appearance of `J` in `G`."*  An appearance is the line graph of a **bipartite**
subdivision, so the replacement path must have the parity of the rung it replaces.  In case 1 of
5.8.2 that parity is not part of the case hypothesis, and has to come from `Berge G`.

The argument is one hole.  Because `J` is 3-connected, the edge of `J` carrying the branch is
not a bridge: 7.1 supplies a second track of `J` between its ends whose first edge is a
different edge at that end, and expanding it along the subdivision gives a track `LT` of `H`
from `b₁` to `b₂` sharing no edge with the branch.  Its rung `LQ` therefore misses the old rung
entirely, and meets the clique at `bᵢ` in exactly one vertex, the one representing its own end
edge.  The boundary condition on `R′` then says that the only edges between `R′` and `LQ` are
the two that close `R′` followed by the reverse of `LQ` into a cycle, and that cycle is induced.
Being Berge, `G` has no odd hole, so `R′` and `LQ` have lengths of the same parity; and `LQ` has
the parity of the old rung because `H` is bipartite and both tracks join `b₁` to `b₂`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGapParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.SubdivisionTrackExpansion

variable {U W : Type*} {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

/-- Every branch-vertex of a `J`-track survives in the expansion of that track. -/
theorem mem_expandTracks_of_mem (hS : SubdivWitness J H ι T) :
    ∀ p : List U, List.IsChain J.Adj p → ∀ x ∈ p, ι x ∈ expandTracks ι T p := by
  intro p
  induction p with
  | nil => intro _ x hx; simp at hx
  | cons a l ih =>
    cases l with
    | nil =>
      intro _ x hx
      rw [List.mem_singleton] at hx
      subst hx
      simp
    | cons b rest =>
      intro hch x hx
      have hab : J.Adj a b := hch.rel_head
      rw [expandTracks_cons_cons, List.mem_append]
      rcases List.mem_cons.mp hx with rfl | hx'
      · left
        have hA : ((T x b).dropLast).head? = some (ι x) := by
          rw [List.head?_dropLast, if_pos (by have := two_le_track_length hS hab; omega)]
          exact track_head? hS hab
        exact List.mem_of_mem_head? hA
      · exact Or.inr (ih hch.tail x hx')


/-- **A branch of a subdivision of a 3-connected graph has a return track.**

The edge of `J` carrying the branch `t` is not a bridge: by 7.1 there is a second track of `J`
between its ends whose first edge is another edge at the first end, and expanding that track
along the subdivision gives a track `LT` of `H` from `b₁` to `b₂` with at least three vertices
and no edge in common with `t`. -/
theorem exists_return_track [Fintype U] [Fintype W]
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H)
    (t : List W) (b₁ b₂ : W) (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (ht : IsBranch H t) (htf : IsTrackFrom H t b₁ b₂) (h2 : 2 ≤ t.length) :
    ∃ LT : List W, IsTrackFrom H LT b₁ b₂ ∧ 3 ≤ LT.length ∧
      ∀ e ∈ trackEdges LT, e ∉ trackEdges t := by
  classical
  obtain ⟨ι, T, hι, htrackT, hlenT, hrev, hdisjT, hnew, hcover, hedges⟩ := hsub
  have hS : SubdivWitness J H ι T := ⟨hι, htrackT, hlenT, hrev, hdisjT, hnew⟩
  have hdeg : ∀ w : U, 3 ≤ (J.neighborSet w).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨u₀, v₀, hu₀v₀, hEdges, hends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrackT hlenT hrev hdisjT hnew hcover hedges hdeg ht h2 htf hb₁ hb₂
  obtain ⟨u, v, huv, hub, hvb, htT⟩ :
      ∃ u v : U, J.Adj u v ∧ ι u = b₁ ∧ ι v = b₂ ∧ t = T u v := by
    rcases hends with ⟨h1, h2'⟩ | ⟨h1, h2'⟩
    · have hTfrom : IsTrackFrom H (T u₀ v₀) b₁ b₂ := by
        simpa [h1, h2'] using htrackT u₀ v₀ hu₀v₀
      exact ⟨u₀, v₀, hu₀v₀, h1.symm, h2'.symm,
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          htf.1.2.1 hTfrom.1.2.1 htf.2.1 hTfrom.2.1 htf.2.2 hTfrom.2.2 (by rw [hEdges])⟩
    · have hTfrom : IsTrackFrom H (T v₀ u₀) b₁ b₂ := by
        simpa [h1, h2'] using htrackT v₀ u₀ hu₀v₀.symm
      have hEdges' : trackEdges t = trackEdges (T v₀ u₀) := by
        rw [hrev u₀ v₀ hu₀v₀,
          Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
        exact hEdges
      exact ⟨v₀, u₀, hu₀v₀.symm, h1.symm, h2'.symm,
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          htf.1.2.1 hTfrom.1.2.1 htf.2.1 hTfrom.2.1 htf.2.2 hTfrom.2.2 (by rw [hEdges'])⟩
  -- two further edges of `J` at `u`
  have hdu : 3 ≤ (J.neighborSet u).ncard := hdeg u
  obtain ⟨x₁, hx₁⟩ : (J.neighborSet u \ ({v} : Set U)).Nonempty := by
    rw [Set.diff_nonempty]
    intro hcon
    have hle := Set.ncard_le_ncard hcon (Set.toFinite _)
    rw [Set.ncard_singleton] at hle
    omega
  obtain ⟨x₂, hx₂⟩ : (J.neighborSet u \ ({v, x₁} : Set U)).Nonempty := by
    rw [Set.diff_nonempty]
    intro hcon
    have hle := Set.ncard_le_ncard hcon (Set.toFinite _)
    have hpair := Set.ncard_pair (show v ≠ x₁ from fun hc => hx₁.2 (by rw [hc]; rfl))
    omega
  have hux₁ : J.Adj u x₁ := hx₁.1
  have hux₂ : J.Adj u x₂ := hx₂.1
  have hx₁v : x₁ ≠ v := fun hc => hx₁.2 (by rw [hc]; rfl)
  have hx₂v : x₂ ≠ v := fun hc => hx₂.2 (Or.inl hc)
  have hx₁₂ : x₁ ≠ x₂ := fun hc => hx₂.2 (Or.inr (by rw [← hc]; rfl))
  have hec₁ : s(u, x₁) ≠ s(u, v) := fun hc => hx₁v (Sym2.congr_right.mp hc)
  have hec₂ : s(u, x₂) ≠ s(u, v) := fun hc => hx₂v (Sym2.congr_right.mp hc)
  have he₁₂ : s(u, x₁) ≠ s(u, x₂) := fun hc => hx₁₂ (Sym2.congr_right.mp hc)
  obtain ⟨Qb, Q₁, Q₂, hQb, hQ₁, hQ₂, -, -, -, -, hfirst₁, -⟩ :=
    Workspace.Statements.S07.SPGT.thm_7_1 J hJ u v huv (s(u, x₁)) (s(u, x₂))
      hux₁ hux₂ (by simp) (by simp) hec₁ hec₂ he₁₂
  obtain ⟨w₁, rest₁, hQ₁shape, hw₁⟩ := hfirst₁
  have hw₁x : w₁ = x₁ := Sym2.congr_right.mp hw₁
  subst hw₁x
  have hQ₁two : 2 ≤ Q₁.length := by rw [hQ₁shape]; simp
  have havoid : s(u, v) ∉ trackEdges Q₁ := by
    intro he
    have heq := edge_eq_firstTrackEdge hQ₁ hQ₁two he (by simp)
    have hfst : firstTrackEdge Q₁ hQ₁two = s(u, w₁) := by
      simp [firstTrackEdge, hQ₁shape]
    exact hx₁v (Sym2.congr_right.mp (heq.trans hfst)).symm
  have hQ₁chain : List.IsChain J.Adj Q₁ := List.isChain_iff_getElem.mpr hQ₁.1.2.2
  refine ⟨expandTracks ι T Q₁, ?_, ?_, ?_⟩
  · have hh := expandTracks_isTrackFrom hS hQ₁
    simpa [hub, hvb] using hh
  · -- `ι x₁` is an interior vertex of the expansion, so it has at least three vertices
    have hbase : IsTrackFrom J [u, v] u v := by
      refine ⟨⟨by simp, by simp [huv.ne], ?_⟩, rfl, rfl⟩
      intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      simpa using huv
    have hExpandBase : expandTracks ι T [u, v] = t := by
      have hEq := expandTracks_cons_cons_full hS u v [] huv (by simp)
      have hEq' : expandTracks ι T [u, v] = T u v := by simpa using hEq
      exact hEq'.trans htT.symm
    have hLTfrom : IsTrackFrom H (expandTracks ι T Q₁) b₁ b₂ := by
      have hh := expandTracks_isTrackFrom hS hQ₁
      simpa [hub, hvb] using hh
    have hmem : ι w₁ ∈ expandTracks ι T Q₁ :=
      mem_expandTracks_of_mem hS Q₁ hQ₁chain w₁ (by rw [hQ₁shape]; simp)
    have hne₁ : ι w₁ ≠ b₁ := by
      rw [← hub]; exact fun hc => (hux₁.ne') (hι hc)
    have hne₂ : ι w₁ ≠ b₂ := by
      rw [← hvb]; exact fun hc => hx₁v (hι hc)
    have hpos : 0 < (expandTracks ι T Q₁).length :=
      List.length_pos_iff.mpr (expandTracks_ne_nil hS hQ₁chain (by rw [hQ₁shape]; simp))
    have hint : ι w₁ ∈ trackInterior (expandTracks ι T Q₁) := by
      by_contra hcon
      rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
        hmem hcon hpos with hc | hc
      · exact hne₁ (by rw [hc,
          Workspace.ProofLemmas.SubdivisionCounting.track_head hLTfrom hpos])
      · exact hne₂ (by rw [hc,
          Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hLTfrom hpos])
    have hlenint : 0 < (trackInterior (expandTracks ι T Q₁)).length :=
      List.length_pos_iff.mpr (fun hc => by rw [hc] at hint; simp at hint)
    have : (trackInterior (expandTracks ι T Q₁)).length =
        (expandTracks ι T Q₁).length - 2 :=
      Workspace.ProofLemmas.PathBasics.interior_length _
    omega
  · -- the two tracks share no edge
    intro e he hcon
    have hbase : IsTrackFrom J [u, v] u v := by
      refine ⟨⟨by simp, by simp [huv.ne], ?_⟩, rfl, rfl⟩
      intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst hi0
      simpa using huv
    have hExpandBase : expandTracks ι T [u, v] = t := by
      have hEq := expandTracks_cons_cons_full hS u v [] huv (by simp)
      have hEq' : expandTracks ι T [u, v] = T u v := by simpa using hEq
      exact hEq'.trans htT.symm
    have htriv : ∀ y ∈ [u, v], y ∈ Q₁ → y = u ∨ y = v := by
      intro y hy _
      simpa using hy
    have hmeet := expandTracks_meet_only_ends hS hbase hQ₁ htriv (Or.inr havoid)
    have hLTfrom : IsTrackFrom H (expandTracks ι T Q₁) b₁ b₂ := by
      have hh := expandTracks_isTrackFrom hS hQ₁
      simpa [hub, hvb] using hh
    -- both endpoints of `e` lie on `t` and on the expansion, hence are `b₁` and `b₂`
    obtain ⟨i, hi, rfl⟩ := hcon
    have hmt₁ : t[i]'(by omega) ∈ t := List.getElem_mem _
    have hmt₂ : t[i + 1]'hi ∈ t := List.getElem_mem _
    have hmL := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges he
    have hmL₁ : t[i]'(by omega) ∈ expandTracks ι T Q₁ := hmL.1
    have hmL₂ : t[i + 1]'hi ∈ expandTracks ι T Q₁ := hmL.2
    have hb : ∀ y : W, y ∈ t → y ∈ expandTracks ι T Q₁ → y = b₁ ∨ y = b₂ := by
      intro y hy hy'
      have := hmeet y (by rw [hExpandBase]; exact hy) hy'
      rw [hub, hvb] at this
      exact this
    have hne : t[i]'(by omega) ≠ t[i + 1]'hi := by
      intro hc
      have := (List.Nodup.getElem_inj_iff htf.1.2.1).mp hc
      omega
    have hb₁b₂ : b₁ ≠ b₂ := by
      intro hc
      have h0 : t[0]'(by omega) = b₁ :=
        Workspace.ProofLemmas.SubdivisionCounting.track_head htf (by omega)
      have hl : t[t.length - 1]'(by omega) = b₂ :=
        Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast htf (by omega)
      have : t[0]'(by omega) = t[t.length - 1]'(by omega) := by rw [h0, hl, hc]
      have := (List.Nodup.getElem_inj_iff htf.1.2.1).mp this
      omega
    have hEe : s(t[i]'(by omega), t[i + 1]'hi) = s(b₁, b₂) := by
      rcases hb _ hmt₁ hmL₁ with h1 | h1 <;> rcases hb _ hmt₂ hmL₂ with h2' | h2'
      · exact absurd (h1.trans h2'.symm) hne
      · rw [h1, h2']
      · rw [h1, h2']; exact Sym2.eq_swap
      · exact absurd (h1.trans h2'.symm) hne
    -- so the expansion would have exactly two vertices, which it does not
    have heL : s(b₁, b₂) ∈ trackEdges (expandTracks ι T Q₁) := hEe ▸ he
    have hLpos : 0 < (expandTracks ι T Q₁).length :=
      List.length_pos_iff.mpr (expandTracks_ne_nil hS hQ₁chain (by rw [hQ₁shape]; simp))
    have hL2 : 2 ≤ (expandTracks ι T Q₁).length :=
      two_le_expandTracks_length hS hQ₁chain hQ₁two
    have hfst := edge_eq_firstTrackEdge hLTfrom hL2 heL (Sym2.mem_mk_left _ _)
    have hlst := edge_eq_lastTrackEdge hLTfrom hL2 heL (Sym2.mem_mk_right _ _)
    have hfl : firstTrackEdge (expandTracks ι T Q₁) hL2 =
        lastTrackEdge (expandTracks ι T Q₁) hL2 := hfst.symm.trans hlst
    simp only [firstTrackEdge, lastTrackEdge] at hfl
    have h0eq : (expandTracks ι T Q₁)[0]'(by omega) =
        (expandTracks ι T Q₁)[(expandTracks ι T Q₁).length - 2]'(by omega) ∨
        (expandTracks ι T Q₁)[0]'(by omega) =
        (expandTracks ι T Q₁)[(expandTracks ι T Q₁).length - 1]'(by omega) := by
      have := (Sym2.eq_iff).mp hfl
      rcases this with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    have hnd := hLTfrom.1.2.1
    have hL3 : 3 ≤ (expandTracks ι T Q₁).length := by
      have hmem : ι w₁ ∈ expandTracks ι T Q₁ :=
        mem_expandTracks_of_mem hS Q₁ hQ₁chain w₁ (by rw [hQ₁shape]; simp)
      have hne₁ : ι w₁ ≠ b₁ := by
        rw [← hub]; exact fun hc => (hux₁.ne') (hι hc)
      have hne₂ : ι w₁ ≠ b₂ := by
        rw [← hvb]; exact fun hc => hx₁v (hι hc)
      have hint : ι w₁ ∈ trackInterior (expandTracks ι T Q₁) := by
        by_contra hcon2
        rcases Workspace.ProofLemmas.DegenerateK4Tracks.mem_ends_of_notMem_interior
          hmem hcon2 hLpos with hc | hc
        · exact hne₁ (by rw [hc,
            Workspace.ProofLemmas.SubdivisionCounting.track_head hLTfrom hLpos])
        · exact hne₂ (by rw [hc,
            Workspace.ProofLemmas.DegenerateK4Tracks.track_getLast hLTfrom hLpos])
      have hlenint : 0 < (trackInterior (expandTracks ι T Q₁)).length :=
        List.length_pos_iff.mpr (fun hc => by rw [hc] at hint; simp at hint)
      have : (trackInterior (expandTracks ι T Q₁)).length =
          (expandTracks ι T Q₁).length - 2 :=
        Workspace.ProofLemmas.PathBasics.interior_length _
      omega
    rcases h0eq with h1 | h1
    · have := (List.Nodup.getElem_inj_iff hnd).mp h1
      omega
    · have := (List.Nodup.getElem_inj_iff hnd).mp h1
      omega


/-- **The replacement path has the parity of the rung it replaces.**

The return track's rung `LQ` misses the old rung, and meets the clique at `bᵢ` in exactly one
vertex.  So `R′` followed by the reverse of `LQ` is a hole of `G`, which is even because `G` is
Berge, and `LQ` has the parity of the old rung because `H` is bipartite. -/
theorem parity_from_return_track {V : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (hJ : IsKConnected J 3)
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) (happ : IsAppearance G J H K)
    (t : List W) (b₁ b₂ : W) (hb₁ : b₁ ∈ branchVertices H) (hb₂ : b₂ ∈ branchVertices H)
    (ht : IsBranch H t) (htf : IsTrackFrom H t b₁ b₂) (h2 : 2 ≤ t.length)
    (r₁ r₂ : V)
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ trackRung φ t ht.1} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ trackRung φ t ht.1} = {r₂})
    (R' : List V) (r₁' r₂' : V) (hR' : IsPathFrom G R' r₁' r₂') (hne : r₁' ≠ r₂')
    (hdisj : ∀ x ∈ R', x ∈ K → x ∈ trackRung φ t ht.1)
    (hboundary : ∀ x ∈ R', ∀ y ∈ K, y ∉ trackRung φ t ht.1 →
      (G.Adj x y ↔ (x = r₁' ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = r₂' ∧ y ∈ NSet G H K φ b₂ \ {r₂}))) :
    Even (pathLength R') ↔ Even (pathLength (trackRung φ t ht.1)) := by
  classical
  obtain ⟨LT, hLTfrom, hLT3, hLTdisj⟩ :=
    exists_return_track hJ happ.1.1 t b₁ b₂ hb₁ hb₂ ht htf h2
  have hLT2 : 2 ≤ LT.length := by omega
  have hLTeq : trackLength LT = LT.length - 1 := rfl
  have hteq : trackLength t = t.length - 1 := rfl
  have hLTlen : 2 ≤ trackLength LT := by omega
  have hclen : 1 ≤ trackLength t := by omega
  -- the two rung ends of the old branch
  have hfirst : firstRungVertex φ t ht.1 h2 = r₁ := by
    have hmem : firstRungVertex φ t ht.1 h2 ∈
        NSet G H K φ b₁ ∩ {v : V | v ∈ trackRung φ t ht.1} :=
      ⟨⟨firstTrackEdge t h2, firstTrackEdge_mem ht.1 h2,
          ⟨firstTrackEdge_mem ht.1 h2, firstTrackEdge_contains htf h2⟩, rfl⟩,
        firstRungVertex_mem φ ht.1 h2⟩
    rw [hr₁] at hmem
    exact hmem
  have hlast : lastRungVertex φ t ht.1 h2 = r₂ := by
    have hmem : lastRungVertex φ t ht.1 h2 ∈
        NSet G H K φ b₂ ∩ {v : V | v ∈ trackRung φ t ht.1} :=
      ⟨⟨lastTrackEdge t h2, lastTrackEdge_mem ht.1 h2,
          ⟨lastTrackEdge_mem ht.1 h2, lastTrackEdge_contains htf h2⟩, rfl⟩,
        lastRungVertex_mem φ ht.1 h2⟩
    rw [hr₂] at hmem
    exact hmem
  -- the return rung misses the old rung
  have hLQQ : ∀ w ∈ trackRung φ LT hLTfrom.1, w ∉ trackRung φ t ht.1 := by
    intro w hw hwQ
    obtain ⟨e, he, heLT, hwe⟩ := (mem_trackRung_iff φ hLTfrom.1).mp hw
    obtain ⟨f, hf, hft, hwf⟩ := (mem_trackRung_iff φ ht.1).mp hwQ
    have hef : e = f := Thm75EndgameHelpers.phi_inj φ he hf (hwe ▸ hwf)
    exact hLTdisj e heLT (hef ▸ hft)
  have hLQK : ∀ w ∈ trackRung φ LT hLTfrom.1, w ∈ K := trackRung_subset_K φ LT hLTfrom.1
  -- the return rung meets the two cliques in exactly its own two ends
  have hℓ₁ : ∀ w ∈ trackRung φ LT hLTfrom.1,
      (w ∈ NSet G H K φ b₁ ↔ w = firstRungVertex φ LT hLTfrom.1 hLT2) := by
    intro w hw
    obtain ⟨e, he, heLT, hwe⟩ := (mem_trackRung_iff φ hLTfrom.1).mp hw
    constructor
    · rintro ⟨g, hg, hgb, hwg⟩
      have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
      have hbe : b₁ ∈ e := hef ▸ hgb.2
      have := edge_eq_firstTrackEdge hLTfrom hLT2 heLT hbe
      rw [hwe]
      simp only [firstRungVertex]
      exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext this)
    · rintro rfl
      exact ⟨firstTrackEdge LT hLT2, firstTrackEdge_mem hLTfrom.1 hLT2,
        ⟨firstTrackEdge_mem hLTfrom.1 hLT2, firstTrackEdge_contains hLTfrom hLT2⟩, rfl⟩
  have hℓ₂ : ∀ w ∈ trackRung φ LT hLTfrom.1,
      (w ∈ NSet G H K φ b₂ ↔ w = lastRungVertex φ LT hLTfrom.1 hLT2) := by
    intro w hw
    obtain ⟨e, he, heLT, hwe⟩ := (mem_trackRung_iff φ hLTfrom.1).mp hw
    constructor
    · rintro ⟨g, hg, hgb, hwg⟩
      have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
      have hbe : b₂ ∈ e := hef ▸ hgb.2
      have := edge_eq_lastTrackEdge hLTfrom hLT2 heLT hbe
      rw [hwe]
      simp only [lastRungVertex]
      exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext this)
    · rintro rfl
      exact ⟨lastTrackEdge LT hLT2, lastTrackEdge_mem hLTfrom.1 hLT2,
        ⟨lastTrackEdge_mem hLTfrom.1 hLT2, lastTrackEdge_contains hLTfrom hLT2⟩, rfl⟩
  have hLQfrom : IsPathFrom G (trackRung φ LT hLTfrom.1)
      (firstRungVertex φ LT hLTfrom.1 hLT2) (lastRungVertex φ LT hLTfrom.1 hLT2) :=
    trackRung_isPathFrom_ends φ hLTfrom hLT2
  have hℓ₁mem : firstRungVertex φ LT hLTfrom.1 hLT2 ∈ trackRung φ LT hLTfrom.1 :=
    firstRungVertex_mem φ hLTfrom.1 hLT2
  have hℓ₂mem : lastRungVertex φ LT hLTfrom.1 hLT2 ∈ trackRung φ LT hLTfrom.1 :=
    lastRungVertex_mem φ hLTfrom.1 hLT2
  have hℓ₁r : firstRungVertex φ LT hLTfrom.1 hLT2 ≠ r₁ := by
    rw [← hfirst]
    intro hc
    exact hLTdisj (firstTrackEdge LT hLT2) (firstTrackEdge_mem_trackEdges hLT2)
      ((Thm75EndgameHelpers.phi_inj φ (firstTrackEdge_mem hLTfrom.1 hLT2)
        (firstTrackEdge_mem ht.1 h2) hc) ▸ firstTrackEdge_mem_trackEdges h2)
  have hℓ₂r : lastRungVertex φ LT hLTfrom.1 hLT2 ≠ r₂ := by
    rw [← hlast]
    intro hc
    exact hLTdisj (lastTrackEdge LT hLT2) (lastTrackEdge_mem_trackEdges hLT2)
      ((Thm75EndgameHelpers.phi_inj φ (lastTrackEdge_mem hLTfrom.1 hLT2)
        (lastTrackEdge_mem ht.1 h2) hc) ▸ lastTrackEdge_mem_trackEdges h2)
  -- the hole
  have hR'2 : 2 ≤ R'.length := by
    rcases Nat.lt_or_ge R'.length 2 with hlt | hge
    · exfalso
      have h1 : R'.length = 1 := by
        have := Workspace.ProofLemmas.PathBasics.path_length_pos hR'.1
        omega
      obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp h1
      rw [hw] at hR'
      have e1 : w = r₁' := by simpa using hR'.2.1
      have e2 : w = r₂' := by simpa using hR'.2.2
      exact hne (e1.symm.trans e2)
    · exact hge
  have hLQlen : (trackRung φ LT hLTfrom.1).length = trackLength LT :=
    trackRung_length φ LT hLTfrom.1
  have hhole : IsHoleList G (R' ++ (trackRung φ LT hLTfrom.1).reverse) := by
    refine Workspace.ProofLemmas.PathGlue.glue_hole hR'
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hLQfrom) ?_ ?_ ?_
    · intro w hw hcon
      have hwLQ : w ∈ trackRung φ LT hLTfrom.1 := List.mem_reverse.mp hcon
      exact hLQQ w hwLQ (hdisj w hw (hLQK w hwLQ))
    · intro w hw y hy
      have hyLQ : y ∈ trackRung φ LT hLTfrom.1 := List.mem_reverse.mp hy
      rw [hboundary w hw y (hLQK y hyLQ) (hLQQ y hyLQ)]
      constructor
      · rintro (⟨h1, h2'⟩ | ⟨h1, h2'⟩)
        · exact Or.inr ⟨h1, (hℓ₁ y hyLQ).mp h2'.1⟩
        · exact Or.inl ⟨h1, (hℓ₂ y hyLQ).mp h2'.1⟩
      · rintro (⟨h1, h2'⟩ | ⟨h1, h2'⟩)
        · exact Or.inr ⟨h1, (hℓ₂ y hyLQ).mpr h2', by rw [h2']; exact hℓ₂r⟩
        · exact Or.inl ⟨h1, (hℓ₁ y hyLQ).mpr h2', by rw [h2']; exact hℓ₁r⟩
    · simp only [List.length_reverse, hLQlen]
      omega
  have heven := hG.1 _ hhole
  simp only [holeLength, List.length_append, List.length_reverse, hLQlen] at heven
  -- parity of the two tracks
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite happ.1.2
  have hpar : Even (trackLength LT) ↔ Even (trackLength t) :=
    (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hLTfrom).trans
      (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col htf).symm
  have hQlen : pathLength (trackRung φ t ht.1) = trackLength t - 1 :=
    trackRung_pathLength φ t ht.1
  rw [hQlen]
  have hA : (R'.length + trackLength LT) % 2 = 0 := by rwa [Nat.even_iff] at heven
  have hB : trackLength LT % 2 = trackLength t % 2 := by
    rcases Nat.even_or_odd (trackLength LT) with hpe | hpo
    · have hpe' := hpar.mp hpe
      rw [Nat.even_iff] at hpe hpe'
      omega
    · have hpo' : ¬ Even (trackLength t) := fun hc => (Nat.not_even_iff_odd.mpr hpo) (hpar.mpr hc)
      rw [Nat.odd_iff] at hpo
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at hpo'
      omega
  simp only [Nat.even_iff, pathLength]
  omega

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGapParity
