import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
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
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.RungReplacementLabelled
import Workspace.ProofLemmas.RungReplacementRungLength
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndSplit
import Workspace.Statements.S07.Thm_7_1

/-!
# The matched prisms when the replaced branch shares one end with the distinguished branch

PAPER (proof of 7.5, claim (2), printed p. 37): *"There also correspond three tracks in `H′`,
yielding a prism in `L(H′)` … Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that `Rb₁b₂` is incident with at
most one of `c₁, c₂`, so these two prisms are related as in 7.4."*

The replaced branch `t` runs from the distinguished end `c₁` to a second branch vertex `b₂`,
which is not `c₂` because two different branches cannot join the same pair of branch vertices.
So the picture is this.  The triangle at `c₁` of the prism we need is `{r, x, z}`, where `r` is
the end of the replaced rung at `c₁` and one of `x, z` is the end `ρ₁` of the distinguished rung
at `c₁`.  Apply 7.1 **once in `J`**, at the edge of `J` carrying `Bc₁c₂` and with the two
prescribed further edges at `c₁`: the one carrying `t` and the one representing the third
triangle vertex.  Expanding the two resulting `J`-tracks along the subdivision gives, together
with `Bc₁c₂` itself, three tracks of `H` from `c₁` to `c₂` meeting only at their ends, so their
rungs form a prism.

The track through `t` begins with the whole of `t` and then continues to `c₂`; its rung is
therefore the rung of `t` followed by the rung of the continuation
(`Thm75Claim2Five82CaseGapSharedEndSplit.trackRung_append`).  Replacing that first half by the
replacement path `R′` gives the second prism: `R′` attaches to the rest of the appearance only
at `p`, into `Nc₁ \ {r}`, and at `s₂`, into `Nb₂ \ {r₂}`, and the continuation meets `Nb₂`
exactly in its own first vertex.  The other two paths and the opposite triangle are untouched,
because neither of their tracks meets `t` anywhere except at `c₁`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.SubdivisionCompose
open Workspace.ProofLemmas.SubdivisionTrackExpansion
open Workspace.ProofLemmas.RungReplacementLabelled
open Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndSplit

/-- Exchanging the second and third paths of a prism gives a prism again. -/
theorem formPrism_swap {V : Type*} {G : SimpleGraph V} {a b : Fin 3 → V} {P₁ P₂ P₃ : List V}
    (h : FormPrism G a b P₁ P₂ P₃) :
    FormPrism G ![a 0, a 2, a 1] ![b 0, b 2, b 1] P₁ P₃ P₂ := by
  obtain ⟨hA, hB, hAB, hq1, hq2, hq3, e12, e13, e23⟩ := h
  refine Workspace.ProofLemmas.PrismBasics.formPrism_of_data
    (hA 0 2 (by decide)) (hA 0 1 (by decide)) ((hA 1 2 (by decide)).symm)
    (hB 0 2 (by decide)) (hB 0 1 (by decide)) ((hB 1 2 (by decide)).symm)
    (hAB 0 0) (hAB 0 2) (hAB 0 1) (hAB 2 0) (hAB 2 2) (hAB 2 1)
    (hAB 1 0) (hAB 1 2) (hAB 1 1) hq1 hq3 hq2 e13 e12 ?_
  intro u hu v hv
  rw [SimpleGraph.adj_comm, e23 v hv u hu]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inl ⟨h2, h1⟩
    · exact Or.inr ⟨h2, h1⟩

/-- **The matched prisms of the shared-end case, with the distinguished rung end in the third
slot of the triangle.**  This is the geometric heart; the general statement follows by
exchanging the two non-`r` triangle vertices. -/
theorem shared_end_prism_pair_core {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (t : List W) (b₂ : W) (ht : IsBranch H t) (htf : IsTrackFrom H t c₁ b₂)
    (hne : trackEdges t ≠ trackEdges B)
    (Rt : List V) (hRt : IsPathList G Rt) (hRtset : {x : V | x ∈ Rt} = rungSet G H K φ t)
    (r r₂ : V)
    (hr : NSet G H K φ c₁ ∩ {x : V | x ∈ Rt} = {r})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ Rt} = {r₂})
    (R' : List V) (p s₂ : V) (hR' : IsPathFrom G R' p s₂) (hpK : p ∉ K)
    (hdisj : ∀ x ∈ R', x ∈ K → x ∈ Rt)
    (hbdry : ∀ x ∈ R', ∀ y ∈ K, y ∉ Rt →
      (G.Adj x y ↔ (x = p ∧ y ∈ NSet G H K φ c₁ \ {r}) ∨
        (x = s₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})))
    (hpar : Even (pathLength R') ↔ Even (pathLength Rt))
    (hB2 : 2 ≤ B.length)
    (x z : V) (hx : x ∈ NSet G H K φ c₁ \ {r}) (hz : z ∈ NSet G H K φ c₁ \ {r}) (hxz : x ≠ z)
    (hanchor : z = firstRungVertex φ B hfrom.1 hB2) :
    ∃ (bb : Fin 3 → V) (P₁ P₂ P₃ P₁' : List V),
      bb 0 ∈ NSet G H K φ c₂ ∧ bb 1 ∈ NSet G H K φ c₂ ∧ bb 2 ∈ NSet G H K φ c₂ ∧
      bb 0 ≠ bb 1 ∧ bb 0 ≠ bb 2 ∧ bb 1 ≠ bb 2 ∧
      FormPrism G ![r, x, z] bb P₁ P₂ P₃ ∧
      Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃) ∧
      2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧ 2 ≤ pathLength P₃ ∧
      Even (pathLength P₁') ∧ 2 ≤ pathLength P₁' ∧
      IsPathFrom G P₁ r (bb 0) ∧ IsPathFrom G P₁' p (bb 0) ∧
      FormPrism G ![p, x, z] bb P₁' P₂ P₃ := by
  classical
  subst hanchor
  -- ## Setting up the subdivision
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisjT, hnew, hcover, hedges⟩ := happ.1.1
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlenT, hrev, hdisjT, hnew⟩
  have hdeg : ∀ a : U, 3 ≤ (J.neighborSet a).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hlen2 : 2 ≤ trackLength B := by omega
  obtain ⟨hcne, hc₁branch, hc₂branch, hcnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂
      hbranch hfrom hlen2
  -- the replaced branch has an edge, and its ends are branch vertices
  have hrmem : r ∈ NSet G H K φ c₁ ∩ {y : V | y ∈ Rt} := by rw [hr]; exact rfl
  have hrRt : r ∈ rungSet G H K φ t := by rw [← hRtset]; exact hrmem.2
  have ht2 : 2 ≤ t.length := by
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := hrRt
    omega
  obtain ⟨-, hb₂branch⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices J hJ H happ.1.1
      t c₁ b₂ ht htf (by simp only [trackLength]; omega)
  -- the rung of `t`, as an ordered path, and the identification of `Rt` with it
  have hRtTr : {y : V | y ∈ Rt} = {y : V | y ∈ trackRung φ t ht.1} :=
    hRtset.trans (Workspace.ProofLemmas.RungReplacementRungLength.rungSet_eq_trackRung φ t ht.1)
  have hrfirst : firstRungVertex φ t ht.1 ht2 = r := by
    have hmem : firstRungVertex φ t ht.1 ht2 ∈ NSet G H K φ c₁ ∩ {y : V | y ∈ Rt} := by
      refine ⟨⟨firstTrackEdge t ht2, firstTrackEdge_mem ht.1 ht2,
        ⟨firstTrackEdge_mem ht.1 ht2, firstTrackEdge_contains htf ht2⟩, rfl⟩, ?_⟩
      rw [hRtTr]
      exact firstRungVertex_mem φ ht.1 ht2
    rw [hr] at hmem
    exact hmem
  have hr₂last : lastRungVertex φ t ht.1 ht2 = r₂ := by
    have hmem : lastRungVertex φ t ht.1 ht2 ∈ NSet G H K φ b₂ ∩ {y : V | y ∈ Rt} := by
      refine ⟨⟨lastTrackEdge t ht2, lastTrackEdge_mem ht.1 ht2,
        ⟨lastTrackEdge_mem ht.1 ht2, lastTrackEdge_contains htf ht2⟩, rfl⟩, ?_⟩
      rw [hRtTr]
      exact lastRungVertex_mem φ ht.1 ht2
    rw [hr₂] at hmem
    exact hmem
  -- ## Naming the two branches inside the subdivision
  obtain ⟨u₀, v₀, hu₀v₀, hBedges, hends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlenT hrev hdisjT hnew hcover hedges hdeg hbranch hB2 hfrom
      hc₁branch hc₂branch
  obtain ⟨u, v, huv, huc₁, hvc₂, hBT⟩ :
      ∃ u v : U, J.Adj u v ∧ ι u = c₁ ∧ ι v = c₂ ∧ B = T u v := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hTfrom : IsTrackFrom H (T u₀ v₀) c₁ c₂ := by
        simpa [h1, h2] using htrack u₀ v₀ hu₀v₀
      exact ⟨u₀, v₀, hu₀v₀, h1.symm, h2.symm,
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          hfrom.1.2.1 hTfrom.1.2.1 hfrom.2.1 hTfrom.2.1 hfrom.2.2 hTfrom.2.2 (by rw [hBedges])⟩
    · have hTfrom : IsTrackFrom H (T v₀ u₀) c₁ c₂ := by
        simpa [h1, h2] using htrack v₀ u₀ hu₀v₀.symm
      have hBedges' : trackEdges B = trackEdges (T v₀ u₀) := by
        rw [hrev u₀ v₀ hu₀v₀, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
        exact hBedges
      exact ⟨v₀, u₀, hu₀v₀.symm, h1.symm, h2.symm,
        Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
          hfrom.1.2.1 hTfrom.1.2.1 hfrom.2.1 hTfrom.2.1 hfrom.2.2 hTfrom.2.2 (by rw [hBedges'])⟩
  obtain ⟨u₁, w₀, hu₁w₀, htedges, htends⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_and_ends
      hι htrack hlenT hrev hdisjT hnew hcover hedges hdeg ht ht2 htf
      hc₁branch hb₂branch
  obtain ⟨w, huw, hwb₂, htT⟩ :
      ∃ b : U, J.Adj u b ∧ ι b = b₂ ∧ t = T u b := by
    obtain ⟨a, b, hab, ha, hb, hT⟩ :
        ∃ a b : U, J.Adj a b ∧ ι a = c₁ ∧ ι b = b₂ ∧ t = T a b := by
      rcases htends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hTfrom : IsTrackFrom H (T u₁ w₀) c₁ b₂ := by
          simpa [h1, h2] using htrack u₁ w₀ hu₁w₀
        exact ⟨u₁, w₀, hu₁w₀, h1.symm, h2.symm,
          Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
            htf.1.2.1 hTfrom.1.2.1 htf.2.1 hTfrom.2.1 htf.2.2 hTfrom.2.2 (by rw [htedges])⟩
      · have hTfrom : IsTrackFrom H (T w₀ u₁) c₁ b₂ := by
          simpa [h1, h2] using htrack w₀ u₁ hu₁w₀.symm
        have htedges' : trackEdges t = trackEdges (T w₀ u₁) := by
          rw [hrev u₁ w₀ hu₁w₀, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
          exact htedges
        exact ⟨w₀, u₁, hu₁w₀.symm, h1.symm, h2.symm,
          Workspace.ProofLemmas.Thm82BranchDelta.eq_of_trackEdges_subset
            htf.1.2.1 hTfrom.1.2.1 htf.2.1 hTfrom.2.1 htf.2.2 hTfrom.2.2 (by rw [htedges'])⟩
    have hau : a = u := hι (by rw [ha, huc₁])
    rw [hau] at hab hT
    exact ⟨b, hab, hb, hT⟩
  -- the two branches leave `c₁` along different edges of `J`
  have hwv : w ≠ v := by
    intro hc
    subst hc
    exact hne (by rw [htT, hBT])
  have hb₂c₂ : b₂ ≠ c₂ := by
    rw [← hwb₂, ← hvc₂]
    exact fun hc => hwv (hι hc)
  have hc₁b₂ : c₁ ≠ b₂ := by
    rw [← huc₁, ← hwb₂]
    exact fun hc => huw.ne (hι hc)
  -- ## The third edge of `J` at `u`, coming from the third triangle vertex `x`
  obtain ⟨e₀, he₀E, he₀inc, hxeq⟩ := hx.1
  have hue₀ : ι u ∈ e₀ := by rw [huc₁]; exact he₀inc.2
  obtain ⟨y, huy, he₀T⟩ := edge_at_embedded_vertex hS hedges he₀E hue₀
  have hyv : y ≠ v := by
    intro hc
    subst hc
    have he₀B : e₀ ∈ trackEdges B := by rw [hBT]; exact he₀T
    have heq := edge_eq_firstTrackEdge hfrom hB2 he₀B he₀inc.2
    exact hxz (by
      rw [hxeq]
      simp only [firstRungVertex]
      exact congrArg (fun q : H.edgeSet => (φ q : V)) (Subtype.ext heq))
  have hyw : y ≠ w := by
    intro hc
    subst hc
    have he₀t : e₀ ∈ trackEdges t := by rw [htT]; exact he₀T
    have heq := edge_eq_firstTrackEdge htf ht2 he₀t he₀inc.2
    refine hx.2 ?_
    show x = r
    rw [← hrfirst, hxeq]
    simp only [firstRungVertex]
    exact congrArg (fun q : H.edgeSet => (φ q : V)) (Subtype.ext heq)
  -- ## 7.1 in `J`
  have hew : s(u, w) ≠ s(u, v) := fun hc => hwv (Sym2.congr_right.mp hc)
  have hey : s(u, y) ≠ s(u, v) := fun hc => hyv (Sym2.congr_right.mp hc)
  have hewy : s(u, w) ≠ s(u, y) := fun hc => hyw (Sym2.congr_right.mp hc).symm
  obtain ⟨-, Qt, Qo, -, hQt, hQo, -, -, hdto, -, hfirstt, hfirsto⟩ :=
    Workspace.Statements.S07.SPGT.thm_7_1 J hJ u v huv (s(u, w)) (s(u, y))
      huw huy (by simp) (by simp) hew hey hewy
  obtain ⟨w₁, restt, hQtshape, hw₁⟩ := hfirstt
  obtain ⟨y₁, resto, hQoshape, hy₁⟩ := hfirsto
  rw [show w₁ = w from Sym2.congr_right.mp hw₁] at hQtshape
  rw [show y₁ = y from Sym2.congr_right.mp hy₁] at hQoshape
  have hQt2 : 2 ≤ Qt.length := by rw [hQtshape]; simp
  have hQo2 : 2 ≤ Qo.length := by rw [hQoshape]; simp
  have havoidt : s(u, v) ∉ trackEdges Qt := by
    intro he
    have heq := edge_eq_firstTrackEdge hQt hQt2 he (by simp)
    have hfst : firstTrackEdge Qt hQt2 = s(u, w) := by simp [firstTrackEdge, hQtshape]
    exact hwv (Sym2.congr_right.mp (heq.trans hfst)).symm
  have havoido : s(u, v) ∉ trackEdges Qo := by
    intro he
    have heq := edge_eq_firstTrackEdge hQo hQo2 he (by simp)
    have hfst : firstTrackEdge Qo hQo2 = s(u, y) := by simp [firstTrackEdge, hQoshape]
    exact hyv (Sym2.congr_right.mp (heq.trans hfst)).symm
  have hQtchain : List.IsChain J.Adj Qt := List.isChain_iff_getElem.mpr hQt.1.2.2
  have hQochain : List.IsChain J.Adj Qo := List.isChain_iff_getElem.mpr hQo.1.2.2
  -- ## The three tracks of `H`
  set LT : List W := expandTracks ι T Qt with hLTdef
  set OT : List W := expandTracks ι T Qo with hOTdef
  have hLT : IsTrackFrom H LT c₁ c₂ := by
    have hh := expandTracks_isTrackFrom hS hQt
    simpa [hLTdef, huc₁, hvc₂] using hh
  have hOT : IsTrackFrom H OT c₁ c₂ := by
    have hh := expandTracks_isTrackFrom hS hQo
    simpa [hOTdef, huc₁, hvc₂] using hh
  have hLT2 : 2 ≤ LT.length := two_le_expandTracks_length hS hQtchain hQt2
  have hOT2 : 2 ≤ OT.length := two_le_expandTracks_length hS hQochain hQo2
  have hbase : IsTrackFrom J [u, v] u v := by
    refine ⟨⟨by simp, by simp [huv.ne], ?_⟩, rfl, rfl⟩
    intro i hi
    have hi0 : i = 0 := by simp at hi; omega
    subst hi0
    simpa using huv
  have hExpandBase : expandTracks ι T [u, v] = B := by
    have hEq := expandTracks_cons_cons_full hS u v [] huv (by simp)
    have hEq' : expandTracks ι T [u, v] = T u v := by simpa using hEq
    exact hEq'.trans hBT.symm
  have htrivt : ∀ q ∈ [u, v], q ∈ Qt → q = u ∨ q = v := by intro q hq _; simpa using hq
  have htrivo : ∀ q ∈ [u, v], q ∈ Qo → q = u ∨ q = v := by intro q hq _; simpa using hq
  have hdLTB : ∀ q ∈ LT, q ∈ B → q = c₁ ∨ q = c₂ := by
    intro q h1 h2
    have hh := expandTracks_meet_only_ends hS hbase hQt htrivt (Or.inr havoidt) q
      (by rw [hExpandBase]; exact h2) h1
    simpa [huc₁, hvc₂] using hh
  have hdOTB : ∀ q ∈ OT, q ∈ B → q = c₁ ∨ q = c₂ := by
    intro q h1 h2
    have hh := expandTracks_meet_only_ends hS hbase hQo htrivo (Or.inr havoido) q
      (by rw [hExpandBase]; exact h2) h1
    simpa [huc₁, hvc₂] using hh
  have hdLTOT : ∀ q ∈ LT, q ∈ OT → q = c₁ ∨ q = c₂ := by
    intro q h1 h2
    have hh := expandTracks_meet_only_ends hS hQt hQo hdto (Or.inl havoidt) q h1 h2
    simpa [huc₁, hvc₂] using hh
  -- ## The first rung vertices of the three tracks
  have hQttail : List.IsChain J.Adj (w :: restt) := by
    rw [hQtshape] at hQtchain; exact hQtchain.tail
  have hQotail : List.IsChain J.Adj (y :: resto) := by
    rw [hQoshape] at hQochain; exact hQochain.tail
  have hfirsttEdge : firstTrackEdge t ht2 ∈ trackEdges LT := by
    rw [hLTdef, hQtshape]
    exact trackEdges_expandTracks_prefix hS huw hQttail
      (by rw [← htT]; exact firstTrackEdge_mem_trackEdges ht2)
  have hLTfirst : firstRungVertex φ LT hLT.1 hLT2 = r := by
    have heq := edge_eq_firstTrackEdge hLT hLT2 hfirsttEdge (firstTrackEdge_contains htf ht2)
    rw [← hrfirst]
    simp only [firstRungVertex]
    exact congrArg (fun q : H.edgeSet => (φ q : V)) (Subtype.ext heq.symm)
  have he₀OT : e₀ ∈ trackEdges OT := by
    rw [hOTdef, hQoshape]
    exact trackEdges_expandTracks_prefix hS huy hQotail he₀T
  have hOTfirst : firstRungVertex φ OT hOT.1 hOT2 = x := by
    have heq := edge_eq_firstTrackEdge hOT hOT2 he₀OT he₀inc.2
    rw [hxeq]
    simp only [firstRungVertex]
    exact congrArg (fun q : H.edgeSet => (φ q : V)) (Subtype.ext heq.symm)
  -- ## The prism from the three tracks
  have hform := threeTracksLineGraphPrism φ hLT hOT hfrom hLT2 hOT2 hB2 hcne hcnadj
    hdLTOT hdLTB (fun q h1 h2 => hdOTB q h1 h2)
  rw [hLTfirst, hOTfirst] at hform
  -- ## Parities and lengths
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite happ.1.2
  have hcolne : col c₁ ≠ col c₂ := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr hodd)
      ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hfrom).2 heq)
  have hoddOf : ∀ (q : List W), IsTrackFrom H q c₁ c₂ → Odd (trackLength q) := by
    intro q hq
    refine Nat.not_even_iff_odd.mp (fun heven => hcolne ?_)
    exact (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hq).1 heven
  have hLTodd : Odd (trackLength LT) := hoddOf LT hLT
  have hOTodd : Odd (trackLength OT) := hoddOf OT hOT
  have hLT3 := three_le_trackLength_of_odd_of_nonadj hLT hLTodd hcnadj
  have hOT3 := three_le_trackLength_of_odd_of_nonadj hOT hOTodd hcnadj
  have hevenOf : ∀ (q : List W) (hq : IsTrackList H q), Odd (trackLength q) →
      Even (pathLength (trackRung φ q hq)) := by
    intro q hq hqo
    obtain ⟨k, hk⟩ := hqo
    exact ⟨k, by rw [trackRung_pathLength]; omega⟩
  have hP₁even : Even (pathLength (trackRung φ LT hLT.1)) := hevenOf LT hLT.1 hLTodd
  have hP₂even : Even (pathLength (trackRung φ OT hOT.1)) := hevenOf OT hOT.1 hOTodd
  have hP₃even : Even (pathLength (trackRung φ B hfrom.1)) := hevenOf B hfrom.1 hodd
  have hP₁len : 2 ≤ pathLength (trackRung φ LT hLT.1) := by
    rw [trackRung_pathLength]; omega
  have hP₂len : 2 ≤ pathLength (trackRung φ OT hOT.1) := by
    rw [trackRung_pathLength]; omega
  have hP₃len : 2 ≤ pathLength (trackRung φ B hfrom.1) := by
    rw [trackRung_pathLength]; omega
  -- ## Splitting the first track at `b₂`
  obtain ⟨M, hMdef⟩ : ∃ M : List W, M = expandTracks ι T (w :: restt) := ⟨_, rfl⟩
  have hMtrack : IsTrackFrom H M b₂ c₂ := by
    have hh := expandTracks_isTrackFrom hS (isTrackFrom_tail (hQtshape ▸ hQt))
    rw [hMdef]
    simpa [hwb₂, hvc₂] using hh
  have hMhead : M.head? = some b₂ := hMtrack.2.1
  obtain ⟨M', hM'⟩ : ∃ M' : List W, M = b₂ :: M' := ⟨M.tail, (List.cons_head?_tail hMhead).symm⟩
  have hLTsplit : LT = t ++ M' := by
    rw [hLTdef, hQtshape, expandTracks_cons_cons_full hS u w restt huw hQttail, ← htT,
      ← hMdef, hM']
    simp
  have hMtrack' : IsTrackFrom H (b₂ :: M') b₂ c₂ := hM' ▸ hMtrack
  have hM2 : 2 ≤ (b₂ :: M').length := by
    have : b₂ ≠ c₂ := hb₂c₂
    rcases M'.eq_nil_or_concat with hnil | ⟨l, a, hla⟩
    · exfalso
      apply this
      have := hMtrack'.2.2
      rw [hnil] at this
      simpa using this
    · rw [hla]; simp
  -- the rung of the first track splits accordingly
  have hsplit : trackRung φ LT hLT.1
      = trackRung φ t ht.1 ++ trackRung φ (b₂ :: M') hMtrack'.1 := by
    rw [trackRung_congr φ hLT.1 (hLTsplit ▸ hLT.1) hLTsplit]
    exact trackRung_append φ ht.1 hMtrack'.1 _ htf.2.2
  set S : List V := trackRung φ (b₂ :: M') hMtrack'.1 with hSdef
  -- ## The continuation `S` and its interaction with everything else
  have hLTnd : LT.Nodup := hLT.1.2.1
  have hdisjtM' : ∀ q ∈ t, q ∉ M' := by
    have hdd := (List.nodup_append.mp (hLTsplit ▸ hLTnd)).2.2
    intro q hq hq'
    exact hdd q hq q hq' rfl
  have hMt : ∀ q ∈ (b₂ :: M'), q ∈ t → q = b₂ := by
    intro q hq hqt
    rcases List.mem_cons.mp hq with h | h
    · exact h
    · exact absurd h (hdisjtM' q hqt)
  have hedgeMt : ∀ e ∈ trackEdges (b₂ :: M'), e ∉ trackEdges t := by
    rintro e ⟨i, hi, rfl⟩ hcon
    have h1 : (b₂ :: M')[i]'(by omega) ∈ t :=
      Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hcon |>.1
    have h2 : (b₂ :: M')[i + 1]'hi ∈ t :=
      Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hcon |>.2
    have e1 := hMt _ (List.getElem_mem _) h1
    have e2 := hMt _ (List.getElem_mem _) h2
    have : (b₂ :: M')[i]'(by omega) = (b₂ :: M')[i + 1]'hi := by rw [e1, e2]
    have := (List.Nodup.getElem_inj_iff hMtrack'.1.2.1).mp this
    omega
  have hSRt : ∀ ww ∈ S, ww ∉ Rt := by
    intro ww hww hcon
    have hww' : ww ∈ trackRung φ t ht.1 := by
      have : ww ∈ {q : V | q ∈ Rt} := hcon
      rw [hRtTr] at this
      exact this
    exact trackRung_disjoint φ hMtrack'.1 ht.1 hedgeMt ww hww hww'
  have hSK : ∀ ww ∈ S, ww ∈ K := trackRung_subset_K φ _ hMtrack'.1
  have hc₁M : c₁ ∉ (b₂ :: M') := by
    intro hcon
    have hc₁t : c₁ ∈ t := List.mem_of_mem_head? htf.2.1
    exact hc₁b₂ (hMt c₁ hcon hc₁t)
  have hSNc₁ : ∀ ww ∈ S, ww ∉ NSet G H K φ c₁ :=
    notMem_nset_of_notMem_track φ hMtrack'.1 hc₁M
  set m₁ : V := firstRungVertex φ (b₂ :: M') hMtrack'.1 hM2 with hm₁def
  set ll : V := lastRungVertex φ (b₂ :: M') hMtrack'.1 hM2 with hlldef
  have hSpath : IsPathFrom G S m₁ ll := trackRung_isPathFrom_ends φ hMtrack' hM2
  have hSNb₂ : ∀ ww ∈ S, (ww ∈ NSet G H K φ b₂ ↔ ww = m₁) :=
    mem_nset_trackRung_iff φ hMtrack' hM2
  have hm₁S : m₁ ∈ S := firstRungVertex_mem φ hMtrack'.1 hM2
  have hllS : ll ∈ S := lastRungVertex_mem φ hMtrack'.1 hM2
  have hm₁r₂ : m₁ ≠ r₂ := by
    intro hc
    refine hSRt m₁ hm₁S ?_
    rw [hc]
    have hmem : r₂ ∈ NSet G H K φ b₂ ∩ {q : V | q ∈ Rt} := by rw [hr₂]; exact rfl
    exact hmem.2
  -- ## The other two tracks avoid the replaced branch
  have hc₂t : c₂ ∉ t := by
    intro hcon
    rw [htT] at hcon
    have hnotint : c₂ ∉ trackInterior (T u w) := fun hi => hnew u w huw c₂ hi ⟨v, hvc₂⟩
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (htrack u w huw).2.1 (htrack u w huw).2.2 hcon hnotint with h | h
    · exact hcne (by rw [← huc₁, ← h])
    · exact hb₂c₂ (by rw [← hwb₂, ← h])
  have hb₂B : b₂ ∉ B := by
    intro hcon
    rw [hBT] at hcon
    have hnotint : b₂ ∉ trackInterior (T u v) := fun hi => hnew u v huv b₂ hi ⟨w, hwb₂⟩
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
      (htrack u v huv).2.1 (htrack u v huv).2.2 hcon hnotint with h | h
    · exact hc₁b₂ (by rw [← huc₁, ← h])
    · exact hb₂c₂ (by rw [← hvc₂, ← h])
  have htLT : ∀ q ∈ t, q ∈ LT := by
    intro q hq; rw [hLTsplit]; exact List.mem_append_left _ hq
  have hOTt : ∀ q ∈ OT, q ∈ t → q = c₁ := by
    intro q h1 h2
    rcases hdLTOT q (htLT q h2) h1 with h | h
    · exact h
    · exact absurd (h ▸ h2) hc₂t
  have hb₂OT : b₂ ∉ OT := by
    intro hcon
    exact hc₁b₂ (hOTt b₂ hcon (List.mem_of_mem_getLast? htf.2.2)).symm
  have hedgeOTt : ∀ e ∈ trackEdges OT, e ∉ trackEdges t := by
    rintro e ⟨i, hi, rfl⟩ hcon
    have h1 : OT[i]'(by omega) ∈ t :=
      (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hcon).1
    have h2 : OT[i + 1]'hi ∈ t :=
      (Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges hcon).2
    have e1 := hOTt _ (List.getElem_mem _) h1
    have e2 := hOTt _ (List.getElem_mem _) h2
    have heq : OT[i]'(by omega) = OT[i + 1]'hi := by rw [e1, e2]
    have := (List.Nodup.getElem_inj_iff hOT.1.2.1).mp heq
    omega
  have hedgeBt : ∀ e ∈ trackEdges B, e ∉ trackEdges t := by
    intro e he hcon
    exact Workspace.ProofLemmas.RungReplacementBranchFacts.trackEdges_disjoint_of_ne
      hJ happ.1.1 hbranch hB2 ht ht2 hne e hcon he
  -- rungs of the other two tracks miss the old rung
  have hnotRt : ∀ (q : List W) (hq : IsTrackList H q),
      (∀ e ∈ trackEdges q, e ∉ trackEdges t) → ∀ ww ∈ trackRung φ q hq, ww ∉ Rt := by
    intro q hq hqd ww hww hcon
    have hww' : ww ∈ trackRung φ t ht.1 := by
      have hmem : ww ∈ {a : V | a ∈ Rt} := hcon
      rw [hRtTr] at hmem
      exact hmem
    exact trackRung_disjoint φ hq ht.1 hqd ww hww hww'
  have hP₂Rt : ∀ ww ∈ trackRung φ OT hOT.1, ww ∉ Rt := hnotRt OT hOT.1 hedgeOTt
  have hP₃Rt : ∀ ww ∈ trackRung φ B hfrom.1, ww ∉ Rt := hnotRt B hfrom.1 hedgeBt
  have hP₂Nb₂ : ∀ ww ∈ trackRung φ OT hOT.1, ww ∉ NSet G H K φ b₂ :=
    notMem_nset_of_notMem_track φ hOT.1 hb₂OT
  have hP₃Nb₂ : ∀ ww ∈ trackRung φ B hfrom.1, ww ∉ NSet G H K φ b₂ :=
    notMem_nset_of_notMem_track φ hfrom.1 hb₂B
  have hP₂Nc₁ : ∀ ww ∈ trackRung φ OT hOT.1, (ww ∈ NSet G H K φ c₁ ↔ ww = x) := by
    intro ww hww
    rw [mem_nset_trackRung_iff φ hOT hOT2 ww hww, hOTfirst]
  have hP₃Nc₁ : ∀ ww ∈ trackRung φ B hfrom.1,
      (ww ∈ NSet G H K φ c₁ ↔ ww = firstRungVertex φ B hfrom.1 hB2) :=
    mem_nset_trackRung_iff φ hfrom hB2
  -- ## Unpacking the old prism
  obtain ⟨hA, hBt, hAB, hq1, hq2, hq3, e12, e13, e23⟩ := hform
  set β0 : V := lastRungVertex φ LT hLT.1 hLT2 with hβ0def
  set β1 : V := lastRungVertex φ OT hOT.1 hOT2 with hβ1def
  set β2 : V := lastRungVertex φ B hfrom.1 hB2 with hβ2def
  have hq1' : IsPathFrom G (trackRung φ LT hLT.1) r β0 := by simpa using hq1
  have hq2' : IsPathFrom G (trackRung φ OT hOT.1) x β1 := by simpa using hq2
  have hq3' : IsPathFrom G (trackRung φ B hfrom.1) (firstRungVertex φ B hfrom.1 hB2) β2 := by
    simpa using hq3
  have E12 : ∀ a ∈ trackRung φ LT hLT.1, ∀ b ∈ trackRung φ OT hOT.1,
      (G.Adj a b ↔ (a = r ∧ b = x) ∨ (a = β0 ∧ b = β1)) := by simpa using e12
  have E13 : ∀ a ∈ trackRung φ LT hLT.1, ∀ b ∈ trackRung φ B hfrom.1,
      (G.Adj a b ↔ (a = r ∧ b = firstRungVertex φ B hfrom.1 hB2) ∨ (a = β0 ∧ b = β2)) := by
    simpa using e13
  have hβ0N : β0 ∈ NSet G H K φ c₂ :=
    ⟨lastTrackEdge LT hLT2, lastTrackEdge_mem hLT.1 hLT2,
      ⟨lastTrackEdge_mem hLT.1 hLT2, lastTrackEdge_contains hLT hLT2⟩, rfl⟩
  have hβ1N : β1 ∈ NSet G H K φ c₂ :=
    ⟨lastTrackEdge OT hOT2, lastTrackEdge_mem hOT.1 hOT2,
      ⟨lastTrackEdge_mem hOT.1 hOT2, lastTrackEdge_contains hOT hOT2⟩, rfl⟩
  have hβ2N : β2 ∈ NSet G H K φ c₂ :=
    ⟨lastTrackEdge B hB2, lastTrackEdge_mem hfrom.1 hB2,
      ⟨lastTrackEdge_mem hfrom.1 hB2, lastTrackEdge_contains hfrom hB2⟩, rfl⟩
  -- ## The end of the first path is the end of the continuation
  have hSne : S ≠ [] := Workspace.ProofLemmas.PathBasics.path_ne_nil hSpath.1
  have hβ0ll : β0 = ll := by
    have h1 : (trackRung φ LT hLT.1).getLast? = some β0 := hq1'.2.2
    rw [hsplit, List.getLast?_append_of_ne_nil _ hSne, hSpath.2.2] at h1
    exact (Option.some_injective _ h1).symm
  have hβ0S : β0 ∈ S := by rw [hβ0ll]; exact hllS
  have hβ0Rt : β0 ∉ Rt := hSRt β0 hβ0S
  -- ## The replacement path glues onto the continuation
  have hxK : x ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₁ hx.1
  have hzK : firstRungVertex φ B hfrom.1 hB2 ∈ K :=
    Thm75EndgameHelpers.nset_subset_K G H K φ c₁ hz.1
  have hoffRt : ∀ ww ∈ NSet G H K φ c₁, ww ≠ r → ww ∉ Rt := by
    intro ww hw hwr hcon
    have hmem : ww ∈ NSet G H K φ c₁ ∩ {q : V | q ∈ Rt} := ⟨hw, hcon⟩
    rw [hr] at hmem
    exact hwr hmem
  have hpR' : p ∈ R' := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR').1
  have hpx : G.Adj p x :=
    (hbdry p hpR' x hxK (hoffRt x hx.1 hx.2)).mpr (Or.inl ⟨rfl, hx⟩)
  have hpz : G.Adj p (firstRungVertex φ B hfrom.1 hB2) :=
    (hbdry p hpR' _ hzK (hoffRt _ hz.1 hz.2)).mpr (Or.inl ⟨rfl, hz⟩)
  have hdisjR'S : ∀ q ∈ R', q ∉ S := by
    intro q hq hqS
    exact hSRt q hqS (hdisj q hq (hSK q hqS))
  have hcrossR'S : ∀ a ∈ R', ∀ vv ∈ S, (G.Adj a vv ↔ (a = s₂ ∧ vv = m₁)) := by
    intro a ha vv hv
    rw [hbdry a ha vv (hSK vv hv) (hSRt vv hv)]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd h2.1 (hSNc₁ vv hv)
      · exact ⟨h1, (hSNb₂ vv hv).mp h2.1⟩
    · rintro ⟨h1, h2⟩
      exact Or.inr ⟨h1, (hSNb₂ vv hv).mpr h2, by rw [h2]; exact hm₁r₂⟩
  have hP₁'path : IsPathFrom G (R' ++ S) p β0 := by
    rw [hβ0ll]
    exact Workspace.ProofLemmas.PathGlue.glue_path hR' hSpath hdisjR'S hcrossR'S
  -- ## Parity and length of the new path
  have hRtlen : Rt.length = trackLength t :=
    Workspace.ProofLemmas.RungReplacementRungLength.rung_length_eq_trackLength φ t ht.1
      (by simp only [trackLength]; omega) Rt hRt hRtset
  have htrlen : (trackRung φ t ht.1).length = trackLength t := trackRung_length φ t ht.1
  have hP₁len' : (trackRung φ LT hLT.1).length = trackLength t + S.length := by
    rw [hsplit, List.length_append, htrlen]
  have hSlenpos : 1 ≤ S.length := List.length_pos_iff.mpr hSne
  have hR'pos : 1 ≤ R'.length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hR'.1
  have htlpos : 1 ≤ trackLength t := by simp only [trackLength]; omega
  have hRtpos : 1 ≤ Rt.length := by omega
  have hE1 : (trackRung φ LT hLT.1).length % 2 = 1 := by
    have := hP₁even
    rw [Nat.even_iff] at this
    simp only [pathLength] at this
    have hpos : 1 ≤ (trackRung φ LT hLT.1).length := by omega
    omega
  have hEp : R'.length % 2 = Rt.length % 2 := by
    rcases Nat.even_or_odd (pathLength R') with hev | hod
    · have h2 := hpar.mp hev
      rw [Nat.even_iff] at hev h2
      simp only [pathLength] at hev h2
      omega
    · have h2 : ¬ Even (pathLength Rt) := fun hc => (Nat.not_even_iff_odd.mpr hod) (hpar.mpr hc)
      rw [Nat.not_even_iff_odd, Nat.odd_iff] at h2
      rw [Nat.odd_iff] at hod
      simp only [pathLength] at hod h2
      omega
  have hnewlen : (R' ++ S).length = R'.length + S.length := List.length_append
  have hP₁'even : Even (pathLength (R' ++ S)) := by
    rw [Nat.even_iff]
    simp only [pathLength, hnewlen]
    omega
  have hP₁'len : 2 ≤ pathLength (R' ++ S) := by
    have hev := hP₁'even
    rw [Nat.even_iff] at hev
    simp only [pathLength, hnewlen] at hev ⊢
    omega
  -- ## Assembling the two prisms
  have hSsub : ∀ a ∈ S, a ∈ trackRung φ LT hLT.1 := by
    intro a ha
    rw [hsplit]
    exact List.mem_append_right _ ha
  have hpne : ∀ ww : V, ww ∈ K → p ≠ ww := fun ww hw hc => hpK (hc ▸ hw)
  have hβ0K : β0 ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hβ0N
  have hβ1K : β1 ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hβ1N
  have hβ2K : β2 ∈ K := Thm75EndgameHelpers.nset_subset_K G H K φ c₂ hβ2N
  have hnotβ0 : ∀ a ∈ R', a ≠ β0 := by
    intro a ha hc
    exact hβ0Rt (hc ▸ hdisj a ha (hc ▸ hβ0K))
  have hnewE12 : ∀ a ∈ R' ++ S, ∀ b ∈ trackRung φ OT hOT.1,
      (G.Adj a b ↔ (a = p ∧ b = x) ∨ (a = β0 ∧ b = β1)) := by
    intro a ha b hb
    rcases List.mem_append.mp ha with ha' | ha'
    · rw [hbdry a ha' b (trackRung_subset_K φ OT hOT.1 b hb) (hP₂Rt b hb)]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₂Nc₁ b hb).mp h2.1⟩
        · exact absurd h2.1 (hP₂Nb₂ b hb)
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₂Nc₁ b hb).mpr h2, by rw [h2]; exact hx.2⟩
        · exact absurd h1 (hnotβ0 a ha')
    · rw [E12 a (hSsub a ha') b hb]
      have har : a ≠ r := fun hc => hSRt a ha' (hc ▸ hrmem.2)
      have hap : a ≠ p := fun hc => hpK (hc ▸ hSK a ha')
      constructor
      · rintro (⟨h1, -⟩ | h1)
        · exact absurd h1 har
        · exact Or.inr h1
      · rintro (⟨h1, -⟩ | h1)
        · exact absurd h1 hap
        · exact Or.inr h1
  have hnewE13 : ∀ a ∈ R' ++ S, ∀ b ∈ trackRung φ B hfrom.1,
      (G.Adj a b ↔ (a = p ∧ b = firstRungVertex φ B hfrom.1 hB2) ∨ (a = β0 ∧ b = β2)) := by
    intro a ha b hb
    rcases List.mem_append.mp ha with ha' | ha'
    · rw [hbdry a ha' b (trackRung_subset_K φ B hfrom.1 b hb) (hP₃Rt b hb)]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₃Nc₁ b hb).mp h2.1⟩
        · exact absurd h2.1 (hP₃Nb₂ b hb)
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inl ⟨h1, (hP₃Nc₁ b hb).mpr h2, by rw [h2]; exact hz.2⟩
        · exact absurd h1 (hnotβ0 a ha')
    · rw [E13 a (hSsub a ha') b hb]
      have har : a ≠ r := fun hc => hSRt a ha' (hc ▸ hrmem.2)
      have hap : a ≠ p := fun hc => hpK (hc ▸ hSK a ha')
      constructor
      · rintro (⟨h1, -⟩ | h1)
        · exact absurd h1 har
        · exact Or.inr h1
      · rintro (⟨h1, -⟩ | h1)
        · exact absurd h1 hap
        · exact Or.inr h1
  refine ⟨![β0, β1, β2], trackRung φ LT hLT.1, trackRung φ OT hOT.1, trackRung φ B hfrom.1,
    R' ++ S, hβ0N, hβ1N, hβ2N, ?_, ?_, ?_, ⟨hA, hBt, hAB, hq1, hq2, hq3, e12, e13, e23⟩,
    hP₁even, hP₂even, hP₃even, hP₁len, hP₂len, hP₃len, hP₁'even, hP₁'len,
    by simpa using hq1', by simpa using hP₁'path, ?_⟩
  · simpa using (hBt 0 1 (by decide)).ne
  · simpa using (hBt 0 2 (by decide)).ne
  · simpa using (hBt 1 2 (by decide)).ne
  · refine Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      hpx hpz (by simpa using hA 1 2 (by decide))
      (by simpa using hBt 0 1 (by decide)) (by simpa using hBt 0 2 (by decide))
      (by simpa using hBt 1 2 (by decide))
      (hpne β0 hβ0K) (hpne β1 hβ1K) (hpne β2 hβ2K)
      (by simpa using hAB 1 0) (by simpa using hAB 1 1) (by simpa using hAB 1 2)
      (by simpa using hAB 2 0) (by simpa using hAB 2 1) (by simpa using hAB 2 2)
      hP₁'path hq2' hq3' hnewE12 hnewE13 (by simpa using e23)

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism
