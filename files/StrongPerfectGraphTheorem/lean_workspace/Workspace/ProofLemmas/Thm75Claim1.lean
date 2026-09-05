import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75PrismThroughBranch
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm75DominantOutsideLineGraph
import Workspace.ProofLemmas.Thm75DominanceTriangles
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.Statements.S07.Thm_7_3

/-!
# 7.5, claim (1)

PAPER (proof of 7.5, printed p. 35):

*"(1) For `i = 1, 2`, at most one vertex of `Nci` is not in `X`.*

*For let `a₁, a₂` be any two distinct vertices in `Nc₁ \ {r₁}`; we shall show that at most one of
`a₁, a₂, r₁` is not in `X`.  By 7.1, there are two paths `Q₁, Q₂` of `H` between `c₁` and `c₂`,
such that `Q₁, Q₂, Bc₁c₂` are vertex-disjoint except for their ends, and for `i = 1, 2`, `aᵢ` is
the first edge of `Qᵢ`.  Let `bᵢ` be the other end-edge of `Qᵢ`.  Both `Q₁` and `Q₂` have odd
length, since `Bc₁c₂` is odd and `H` is bipartite; and they have length `≥ 3` since `c₁, c₂` are
nonadjacent (for they are the ends of a branch of length `> 1`.)  Hence there are two paths
`P₁, P₂` of `L(H)` from `Nc₁` to `Nc₂`, such that `P₁, P₂, Rc₁c₂` are vertex-disjoint and form a
prism, and `Pᵢ` is from `aᵢ` to `bᵢ`.  Now `Bc₁c₂` is odd and therefore `Rc₁c₂` is even, and
similarly `P₁` and `P₂` are even.  By hypothesis, each member of `Y` is adjacent to at least two
vertices of the triangle `{a₁, a₂, r₁}` and to two vertices of the triangle `{b₁, b₂, r₂}`.  By
7.3 it follows that `X` contains at least two members of `{a₁, a₂, r₁}`.  This proves (1)."*

`X` is *"the set of all `Y`-complete vertices in `G`"*, so "at most one vertex of `Nci` is not in
`X`" is `(Nci \ X).Subsingleton`.

Cited: **7.1** (three internally disjoint tracks of a 3-connected `J` through prescribed first
edges) and **7.3** (a `Y` all of whose members are major for a long prism saturates the prism).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup

private theorem isBranch_reverse {W : Type*} {H : SimpleGraph W} {q : List W}
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

private theorem two_missing_contradicts_saturation {V : Type*} [Finite V]
    {a b c x z : V} {X : Set V}
    (hsat : 2 ≤ (({a, b, c} : Set V) ∩ X).ncard)
    (hx : x ∈ ({a, b, c} : Set V)) (hz : z ∈ ({a, b, c} : Set V))
    (hxz : x ≠ z) (hxX : x ∉ X) (hzX : z ∉ X) : False := by
  classical
  have hpairsub : ({x, z} : Set V) ⊆ ({a, b, c} : Set V) := by
    rintro u (rfl | rfl)
    · exact hx
    · exact hz
  have hdiff := Set.ncard_diff hpairsub
  have hpaircard := Set.ncard_pair hxz
  have hbc := Set.ncard_insert_le b ({c} : Set V)
  have habc := Set.ncard_insert_le a ({b, c} : Set V)
  have hrestcard : (({a, b, c} : Set V) \ {x, z}).ncard ≤ 1 := by
    simp only [Set.ncard_singleton] at hbc
    omega
  have hsub : ({a, b, c} : Set V) ∩ X ⊆ ({a, b, c} : Set V) \ {x, z} := by
    rintro u ⟨hu, huX⟩
    refine ⟨hu, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hux
      exact hxX (hux ▸ huX)
    · intro huz
      exact hzX (huz ▸ huX)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

/-- **7.5, claim (1)**: *"For `i = 1, 2`, at most one vertex of `Nci` is not in `X`."* -/
theorem thm75Claim1 {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) :
    (NSet G H K φ c₁ \ {x : V | VertexComplete G x Y}).Subsingleton ∧
      (NSet G H K φ c₂ \ {x : V | VertexComplete G x Y}).Subsingleton := by
  classical
  have side : ∀ (D : List W) (d₁ d₂ : W),
      IsBranch H D → IsTrackFrom H D d₁ d₂ → Odd (trackLength D) →
      3 ≤ trackLength D →
      (∀ y ∈ Y, IsDominantFor G (NSet G H K φ d₁) (NSet G H K φ d₂) y) →
      (NSet G H K φ d₁ \ {x : V | VertexComplete G x Y}).Subsingleton := by
    intro D d₁ d₂ hD hDf hDodd hDlen hdom
    obtain ⟨hdne, hd₁, hd₂, -⟩ :=
      Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H happ.1.1 D d₁ d₂ hD hDf (by omega)
    obtain ⟨r₁, r₂, hr₁, hr₂, _hr₁R, _hr₂R, hprisms⟩ :=
      Workspace.ProofLemmas.Thm75PrismThroughBranch.thm75PrismThroughBranch
        G hG J hJ H K φ happ D d₁ d₂ hD hDf hDodd hDlen
    have hYoutside : ∀ y ∈ Y, y ∉ K := by
      intro y hy
      exact Workspace.ProofLemmas.Thm75DominantOutsideLineGraph.thm75DominantOutsideLineGraph
        G J hJ H K φ happ D d₁ d₂ hD hDf hDlen y (hdom y hy)
    rintro x ⟨hxN, hxX⟩ z ⟨hzN, hzX⟩
    by_contra hxz
    have hextra (u : V) (huN : u ∈ NSet G H K φ d₁) (hur : u ≠ r₁) :
        ∃ w ∈ NSet G H K φ d₁, w ≠ r₁ ∧ w ≠ u := by
      by_contra hno
      have hsub : NSet G H K φ d₁ ⊆ ({r₁, u} : Set V) := by
        intro w hw
        by_cases hwr : w = r₁
        · exact Or.inl hwr
        by_cases hwu : w = u
        · exact Or.inr hwu
        · exact (hno ⟨w, hw, hwr, hwu⟩).elim
      have hncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hthree := Thm75DominanceTriangles.three_le_nset_ncard G H K φ d₁ hd₁
      rw [Set.ncard_pair (Ne.symm hur)] at hncard
      omega
    obtain ⟨a₁, a₂, ha₁, ha₂, ha₁r, ha₂r, ha₁a₂, hxtri, hztri⟩ :
        ∃ a₁ a₂ : V,
          a₁ ∈ NSet G H K φ d₁ ∧ a₂ ∈ NSet G H K φ d₁ ∧
          a₁ ≠ r₁ ∧ a₂ ≠ r₁ ∧ a₁ ≠ a₂ ∧
          x ∈ ({a₁, a₂, r₁} : Set V) ∧ z ∈ ({a₁, a₂, r₁} : Set V) := by
      by_cases hxr : x = r₁
      · have hzr : z ≠ r₁ := by
          intro h
          exact hxz (hxr.trans h.symm)
        obtain ⟨w, hwN, hwr, hwz⟩ := hextra z hzN hzr
        exact ⟨z, w, hzN, hwN, hzr, hwr, Ne.symm hwz, by simp [hxr], by simp⟩
      · by_cases hzr : z = r₁
        · obtain ⟨w, hwN, hwr, hwx⟩ := hextra x hxN hxr
          exact ⟨x, w, hxN, hwN, hxr, hwr, Ne.symm hwx, by simp, by simp [hzr]⟩
        · exact ⟨x, z, hxN, hzN, hxr, hzr, hxz, by simp, by simp⟩
    obtain ⟨b₁, b₂, P₁, P₂, R, hb₁, hb₂, hform,
        hP₁even, hP₂even, hReven, hP₁len, hP₂len, hRlen,
        hP₁K, hP₂K, hRK⟩ :=
      hprisms a₁ a₂ ha₁ ha₂ ha₁r ha₂r ha₁a₂
    have hP₁out : ∀ v ∈ P₁, v ∉ Y := by
      intro v hv hvY
      exact hYoutside v hvY (hP₁K v hv)
    have hP₂out : ∀ v ∈ P₂, v ∉ Y := by
      intro v hv hvY
      exact hYoutside v hvY (hP₂K v hv)
    have hRout : ∀ v ∈ R, v ∉ Y := by
      intro v hv hvY
      exact hYoutside v hvY (hRK v hv)
    have hmajor : ∀ y ∈ Y, MajorForPrism G ![a₁, a₂, r₁] ![b₁, b₂, r₂] y := by
      intro y hy
      have htri := (Thm75DominanceTriangles.isDominantFor_iff_triangles
        φ hd₁ hd₂ y).mp (hdom y hy)
      unfold MajorForPrism SaturatesPrism
      constructor
      · simpa using htri.1 a₁ ha₁ a₂ ha₂ r₁ hr₁
          ha₁a₂ ha₁r ha₂r
      · have hb₁b₂ : b₁ ≠ b₂ := (hform.2.1 0 1 (by decide)).ne
        have hb₁r₂ : b₁ ≠ r₂ := (hform.2.1 0 2 (by decide)).ne
        have hb₂r₂ : b₂ ≠ r₂ := (hform.2.1 1 2 (by decide)).ne
        simpa using htri.2 b₁ hb₁ b₂ hb₂ r₂ hr₂
          hb₁b₂ hb₁r₂ hb₂r₂
    have hsat := Workspace.Statements.S07.SPGT.thm_7_3
      G hG Y hYanti ![a₁, a₂, r₁] ![b₁, b₂, r₂] P₁ P₂ R hform
      hP₁out hP₂out hRout (by omega) (by omega) (by omega) hmajor
    exact two_missing_contradicts_saturation hsat.1 hxtri hztri hxz hxX hzX
  refine ⟨side B c₁ c₂ hbranch hfrom hodd hlen hYdom, ?_⟩
  have hbranchRev : IsBranch H B.reverse := isBranch_reverse hbranch
  have hfromRev : IsTrackFrom H B.reverse c₂ c₁ :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom
  have hoddRev : Odd (trackLength B.reverse) := by
    simpa [trackLength] using hodd
  have hlenRev : 3 ≤ trackLength B.reverse := by
    simpa [trackLength] using hlen
  apply side B.reverse c₂ c₁ hbranchRev hfromRev hoddRev hlenRev
  intro y hy
  exact ⟨(hYdom y hy).2, (hYdom y hy).1⟩

end Workspace.ProofLemmas.Thm75Claim1
