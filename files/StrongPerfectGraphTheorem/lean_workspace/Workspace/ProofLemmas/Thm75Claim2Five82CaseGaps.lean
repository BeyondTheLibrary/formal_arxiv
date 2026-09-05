import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.RungReplacementLabelled
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGapPrism
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGapParity
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEnd
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.PathBasics

/-!
# The two geometric inputs of the 5.8.2 rung replacement that are still open

Both remaining gaps of the printed rung-replacement paragraphs of 7.5 claim (2) are collected
here, each with the paper sentence it encodes.  Everything else in the two paragraphs — the
splice, the four replacement inputs, the boundary dictionary, the new appearance and its clique
dictionary — is proved elsewhere in this lane.

* `case_one_parity` is *"and `H'` is bipartite"*, which in case 1 is not supplied by the case
  hypothesis and has to be deduced from `Berge G`.
* `case_one_single_clique_swap` and `shared_end_single_clique_swap` are the two occurrences of
  *"these two prisms are related as in 7.4"*.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance
open Workspace.ProofLemmas.RungReplacementLabelled

/-- **Remaining gap: the replacement path has the parity of the rung it replaces.**

PAPER (proof of 7.5, claim (2), printed p. 37): *"So if in `L(H)` we replace `Rb₁b₂` by `R′` we
obtain another appearance of `J` in `G`, say `L(H′)`."*  An appearance is the line graph of a
**bipartite** subdivision, so the new branch must have the parity of the old one.  In cases 2,
3 and 4 of 5.8.2 the case hypothesis supplies that parity outright; in case 1 it does not, and
the paper leaves it to be read off from `Berge G`.

The argument is one hole.  Because `J` is 3-connected, the edge of `J` carrying the branch is
not a bridge, so after deleting that branch there is still a track from `b₁` to `b₂`; its rung
`LQ` runs from a vertex of `Nb₁ \ {r₁}` to a vertex of `Nb₂ \ {r₂}`.  The boundary condition
`hboundary` says that `R′` meets `LQ` in no vertex and sends exactly one edge to each of its
ends, so `R′` followed by the reverse of `LQ` is a hole of `G`.  Being Berge, `G` has no odd
hole, so `pathLength R′` and `pathLength LQ` have the same parity.  Since `H` is bipartite and
`LQ` and the old rung come from two tracks with the same ends, `LQ` has the parity of the old
rung.

The hypothesis `hne` is needed and is not cosmetic: when the two ends of `R′` coincide (case 3
of 5.8.2) the replacement path is a single vertex anticomplete to the old rung, no hole arises,
and the parity really is not determined. -/
theorem case_one_parity {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
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
    Even (pathLength R') ↔ Even (pathLength (trackRung φ t ht.1)) :=
  Workspace.ProofLemmas.Thm75Claim2Five82CaseGapParity.parity_from_return_track
    G hG hJ K φ happ t b₁ b₂ hb₁ hb₂ ht htf h2 r₁ r₂ hr₁ hr₂ R' r₁' r₂' hR' hne hdisj hboundary

/-- **Remaining gap: the matched prisms of the same-branch case 1.**

PAPER (proof of 7.5, claim (2), printed p. 37): *"There also correspond three tracks in `H′`,
yielding a prism in `L(H′)` … these two prisms are related as in 7.4."*

Here the replaced branch **is** the distinguished branch `Bc₁c₂`, and only the clique at `c₁`
changes: it loses the rung end `r₁` and gains the end `p₁` of the replacement path.

The construction is the one described in the plan for this lane.  For distinct
`x, z ∈ Nc₁ \ {r₁}`, apply 7.1 through the distinguished branch
(`Thm75PrismThroughBranch.thm75PrismThroughBranch`) to the **old** appearance and arrange its
output so that the third path is the distinguished rung itself and the first triangle is
`{r₁, x, z}`.  Replacing that one path by `R′` — legitimate because `R′` meets `K` only inside
the old rung and attaches to the rest of `K` only at `p₁` and `r₂` — gives a prism with the same
opposite triangle and the same other two paths.  Reversing the roles of the two prisms gives the
second `SwapPrisms` instance, because `Nc₁ \ {r₁}` and `((Nc₁ \ {r₁}) ∪ {p₁}) \ {p₁}` are the
same set and `R′` is even of length at least two. -/
theorem case_one_single_clique_swap {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (r₁ r₂ p₁ : V)
    (hr₁ : NSet G H K φ c₁ ∩ {x : V | x ∈ trackRung φ B hbranch.1} = {r₁})
    (hr₂ : NSet G H K φ c₂ ∩ {x : V | x ∈ trackRung φ B hbranch.1} = {r₂})
    (hp₁K : p₁ ∉ K)
    (R' : List V) (hR' : IsPathFrom G R' p₁ r₂)
    (hdisj : ∀ x ∈ R', x ∈ K → x ∈ trackRung φ B hbranch.1)
    (hboundary : ∀ x ∈ R', ∀ y ∈ K, y ∉ trackRung φ B hbranch.1 →
      (G.Adj x y ↔ (x = p₁ ∧ y ∈ NSet G H K φ c₁ \ {r₁}) ∨
        (x = r₂ ∧ y ∈ NSet G H K φ c₂ \ {r₂})))
    (hR'even : Even (pathLength R')) (hR'len : 2 ≤ pathLength R') :
    SingleCliqueSwap G (NSet G H K φ c₁) (NSet G H K φ c₂)
      ((NSet G H K φ c₁ \ {r₁}) ∪ {p₁}) := by
  classical
  have hr₁N : r₁ ∈ NSet G H K φ c₁ := by
    have : r₁ ∈ NSet G H K φ c₁ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := by rw [hr₁]; rfl
    exact this.1
  have hr₂N : r₂ ∈ NSet G H K φ c₂ := by
    have : r₂ ∈ NSet G H K φ c₂ ∩ {v : V | v ∈ trackRung φ B hbranch.1} := by rw [hr₂]; rfl
    exact this.1
  have hp₁N₁ : p₁ ∉ NSet G H K φ c₁ := fun h =>
    hp₁K (Thm75EndgameHelpers.nset_subset_K G H K φ c₁ h)
  have hpair := Workspace.ProofLemmas.Thm75Claim2Five82CaseGapPrism.swap_prism_pair
    G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen r₁ r₂ p₁ hr₁ hr₂ hp₁K
    R' hR' hboundary
  refine ⟨r₁, p₁, r₁, p₁, hr₁N, Or.inr rfl, hr₁N, Or.inr rfl, rfl, ?_, ?_, ?_⟩
  · ext v
    constructor
    · intro hv
      by_cases hvr : v = r₁
      · exact Or.inr hvr
      · exact Or.inl ⟨Or.inl ⟨hv, hvr⟩, fun hc => hp₁N₁ ((show v = p₁ from hc) ▸ hv)⟩
    · rintro (⟨hv, hvp⟩ | hv)
      · rcases hv with h | h
        · exact h.1
        · exact absurd h hvp
      · exact (show v = r₁ from hv) ▸ hr₁N
  · intro x hx z hz hxz _
    obtain ⟨bb, Rg, P₁, P₂, hbb0, hbb1, hbb2, hne01, hne02, hne12, hprism1,
      hevRg, hevP₁, hevP₂, hlRg, hlP₁, hlP₂, hRgfrom, hprism2⟩ := hpair x z hx hz hxz
    exact ⟨bb, Rg, P₁, P₂, R', hbb0 ▸ hr₂N, hbb1, hbb2, hne01, hne02, hne12, hprism1,
      hevRg, hevP₁, hevP₂, hlRg, hlP₁, hlP₂, hbb0 ▸ hR', hprism2⟩
  · intro x hx z hz hxz _
    have hconv : ∀ w : V, w ∈ ((NSet G H K φ c₁ \ {r₁}) ∪ {p₁}) \ {p₁} →
        w ∈ NSet G H K φ c₁ \ {r₁} := by
      rintro w ⟨hw, hwp⟩
      rcases hw with h | h
      · exact h
      · exact absurd h hwp
    obtain ⟨bb, Rg, P₁, P₂, hbb0, hbb1, hbb2, hne01, hne02, hne12, hprism1,
      hevRg, hevP₁, hevP₂, hlRg, hlP₁, hlP₂, hRgfrom, hprism2⟩ :=
      hpair x z (hconv x hx) (hconv z hz) hxz
    exact ⟨bb, R', P₁, P₂, Rg, hbb0 ▸ hr₂N, hbb1, hbb2, hne01, hne02, hne12, hprism2,
      hR'even, hevP₁, hevP₂, hR'len, hlP₁, hlP₂, hbb0 ▸ hRgfrom, hprism1⟩

/-- **Remaining gap: the matched prisms when the replaced branch shares one end with the
distinguished branch.**

PAPER (proof of 7.5, claim (2), printed p. 37): *"Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that
`Rb₁b₂` is incident with at most one of `c₁, c₂`, so these two prisms are related as in 7.4."*

The replaced branch `t` is not the distinguished branch `Bc₁c₂`, but one of its two ends is the
distinguished end `c₁`; `hshared` says which one, and names the rung end `r` that the clique at
`c₁` loses and the vertex `p` that it gains.  The clique at `c₂` and the distinguished rung are
untouched, because a branch different from `Bc₁c₂` cannot be incident with both `c₁` and `c₂`.

The construction applies 7.1 **once in `J`**, prescribing the three initial edges at `c₁`, and
expands the same three `J`-tracks in the old and in the new subdivision.  The replaced branch is
the initial branch of the track that starts with the edge represented by `r`; the other two
tracks avoid it, so their rung paths are literally unchanged under the edge-label dictionary,
and the opposite triangle at `c₂` is unchanged.  For the reverse direction, both subdivisions
still contain the odd distinguished branch of length at least three, so its two ends have
opposite colours and are nonadjacent, and every track between them is odd of length at least
three, giving even rung paths of length at least two. -/
theorem shared_end_single_clique_swap {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W) (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (t : List W) (b₁ b₂ : W) (ht : IsBranch H t) (htf : IsTrackFrom H t b₁ b₂)
    (hne : trackEdges t ≠ trackEdges B)
    (Rt : List V) (hRt : IsPathList G Rt) (hRtset : {x : V | x ∈ Rt} = rungSet G H K φ t)
    (r₁ r₂ s₁ s₂ : V)
    (hr₁ : NSet G H K φ b₁ ∩ {x : V | x ∈ Rt} = {r₁})
    (hr₂ : NSet G H K φ b₂ ∩ {x : V | x ∈ Rt} = {r₂})
    (R' : List V) (hR' : IsPathFrom G R' s₁ s₂)
    (hdisj : ∀ x ∈ R', x ∈ K → x ∈ Rt)
    (hbdry : ∀ x ∈ R', ∀ y ∈ K, y ∉ Rt →
      (G.Adj x y ↔ (x = s₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁}) ∨
        (x = s₂ ∧ y ∈ NSet G H K φ b₂ \ {r₂})))
    (hpar : Even (pathLength R') ↔ Even (pathLength Rt))
    (r p : V) (hpK : p ∉ K)
    (hshared : (c₁ = b₁ ∧ r = r₁ ∧ p = s₁) ∨ (c₁ = b₂ ∧ r = r₂ ∧ p = s₂)) :
    SingleCliqueSwap G (NSet G H K φ c₁) (NSet G H K φ c₂)
      ((NSet G H K φ c₁ \ {r}) ∪ {p}) := by
  classical
  rcases hshared with ⟨hc, hrr, hpp⟩ | ⟨hc, hrr, hpp⟩
  · subst hc; subst hrr; subst hpp
    exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEnd.shared_end_swap_normalized
      G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen t b₂ ht htf hne
      Rt hRt hRtset r r₂ hr₁ hr₂ R' p s₂ hR' hpK hdisj hbdry hpar
  · subst hc; subst hrr; subst hpp
    have ht' : IsBranch H t.reverse := Thm57Claim2Structure.isBranch_reverse ht
    have htf' : IsTrackFrom H t.reverse c₁ b₁ := TrackSlice.isTrackFrom_reverse htf
    have hne' : trackEdges t.reverse ≠ trackEdges B := by
      rw [SubdivisionCounting.trackEdges_reverse]; exact hne
    have hRtset' : {x : V | x ∈ Rt} = rungSet G H K φ t.reverse := by
      rw [hRtset]
      simp only [rungSet, SubdivisionCounting.trackEdges_reverse]
    have hR'' : IsPathFrom G R'.reverse p s₁ := PathBasics.isPathFrom_reverse hR'
    have hdisj' : ∀ x ∈ R'.reverse, x ∈ K → x ∈ Rt := fun x hx =>
      hdisj x (List.mem_reverse.mp hx)
    have hbdry' : ∀ x ∈ R'.reverse, ∀ y ∈ K, y ∉ Rt →
        (G.Adj x y ↔ (x = p ∧ y ∈ NSet G H K φ c₁ \ {r}) ∨
          (x = s₁ ∧ y ∈ NSet G H K φ b₁ \ {r₁})) := by
      intro x hx y hy hyR
      rw [hbdry x (List.mem_reverse.mp hx) y hy hyR]
      tauto
    have hpar' : Even (pathLength R'.reverse) ↔ Even (pathLength Rt) := by
      rw [PathBasics.pathLength_reverse]; exact hpar
    exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEnd.shared_end_swap_normalized
      G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen t.reverse b₁ ht' htf' hne'
      Rt hRt hRtset' r r₁ hr₂ hr₁ R'.reverse p s₁ hR'' hpK hdisj' hbdry' hpar'

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGaps
