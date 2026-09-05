import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm75Setup
import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.RungReplacementLabelled
import Workspace.ProofLemmas.RungReplacementBranchFacts
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.ThreeTracksLineGraphPrism
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim2Structure
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism

/-!
# The matched prisms when the replaced branch shares one end with the distinguished branch

PAPER (proof of 7.5, claim (2), printed p. 37): *"Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that
`Rb₁b₂` is incident with at most one of `c₁, c₂`, so these two prisms are related as in 7.4."*

The replaced branch `t` is a branch other than the distinguished branch `Bc₁c₂`, but one of its
two ends is the distinguished end `c₁`.  The clique at `c₁` therefore loses the rung end `r` of
`t` and gains the end `p` of the replacement path; the clique at `c₂` and the distinguished rung
are untouched, since a branch different from `Bc₁c₂` cannot be incident with both `c₁` and `c₂`.

This module reduces the required `SingleCliqueSwap` to a **single** geometric statement,
`shared_end_prism_pair`: the matched pair of prisms itself.  Everything else — the choice of
anchor (the distinguished rung end `ρ₁` at `c₁`, which is different from `r` because two
branches share no edge), the two set identities, and the symmetry between the two ways the
replaced branch can be oriented — is proved here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEnd

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.ThreeTracksLineGraphPrism
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance
open Workspace.ProofLemmas.RungReplacementLabelled

/-- **The clique at an end of a branch meets that branch's rung in exactly one vertex**, namely
the vertex representing the branch's end edge at that vertex. -/
theorem nset_inter_trackRung {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {q : List W} {a b : W} (hq : IsTrackFrom H q a b)
    (h2 : 2 ≤ q.length) :
    NSet G H K φ a ∩ {x : V | x ∈ trackRung φ q hq.1} =
      {firstRungVertex φ q hq.1 h2} := by
  ext w
  constructor
  · rintro ⟨⟨g, hg, hga, hwg⟩, hwQ⟩
    obtain ⟨e, he, heq, hwe⟩ := (mem_trackRung_iff φ hq.1).mp hwQ
    have hef : e = g := Thm75EndgameHelpers.phi_inj φ he hg (hwe ▸ hwg)
    have hae : a ∈ e := hef ▸ hga.2
    have hfst := edge_eq_firstTrackEdge hq h2 heq hae
    show w = _
    rw [hwe]
    simp only [firstRungVertex]
    exact congrArg (fun y : H.edgeSet => (φ y : V)) (Subtype.ext hfst)
  · intro hw
    have hw' : w = firstRungVertex φ q hq.1 h2 := hw
    subst hw'
    exact ⟨⟨firstTrackEdge q h2, firstTrackEdge_mem hq.1 h2,
        ⟨firstTrackEdge_mem hq.1 h2, firstTrackEdge_contains hq h2⟩, rfl⟩,
      firstRungVertex_mem φ hq.1 h2⟩


/-- **Remaining gap: the matched prisms of the shared-end case.**

PAPER (proof of 7.5, claim (2), printed p. 37): *"There also correspond three tracks in `H′`,
yielding a prism in `L(H′)` … Since `Rb₁b₂ ≠ Rc₁c₂`, it follows that `Rb₁b₂` is incident with at
most one of `c₁, c₂`, so these two prisms are related as in 7.4."*

The replaced branch `t` runs from the distinguished end `c₁` to some other branch vertex `b₂`,
its rung `Rt` has the end `r` at `c₁`, and the replacement path `R′` has the end `p` at `c₁`.
The triple `{r, x, z}` contains the distinguished rung end `ρ₁` at `c₁`, so 7.1 applies **once
in `J`** with the three prescribed initial edges at `c₁`: the edge represented by `r`, the edge
represented by the other of `x, z`, and the edge represented by `ρ₁`.  Expanding those three
`J`-tracks in the old subdivision gives the first prism, with its third path the distinguished
rung; expanding the same three `J`-tracks in the subdivision produced by the replacement gives
the second one.  Only the first path changes, because only the track that begins with the
branch `t` meets `t` at all, and the opposite triangle sits at `c₂`, which the replaced branch
does not touch.

This is the one geometric statement of the 5.8.2 rung replacement that is still open. -/
theorem shared_end_prism_pair {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
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
    (hanchor : x = firstRungVertex φ B hfrom.1 hB2 ∨ z = firstRungVertex φ B hfrom.1 hB2) :
    ∃ (bb : Fin 3 → V) (P₁ P₂ P₃ P₁' : List V),
      bb 0 ∈ NSet G H K φ c₂ ∧ bb 1 ∈ NSet G H K φ c₂ ∧ bb 2 ∈ NSet G H K φ c₂ ∧
      bb 0 ≠ bb 1 ∧ bb 0 ≠ bb 2 ∧ bb 1 ≠ bb 2 ∧
      FormPrism G ![r, x, z] bb P₁ P₂ P₃ ∧
      Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃) ∧
      2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧ 2 ≤ pathLength P₃ ∧
      Even (pathLength P₁') ∧ 2 ≤ pathLength P₁' ∧
      IsPathFrom G P₁ r (bb 0) ∧ IsPathFrom G P₁' p (bb 0) ∧
      FormPrism G ![p, x, z] bb P₁' P₂ P₃ := by
  rcases hanchor with hax | haz
  · -- the distinguished rung end is the second triangle vertex: run the core lemma with the
    -- two non-`r` vertices exchanged, then exchange the second and third paths back
    obtain ⟨bb, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hn01, hn02, hn12, hpr1,
      he1, he2, he3, hl1, hl2, hl3, he1', hl1', hpath1, hpath1', hpr2⟩ :=
      Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism.shared_end_prism_pair_core
        G J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen t b₂ ht htf hne
        Rt hRt hRtset r r₂ hr hr₂ R' p s₂ hR' hpK hdisj hbdry hpar hB2
        z x hz hx (Ne.symm hxz) hax
    exact ⟨![bb 0, bb 2, bb 1], P₁, P₃, P₂, P₁', by simpa using hb0, by simpa using hb2,
      by simpa using hb1, by simpa using hn02, by simpa using hn01,
      by simpa using (Ne.symm hn12),
      by simpa using
        Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism.formPrism_swap hpr1,
      he1, he3, he2, hl1, hl3, hl2, he1', hl1', by simpa using hpath1,
      by simpa using hpath1',
      by simpa using
        Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism.formPrism_swap hpr2⟩
  · exact Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEndPrism.shared_end_prism_pair_core
      G J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen t b₂ ht htf hne
      Rt hRt hRtset r r₂ hr hr₂ R' p s₂ hR' hpK hdisj hbdry hpar hB2
      x z hx hz hxz haz

/-- **The shared-end clique swap, with the replaced branch oriented away from `c₁`.** -/
theorem shared_end_swap_normalized {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
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
    (hpar : Even (pathLength R') ↔ Even (pathLength Rt)) :
    SingleCliqueSwap G (NSet G H K φ c₁) (NSet G H K φ c₂)
      ((NSet G H K φ c₁ \ {r}) ∪ {p}) := by
  classical
  have hB2 : 2 ≤ B.length := by simp only [trackLength] at hlen; omega
  set ρ₁ : V := firstRungVertex φ B hfrom.1 hB2 with hρ₁def
  have hρ₁ : NSet G H K φ c₁ ∩ {y : V | y ∈ trackRung φ B hfrom.1} = {ρ₁} :=
    nset_inter_trackRung φ hfrom hB2
  have hρ₁N : ρ₁ ∈ NSet G H K φ c₁ := by
    have : ρ₁ ∈ NSet G H K φ c₁ ∩ {y : V | y ∈ trackRung φ B hfrom.1} := by rw [hρ₁]; rfl
    exact this.1
  have hrmem : r ∈ NSet G H K φ c₁ ∩ {y : V | y ∈ Rt} := by rw [hr]; rfl
  have hrN : r ∈ NSet G H K φ c₁ := hrmem.1
  -- the replaced branch has at least one edge
  have ht2 : 2 ≤ t.length := by
    have hmem : r ∈ rungSet G H K φ t := by rw [← hRtset]; exact hrmem.2
    obtain ⟨e, -, ⟨i, hi, -⟩, -⟩ := hmem
    omega
  -- the two branches share no edge, so their rung ends at `c₁` differ
  have hrρ : r ≠ ρ₁ := by
    intro hc
    obtain ⟨e, he, het, hre⟩ : r ∈ rungSet G H K φ t := by rw [← hRtset]; exact hrmem.2
    have hρmem : ρ₁ ∈ trackRung φ B hfrom.1 := by
      have : ρ₁ ∈ NSet G H K φ c₁ ∩ {y : V | y ∈ trackRung φ B hfrom.1} := by rw [hρ₁]; rfl
      exact this.2
    obtain ⟨f, hf, hfB, hρf⟩ := (mem_trackRung_iff φ hfrom.1).mp hρmem
    have hef : e = f := Thm75EndgameHelpers.phi_inj φ he hf (by rw [← hre, hc, hρf])
    exact Workspace.ProofLemmas.RungReplacementBranchFacts.trackEdges_disjoint_of_ne
      hJ happ.1.1 hbranch hB2 ht ht2 hne e het (hef ▸ hfB)
  have hpN₁ : p ∉ NSet G H K φ c₁ := fun hc =>
    hpK (Thm75EndgameHelpers.nset_subset_K G H K φ c₁ hc)
  have hρ₁N' : ρ₁ ∈ (NSet G H K φ c₁ \ {r}) ∪ {p} := Or.inl ⟨hρ₁N, fun hc => hrρ hc.symm⟩
  refine ⟨r, p, ρ₁, ρ₁, hrN, Or.inr rfl, hρ₁N, hρ₁N', rfl, ?_, ?_, ?_⟩
  · ext w
    constructor
    · intro hw
      by_cases hwr : w = r
      · exact Or.inr hwr
      · exact Or.inl ⟨Or.inl ⟨hw, hwr⟩, fun hc => hpN₁ ((show w = p from hc) ▸ hw)⟩
    · rintro (⟨hw, hwp⟩ | hw)
      · rcases hw with h | h
        · exact h.1
        · exact absurd h hwp
      · exact (show w = r from hw) ▸ hrN
  · intro y hy w hw hyw hanch
    have hanchor : y = ρ₁ ∨ w = ρ₁ := by
      rcases hanch with h | h | h
      · exact absurd h hrρ
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨bb, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hn01, hn02, hn12, hpr1,
      he1, he2, he3, hl1, hl2, hl3, he1', hl1', hpath1, hpath1', hpr2⟩ :=
      shared_end_prism_pair G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen
        t b₂ ht htf hne Rt hRt hRtset r r₂ hr hr₂ R' p s₂ hR' hpK hdisj hbdry hpar hB2
        y w hy hw hyw hanchor
    exact ⟨bb, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hn01, hn02, hn12, hpr1,
      he1, he2, he3, hl1, hl2, hl3, hpath1', hpr2⟩
  · intro y hy w hw hyw hanch
    have hconv : ∀ v : V, v ∈ ((NSet G H K φ c₁ \ {r}) ∪ {p}) \ {p} →
        v ∈ NSet G H K φ c₁ \ {r} := by
      rintro v ⟨hv, hvp⟩
      rcases hv with h | h
      · exact h
      · exact absurd h hvp
    have hanchor : y = ρ₁ ∨ w = ρ₁ := by
      rcases hanch with h | h | h
      · exact absurd h (fun hc => hpN₁ (hc ▸ hρ₁N))
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨bb, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hn01, hn02, hn12, hpr1,
      he1, he2, he3, hl1, hl2, hl3, he1', hl1', hpath1, hpath1', hpr2⟩ :=
      shared_end_prism_pair G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen
        t b₂ ht htf hne Rt hRt hRtset r r₂ hr hr₂ R' p s₂ hR' hpK hdisj hbdry hpar hB2
        y w (hconv y hy) (hconv w hw) hyw hanchor
    exact ⟨bb, P₁', P₂, P₃, P₁, hb0, hb1, hb2, hn01, hn02, hn12, hpr2,
      he1', he2, he3, hl1', hl2, hl3, hpath1, hpr1⟩

end Workspace.ProofLemmas.Thm75Claim2Five82CaseGapSharedEnd
