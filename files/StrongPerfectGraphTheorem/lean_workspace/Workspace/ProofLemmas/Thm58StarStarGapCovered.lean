import Workspace.ProofLemmas.Thm58StarStarTracks
import Workspace.ProofLemmas.Thm58StarStarGapCoveredHoles
import Workspace.ProofLemmas.Thm58StarStarGapLocal

/-!
# The final paragraph of 5.8 (4)

When the two attachment sets `A₁, A₂` do have a common vertex `w` of `J`, the paper finishes
claim (4) with one long paragraph.  The first half of it is bookkeeping — `w` is a common
neighbour of the two star vertices off the branch, and each `Aᵢ` is a single vertex of `L(H)`,
namely the edge `vᵢw` — and is proved in `Thm58StarStarAdjacentGap`.  What is left open here is
the paragraph from *"Since `X` is not local it is not a subset of `N_w`"* onwards.

That paragraph is proved in three steps, spread over
`Thm58StarStarGapCoveredSetup` (the branch has even length, so `r₁ ≠ r₂`, and the hole
`p₁-⋯-pₙ-a₂-a₁-p₁` is even, so `n` is even), `Thm58StarStarGapCoveredTrack` (the path `T` of
`L(H)`), and `Thm58StarStarGapCoveredHoles` (the two completions of `T`).  What is left for
this file is the paper's *"there is a vertex of `R_{v₁v₂}` in `X` ... so we may assume that
`r₁ ∈ X`"*: the choice of which end of the rung has a neighbour on the outside path, and the
symmetry between the two ends that lets us assume it is `r₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapCovered

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles
open ThreeTracksLineGraphPrism TrackToRungPath
open Thm58StarStarGapCoveredSetup Thm58StarStarGapCoveredHoles

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ w : Fin n}
  {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

section CovLemmas

variable (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂)

include hc

/-- Reversing the outside path exchanges the two star vertices and the two ends of the rung.
This is the paper's *"we may assume that `r₁ ∈ X`"*. -/
theorem cov_swap : Cov G m J n H K φ N F P.reverse p₂ p₁ c₂ c₁ w q.reverse R.reverse r₂ r₁ := by
  have hrev : {x : V | x ∈ R.reverse} = {x : V | x ∈ R} := by ext x; simp
  refine ⟨Thm58StarStarTracks.context_swap hc.ctx,
    Thm57Claim2Structure.isBranch_reverse hc.branch, TrackSlice.isTrackFrom_reverse hc.from',
    by simpa using hc.len2, PathBasics.isPathFrom_reverse hc.rung, ?_, ?_, ?_,
    hc.adjw₂, hc.adjw₁, ?_, ?_, hc.sing₂, hc.sing₁, hc.ne₂, hc.ne₁⟩
  · rw [SubdivisionCounting.trackEdges_reverse, hrev]
    exact hc.rungSet
  · rw [hrev]; exact hc.int₂
  · rw [hrev]; exact hc.int₁
  · rw [SubdivisionCounting.trackEdges_reverse]; exact hc.off₂
  · rw [SubdivisionCounting.trackEdges_reverse]; exact hc.off₁

/-- PAPER: *"Since `X` is not local it is not a subset of `N_w` and so there is a vertex of
`R_{v₁v₂}` in `X`.  Since `Xᵢ ⊆ N_{vᵢ}` for `i = 1, 2`, no internal vertex of `R_{v₁v₂}` is in
`X`, so we may assume that `r₁ ∈ X`.  Since `r₁ ∉ N_{v₂}` it follows that `r₁ ∉ X₂`, and hence
`p₁` is the only vertex in `F` adjacent to `r₁`."*

Only the ends of the outside path can attach to an end of the rung, so the vertex of the rung
in `X` is a neighbour of `p₁` or of `pₙ`. -/
theorem end_of_rung_attaches : G.Adj p₁ r₁ ∨ G.Adj p₂ r₂ := by
  classical
  have hnl := hc.ctx.ready.2.2.2.2.2.1
  have hnotsub : ¬ ({e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      (φ ⟨e, he⟩ : V) ∈ attachments G F K} ⊆ incidentEdges H w) := fun hsub =>
    hnl (Thm58StarStarGapLocal.local_of_common_vertex hc.ctx.ready.2.1 hc.ctx.ready.2.2.1.1 hsub)
  rw [Set.not_subset] at hnotsub
  obtain ⟨e, ⟨he, hatt⟩, hnw⟩ := hnotsub
  have hwe : w ∉ e := fun hcon => hnw ⟨he, hcon⟩
  have hxw : (φ ⟨e, he⟩ : V) ∉ N w := fun hcon =>
    hwe ((Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) he).mp hcon)
  obtain ⟨hxK, z, hzF, hxz⟩ := hatt
  by_cases hz₁ : z = p₁
  · subst hz₁
    by_cases hxr : (φ ⟨e, he⟩ : V) = r₁
    · exact Or.inl (hxr ▸ hxz.symm)
    · exfalso
      have hmem : (φ ⟨e, he⟩ : V) ∈ N c₁ \ {r₁} :=
        ⟨first_adj_mem hc.ctx hxK hxz.symm, by simpa using hxr⟩
      have := hc.sing₁ _ hmem hxz.symm
      rw [this] at hxw
      exact hxw (a₁_mem_starw hc)
  by_cases hz₂ : z = p₂
  · subst hz₂
    by_cases hxr : (φ ⟨e, he⟩ : V) = r₂
    · exact Or.inr (hxr ▸ hxz.symm)
    · exfalso
      have hmem : (φ ⟨e, he⟩ : V) ∈ N c₂ \ {r₂} :=
        ⟨last_adj_mem hc.ctx hxK hxz.symm, by simpa using hxr⟩
      have := hc.sing₂ _ hmem hxz.symm
      rw [this] at hxw
      exact hxw (a₂_mem_starw hc)
  · exfalso
    have hmem := mid_adj_mem hc.ctx (mem_path hc.ctx hzF) hz₁ hz₂ hxK hxz.symm
    have hrung : (φ ⟨e, he⟩ : V) ∈ R := by
      have := Thm58StarStarGeometry.stars_inter_subset_rung hc.ctx hc.branch hc.from' hc.len2 hmem
      exact (mem_R_iff' hc _).mpr this
    have h₁ : (φ ⟨e, he⟩ : V) ∈ N c₁ ∩ {x : V | x ∈ R} := ⟨hmem.1, hrung⟩
    rw [hc.int₁] at h₁
    rw [h₁] at hmem
    exact r₁_not_mem_star₂ hc hmem.2

end CovLemmas

/-- GAP — PAPER, proof of 5.8 (4), printed p. 27, the final paragraph from its third sentence
on: *"Since `X` is not local it is not a subset of `N_w` and so there is a vertex of
`R_{v₁v₂}` in `X`.  Since `Xᵢ ⊆ N_{vᵢ}` for `i = 1, 2`, no internal vertex of `R_{v₁v₂}` is in
`X`, so we may assume that `r₁ ∈ X`.  Since `r₁ ∉ N_{v₂}` it follows that `r₁ ∉ X₂`, and hence
`p₁` is the only vertex in `F` adjacent to `r₁`.  Now the hole `p₁-⋯-pₙ-a₂-a₁-p₁` is even, and
so `n` is even.  If we delete the vertex `v₂` and the edge `a₁` from `H`, what remains is still
connected, and so contains a track from `w` to `v₁`.  Hence there is a path `T` in `L(H)` from
some `a₃ ∈ N(w)` to `r₁`, disjoint from `N_{v₂} ∪ a₁`.  But `T` can be completed to a hole via
`r₁-R_{v₁v₂}-r₂-a₂-a₃` and via `r₁-p₁-⋯-pₙ-a₂-a₃`, and these two completions have different
parity, a contradiction."*

The two sentences before this one are proved in `Thm58StarStarAdjacentGap.covered_holes`, and
they are exactly the hypotheses `hw₁`, `hw₂`, `hs₁`, `hs₂`, `hsing₁`, `hsing₂` below: the
covering vertex `w` of `V(J)` is a common neighbour of the two star vertices whose two edges to
them are off the branch, and `Aᵢ` is the single vertex `vᵢw` of `L(H)`.  Since the argument
ends in *"a contradiction"*, the conclusion is the pair of holes of different parity that 5.8
is looking for. -/
theorem covered_endgame (h : Context G m J n H K φ N F P p₁ p₂ c₁ c₂)
    (hq : IsBranch H q) (hfrom : IsTrackFrom H q c₁ c₂) (hq2 : 2 ≤ q.length)
    (hR : IsPathFrom G R r₁ r₂)
    (hRset : {x : V | x ∈ R} = edgeImage φ (trackEdges q))
    (hi₁ : N c₁ ∩ {x : V | x ∈ R} = {r₁}) (hi₂ : N c₂ ∩ {x : V | x ∈ R} = {r₂})
    (hw₁ : H.Adj c₁ w) (hw₂ : H.Adj c₂ w)
    (hs₁ : s(c₁, w) ∉ trackEdges q) (hs₂ : s(c₂, w) ∉ trackEdges q)
    (hsing₁ : ∀ x ∈ N c₁ \ {r₁}, G.Adj p₁ x → x = (φ ⟨s(c₁, w), hw₁⟩ : V))
    (hsing₂ : ∀ x ∈ N c₂ \ {r₂}, G.Adj p₂ x → x = (φ ⟨s(c₂, w), hw₂⟩ : V))
    (hA₁ : ∃ x ∈ N c₁ \ {r₁}, G.Adj p₁ x) (hA₂ : ∃ x ∈ N c₂ \ {r₂}, G.Adj p₂ x)
    (hB : (∃ x ∈ N c₁ \ {r₁}, ¬ G.Adj p₁ x) ∨ (∃ x ∈ N c₂ \ {r₂}, ¬ G.Adj p₂ x)) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  have hcov : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂ :=
    ⟨h, hq, hfrom, hq2, hR, hRset, hi₁, hi₂, hw₁, hw₂, hs₁, hs₂, hsing₁, hsing₂, hA₁, hA₂⟩
  rcases end_of_rung_attaches hcov with hadj | hadj
  · exact holes_of_T hcov hadj
  · exact holes_of_T (cov_swap hcov) hadj

end Workspace.ProofLemmas.Thm58StarStarGapCovered
