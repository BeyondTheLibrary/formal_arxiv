import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# 8.5: reading the branch supplied by 5.8 in the language of the strip system

Statement 5.8 speaks about a branch of `H` with ends `b₁, b₂`, about the sets `N_{b₁}, N_{b₂}`
of line-graph vertices incident with those ends, and about the path `R` of `L(H)` carried by
the branch.  The endgame of 8.5 needs all of that back in strip-system language: the branch is
the branch of an edge `ij` of `J`, `N_{b₁}` is the set of `N_i`-ends of the chosen rungs at
`i`, and `R` is the chosen rung `R_ij`.

The two dictionaries of `Thm84BranchRungDictionaryAt` supply this.  Note that the two
dictionaries are obtained from separate calls and therefore carry *a priori* different
embeddings `V(J) → V(H)`; the proof below never compares them.  It uses the rung-end
dictionary to describe `N_{b₁}` and `N_{b₂}`, and the branch dictionary only through its last
clause, *"every branch of `H` carries the vertex set of some rung"*, and then pins the edge
down by the strip a chosen vertex lies in.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgameBranchEdge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]

/-- Every vertex of the subdivision `H` has a neighbour. -/
theorem exists_adj_in_subdivision
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H) :
    ∀ w : W, ∃ x : W, H.Adj w x := by
  classical
  obtain ⟨ι₀, T, hι₀, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hForms.2.1.1
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard :=
    fun u => SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  intro w
  rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
  · have hb : ι₀ a ∈ branchVertices H :=
      SubdivisionCounting.range_subset_branchVertices hι₀ htrack hlen hdisjint hnew hdeg
        ⟨a, rfl⟩
    have h3 : 3 ≤ (H.neighborSet (ι₀ a)).ncard := hb
    obtain ⟨x, hx⟩ : (H.neighborSet (ι₀ a)).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]; omega
    exact ⟨x, hx⟩
  · rw [SubdivisionCounting.mem_trackInterior_iff] at hw
    obtain ⟨k, hk, hkw⟩ := hw
    refine ⟨(T a b)[k + 2]'(by omega), ?_⟩
    rw [← hkw]
    exact (htrack a b hab).1.2.2 (k + 1) (by omega)

/-- The two ends of a branch are different. -/
theorem ends_ne_of_branch
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    {b1 b2 : W} {q : List W} (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2) :
    b1 ≠ b2 := by
  classical
  have hnbr := exists_adj_in_subdivision G J hJ S N H Rchoice hForms
  have hq2 :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.two_le_length_of_isBranch hnbr hq
  intro heq
  have hhead : q[0]'(by omega) = b1 :=
    SubdivisionCounting.track_head hqfrom (by omega)
  have hlast : q[q.length - 1]'(by omega) = b2 := by
    have h := hqfrom.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
    exact Option.some_injective _ h
  have he : q[0]'(by omega) = q[q.length - 1]'(by omega) := by rw [hhead, hlast, heq]
  have hi := hq.1.2.1.getElem_inj_iff.mp he
  omega

/-- **The branch of 5.8, read in the strip system.**

`Nc b₁` is the set of `N_i`-ends of the chosen rungs at `i`, `Nc b₂` the set of `N_j`-ends of
the chosen rungs at `j`, the path carried by the branch is the chosen rung `R_ij`, and `ij` is
an edge of `J`. -/
theorem branch_edge_data
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (hRsymm : ∀ u v : U, J.Adj u v → Rchoice v u = (Rchoice u v).reverse)
    (φ : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (b1 b2 : W) (q : List W) (Rline : List V) (r1 r2 : V)
    (hb1 : b1 ∈ branchVertices H) (hb2 : b2 ∈ branchVertices H)
    (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2)
    (hRimage : {x : V | x ∈ Rline} =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hr1 : Nc b1 ∩ {x : V | x ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {x : V | x ∈ Rline} = {r2}) :
    ∃ i j : U, J.Adj i j ∧
      (Nc b1 ⊆ N i) ∧ (Nc b2 ⊆ N j) ∧
      (∀ w : U, J.Adj i w → ∃ r : V, r ∈ Rchoice i w ∧ r ∈ N i ∧ r ∈ Nc b1) ∧
      (∀ w : U, J.Adj j w → ∃ r : V, r ∈ Rchoice j w ∧ r ∈ N j ∧ r ∈ Nc b2) ∧
      {x : V | x ∈ Rline} = {x : V | x ∈ Rchoice i j} := by
  classical
  obtain ⟨ι, E, hιinj, hrange, hEedge, hincid, hEinj, hEφ⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.rungEndDictionaryAt
      G J hJ S N hSN H Rchoice hForms φ
  obtain ⟨i, hi⟩ : b1 ∈ Set.range ι := by rw [hrange]; exact hb1
  obtain ⟨j, hj⟩ : b2 ∈ Set.range ι := by rw [hrange]; exact hb2
  -- the image of an incident edge is the `N`-end of the corresponding rung
  have hend : ∀ (a w : U) (haw : J.Adj a w),
      ∃ r : V, r ∈ Rchoice a w ∧ r ∈ N a ∧
        (↑(φ ⟨E a w, hEedge a w haw⟩) : V) = r := by
    intro a w haw
    obtain ⟨-, s, t, hpath, hsub, hs, -⟩ := hForms.1 a w haw
    have hsR : s ∈ Rchoice a w := List.mem_of_mem_head? hpath.2.1
    exact ⟨s, hsR, (hs s hsR).mpr rfl, hEφ a w haw (hEedge a w haw) s t hpath⟩
  -- the description of `Nc (ι a)`
  have hNcmem : ∀ (a : U) (z : V), z ∈ Nc (ι a) →
      ∃ w : U, J.Adj a w ∧ z ∈ Rchoice a w ∧ z ∈ N a := by
    intro a z hz
    rw [hNc (ι a)] at hz
    obtain ⟨e, he, hinc, hze⟩ := hz
    rw [hincid a] at hinc
    obtain ⟨w, haw, hew⟩ := hinc
    obtain ⟨r, hrR, hrN, hrφ⟩ := hend a w haw
    subst hew
    rw [hrφ] at hze
    exact ⟨w, haw, hze ▸ hrR, hze ▸ hrN⟩
  have hNcin : ∀ (a w : U), J.Adj a w →
      ∃ r : V, r ∈ Rchoice a w ∧ r ∈ N a ∧ r ∈ Nc (ι a) := by
    intro a w haw
    obtain ⟨r, hrR, hrN, hrφ⟩ := hend a w haw
    refine ⟨r, hrR, hrN, ?_⟩
    rw [hNc (ι a)]
    exact ⟨E a w, hEedge a w haw, by rw [hincid a]; exact ⟨w, haw, rfl⟩, hrφ.symm⟩
  -- the branch carries the vertex set of some rung
  obtain ⟨ι', B, -, -, -, hBrung, hsurj⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.branchRungDictionaryAt
      G J hJ S N hSN H Rchoice hForms φ
  obtain ⟨u, v, huv, hqB⟩ := hsurj q hq
  have hRlineuv : {x : V | x ∈ Rline} = {x : V | x ∈ Rchoice u v} := by
    rw [hRimage, ← hBrung u v huv, hqB]
  -- `r₁` lies in a rung at `i` and in `S_uv`
  have hr1mem : r1 ∈ Nc b1 ∧ r1 ∈ {x : V | x ∈ Rline} := by
    have : r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} := by rw [hr1]; rfl
    exact this
  have hr2mem : r2 ∈ Nc b2 ∧ r2 ∈ {x : V | x ∈ Rline} := by
    have : r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} := by rw [hr2]; rfl
    exact this
  have hiuv : i = u ∨ i = v := by
    obtain ⟨w1, hiw1, hr1R, -⟩ := hNcmem i r1 (by rw [hi]; exact hr1mem.1)
    have h1 : r1 ∈ S i w1 :=
      StripSystemBasics.rung_subset_strip (hForms.1 i w1 hiw1) r1 hr1R
    have h2 : r1 ∈ S u v := by
      have : r1 ∈ {x : V | x ∈ Rchoice u v} := by rw [← hRlineuv]; exact hr1mem.2
      exact StripSystemBasics.rung_subset_strip (hForms.1 u v huv) r1 this
    rcases Sym2.eq_iff.mp
        (StripSystemBasics.edge_eq_of_mem_strips hSN hiw1 huv h1 h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hjuv : j = u ∨ j = v := by
    obtain ⟨w2, hjw2, hr2R, -⟩ := hNcmem j r2 (by rw [hj]; exact hr2mem.1)
    have h1 : r2 ∈ S j w2 :=
      StripSystemBasics.rung_subset_strip (hForms.1 j w2 hjw2) r2 hr2R
    have h2 : r2 ∈ S u v := by
      have : r2 ∈ {x : V | x ∈ Rchoice u v} := by rw [← hRlineuv]; exact hr2mem.2
      exact StripSystemBasics.rung_subset_strip (hForms.1 u v huv) r2 this
    rcases Sym2.eq_iff.mp
        (StripSystemBasics.edge_eq_of_mem_strips hSN hjw2 huv h1 h2) with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hbne : b1 ≠ b2 := ends_ne_of_branch G J hJ S N H Rchoice hForms hq hqfrom
  have hij : i ≠ j := by
    intro h
    exact hbne (by rw [← hi, ← hj, h])
  -- `{i,j} = {u,v}`
  have hkey : (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
    rcases hiuv with h1 | h1 <;> rcases hjuv with h2 | h2
    · exact absurd (h1.trans h2.symm) hij
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
    · exact absurd (h1.trans h2.symm) hij
  refine ⟨i, j, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hkey with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact huv
    · exact huv.symm
  · intro z hz
    exact (hNcmem i z (by rw [hi]; exact hz)).choose_spec.2.2
  · intro z hz
    exact (hNcmem j z (by rw [hj]; exact hz)).choose_spec.2.2
  · intro w hiw
    rw [← hi]
    exact hNcin i w hiw
  · intro w hjw
    rw [← hj]
    exact hNcin j w hjw
  · rcases hkey with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hRlineuv
    · rw [hRlineuv, hRsymm j i huv]
      ext z
      simp

end Workspace.ProofLemmas.Thm85EndgameBranchEdge
