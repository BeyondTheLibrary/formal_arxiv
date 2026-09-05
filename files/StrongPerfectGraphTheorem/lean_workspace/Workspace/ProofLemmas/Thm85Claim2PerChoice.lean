import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm85Claim2Cases
import Workspace.ProofLemmas.Thm85Claim3Common

/-!
# 8.5, claim (2): what one choice of rungs gives

PAPER (proof of 8.5, claim (2), printed p. 42):

*"The branch containing `x'` does not meet `x`, so `D` is the branch between `u` and `v`, and
`d = v`.  Hence `x'` is incident with `v` in `H`, and `δ_H(v) ⊆ X ∪ E(D)`.  Consequently, for
all neighbours `w ≠ u` of `v` in `J`, `X` contains the vertex of `R_vw` that belongs to `N_v`,
and contains no other vertex of `R_vw`."*

That last sentence is what a *single* choice of rungs yields, and it is what this module
proves.  The vertex called `u` there is recovered here as the second end `u₀` of the branch
supplied by 5.8; the caller of this module identifies `u₀` with `u` by feeding in the vertex
`x ∈ X ∩ S_uv \ N_v`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm85Claim2PerChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]

/-- **"For all neighbours `w ≠ u` of `v` in `J`, `X` contains the vertex of `R_vw` that belongs
to `N_v`, and contains no other vertex of `R_vw`."**  (Proof of 8.5, claim (2), printed p. 42.)

The neighbour `u` of the paper is produced here as `u₀`, the vertex of `J` at the far end of
the branch that 5.8 returns. -/
theorem per_choice_attachments_at_v
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V)
    (hFmin : ∀ F1 : Set V, F1 ⊆ F → ConnectedSet G F1 →
      ¬ LocalForStripSystem J S N (attachments G F1 (stripSystemVertices J S)) → F1 = F)
    (v : U)
    (hXv : attachments G F (stripSystemVertices J S) ⊆
      ⋃ (a : U) (_ : J.Adj a v), S a v)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p1 p2 : V) (hP : IsPathFrom G P p1 p2) (hPF : ∀ x ∈ P, x ∈ F)
    (b1 b2 : W) (q : List W) (Rline : List V) (r1 r2 : V)
    (hb1 : b1 ∈ branchVertices H) (hb2 : b2 ∈ branchVertices H)
    (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2)
    (hRimage : {x : V | x ∈ Rline} =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (hr1 : Nc b1 ∩ {x : V | x ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {x : V | x ∈ Rline} = {r2})
    (hfirst :
      (∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
      (∃ x ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 x) ∧
      (∀ x ∈ P, ∀ y ∈
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {t : V | t ∈ Rchoice a b}),
        y ≠ r1 → G.Adj x y →
        (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
        (x = p2 ∧ y ∈ {t : V | t ∈ Rline} \ {r1}))) :
    ∃ u0 : U, J.Adj v u0 ∧
      ∀ w : U, J.Adj v w → w ≠ u0 → ∀ z ∈ Rchoice v w,
        (z ∈ attachments G F (stripSystemVertices J S) ↔ z ∈ N v) := by
  classical
  obtain ⟨hcomp1, ⟨x0, hx0R, hx0adj⟩, hall⟩ := hfirst
  obtain ⟨iota, E, hiotainj, hrange, hEedge, hincident, hEinj, hEphi⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.rungEndDictionaryAt
      G J hJ S N hSN H Rchoice hForms phi
  obtain ⟨a1, a2, ha12adj, ha1, ha2, hr1N, hr2N, hRlineS, hRlineU⟩ :=
    Workspace.ProofLemmas.Thm85Claim3Common.branch_ends_dictionary
      G J hJ S N hSN H Rchoice hForms phi Nc hNc iota E hrange hEedge hincident hEphi
      b1 b2 q Rline r1 r2 hb1 hb2 hq hqfrom hRimage hr1 hr2
  have hbne : b1 ≠ b2 :=
    Workspace.ProofLemmas.Thm85Claim3Common.branch_ends_ne
      G J hJ S N H Rchoice hForms b1 b2 q hq hqfrom
  have ha1ne2 : a1 ≠ a2 := by
    intro h; exact hbne (by rw [← ha1, ← ha2, h])
  have hr1R : r1 ∈ Rline :=
    (show r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} by rw [hr1]; simp).2
  have hr1S : r1 ∈ S a1 a2 := hRlineS r1 hr1R
  have hp1F : p1 ∈ F := hPF p1 (List.mem_of_mem_head? hP.2.1)
  have hp2F : p2 ∈ F := hPF p2 (List.mem_of_getLast? hP.2.2)
  have hp1P : p1 ∈ P := List.mem_of_mem_head? hP.2.1
  have hp2P : p2 ∈ P := List.mem_of_getLast? hP.2.2
  have hcomp1' : ∀ x ∈ {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H (iota a1) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r1}, G.Adj p1 x := by
    intro x hx
    exact hcomp1 x (by rw [hNc b1, ← ha1]; exact hx)
  -- `a₁` is the common centre `v`
  obtain ⟨w1, w1', haw1, haw1', hn1, hm1, hm1'⟩ :=
    Workspace.ProofLemmas.Thm85Claim2Cases.two_active_strips_at_branch
      G J hJ S N H Rchoice hForms phi iota E hEedge hincident hEinj hEphi F p1 hp1F a1 r1
      hcomp1'
  have ha1v : a1 = v :=
    Workspace.ProofLemmas.Thm85Claim2Cases.eq_common_center_of_two_active
      G J S N hSN _ v a1 w1 w1' hXv haw1 haw1' hn1 hm1 hm1'
  subst ha1v
  refine ⟨a2, ha12adj, ?_⟩
  -- a neighbour `w₀ ≠ a₂` of `a₁`, giving the first attachment of the path
  obtain ⟨w0, hw0mem⟩ : (J.neighborSet a1 \ {a2}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    have := Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff
      (a := a2) (SubdivisionCounting.three_le_degree_of_three_connected J hJ a1)
    omega
  have haw0 : J.Adj a1 w0 := hw0mem.1
  have hw0a2 : w0 ≠ a2 := hw0mem.2
  -- the two attachments of the path
  have hstripne : ∀ w : U, J.Adj a1 w → w ≠ a2 → ∀ z ∈ S a1 w, z ≠ r1 := by
    intro w hw hwa2 z hz hcon
    have hedge : s(a1, w) = s(a1, a2) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hw ha12adj (hcon ▸ hz) hr1S
    rcases Sym2.eq_iff.mp hedge with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hwa2 h2
    · exact ha1ne2 h1
  have hend : ∀ (w : U) (hw : J.Adj a1 w), ∃ s : V, s ∈ Rchoice a1 w ∧ s ∈ S a1 w ∧
      s ∈ N a1 ∧ (↑(phi ⟨E a1 w, hEedge a1 w hw⟩) : V) = s ∧
      (∀ z ∈ Rchoice a1 w, z ∈ N a1 → z = s) := by
    intro w hw
    obtain ⟨-, s, t, hpath, hsub, hs, -⟩ := hForms.1 a1 w hw
    have hsR : s ∈ Rchoice a1 w := List.mem_of_mem_head? hpath.2.1
    exact ⟨s, hsR, hsub s hsR, (hs s hsR).mpr rfl,
      hEphi a1 w hw (hEedge a1 w hw) s t hpath, fun z hz hzN => (hs z hz).mp hzN⟩
  have hNcmem : ∀ (w : U) (hw : J.Adj a1 w), (↑(phi ⟨E a1 w, hEedge a1 w hw⟩) : V) ∈ Nc b1 := by
    intro w hw
    rw [hNc b1, ← ha1]
    exact ⟨E a1 w, hEedge a1 w hw, by rw [hincident a1]; exact ⟨w, hw, rfl⟩, rfl⟩
  obtain ⟨y1, hy1R, hy1S, hy1N, hy1img, -⟩ := hend w0 haw0
  have hy1Nc : y1 ∈ Nc b1 := by rw [← hy1img]; exact hNcmem w0 haw0
  have hy1ne : y1 ≠ r1 := hstripne w0 haw0 hw0a2 y1 hy1S
  have hy1adj : G.Adj p1 y1 := hcomp1 y1 ⟨hy1Nc, by simpa using hy1ne⟩
  have hx0S : x0 ∈ S a1 a2 := hRlineS x0 hx0R.1
  have hx0ne : x0 ≠ r1 := by simpa using hx0R.2
  have hx0notN : x0 ∉ N a1 := fun h => hx0ne (hRlineU x0 hx0R.1 h)
  have hFP : {z : V | z ∈ P} = F :=
    Workspace.ProofLemmas.Thm85Claim3Common.path_eq_F_of_two_attachments
      G J S N hSN F hFmin P hP.1 hPF a1 a2 w0 haw0 ha12adj hw0a2 ha1ne2
      p1 p2 y1 x0 hp1P hp2P hy1S hx0S hx0notN hy1adj hx0adj
  -- the conclusion
  intro w hvw hwa2 z hzR
  obtain ⟨-, s, t, hpath, hsub, hs, -⟩ := hForms.1 a1 w hvw
  have hzS : z ∈ S a1 w := hsub z hzR
  have hzne : z ≠ r1 := hstripne w hvw hwa2 z hzS
  constructor
  · rintro ⟨-, f, hfF, hzf⟩
    have hfP : f ∈ P := by rw [← hFP] at hfF; exact hfF
    have hzK : z ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {t : V | t ∈ Rchoice a b}) := by
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨a1, w, hvw, hzR⟩
    rcases hall f hfP z hzK hzne hzf.symm with ⟨-, hz1⟩ | ⟨-, hz2⟩
    · obtain ⟨w2, -, hzN, -⟩ :=
        Workspace.ProofLemmas.Thm85Claim3Common.mem_Nc_decode
          G J S N H Rchoice hForms phi iota E hincident hEphi Nc hNc a1 z
          (by rw [ha1]; exact hz1.1)
      exact hzN
    · exact absurd (hRlineS z hz2.1) (fun h => hstripne w hvw hwa2 z hzS
        (by
          have hedge : s(a1, w) = s(a1, a2) :=
            StripSystemBasics.edge_eq_of_mem_strips hSN hvw ha12adj hzS h
          exact absurd hedge (by
            intro hc
            rcases Sym2.eq_iff.mp hc with ⟨-, h2⟩ | ⟨h1, -⟩
            · exact hwa2 h2
            · exact ha1ne2 h1)))
  · intro hzN
    obtain ⟨s0, hs0R, hs0S, hs0N, hs0img, hs0uniq⟩ := hend w hvw
    have hzs0 : z = s0 := hs0uniq z hzR hzN
    have hs0Nc : s0 ∈ Nc b1 := by rw [← hs0img]; exact hNcmem w hvw
    have hs0ne : s0 ≠ r1 := hstripne w hvw hwa2 s0 hs0S
    have hadj : G.Adj p1 s0 := hcomp1 s0 ⟨hs0Nc, by simpa using hs0ne⟩
    rw [hzs0]
    exact ⟨StripSystemBasics.strip_subset_vertices hvw hs0S, p1, hp1F, hadj.symm⟩

end Workspace.ProofLemmas.Thm85Claim2PerChoice
