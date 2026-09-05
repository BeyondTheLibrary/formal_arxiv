import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm85Claim3Common

/-!
# 8.5, claim (3): the remaining 5.8.2 analysis
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85Claim3Closing

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- PAPER (proof of 8.5, claim (3), printed p. 42):

*"If there are no two disjoint edges in `K`, then by (1) and 5.8, it follows that either
`X ∩ V(L(H))` is local (with respect to `L(H)`) or 5.8.2.a holds, and in either case there
is a branch `D` of `H` with an end `d` such that every edge of `X ∩ E(H)` either is in
`E(D)` or is incident with `d`. In particular, every branch containing an edge of `X` is
incident with `d`, and so `d` meets all edges of `J` in `K`."*

This lemma is the non-local half of that sentence.  The local half is proved in
`Thm85Claim3Analysis.common_end_of_local_choice`. -/
theorem common_end_of_branch_outcome
    {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V)
    (hFmin : ∀ F1 : Set V, F1 ⊆ F → ConnectedSet G F1 →
      ¬ LocalForStripSystem J S N (attachments G F1 (stripSystemVertices J S)) → F1 = F)
    (hnodisjoint : ∀ a b c d : U, J.Adj a b → J.Adj c d → [a, b, c, d].Nodup →
      ¬ ((attachments G F (stripSystemVertices J S) ∩ S a b).Nonempty ∧
        (attachments G F (stripSystemVertices J S) ∩ S c d).Nonempty))
    (Rchoice : U → U → List V)
    (hmeet : ∀ a b : U, J.Adj a b →
      (attachments G F (stripSystemVertices J S) ∩ S a b).Nonempty →
      ∃ z ∈ attachments G F (stripSystemVertices J S), z ∈ Rchoice a b)
    (H : SimpleGraph W) (hForms : FormsLineGraph G J S N Rchoice H)
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
    (hRline : IsPathList G Rline)
    (hRimage : {x : V | x ∈ Rline} =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ trackEdges q ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (hr1 : Nc b1 ∩ {x : V | x ∈ Rline} = {r1})
    (hr2 : Nc b2 ∩ {x : V | x ∈ Rline} = {r2})
    (hcases :
      ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∃ x ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          y ≠ r1 → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
          (x = p2 ∧ y ∈ {z : V | z ∈ Rline} \ {r1}))) ∨
      ((∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨ (x = p2 ∧ y ∈ Nc b2 \ {r2}) ∨
          (x = p1 ∧ y = r1) ∨ (x = p2 ∧ y = r2)) ∧
        (Even (pathLength P) ↔ Even (pathLength Rline))) ∨
      (p1 = p2 ∧
        (∀ x ∈ (Nc b1 ∪ Nc b2) \ {r1, r2}, G.Adj p1 x) ∧
        (∀ y ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          G.Adj p1 y → y ∈ Nc b1 ∪ Nc b2 ∪ {z : V | z ∈ Rline}) ∧
        Even (pathLength Rline)) ∨
      (r1 = r2 ∧
        (∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
        (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x) ∧
        (∀ x ∈ P, ∀ y ∈
          (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
          y ≠ r1 → G.Adj x y →
          (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨ (x = p2 ∧ y ∈ Nc b2 \ {r2})) ∧
        Even (pathLength P))) :
    ∃ d : U, ∀ a b : U, J.Adj a b →
      (attachments G F (stripSystemVertices J S) ∩ S a b).Nonempty →
      d = a ∨ d = b := by
  classical
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
  have hr2R : r2 ∈ Rline :=
    (show r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} by rw [hr2]; simp).2
  have hr1S : r1 ∈ S a1 a2 := hRlineS r1 hr1R
  have hr2S : r2 ∈ S a1 a2 := hRlineS r2 hr2R
  have hp1F : p1 ∈ F := hPF p1 (List.mem_of_mem_head? hP.2.1)
  have hp2F : p2 ∈ F := hPF p2 (List.mem_of_getLast? hP.2.2)
  -- The rung end of `a₁w` is `r₁` only for `w = a₂`.
  have hexc1 : ∀ (w : U) (hw : J.Adj a1 w), w ≠ a2 →
      (↑(phi ⟨E a1 w, hEedge a1 w hw⟩) : V) ≠ r1 := by
    intro w hw hwne hcon
    obtain ⟨-, s, t, hpath, hsub, -, -⟩ := hForms.1 a1 w hw
    have hsR : s ∈ Rchoice a1 w := List.mem_of_mem_head? hpath.2.1
    have himg : (↑(phi ⟨E a1 w, hEedge a1 w hw⟩) : V) = s :=
      hEphi a1 w hw (hEedge a1 w hw) s t hpath
    have hr1Sw : r1 ∈ S a1 w := by rw [← hcon, himg]; exact hsub s hsR
    have hedge : s(a1, w) = s(a1, a2) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hw ha12adj hr1Sw hr1S
    rcases Sym2.eq_iff.mp hedge with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hwne h2
    · exact ha1ne2 h1
  have hexc2 : ∀ (w : U) (hw : J.Adj a2 w), w ≠ a1 →
      (↑(phi ⟨E a2 w, hEedge a2 w hw⟩) : V) ≠ r2 := by
    intro w hw hwne hcon
    obtain ⟨-, s, t, hpath, hsub, -, -⟩ := hForms.1 a2 w hw
    have hsR : s ∈ Rchoice a2 w := List.mem_of_mem_head? hpath.2.1
    have himg : (↑(phi ⟨E a2 w, hEedge a2 w hw⟩) : V) = s :=
      hEphi a2 w hw (hEedge a2 w hw) s t hpath
    have hr2Sw : r2 ∈ S a2 w := by rw [← hcon, himg]; exact hsub s hsR
    have hedge : s(a2, w) = s(a1, a2) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hw ha12adj hr2Sw hr2S
    rcases Sym2.eq_iff.mp hedge with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ha1ne2 h1.symm
    · exact hwne h2
  rcases Workspace.ProofLemmas.Thm85Claim3Common.first_case_or_both_ends
      G J Rchoice Nc P p1 p2 b1 b2 Rline r1 r2 hr1 hr2 hcases with
    ⟨hcomp1, ⟨x0, hx0R, hx0adj⟩, hall⟩ | ⟨hc1, hc2⟩
  · -- 5.8.2.a: every active edge of `J` is incident with `a₁`.
    have hcomp1' : ∀ x ∈ {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H (iota a1) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r1}, G.Adj p1 x := by
      intro x hx
      exact hcomp1 x (by rw [hNc b1, ← ha1]; exact hx)
    -- a neighbour `w ≠ a₂` of `a₁`, and the end `y₁` of the rung `R_{a₁w}`
    obtain ⟨w, hwmem⟩ : (J.neighborSet a1 \ {a2}).Nonempty := by
      rw [← Set.ncard_pos (Set.toFinite _)]
      have := Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff
        (a := a2) (SubdivisionCounting.three_le_degree_of_three_connected J hJ a1)
      omega
    have haw : J.Adj a1 w := hwmem.1
    have hwa2 : w ≠ a2 := hwmem.2
    obtain ⟨-, sy, ty, hpathy, hsuby, hsy, -⟩ := hForms.1 a1 w haw
    have hsyR : sy ∈ Rchoice a1 w := List.mem_of_mem_head? hpathy.2.1
    have hy1img : (↑(phi ⟨E a1 w, hEedge a1 w haw⟩) : V) = sy :=
      hEphi a1 w haw (hEedge a1 w haw) sy ty hpathy
    have hy1S : sy ∈ S a1 w := hsuby sy hsyR
    have hy1Nc : sy ∈ Nc b1 := by
      rw [hNc b1, ← ha1]
      exact ⟨E a1 w, hEedge a1 w haw, by rw [hincident a1]; exact ⟨w, haw, rfl⟩, hy1img.symm⟩
    have hy1ne : sy ≠ r1 := by
      have := hexc1 w haw hwa2
      rw [hy1img] at this
      exact this
    have hy1adj : G.Adj p1 sy := hcomp1 sy ⟨hy1Nc, by simpa using hy1ne⟩
    have hx0S : x0 ∈ S a1 a2 := hRlineS x0 hx0R.1
    have hx0ne : x0 ≠ r1 := by simpa using hx0R.2
    have hx0notN : x0 ∉ N a1 := fun h => hx0ne (hRlineU x0 hx0R.1 h)
    have hp1P : p1 ∈ P := List.mem_of_mem_head? hP.2.1
    have hp2P : p2 ∈ P := List.mem_of_getLast? hP.2.2
    have hy1att : sy ∈ attachments G {x : V | x ∈ P} (stripSystemVertices J S) :=
      ⟨StripSystemBasics.strip_subset_vertices haw hy1S, p1, hp1P, hy1adj.symm⟩
    have hx0att : x0 ∈ attachments G {x : V | x ∈ P} (stripSystemVertices J S) :=
      ⟨StripSystemBasics.strip_subset_vertices ha12adj hx0S, p2, hp2P, hx0adj.symm⟩
    have hnotlocal : ¬ LocalForStripSystem J S N
        (attachments G {x : V | x ∈ P} (stripSystemVertices J S)) := by
      rintro (⟨v, hv⟩ | ⟨c, d, hcd, hsub⟩)
      · have hy1v : sy ∈ N v := hv hy1att
        have hx0v : x0 ∈ N v := hv hx0att
        have hva2 : v = a2 := by
          by_contra hc
          have hva1 : v ≠ a1 := by rintro rfl; exact hx0notN hx0v
          have h0 : x0 ∈ S a1 a2 ∩ N v := ⟨hx0S, hx0v⟩
          rw [StripSystemBasics.strip_inter_N_eq_empty hSN ha12adj hva1 hc] at h0
          exact h0
        subst hva2
        have h0 : sy ∈ S a1 w ∩ N v := ⟨hy1S, hy1v⟩
        rw [StripSystemBasics.strip_inter_N_eq_empty hSN haw (Ne.symm ha1ne2)
          (Ne.symm hwa2)] at h0
        exact h0
      · have h1 : s(c, d) = s(a1, w) :=
          StripSystemBasics.edge_eq_of_mem_strips hSN hcd haw (hsub hy1att) hy1S
        have h2 : s(c, d) = s(a1, a2) :=
          StripSystemBasics.edge_eq_of_mem_strips hSN hcd ha12adj (hsub hx0att) hx0S
        rcases Sym2.eq_iff.mp (h1.symm.trans h2) with ⟨-, h4⟩ | ⟨h3, -⟩
        · exact hwa2 h4
        · exact ha1ne2 h3
    have hFP : {x : V | x ∈ P} = F :=
      hFmin {x : V | x ∈ P} (fun x hx => hPF x hx)
        (Workspace.ProofLemmas.KiteTailBasics.connectedSet_of_isPathList hP.1) hnotlocal
    refine ⟨a1, ?_⟩
    intro c d hcd hactive
    obtain ⟨z, hzX, hzR⟩ := hmeet c d hcd hactive
    obtain ⟨-, -, -, -, hsubcd, -, -⟩ := hForms.1 c d hcd
    have hzS : z ∈ S c d := hsubcd z hzR
    have hfinish : ∀ (e1 e2 : U), J.Adj e1 e2 → z ∈ S e1 e2 → a1 = e1 ∨ a1 = e2 →
        a1 = c ∨ a1 = d := by
      intro e1 e2 he hz he1
      have hedge : s(c, d) = s(e1, e2) :=
        StripSystemBasics.edge_eq_of_mem_strips hSN hcd he hzS hz
      rcases Sym2.eq_iff.mp hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases he1 with h | h
      · exact Or.inl (h.trans h1.symm)
      · exact Or.inr (h.trans h2.symm)
      · exact Or.inr (h.trans h2.symm)
      · exact Or.inl (h.trans h1.symm)
    by_cases hzr1 : z = r1
    · exact hfinish a1 a2 ha12adj (by rw [hzr1]; exact hr1S) (Or.inl rfl)
    · obtain ⟨f, hfF, hzf⟩ := hzX.2
      have hfP : f ∈ P := by rw [← hFP] at hfF; exact hfF
      have hzK : z ∈ (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}) := by
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨c, d, hcd, hzR⟩
      rcases hall f hfP z hzK hzr1 hzf.symm with ⟨-, hz1⟩ | ⟨-, hz2⟩
      · obtain ⟨w2, hw2, -, hzS2⟩ :=
          Workspace.ProofLemmas.Thm85Claim3Common.mem_Nc_decode
            G J S N H Rchoice hForms phi iota E hincident hEphi Nc hNc a1 z
            (by rw [ha1]; exact hz1.1)
        exact hfinish a1 w2 hw2 hzS2 (Or.inl rfl)
      · exact hfinish a1 a2 ha12adj (hRlineS z hz2.1) (Or.inl rfl)
  · -- 5.8.2.b, 5.8.2.c, 5.8.2.d: two disjoint edges of `J` become active, contrary to
    -- the hypothesis of claim (3).
    exfalso
    have hc1' : ∀ x ∈ {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H (iota a1) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r1}, G.Adj p1 x := by
      intro x hx
      exact hc1 x (by rw [hNc b1, ← ha1]; exact hx)
    have hc2' : ∀ x ∈ {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H (iota a2) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r2}, G.Adj p2 x := by
      intro x hx
      exact hc2 x (by rw [hNc b2, ← ha2]; exact hx)
    have hd1 : 2 ≤ (J.neighborSet a1 \ {a2}).ncard :=
      Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff
        (SubdivisionCounting.three_le_degree_of_three_connected J hJ a1)
    have hd2 : 2 ≤ (J.neighborSet a2 \ {a1}).ncard :=
      Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff
        (SubdivisionCounting.three_le_degree_of_three_connected J hJ a2)
    obtain ⟨u1, u2, hu1, hu2, hu12⟩ :=
      Workspace.ProofLemmas.Thm84RungEndDictionary.exists_two_mem hd1
    obtain ⟨v1, v2, hv1, hv2, hv12⟩ :=
      Workspace.ProofLemmas.Thm84RungEndDictionary.exists_two_mem hd2
    obtain ⟨w, w', hw, hw', hww'⟩ : ∃ w w' : U, w ∈ J.neighborSet a1 \ {a2} ∧
        w' ∈ J.neighborSet a2 \ {a1} ∧ w ≠ w' := by
      by_cases hcv : u1 = v1
      · exact ⟨u1, v2, hu1, hv2, by rw [hcv]; exact hv12⟩
      · exact ⟨u1, v1, hu1, hv1, hcv⟩
    have haw : J.Adj a1 w := hw.1
    have haw' : J.Adj a2 w' := hw'.1
    have hact1 : (attachments G F (stripSystemVertices J S) ∩ S a1 w).Nonempty :=
      Workspace.ProofLemmas.Thm85Claim3Common.active_of_rung_end_ne
        G J S N H Rchoice hForms phi iota E hEedge hincident hEphi F p1 hp1F a1 r1 hc1'
        w haw (hexc1 w haw hw.2)
    have hact2 : (attachments G F (stripSystemVertices J S) ∩ S a2 w').Nonempty :=
      Workspace.ProofLemmas.Thm85Claim3Common.active_of_rung_end_ne
        G J S N H Rchoice hForms phi iota E hEedge hincident hEphi F p2 hp2F a2 r2 hc2'
        w' haw' (hexc2 w' haw' hw'.2)
    refine hnodisjoint a1 w a2 w' haw haw' ?_ ⟨hact1, hact2⟩
    have e1 : a1 ≠ w := haw.ne
    have e2 : a2 ≠ w' := haw'.ne
    have e3 : a1 ≠ w' := fun h => hw'.2 (by rw [← h]; rfl)
    have e4 : w ≠ a2 := hw.2
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
      not_or]
    tauto

end Workspace.ProofLemmas.Thm85Claim3Closing
