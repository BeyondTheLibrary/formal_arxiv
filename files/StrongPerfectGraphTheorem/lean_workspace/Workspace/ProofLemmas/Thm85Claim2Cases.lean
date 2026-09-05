import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt

/-!
# 8.5, claim (2): excluding the last three cases of 5.8.2

If an end `c` of the branch supplied by 5.8 has all but one of its incident line-graph
vertices complete to a vertex of `F`, then at least two different strips at the corresponding
vertex of `J` meet the attachment set.  This is the counting step behind the sentence
*"Since for every vertex `w` except at most one, only one strip meets both `N_w` and `X`, it
follows that 5.8.2.a holds."*
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85Claim2Cases

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]

/-- If every member of `X` lies in a strip at `v`, a vertex at which two different strips
meet `X` must be `v` itself. -/
theorem eq_common_center_of_two_active
    (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (X : Set V) (v a w w' : U)
    (hXv : X ⊆ ⋃ (u : U) (_ : J.Adj u v), S u v)
    (haw : J.Adj a w) (haw' : J.Adj a w') (hww' : w ≠ w')
    (hmeet : (X ∩ S a w).Nonempty) (hmeet' : (X ∩ S a w').Nonempty) :
    a = v := by
  have one : ∀ b : U, J.Adj a b → (X ∩ S a b).Nonempty → a = v ∨ b = v := by
    intro b hab ⟨x, hxX, hxS⟩
    have hxv := hXv hxX
    simp only [Set.mem_iUnion] at hxv
    obtain ⟨c, hcv, hxScv⟩ := hxv
    have hedge : s(a, b) = s(c, v) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN hab hcv hxS hxScv
    rcases Sym2.eq_iff.mp hedge with ⟨-, hbv⟩ | ⟨hav, -⟩
    · exact Or.inr hbv
    · exact Or.inl hav
  rcases one w haw hmeet with hav | hwv
  · exact hav
  · rcases one w' haw' hmeet' with hav | hw'v
    · exact hav
    · exact False.elim (hww' (hwv.trans hw'v.symm))

/-- Completeness to all but one member of the line-graph clique at `iota a` makes two
different strips at `a` meet the attachment set of `F`. -/
theorem two_active_strips_at_branch
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V)
    (H : SimpleGraph W) (R : U → U → List V)
    (hForms : FormsLineGraph G J S N R H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (iota : U → W) (E : U → U → Sym2 W)
    (hEedge : ∀ u v : U, J.Adj u v → E u v ∈ H.edgeSet)
    (hincident : ∀ u : U,
      incidentEdges H (iota u) = {e : Sym2 W | ∃ v : U, J.Adj u v ∧ e = E u v})
    (hEinj : ∀ u v v' : U, J.Adj u v → J.Adj u v' → E u v = E u v' → v = v')
    (hEphi : ∀ u v : U, J.Adj u v → ∀ he : E u v ∈ H.edgeSet, ∀ s t : V,
      IsPathFrom G (R u v) s t → (↑(phi ⟨E u v, he⟩) : V) = s)
    (F : Set V) (p : V) (hpF : p ∈ F) (a : U) (r : V)
    (hcomplete : ∀ x ∈
      {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H (iota a) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r},
      G.Adj p x) :
    ∃ w w' : U, J.Adj a w ∧ J.Adj a w' ∧ w ≠ w' ∧
      (attachments G F (stripSystemVertices J S) ∩ S a w).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S a w').Nonempty := by
  classical
  have hdeg : 3 ≤ (J.neighborSet a).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ a
  obtain ⟨w0, hw0⟩ : (J.neighborSet a).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  have hdiff : 2 ≤ (J.neighborSet a \ {w0}).ncard :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff hdeg
  obtain ⟨w1, w2, hw1, hw2, hw12⟩ :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.exists_two_mem hdiff
  have hw01 : w0 ≠ w1 := fun h => hw1.2 (by simpa [h])
  have hw02 : w0 ≠ w2 := fun h => hw2.2 (by simpa [h])
  have hadj0 : J.Adj a w0 := hw0
  have hadj1 : J.Adj a w1 := hw1.1
  have hadj2 : J.Adj a w2 := hw2.1
  let imageEnd (w : U) (haw : J.Adj a w) : V :=
    ↑(phi ⟨E a w, hEedge a w haw⟩)
  have hbad : ∀ w w' : U, ∀ haw : J.Adj a w, ∀ haw' : J.Adj a w',
      imageEnd w haw = r → imageEnd w' haw' = r → w = w' := by
    intro w w' haw haw' hw hw'
    have himg : phi ⟨E a w, hEedge a w haw⟩ = phi ⟨E a w', hEedge a w' haw'⟩ := by
      apply Subtype.ext
      exact hw.trans hw'.symm
    have hedge : E a w = E a w' := congrArg Subtype.val (phi.injective himg)
    exact hEinj a w w' haw haw' hedge
  have hactive : ∀ w : U, ∀ haw : J.Adj a w, imageEnd w haw ≠ r →
      (attachments G F (stripSystemVertices J S) ∩ S a w).Nonempty := by
    intro w haw hne
    obtain ⟨-, s, t, hpath, hRsub, hs, -⟩ := hForms.1 a w haw
    have hsR : s ∈ R a w := List.mem_of_mem_head? hpath.2.1
    have hsS : s ∈ S a w := hRsub s hsR
    have himg : imageEnd w haw = s := hEphi a w haw (hEedge a w haw) s t hpath
    have hinc : E a w ∈ incidentEdges H (iota a) := by
      rw [hincident a]
      exact ⟨w, haw, rfl⟩
    have hmem : imageEnd w haw ∈
        {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
          e ∈ incidentEdges H (iota a) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r} := by
      constructor
      · exact ⟨E a w, hEedge a w haw, hinc, rfl⟩
      · simpa using hne
    have hadj : G.Adj p (imageEnd w haw) := hcomplete _ hmem
    refine ⟨imageEnd w haw, ?_, ?_⟩
    · refine ⟨?_, p, hpF, hadj.symm⟩
      exact StripSystemBasics.strip_subset_vertices haw (by rwa [himg])
    · rwa [himg]
  by_cases hb0 : imageEnd w0 hadj0 = r
  · have hb1 : imageEnd w1 hadj1 ≠ r := fun h => hw01 (hbad w0 w1 hadj0 hadj1 hb0 h)
    have hb2 : imageEnd w2 hadj2 ≠ r := fun h => hw02 (hbad w0 w2 hadj0 hadj2 hb0 h)
    exact ⟨w1, w2, hadj1, hadj2, hw12, hactive w1 hadj1 hb1, hactive w2 hadj2 hb2⟩
  · by_cases hb1 : imageEnd w1 hadj1 = r
    · have hb2 : imageEnd w2 hadj2 ≠ r := fun h => hw12 (hbad w1 w2 hadj1 hadj2 hb1 h)
      exact ⟨w0, w2, hadj0, hadj2, hw02, hactive w0 hadj0 hb0, hactive w2 hadj2 hb2⟩
    · exact ⟨w0, w1, hadj0, hadj1, hw01, hactive w0 hadj0 hb0, hactive w1 hadj1 hb1⟩

/-- Under the common-centre hypothesis of claim (2), the branch alternative of 5.8 can only
be its first subcase.  The other three subcases make two strips active at both ends of the
branch, while only the common centre can have two active strips. -/
theorem branch_outcome_forces_first_case
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (Rchoice : U → U → List V)
    (hForms : FormsLineGraph G J S N Rchoice H)
    (phi : H.lineGraph ≃g
      G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rchoice a b}))
    (Nc : W → Set V)
    (hNc : ∀ c : W, Nc c =
      {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(phi ⟨e, he⟩) : V)})
    (F : Set V) (v0 : U)
    (hXv : attachments G F (stripSystemVertices J S) ⊆
      ⋃ (u : U) (_ : J.Adj u v0), S u v0)
    (P : List V) (p1 p2 : V) (hPfrom : IsPathFrom G P p1 p2)
    (hPF : ∀ x ∈ P, x ∈ F)
    (b1 b2 : W) (q : List W) (Rline : List V) (r1 r2 : V)
    (hb1 : b1 ∈ branchVertices H) (hb2 : b2 ∈ branchVertices H)
    (hq : IsBranch H q) (hqfrom : IsTrackFrom H q b1 b2)
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
    (∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) ∧
      (∃ x ∈ {y : V | y ∈ Rline} \ {r1}, G.Adj p2 x) ∧
      (∀ x ∈ P, ∀ y ∈
        (⋃ (a : U) (b : U) (_ : J.Adj a b), {z : V | z ∈ Rchoice a b}),
        y ≠ r1 → G.Adj x y →
        (x = p1 ∧ y ∈ Nc b1 \ {r1}) ∨
        (x = p2 ∧ y ∈ {z : V | z ∈ Rline} \ {r1})) := by
  classical
  obtain ⟨iota, E, hiota, hrange, hEedge, hincident, hEinj, hEphi⟩ :=
    Workspace.ProofLemmas.Thm84BranchRungDictionaryAt.rungEndDictionaryAt
      G J hJ S N hSN H Rchoice hForms phi
  obtain ⟨a1, ha1⟩ : b1 ∈ Set.range iota := by rw [hrange]; exact hb1
  obtain ⟨a2, ha2⟩ : b2 ∈ Set.range iota := by rw [hrange]; exact hb2
  have hp1F : p1 ∈ F := hPF p1 (List.mem_of_mem_head? hPfrom.2.1)
  have hp2F : p2 ∈ F := hPF p2 (List.mem_of_getLast? hPfrom.2.2)
  have hr1R : r1 ∈ Rline :=
    (show r1 ∈ Nc b1 ∩ {x : V | x ∈ Rline} by rw [hr1]; simp).2
  have hr2R : r2 ∈ Rline :=
    (show r2 ∈ Nc b2 ∩ {x : V | x ∈ Rline} by rw [hr2]; simp).2
  have hbne : b1 ≠ b2 := by
    obtain ⟨iota0, T, hiota0, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ :=
      hForms.2.1.1
    have hdeg : ∀ a : U, 3 ≤ (J.neighborSet a).ncard := fun a =>
      SubdivisionCounting.three_le_degree_of_three_connected J hJ a
    have hnbr : ∀ w : W, ∃ z : W, H.Adj w z := by
      intro w
      rcases hcover w with ⟨a, rfl⟩ | ⟨a, b, hab, hw⟩
      · obtain ⟨z, hz⟩ : (J.neighborSet a).Nonempty := by
          rw [← Set.ncard_pos (Set.toFinite _)]
          have := hdeg a
          omega
        have hlen2 : 2 ≤ (T a z).length := by
          have := hlen a z hz
          simp only [trackLength] at this
          omega
        refine ⟨(T a z)[1]'(by omega), ?_⟩
        have hadj := (htrack a z hz).1.2.2 0 (by omega)
        rw [SubdivisionCounting.track_head (htrack a z hz) (by omega)] at hadj
        exact hadj
      · rw [SubdivisionCounting.mem_trackInterior_iff] at hw
        obtain ⟨j, hj, rfl⟩ := hw
        exact ⟨(T a b)[j + 2]'(by omega), (htrack a b hab).1.2.2 (j + 1) (by omega)⟩
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
  have eliminate :
      (∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x) →
      (∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x) → False := by
    intro hcomp1 hcomp2
    have hc1 : ∀ x ∈
        {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
          e ∈ incidentEdges H (iota a1) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r1},
        G.Adj p1 x := by
      intro x hx
      exact hcomp1 x (by rw [hNc b1]; simpa [ha1] using hx)
    have hc2 : ∀ x ∈
        {z : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
          e ∈ incidentEdges H (iota a2) ∧ z = (↑(phi ⟨e, he⟩) : V)} \ {r2},
        G.Adj p2 x := by
      intro x hx
      exact hcomp2 x (by rw [hNc b2]; simpa [ha2] using hx)
    obtain ⟨w1, w1', haw1, haw1', hn1, hm1, hm1'⟩ :=
      two_active_strips_at_branch G J hJ S N H Rchoice hForms phi iota E hEedge
        hincident hEinj hEphi F p1 hp1F a1 r1 hc1
    obtain ⟨w2, w2', haw2, haw2', hn2, hm2, hm2'⟩ :=
      two_active_strips_at_branch G J hJ S N H Rchoice hForms phi iota E hEedge
        hincident hEinj hEphi F p2 hp2F a2 r2 hc2
    have ha1v := eq_common_center_of_two_active G J S N hSN _ v0 a1 w1 w1' hXv
      haw1 haw1' hn1 hm1 hm1'
    have ha2v := eq_common_center_of_two_active G J S N hSN _ v0 a2 w2 w2' hXv
      haw2 haw2' hn2 hm2 hm2'
    have hb12 : b1 = b2 := by rw [← ha1, ← ha2, ha1v, ha2v]
    exact hbne hb12
  rcases hcases with hfirst | hsecond | hthird | hfourth
  · exact hfirst
  · exact (eliminate hsecond.1 hsecond.2.1).elim
  · have hc1 : ∀ x ∈ Nc b1 \ {r1}, G.Adj p1 x := by
      intro x hx
      apply hthird.2.1 x
      refine ⟨Or.inl hx.1, ?_⟩
      intro hpair
      rcases hpair with h | h
      · exact hx.2 h
      · have hxr2 : x = r2 := h
        have hxR : x ∈ Rline := by rwa [hxr2]
        have hxI : x ∈ Nc b1 ∩ {z : V | z ∈ Rline} := ⟨hx.1, hxR⟩
        rw [hr1] at hxI
        exact hx.2 (by simpa using hxI)
    have hc2 : ∀ x ∈ Nc b2 \ {r2}, G.Adj p2 x := by
      intro x hx
      rw [← hthird.1]
      apply hthird.2.1 x
      refine ⟨Or.inr hx.1, ?_⟩
      intro hpair
      rcases hpair with h | h
      · have hxr1 : x = r1 := h
        have hxR : x ∈ Rline := by rwa [hxr1]
        have hxI : x ∈ Nc b2 ∩ {z : V | z ∈ Rline} := ⟨hx.1, hxR⟩
        rw [hr2] at hxI
        exact hx.2 (by simpa using hxI)
      · exact hx.2 h
    exact (eliminate hc1 hc2).elim
  · exact (eliminate hfourth.2.1 hfourth.2.2.1).elim

end Workspace.ProofLemmas.Thm85Claim2Cases
