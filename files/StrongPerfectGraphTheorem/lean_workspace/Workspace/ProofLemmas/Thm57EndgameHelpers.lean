import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm57Setup
import Workspace.ProofLemmas.Thm57Claim4
import Workspace.ProofLemmas.Thm57EndgameConnectivity
import Workspace.ProofLemmas.Thm57EndgameParity
import Workspace.ProofLemmas.Thm57EndgameKonig
import Workspace.ProofLemmas.Thm57EndgameComponent
import Workspace.ProofLemmas.Thm57EndgameSeparation
import Workspace.ProofLemmas.TrackSlice
import Workspace.Statements.S05.Thm_5_5
import Workspace.Statements.S05.Thm_5_6

/-!
# The two-centre reduction and the 5.6 step in the endgame of 5.7

This module follows the last two paragraphs of the printed proof.  It separates the graph
separation step from the set bookkeeping needed to apply 5.6.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameHelpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Remaining gap in the first paragraph of the endgame (printed pp. 24--25):

> By (4), there is no 3-edge matching among the edges in `X` that meet `V(A)`; and since this
> set of edges forms a bipartite subgraph, it follows from Kőnig's theorem that there are two
> vertices `c₁,c₂` such that every such edge is incident with one of them. ... Hence every
> edge in `X` is incident with one of `c₁,c₂`.

The conclusion also records the preceding use of (2), which lets the proof choose the two
centres outside a common branch. -/
theorem twoCentresCover_gap (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hdisj : TwoDisjointEdges H X) (hnoB : ¬ SomeBranchMeetsAll H X)
    (hnotsat : ¬ SaturatesLineGraph H X)
    (hclaim4 : ¬ ∃ (A : Set W) (x₁ x₂ x₃ : Sym2 W),
      ConnectedSet (H.deleteEdges X) A ∧
      x₁ ∈ X ∧ x₂ ∈ X ∧ x₃ ∈ X ∧
      DisjointEdges x₁ x₂ ∧ DisjointEdges x₁ x₃ ∧ DisjointEdges x₂ x₃ ∧
      (∃ v ∈ A, v ∈ x₁) ∧ (∃ v ∈ A, v ∈ x₂) ∧ (∃ v ∈ A, v ∈ x₃)) :
    ∃ c₁ c₂ : W,
      (¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
      X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂ := by
  classical
  obtain ⟨A, hconn, hlarge, hnoA, hboundary⟩ :=
    Thm57EndgameComponent.exists_component H hc3 X hnotsat
  obtain ⟨a, _⟩ := Set.nonempty_of_ncard_ne_zero (by omega : A.ncard ≠ 0)
  letI : Nonempty W := ⟨a⟩
  let Y : Set (Sym2 W) := {e ∈ X | ∃ v ∈ A, v ∈ e}
  have hYE : Y ⊆ H.edgeSet := fun _ he => hXE he.1
  have hno : ¬ ∃ e ∈ Y, ∃ f ∈ Y, ∃ g ∈ Y,
      DisjointEdges e f ∧ DisjointEdges e g ∧ DisjointEdges f g := by
    rintro ⟨e, he, f, hf, g, hg, hef, heg, hfg⟩
    exact hclaim4 ⟨A, e, f, g, hconn, he.1, hf.1, hg.1,
      hef, heg, hfg, he.2, hf.2, hg.2⟩
  obtain ⟨c₁, c₂, hcover⟩ := Thm57EndgameKonig.two_vertex_cover H hbip Y hYE hno
  exact ⟨c₁, c₂, Thm57EndgameSeparation.extend_cover H hc3 X hXE hnoB A hlarge
    hnoA hboundary c₁ c₂ (fun e he hmeet => hcover e ⟨he, hmeet⟩)⟩

/-- Remaining separation facts used when 5.5 and then 5.6 are applied in the endgame:

> Consequently `c₁,c₂` are nonadjacent, and `H \ {c₁,c₂}` is connected, by 5.5.

The last conjunct is the same 5.5 separation argument for the ends of an edge in
`A₁ ∪ A₂`; it is the connectivity premise in the printed application of 5.6. -/
theorem connectivityFacts_gap (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    (c₁ c₂ : W)
    (hnoBranch : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    ¬ H.Adj c₁ c₂ ∧
      ConnectedSet H (({c₁, c₂} : Set W)ᶜ) ∧
      ∀ e ∈ H.edgeSet, ∀ u v : W, e = s(u, v) →
        ConnectedSet H (({u, v} : Set W)ᶜ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hadj
    exact hnoBranch
      (Thm57EndgameConnectivity.adjacent_vertices_lie_in_branch H hc3 hadj)
  · exact Thm57EndgameConnectivity.connected_compl_pair_of_no_common_branch
      H hc3 c₁ c₂ hnoBranch
  · exact Thm57EndgameConnectivity.edgeEndDeletionConnected_gap H hc3

/-- Remaining parity step in the last paragraph of the proof:

> By (1) we may assume that there exist disjoint edges `a₁c₁ ∈ A₁` and
> `a₂c₂ ∈ A₂`. Take a minimal track in `H \ {c₁,c₂}` between `a₁,a₂`;
> then by the hypothesis of the theorem, this track has odd length, and so `c₁,c₂` have
> opposite biparity.
-/
theorem coverCentresDifferentBiparity_gap (H : SimpleGraph W) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet) (hnotrack : NoEvenTrack57 H X)
    (c₁ c₂ : W) (hconn : ConnectedSet H (({c₁, c₂} : Set W)ᶜ))
    (hcover : X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (hdisj : TwoDisjointEdges H X) :
    DifferentBiparity H c₁ c₂ := by
  exact Thm57EndgameParity.coverCentresDifferentBiparity
    H hbip X hXE hnotrack c₁ c₂ hconn hcover hdisj

private theorem sym2_eq_of_mem_of_mem {a b : W} {e : Sym2 W}
    (ha : a ∈ e) (hb : b ∈ e) (hab : a ≠ b) : e = s(a, b) := by
  exact (Sym2.mem_and_mem_iff hab).mp ⟨ha, hb⟩

private theorem last_getElem {l : List W} {b : W} (h : l.getLast? = some b)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = b := by
  have hne : l ≠ [] := by intro hc; subst hc; simp at h0
  have h1 := List.getLast?_eq_some_getLast hne
  rw [h] at h1
  have h2 : b = l.getLast hne := Option.some_injective _ h1
  rw [h2]
  exact (List.getLast_eq_getElem hne).symm

private theorem allocate_disjoint_edges (H : SimpleGraph W) (X : Set (Sym2 W))
    (c₁ c₂ : W) (hcover : X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (hdisj : TwoDisjointEdges H X) :
    ∃ e₁ ∈ incidentEdges H c₁ ∩ X, ∃ e₂ ∈ incidentEdges H c₂ ∩ X,
      DisjointEdges e₁ e₂ := by
  obtain ⟨e, heX, f, hfX, hef⟩ := hdisj
  rcases hcover heX with he1 | he2
  · rcases hcover hfX with hf1 | hf2
    · exact False.elim (hef c₁ ⟨he1.2, hf1.2⟩)
    · exact ⟨e, ⟨he1, heX⟩, f, ⟨hf2, hfX⟩, hef⟩
  · rcases hcover hfX with hf1 | hf2
    · refine ⟨f, ⟨hf1, hfX⟩, e, ⟨he2, heX⟩, ?_⟩
      intro w hw
      exact hef w ⟨hw.2, hw.1⟩
    · exact False.elim (hef c₂ ⟨he2.2, hf2.2⟩)

private theorem differentBiparity_symm {H : SimpleGraph W} {a b : W}
    (h : DifferentBiparity H a b) : DifferentBiparity H b a := by
  intro q hq
  have hr := h q.reverse (Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hq)
  simpa only [trackLength, List.length_reverse] using hr

/-- A track returned by alternative 1 of 5.6 would be an even track forbidden by the
hypothesis of 5.7. -/
private theorem no_five_six_track (H : SimpleGraph W) (X : Set (Sym2 W))
    (hnotrack : NoEvenTrack57 H X) (c₁ c₂ : W)
    (hcover : X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (hdiff : DifferentBiparity H c₁ c₂)
    (q : List W) (hlen : 3 ≤ q.length) (hq : IsTrackList H q)
    (hfirst : s(q[0], q[1]) ∈ incidentEdges H c₁ ∩ X)
    (hsecond : s(q[1], q[2]) ∈
      incidentEdges H c₁ \ (incidentEdges H c₁ ∩ X))
    (hlastv : q.getLast? = some c₂)
    (hlast : s(q[q.length - 2], q[q.length - 1]) ∈ incidentEdges H c₂ ∩ X) :
    False := by
  have hq1c : q[1]'(by omega) = c₁ := by
    by_contra hne
    have hfirstEq : s(q[0], q[1]) = s(q[1], c₁) :=
      sym2_eq_of_mem_of_mem (by simp) hfirst.1.2 hne
    have hsecondEq : s(q[1], q[2]) = s(q[1], c₁) :=
      sym2_eq_of_mem_of_mem (by simp) hsecond.1.2 hne
    apply hsecond.2
    rw [hsecondEq, ← hfirstEq]
    exact hfirst
  have htail : IsTrackFrom H q.tail c₁ c₂ := by
    refine ⟨⟨?_, hq.2.1.tail, ?_⟩, ?_, ?_⟩
    · intro he
      have : q.tail.length = 0 := by rw [he]; rfl
      simp only [List.length_tail] at this
      omega
    · intro i hi
      have h := hq.2.2 (i + 1) (by simp only [List.length_tail] at hi; omega)
      simpa only [List.getElem_tail] using h
    · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by
        simp only [List.length_tail]; omega)]
      exact congrArg some (by simpa only [List.getElem_tail] using hq1c)
    · rw [List.getLast?_tail, if_neg (by omega)]
      exact hlastv
  have hoddTail : Odd (trackLength q.tail) := hdiff q.tail htail
  have heven : Even (trackLength q) := by
    obtain ⟨k, hk⟩ := hoddTail
    refine ⟨k + 1, ?_⟩
    simp only [trackLength, List.length_tail] at hk ⊢
    omega
  have hnot3 : q.length ≠ 3 := by
    intro h3
    have hi1 : q[1]'(by omega) = q[q.length - 2]'(by omega) :=
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q (by omega)
        (by omega) (by omega)
    have hi2 : q[2]'(by omega) = q[q.length - 1]'(by omega) :=
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q (by omega)
        (by omega) (by omega)
    have hedge : s(q[1], q[2]) = s(q[q.length - 2], q[q.length - 1]) := by
      exact congrArg₂ (fun a b : W => s(a, b)) hi1 hi2
    apply hsecond.2
    exact ⟨hsecond.1, hedge ▸ hlast.2⟩
  have h5 : 5 ≤ q.length := by
    obtain ⟨k, hk⟩ := heven
    simp only [trackLength] at hk
    omega
  apply hnotrack
  refine ⟨q, h5, hq, heven, hfirst.2, hlast.2, ?_⟩
  intro e he heFirst heLast heX
  obtain ⟨i, hi, rfl⟩ := he
  rcases hcover heX with hc1 | hc2
  · rcases Sym2.mem_iff.mp hc1.2 with hic | hic
    · have hii : i = 1 := hq.2.1.getElem_inj_iff.mp
        (hic.symm.trans hq1c.symm)
      subst i
      exact hsecond.2 ⟨hsecond.1, heX⟩
    · have hii : i + 1 = 1 := hq.2.1.getElem_inj_iff.mp
        (hic.symm.trans hq1c.symm)
      have : i = 0 := by omega
      subst i
      exact heFirst rfl
  · have hlastElem : q[q.length - 1]'(by omega) = c₂ :=
      last_getElem hlastv (by omega)
    rcases Sym2.mem_iff.mp hc2.2 with hic | hic
    · have hii : i = q.length - 1 := hq.2.1.getElem_inj_iff.mp
        (hic.symm.trans hlastElem.symm)
      omega
    · have hii : i + 1 = q.length - 1 := hq.2.1.getElem_inj_iff.mp
        (hic.symm.trans hlastElem.symm)
      have : i = q.length - 2 := by omega
      subst i
      apply heLast
      exact congrArg (fun z : W => s(q[q.length - 2], z))
        (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
          (by omega) (by omega) (by omega))

/-- The part of the endgame after the two covering vertices have been found. -/
theorem endgame_from_two_centres (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) (hdisj : TwoDisjointEdges H X)
    (c₁ c₂ : W)
    (hnoBranch : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hcover : X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂) :
    Stmt57_6 H X := by
  classical
  obtain ⟨hnadj, hconn, hEdgeConn⟩ := connectivityFacts_gap H hc3 c₁ c₂ hnoBranch
  have hdiff : DifferentBiparity H c₁ c₂ :=
    coverCentresDifferentBiparity_gap H hbip X hXE hnotrack c₁ c₂ hconn hcover hdisj
  let A₁ : Set (Sym2 W) := incidentEdges H c₁ ∩ X
  let B₁ : Set (Sym2 W) := incidentEdges H c₁ \ A₁
  let A₂ : Set (Sym2 W) := incidentEdges H c₂ ∩ X
  let B₂ : Set (Sym2 W) := incidentEdges H c₂ \ A₂
  obtain ⟨e₁, he₁, e₂, he₂, hedisj⟩ :=
    allocate_disjoint_edges H X c₁ c₂ hcover hdisj
  have he₁A : e₁ ∈ A₁ := he₁
  have he₂A : e₂ ∈ A₂ := he₂
  have hpart₁ : A₁ ∪ B₁ = incidentEdges H c₁ := by
    ext e
    simp only [A₁, B₁, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hpart₂ : A₂ ∪ B₂ = incidentEdges H c₂ := by
    ext e
    simp only [A₂, B₂, Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hpartsDisj₁ : Disjoint A₁ B₁ := by
    refine Set.disjoint_left.mpr ?_
    intro e heA heB
    exact heB.2 heA
  have hpartsDisj₂ : Disjoint A₂ B₂ := by
    refine Set.disjoint_left.mpr ?_
    intro e heA heB
    exact heB.2 heA
  have hAconn : ∀ e ∈ A₁ ∪ A₂, ∀ u v : W, e = s(u, v) →
      ConnectedSet H (({u, v} : Set W)ᶜ) := by
    intro e he u v huv
    apply hEdgeConn e
    · rcases he with he | he
      · exact he.1.1
      · exact he.1.1
    · exact huv
  have hnocover : ¬ ∃ w : W, ∀ e ∈ A₁ ∪ A₂, w ∈ e := by
    rintro ⟨w, hw⟩
    exact hedisj w ⟨hw e₁ (Or.inl he₁A), hw e₂ (Or.inr he₂A)⟩
  have hBempty : B₁ = ∅ ∧ B₂ = ∅ := by
    have hnone : ¬ (B₁.Nonempty ∨ B₂.Nonempty) := by
      intro hB
      have hout := _root_.Workspace.Statements.S05.SPGT.thm_5_6
        H c₁ c₂ hnadj hconn A₁ B₁ A₂ B₂ hpart₁ hpartsDisj₁
        hpart₂ hpartsDisj₂ ⟨e₁, he₁A⟩ ⟨e₂, he₂A⟩ hB hAconn hnocover
      rcases hout with ⟨q, hlen, hq, hfirst, hsecond, hlastv, hlast⟩ |
          ⟨q, hlen, hq, hfirst, hsecond, hlastv, hlast⟩
      · exact no_five_six_track H X hnotrack c₁ c₂ hcover hdiff q hlen hq
          hfirst hsecond hlastv hlast
      · have hcover' : X ⊆ incidentEdges H c₂ ∪ incidentEdges H c₁ := by
          intro e he
          rcases hcover he with he | he
          · exact Or.inr he
          · exact Or.inl he
        exact no_five_six_track H X hnotrack c₂ c₁ hcover'
          (differentBiparity_symm hdiff) q hlen hq hfirst hsecond hlastv hlast
    constructor
    · apply Set.not_nonempty_iff_eq_empty.mp
      intro h
      exact hnone (Or.inl h)
    · apply Set.not_nonempty_iff_eq_empty.mp
      intro h
      exact hnone (Or.inr h)
  have hstars : incidentEdges H c₁ ∪ incidentEdges H c₂ ⊆ X := by
    intro e he
    rcases he with he | he
    · have : e ∈ A₁ ∪ B₁ := hpart₁.symm ▸ he
      rcases this with heA | heB
      · exact heA.2
      · rw [hBempty.1] at heB
        exact False.elim heB
    · have : e ∈ A₂ ∪ B₂ := hpart₂.symm ▸ he
      rcases this with heA | heB
      · exact heA.2
      · rw [hBempty.2] at heB
        exact False.elim heB
  exact ⟨c₁, c₂, hdiff, hnoBranch, Set.Subset.antisymm hcover hstars⟩

/-- The complete endgame, reduced to its two-centre step and the later 5.6 argument. -/
theorem endgame_core (H : SimpleGraph W) (hbip : H.IsBipartite)
    (hc3 : CyclicallyThreeConnected H) (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet)
    (hnotrack : NoEvenTrack57 H X) (hdisj : TwoDisjointEdges H X)
    (hnoB : ¬ SomeBranchMeetsAll H X) (hnotsat : ¬ SaturatesLineGraph H X) :
    Stmt57_6 H X := by
  have hclaim4 := Workspace.ProofLemmas.Thm57Claim4.thm57Claim4
    H hbip hc3 X hXE hnotrack
  obtain ⟨c₁, c₂, hnoBranch, hcover⟩ :=
    twoCentresCover_gap H hbip hc3 X hXE hdisj hnoB hnotsat hclaim4
  exact endgame_from_two_centres H hbip hc3 X hXE hnotrack hdisj
    c₁ c₂ hnoBranch hcover

end Workspace.ProofLemmas.Thm57EndgameHelpers
