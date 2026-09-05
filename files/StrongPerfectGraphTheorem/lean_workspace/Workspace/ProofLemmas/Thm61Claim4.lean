import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim2
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61Claim1Helpers
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-!
# 6.1, claim (4): `b₃` is a triad

PAPER (proof of 6.1, printed p. 30), the third claim of the odd case:

> *"(4) If `Q` is odd then `b₃` is a triad.*
>
> *For suppose not; then `f₃ ∉ E(B₃)`, and there is a second edge `f₃' ∈ X` incident with `b₃`.
> By (3), the edge `f₃` meets one of `e₁, e₂`, and from the symmetry we may assume that it meets
> `e₁`.  Thus `f₃ = b₁b₃` and `E(B₁) = {e₁}`.  Since `H` is bipartite, it follows that `B₃` is
> even.  Thus `f₃'` is not incident with `b`, and by (3) applied to `f₃'`, `e₁` and `e₂` we
> deduce that `f₃' = b₂b₃` and `E(B₂) = {e₂}`.  But the edges `e₁, e₂, f₃', f₃` contradict (2).
> This proves (4)."*

The configuration `b`, `eᵢ`, `Bᵢ`, `bᵢ`, `fᵢ` is the one fixed in the paragraph preceding (4),
named `Thm61BranchChoice.BranchChoice` / `Thm61BranchChoice.OddFChoice`; *"`b₃` is a triad"* is
`Thm61BranchChoice.Triad G H K φ Y b₃`.  The two results the printed argument cites are
`Workspace.ProofLemmas.Thm61Claim2.thm_6_1_claim2` and
`Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3`, both already proved.

The claim is applied later *"with `b, b₃` exchanged"* (end of the proof of (5)) and *"with
`b, b₁` exchanged"* (proof of (6)), which is why it is stated for an arbitrary configuration
rather than for the fixed one.

**Status: statement only — this module is a work item.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim1Helpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- An edge outside a track, incident with an internal vertex of the track, is a third
incident edge there; hence that vertex is a branch-vertex. -/
private theorem branch_of_external_edge_at_interior {W : Type*} [Finite W]
    {H : SimpleGraph W} {B : List W} {w : W} {f : Sym2 W}
    (hB : IsTrackList H B) (hw : w ∈ trackInterior B)
    (hfE : f ∈ H.edgeSet) (hwf : w ∈ f) (hfout : f ∉ trackEdges B) :
    w ∈ branchVertices H := by
  classical
  obtain ⟨j, hj, hjw⟩ := (SubdivisionCounting.mem_trackInterior_iff B w).mp hw
  let e₁ : Sym2 W := s(B[j]'(by omega), B[j + 1]'(by omega))
  let e₂ : Sym2 W := s(B[j + 1]'(by omega), B[j + 2]'(by omega))
  have he₁B : e₁ ∈ trackEdges B := ⟨j, by omega, rfl⟩
  have he₂B : e₂ ∈ trackEdges B := ⟨j + 1, by omega, rfl⟩
  have he₁E : e₁ ∈ H.edgeSet := hB.2.2 j (by omega)
  have he₂E : e₂ ∈ H.edgeSet := hB.2.2 (j + 1) (by omega)
  have hw₁ : w ∈ e₁ := by
    change w ∈ s(B[j]'(by omega), B[j + 1]'(by omega))
    rw [← hjw]
    exact Sym2.mem_mk_right _ _
  have hw₂ : w ∈ e₂ := by
    change w ∈ s(B[j + 1]'(by omega), B[j + 2]'(by omega))
    rw [← hjw]
    exact Sym2.mem_mk_left _ _
  have he₁e₂ : e₁ ≠ e₂ := by
    intro h
    dsimp [e₁, e₂] at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, -⟩ | ⟨h1, -⟩
    · have := hB.2.1.getElem_inj_iff.mp h1
      omega
    · have := hB.2.1.getElem_inj_iff.mp h1
      omega
  have he₁f : e₁ ≠ f := by
    intro h
    exact hfout (h ▸ he₁B)
  have he₂f : e₂ ≠ f := by
    intro h
    exact hfout (h ▸ he₂B)
  have hsub : ({e₁, e₂, f} : Set (Sym2 W)) ⊆ incidentEdges H w := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl
    · exact ⟨he₁E, hw₁⟩
    · exact ⟨he₂E, hw₂⟩
    · exact ⟨hfE, hwf⟩
  have hthree : ({e₁, e₂, f} : Set (Sym2 W)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨e₁, e₂, f, he₁e₂, he₁f, he₂f, rfl⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hthree, incidentEdges_ncard] at hle
  exact hle

/-- **6.1(4)** *"If `Q` is odd then `b₃` is a triad."* -/
theorem thm_6_1_claim4
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃) :
    Triad G H K φ Y b₃ := by
  classical
  rcases hbc with ⟨hb, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  rcases hf with ⟨⟨hf₁X, hf₁inc, hpref₁⟩, ⟨hf₂X, hf₂inc, hpref₂⟩,
    ⟨hf₃X, hf₃inc, hpref₃⟩⟩
  have edge_length : ∀ {B : List (Fin n)} {e : Sym2 (Fin n)},
      e ∈ trackEdges B → 1 ≤ trackLength B := by
    intro B e he
    obtain ⟨i, hi, -⟩ := he
    simp only [trackLength]
    omega
  have hlen₁ : 1 ≤ trackLength B₁ := edge_length he₁B₁
  have hlen₂ : 1 ≤ trackLength B₂ := edge_length he₂B₂
  have hlen₃ : 1 ≤ trackLength B₃ := edge_length he₃B₃
  have hlist₁ : 2 ≤ B₁.length := by simp only [trackLength] at hlen₁; omega
  have hlist₂ : 2 ≤ B₂.length := by simp only [trackLength] at hlen₂; omega
  have hlist₃ : 2 ≤ B₃.length := by simp only [trackLength] at hlen₃; omega
  have hends₁ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₁ b b₁ hB₁ hfrom₁ hlen₁
  have hends₂ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₂ b b₂ hB₂ hfrom₂ hlen₂
  have hends₃ := Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
    J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ hlen₃
  have hb₁v : b₁ ∈ branchVertices H := hends₁.2
  have hb₂v : b₂ ∈ branchVertices H := hends₂.2
  have hb₃v : b₃ ∈ branchVertices H := hends₃.2
  have ends_ne : ∀ (B : List (Fin n)) (c : Fin n), IsTrackFrom H B b c →
      2 ≤ B.length → b ≠ c := by
    intro B c hfrom hlen heq
    have h0 : B[0]'(by omega) = b := head_getElem hfrom.2.1 (by omega)
    have hl : B[B.length - 1]'(by omega) = c := last_getElem hfrom.2.2 (by omega)
    have hi : (0 : ℕ) = B.length - 1 :=
      hfrom.1.2.1.getElem_inj_iff.mp (by rw [h0, hl, heq])
    omega
  have hbb₁ : b ≠ b₁ := ends_ne B₁ b₁ hfrom₁ hlist₁
  have hbb₂ : b ≠ b₂ := ends_ne B₂ b₂ hfrom₂ hlist₂
  have hbb₃ : b ≠ b₃ := ends_ne B₃ b₃ hfrom₃ hlist₃
  obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
  have hdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have far_ne : ∀ (B B' : List (Fin n)) (c c' : Fin n) (e e' : Sym2 (Fin n)),
      IsBranch H B → IsTrackFrom H B b c → 2 ≤ B.length → c ∈ branchVertices H →
      IsBranch H B' → IsTrackFrom H B' b c' → 2 ≤ B'.length →
      e ∈ trackEdges B → e ∈ incidentEdges H b →
      e' ∈ trackEdges B' → e' ∈ incidentEdges H b → e ≠ e' → c ≠ c' := by
    intro B B' c c' e e' hBr hFr hL hc hBr' hFr' hL' heB heI heB' heI' hee' hcc'
    have hEq : trackEdges B = trackEdges B' :=
      Workspace.ProofLemmas.BranchClassification.trackEdges_eq_of_same_ends
        hι htrack hTlen hrev hdisj hnew hcover hedges hdeg
        hBr hL hFr hBr' hL' hFr' hb hc (Or.inl ⟨rfl, hcc'.symm⟩)
    have heB'' : e ∈ trackEdges B' := hEq ▸ heB
    have heFirst := trackEdge_at_head hFr' hL' heB'' heI.2
    have heFirst' := trackEdge_at_head hFr' hL' heB' heI'.2
    exact hee' (heFirst.trans heFirst'.symm)
  obtain ⟨-, -, -, -, -, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₁e₂ : e₁ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ he₁X₁) (h ▸ he₂X₂)
  have hb₁b₂ : b₁ ≠ b₂ := far_ne B₁ B₂ b₁ b₂ e₁ e₂ hB₁ hfrom₁ hlist₁ hb₁v
    hB₂ hfrom₂ hlist₂ he₁B₁ he₁inc he₂B₂ he₂inc he₁e₂
  have hb₁b₃ : b₁ ≠ b₃ := far_ne B₁ B₃ b₁ b₃ e₁ e₃ hB₁ hfrom₁ hlist₁ hb₁v
    hB₃ hfrom₃ hlist₃ he₁B₁ he₁inc he₃B₃ he₃inc he₃e₁.symm
  have hb₂b₃ : b₂ ≠ b₃ := far_ne B₂ B₃ b₂ b₃ e₂ e₃ hB₂ hfrom₂ hlist₂ hb₂v
    hB₃ hfrom₃ hlist₃ he₂B₂ he₂inc he₃B₃ he₃inc he₃e₂.symm
  refine ⟨hb₃v, ?_⟩
  intro x hx y hyx
  by_contra hxy
  have hexout : ∃ g ∈ completeEdges G H K φ Y,
      g ∈ incidentEdges H b₃ ∧ g ∉ trackEdges B₃ := by
    by_cases hxB : x ∈ trackEdges B₃
    · refine ⟨y, hyx.2, hyx.1, ?_⟩
      intro hyB
      have hxlast := trackEdge_at_last hfrom₃ hlist₃ hxB hx.1.2
      have hylast := trackEdge_at_last hfrom₃ hlist₃ hyB hyx.1.2
      exact hxy (hxlast.trans hylast.symm)
    · exact ⟨x, hx.2, hx.1, hxB⟩
  have hf₃out : f₃ ∉ trackEdges B₃ := hpref₃ hexout
  obtain ⟨f₃', hf₃'X, hf₃'inc, hf₃'ne⟩ :
      ∃ f₃' : Sym2 (Fin n), f₃' ∈ completeEdges G H K φ Y ∧
        f₃' ∈ incidentEdges H b₃ ∧ f₃' ≠ f₃ := by
    by_cases hxf₃ : x ≠ f₃
    · exact ⟨x, hx.2, hx.1, hxf₃⟩
    · have hxf₃' : x = f₃ := not_ne_iff.mp hxf₃
      have hyf₃ : y ≠ f₃ := by
        intro hyf₃
        exact hxy (hxf₃'.trans hyf₃.symm)
      exact ⟨y, hyx.2, hyx.1, hyf₃⟩
  have hbnf₃ : b ∉ f₃ := by
    intro hbf₃
    have hf₃eq : f₃ = s(b, b₃) := eq_sym2_of_mem_mem hbb₃ hbf₃ hf₃inc.2
    have hbb₃adj : H.Adj b b₃ := H.mem_edgeSet.mp (hf₃eq ▸ hf₃X.1)
    by_cases hshort : trackLength B₃ = 1
    · have hlen : B₃.length = 2 := by simp only [trackLength] at hshort; omega
      have hE := trackEdges_of_len_two hfrom₃ hlen
      apply hf₃out
      rw [hE, hf₃eq]
      exact Set.mem_singleton _
    · have hlong : 2 ≤ trackLength B₃ := by omega
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ hlong).2.2.2 hbb₃adj
  have identify : ∀ (B : List (Fin n)) (c : Fin n) (e f : Sym2 (Fin n)),
      IsBranch H B → IsTrackFrom H B b c → 2 ≤ B.length →
      c ∈ branchVertices H → b ≠ c → c ≠ b₃ →
      e ∈ trackEdges B → e ∈ incidentEdges H b →
      f ∈ H.edgeSet → f ∈ incidentEdges H b₃ → b ∉ f → MeetEdges f e →
      trackLength B = 1 ∧ e = s(b, c) ∧ f = s(c, b₃) := by
    intro B c e f hBr hFr hL hcv hbc hcb₃ heB heI hfE hfI hbnf hmeet
    have hb₃notB : b₃ ∉ B := by
      intro hb₃B
      have hb₃notint : b₃ ∉ trackInterior B := fun hi => hBr.2.1 b₃ hi hb₃v
      rcases SubdivisionCompose.mem_ends_of_mem hFr.2.1 hFr.2.2 hb₃B hb₃notint with h | h
      · exact hbb₃ h.symm
      · exact hcb₃ h.symm
    have hfoutB : f ∉ trackEdges B := by
      intro hfB
      exact trackEdge_avoids hb₃notB hfB hfI.2
    have hm : ∃ w : Fin n, w ∈ f ∧ w ∈ e := by
      simpa only [MeetEdges, DisjointEdges, not_forall, not_not] using hmeet
    obtain ⟨w, hwf, hwe⟩ := hm
    have hwb : w ≠ b := fun h => hbnf (h ▸ hwf)
    have hwB : w ∈ B := by
      obtain ⟨i, hi, hie⟩ := heB
      rw [hie] at hwe
      rcases Sym2.mem_iff.mp hwe with h | h <;> rw [h] <;> exact List.getElem_mem _
    have hwc : w = c := by
      by_contra hwc
      have hwint : w ∈ trackInterior B := by
        by_contra hwint
        rcases SubdivisionCompose.mem_ends_of_mem hFr.2.1 hFr.2.2 hwB hwint with h | h
        · exact hwb h
        · exact hwc h
      exact hBr.2.1 w hwint
        (branch_of_external_edge_at_interior hBr.1 hwint hfE hwf hfoutB)
    have heq : e = s(b, c) :=
      eq_sym2_of_mem_mem hbc heI.2 (hwc ▸ hwe)
    have hfeq : f = s(c, b₃) :=
      eq_sym2_of_mem_mem hcb₃ (hwc ▸ hwf) hfI.2
    have heFirst := trackEdge_at_head hFr hL heB heI.2
    have h0 : B[0]'(by omega) = b := head_getElem hFr.2.1 (by omega)
    have hl : B[B.length - 1]'(by omega) = c := last_getElem hFr.2.2 (by omega)
    have hcFirst : c ∈ s(B[0]'(by omega), B[1]'(by omega)) := by
      rw [← heFirst, heq]
      exact Sym2.mem_mk_right _ _
    have hc0 : c ≠ B[0]'(by omega) := by rw [h0]; exact hbc.symm
    have hc1 : c = B[1]'(by omega) := (Sym2.mem_iff.mp hcFirst).resolve_left hc0
    have hi : (1 : ℕ) = B.length - 1 :=
      hFr.1.2.1.getElem_inj_iff.mp (hc1.symm.trans hl.symm)
    have hlen : trackLength B = 1 := by simp only [trackLength]; omega
    exact ⟨hlen, heq, hfeq⟩
  have he₁e₂meet : MeetEdges e₁ e₂ := by
    intro hd
    exact hd b ⟨he₁inc.2, he₂inc.2⟩
  have hm₃ := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
    G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
    e₁ e₂ f₃ he₁X₁ he₂X₂ he₁e₂meet hf₃X
  have hm₃' := Workspace.ProofLemmas.Thm61Claim3.thm_6_1_claim3
    G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
    e₁ e₂ f₃' he₁X₁ he₂X₂ he₁e₂meet hf₃'X
  have no_other_at_b : ∀ (c : Fin n) (e f g : Sym2 (Fin n)),
      e ∈ H.edgeSet → f ∈ H.edgeSet → g ∈ incidentEdges H b₃ →
      e = s(b, c) → f = s(c, b₃) → b ∈ g → False := by
    intro c e f g heE hfE hgI heq hfeq hbg
    have hgeq : g = s(b, b₃) := eq_sym2_of_mem_mem hbb₃ hbg hgI.2
    have hbcAdj : H.Adj b c := H.mem_edgeSet.mp (heq ▸ heE)
    have hcb₃Adj : H.Adj c b₃ := H.mem_edgeSet.mp (hfeq ▸ hfE)
    have hbb₃Adj : H.Adj b b₃ := H.mem_edgeSet.mp (hgeq ▸ hgI.1)
    exact no_triangle_of_bipartite hsub.2 hbcAdj hcb₃Adj hbb₃Adj
  have four_cycle_contra : ∀ (g₁ g₂ : Sym2 (Fin n)),
      e₁ = s(b, b₁) → e₂ = s(b, b₂) →
      g₁ = s(b₁, b₃) → g₂ = s(b₂, b₃) →
      g₁ ∈ completeEdges G H K φ Y → g₂ ∈ completeEdges G H K φ Y → False := by
    intro g₁ g₂ he₁eq he₂eq hg₁eq hg₂eq hg₁X hg₂X
    have hnd : [b₁, b, b₂, b₃].Nodup := by
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hbb₁.symm, hb₁b₂, hb₁b₃⟩
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨hbb₂, hbb₃⟩
      refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
      simpa only [List.mem_singleton] using hb₂b₃
    have he₁eq' : e₁ = s(b₁, b) := by
      rw [Sym2.eq_swap]
      exact he₁eq
    have hg₁eq' : g₁ = s(b₃, b₁) := by
      rw [Sym2.eq_swap]
      exact hg₁eq
    have ha₁ : H.Adj b₁ b := H.mem_edgeSet.mp (he₁eq' ▸ he₁inc.1)
    have ha₂ : H.Adj b b₂ := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
    have ha₃ : H.Adj b₂ b₃ := H.mem_edgeSet.mp (hg₂eq ▸ hg₂X.1)
    have ha₄ : H.Adj b₃ b₁ := H.mem_edgeSet.mp (hg₁eq' ▸ hg₁X.1)
    exact Workspace.ProofLemmas.Thm61Claim2.thm_6_1_claim2
      G hG H hsub.2 K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
      b₁ b b₂ b₃ hnd ha₁ ha₂ ha₃ ha₄ hb
      (he₁eq' ▸ he₁X₁) (he₂eq ▸ he₂X₂) (hg₂eq ▸ hg₂X) (hg₁eq' ▸ hg₁X)
  rcases hm₃ with hm₃₁ | hm₃₂
  · have hi₁ := identify B₁ b₁ e₁ f₃ hB₁ hfrom₁ hlist₁ hb₁v hbb₁ hb₁b₃
      he₁B₁ he₁inc hf₃X.1 hf₃inc hbnf₃ hm₃₁
    have hbnf₃' : b ∉ f₃' := by
      intro hbf₃'
      exact no_other_at_b b₁ e₁ f₃ f₃' he₁inc.1 hf₃X.1 hf₃'inc
        hi₁.2.1 hi₁.2.2 hbf₃'
    rcases hm₃' with hm₃₁' | hm₃₂'
    · have hi₁' := identify B₁ b₁ e₁ f₃' hB₁ hfrom₁ hlist₁ hb₁v hbb₁ hb₁b₃
        he₁B₁ he₁inc hf₃'X.1 hf₃'inc hbnf₃' hm₃₁'
      exact hf₃'ne (hi₁'.2.2.trans hi₁.2.2.symm)
    · have hi₂ := identify B₂ b₂ e₂ f₃' hB₂ hfrom₂ hlist₂ hb₂v hbb₂ hb₂b₃
        he₂B₂ he₂inc hf₃'X.1 hf₃'inc hbnf₃' hm₃₂'
      exact four_cycle_contra f₃ f₃' hi₁.2.1 hi₂.2.1 hi₁.2.2 hi₂.2.2
        hf₃X hf₃'X
  · have hi₂ := identify B₂ b₂ e₂ f₃ hB₂ hfrom₂ hlist₂ hb₂v hbb₂ hb₂b₃
      he₂B₂ he₂inc hf₃X.1 hf₃inc hbnf₃ hm₃₂
    have hbnf₃' : b ∉ f₃' := by
      intro hbf₃'
      exact no_other_at_b b₂ e₂ f₃ f₃' he₂inc.1 hf₃X.1 hf₃'inc
        hi₂.2.1 hi₂.2.2 hbf₃'
    rcases hm₃' with hm₃₁' | hm₃₂'
    · have hi₁ := identify B₁ b₁ e₁ f₃' hB₁ hfrom₁ hlist₁ hb₁v hbb₁ hb₁b₃
        he₁B₁ he₁inc hf₃'X.1 hf₃'inc hbnf₃' hm₃₁'
      exact four_cycle_contra f₃' f₃ hi₁.2.1 hi₂.2.1 hi₁.2.2 hi₂.2.2
        hf₃'X hf₃X
    · have hi₂' := identify B₂ b₂ e₂ f₃' hB₂ hfrom₂ hlist₂ hb₂v hbb₂ hb₂b₃
        he₂B₂ he₂inc hf₃'X.1 hf₃'inc hbnf₃' hm₃₂'
      exact hf₃'ne (hi₂'.2.2.trans hi₂.2.2.symm)

end Workspace.ProofLemmas.Thm61Claim4
