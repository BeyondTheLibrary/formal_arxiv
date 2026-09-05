import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm57EndgameEdgeDeletion
import Workspace.Statements.S05.Thm_5_5

/-!
# Separation facts for the endgame of 5.7

Theorem 5.5 says that a separation of a cyclically 3-connected graph with at most two shared
vertices has one side inside a branch.  We use its contrapositive for two vertices which are
not together in a branch.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameConnectivity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Every edge of a cyclically 3-connected graph is contained in one of its branches. -/
theorem adjacent_vertices_lie_in_branch (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) {a b : W} (hab : H.Adj a b) :
    ∃ q : List W, IsBranch H q ∧ a ∈ q ∧ b ∈ q := by
  classical
  obtain ⟨n, J, hJ, ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hc3
  have hdeg : ∀ u : Fin n, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices
      hι htrack hlen hdisj hnew hdeg
  have hbrange : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  have hbranch : ∀ u v : Fin n, J.Adj u v → IsBranch H (T u v) := by
    intro u v huv
    apply Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
    · exact fun h => huv.ne (hι h)
    · intro w hw hwb
      exact hnew u v huv w hw (hbrange hwb)
    · exact hrange ⟨u, rfl⟩
    · exact hrange ⟨v, rfl⟩
  have hedge : s(a, b) ∈ H.edgeSet := H.mem_edgeSet.mpr hab
  rw [hedges] at hedge
  simp only [Set.mem_iUnion] at hedge
  obtain ⟨u, v, huv, he⟩ := hedge
  obtain ⟨i, hi, hie⟩ := he
  refine ⟨T u v, hbranch u v huv, ?_, ?_⟩
  · rcases Sym2.eq_iff.mp hie with h | h
    · rw [h.1]
      exact List.getElem_mem _
    · rw [h.1]
      exact List.getElem_mem _
  · rcases Sym2.eq_iff.mp hie with h | h
    · rw [h.2]
      exact List.getElem_mem _
    · rw [h.2]
      exact List.getElem_mem _

/-- If two vertices of a cyclically 3-connected graph are not together in a branch, deleting
them leaves a connected set.  This is the direct contrapositive use of 5.5 in the endgame. -/
theorem connected_compl_pair_of_no_common_branch (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) (c₁ c₂ : W)
    (hnoBranch : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) :
    ConnectedSet H (({c₁, c₂} : Set W)ᶜ) := by
  classical
  let P : Set W := {c₁, c₂}
  let S : Set W := Pᶜ
  by_contra hcon
  unfold ConnectedSet at hcon
  change ¬ ∀ u v, (H.induce S).Reachable u v at hcon
  push Not at hcon
  obtain ⟨u, v, huv⟩ := hcon
  let R : Set W := {x : W | ∃ hx : x ∈ S,
    (H.induce S).Reachable u ⟨x, hx⟩}
  have hRiff : ∀ {x y : W}, x ∈ S → y ∈ S → H.Adj x y → (x ∈ R ↔ y ∈ R) := by
    intro x y hxS hyS hxy
    constructor
    · rintro ⟨hxS', hreach⟩
      have hadj : (H.induce S).Adj ⟨x, hxS'⟩ ⟨y, hyS⟩ := hxy
      exact ⟨hyS, hreach.trans (SimpleGraph.Adj.reachable hadj)⟩
    · rintro ⟨hyS', hreach⟩
      have hadj : (H.induce S).Adj ⟨y, hyS'⟩ ⟨x, hxS⟩ := hxy.symm
      exact ⟨hxS, hreach.trans (SimpleGraph.Adj.reachable hadj)⟩
  let CV : Set W := R ∪ P
  let DV : Set W := (S \ R) ∪ P
  let C : H.Subgraph := (⊤ : H.Subgraph).induce CV
  let D : H.Subgraph := (⊤ : H.Subgraph).induce DV
  have hvertex : ∀ x : W, x ∈ CV ∨ x ∈ DV := by
    intro x
    by_cases hxP : x ∈ P
    · exact Or.inl (Or.inr hxP)
    · have hxS : x ∈ S := hxP
      by_cases hxR : x ∈ R
      · exact Or.inl (Or.inl hxR)
      · exact Or.inr (Or.inl ⟨hxS, hxR⟩)
  have hedgeSide : ∀ {x y : W}, H.Adj x y →
      (x ∈ CV ∧ y ∈ CV) ∨ (x ∈ DV ∧ y ∈ DV) := by
    intro x y hxy
    by_cases hxP : x ∈ P
    · rcases hvertex y with hyC | hyD
      · exact Or.inl ⟨Or.inr hxP, hyC⟩
      · exact Or.inr ⟨Or.inr hxP, hyD⟩
    by_cases hyP : y ∈ P
    · rcases hvertex x with hxC | hxD
      · exact Or.inl ⟨hxC, Or.inr hyP⟩
      · exact Or.inr ⟨hxD, Or.inr hyP⟩
    have hxS : x ∈ S := hxP
    have hyS : y ∈ S := hyP
    by_cases hxR : x ∈ R
    · have hyR : y ∈ R := (hRiff hxS hyS hxy).mp hxR
      exact Or.inl ⟨Or.inl hxR, Or.inl hyR⟩
    · have hyR : y ∉ R := fun h => hxR ((hRiff hxS hyS hxy).mpr h)
      exact Or.inr ⟨Or.inl ⟨hxS, hxR⟩, Or.inl ⟨hyS, hyR⟩⟩
  have hunion : C ⊔ D = ⊤ := by
    apply le_antisymm le_top
    constructor
    · intro x _
      rcases hvertex x with hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
    · intro x y hxy
      rcases hedgeSide hxy with h | h
      · exact Or.inl ⟨h.1, h.2, hxy⟩
      · exact Or.inr ⟨h.1, h.2, hxy⟩
  have hcapSub : (C ⊓ D).verts ⊆ P := by
    intro x hx
    change x ∈ CV ∩ DV at hx
    by_cases hxP : x ∈ P
    · exact hxP
    have hxR : x ∈ R := hx.1.resolve_right hxP
    have hxNR : x ∈ S \ R := hx.2.resolve_right hxP
    exact False.elim (hxNR.2 hxR)
  have hcap : (C ⊓ D).verts.ncard ≤ 2 := by
    have hle := Set.ncard_le_ncard hcapSub (Set.toFinite _)
    have hPle : P.ncard ≤ 2 := by
      calc
        P.ncard = ({c₁, c₂} : Set W).ncard := rfl
        _ ≤ ({c₂} : Set W).ncard + 1 := Set.ncard_insert_le c₁ {c₂}
        _ = 2 := by simp
    omega
  have huR : (u : W) ∈ R := ⟨u.2, SimpleGraph.Reachable.refl u⟩
  have hvNR : (v : W) ∉ R := by
    rintro ⟨hvS, hreach⟩
    exact huv hreach
  have hCne : C.verts ≠ Set.univ := by
    change CV ≠ Set.univ
    apply (Set.ne_univ_iff_exists_notMem CV).mpr
    refine ⟨(v : W), ?_⟩
    intro hvC
    rcases hvC with hvR | hvP
    · exact hvNR hvR
    · exact v.2 hvP
  have hDne : D.verts ≠ Set.univ := by
    change DV ≠ Set.univ
    apply (Set.ne_univ_iff_exists_notMem DV).mpr
    refine ⟨(u : W), ?_⟩
    intro huD
    rcases huD with huSR | huP
    · exact huSR.2 huR
    · exact u.2 huP
  rcases _root_.Workspace.Statements.S05.SPGT.thm_5_5
      H hc3 C D hunion hcap hCne hDne with hC | hD
  · obtain ⟨q, hq, hCV, -⟩ := hC
    apply hnoBranch
    refine ⟨q, hq, hCV ?_, hCV ?_⟩
    · exact Or.inr (by simp [P])
    · exact Or.inr (by simp [P])
  · obtain ⟨q, hq, hDV, -⟩ := hD
    apply hnoBranch
    refine ⟨q, hq, hDV ?_, hDV ?_⟩
    · exact Or.inr (by simp [P])
    · exact Or.inr (by simp [P])

/-- Remaining implicit connectivity premise in the paper's application of 5.6 (printed p. 21):

> Assume that for every edge `uv ∈ A₁ ∪ A₂`, `H \ {u,v}` is connected.

For theorem 5.7, each member of `A₁ ∪ A₂` is an edge of the cyclically 3-connected graph `H`,
so this lemma records exactly the instance needed at the call to 5.6. -/
theorem edgeEndDeletionConnected_gap (H : SimpleGraph W)
    (hc3 : CyclicallyThreeConnected H) (e : Sym2 W) (he : e ∈ H.edgeSet)
    (u v : W) (huv : e = s(u, v)) : ConnectedSet H (({u, v} : Set W)ᶜ) := by
  apply Thm57EndgameEdgeDeletion.connected_compl_edge H hc3
  exact H.mem_edgeSet.mp (huv ▸ he)

end Workspace.ProofLemmas.Thm57EndgameConnectivity
