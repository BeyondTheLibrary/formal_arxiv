import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim2
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers
import Workspace.ProofLemmas.Thm61OddLabelled
import Workspace.ProofLemmas.Thm61OddEdgeClasses
import Workspace.ProofLemmas.Thm61OddComplement

/-!
# 6.1(7): the short-branch endgame

This module isolates the last paragraph of the odd case.  Claims (5) and (6) reduce the proof
to the case in which each of the three branches chosen at `b` has one edge.  The paper then
identifies the resulting graph and constructs the enlargement in the complement.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61OddEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim2
open Workspace.ProofLemmas.Thm61Claim3
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- The part of the last paragraph of (7) that names `x₁,x₂` and joins them to `b₃`. -/
def ShortOddSkeleton {V : Type*} (G : SimpleGraph V)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (b₁ b₂ b₃ x₁ x₂ : Fin n) (f₁ f₂ : Sym2 (Fin n)) : Prop :=
  f₁ = s(b₁, x₁) ∧ f₂ = s(b₂, x₂) ∧ x₁ ≠ x₂ ∧
  H.Adj b₁ x₁ ∧ H.Adj b₂ x₂ ∧ H.Adj x₁ b₃ ∧ H.Adj x₂ b₃ ∧
  s(x₁, b₃) ∉ completeEdges G H K φ Y ∧
  s(x₂, b₃) ∉ completeEdges G H K φ Y

/-- The first four sentences of the short-branch endgame in 6.1(7). -/
theorem short_odd_skeleton
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    (htriad₃ : Triad G H K φ Y b₃)
    (hB₁ : trackLength B₁ = 1) (hB₂ : trackLength B₂ = 1)
    (hB₃ : trackLength B₃ = 1) :
    ∃ x₁ x₂ : Fin n, ShortOddSkeleton G H K φ Y b₁ b₂ b₃ x₁ x₂ f₁ f₂ := by
  classical
  have hbc' := hbc
  rcases hbc' with ⟨hbV, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, -, -,
    hBr₁, he₁B₁, hfrom₁, hBr₂, he₂B₂, hfrom₂, hBr₃, he₃B₃, hfrom₃⟩
  have hf' := hf
  rcases hf' with ⟨⟨hf₁X, hf₁inc, -⟩, ⟨hf₂X, hf₂inc, -⟩, ⟨-, -, -⟩⟩
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, -, -⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  obtain ⟨-, -, -, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
    hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  have he₁eq : e₁ = s(b, b₁) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁] at he₁B₁
    exact Set.mem_singleton_iff.mp he₁B₁
  have he₂eq : e₂ = s(b, b₂) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂] at he₂B₂
    exact Set.mem_singleton_iff.mp he₂B₂
  have he₃eq : e₃ = s(b, b₃) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₃ hB₃] at he₃B₃
    exact Set.mem_singleton_iff.mp he₃B₃
  obtain ⟨x₁, -, hf₁eq⟩ := edge_track_from_incident hf₁inc
  obtain ⟨x₂, -, hf₂eq⟩ := edge_track_from_incident hf₂inc
  have hb₁x₁ : H.Adj b₁ x₁ := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [← hf₁eq]
    exact hf₁inc.1
  have hb₂x₂ : H.Adj b₂ x₂ := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [← hf₂eq]
    exact hf₂inc.1
  have hbb₁A : H.Adj b b₁ := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [← he₁eq]
    exact he₁inc.1
  have hbb₂A : H.Adj b b₂ := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [← he₂eq]
    exact he₂inc.1
  have hbb₃A : H.Adj b b₃ := by
    apply (SimpleGraph.mem_edgeSet H).mp
    rw [← he₃eq]
    exact he₃inc.1
  have hf₁e₁ : f₁ ≠ e₁ := by
    intro h
    exact (Set.disjoint_left.mp hXX₁ hf₁X) (h ▸ he₁X₁)
  have hf₂e₂ : f₂ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hXX₂ hf₂X) (h ▸ he₂X₂)
  have hx₁b : x₁ ≠ b := by
    intro h
    apply hf₁e₁
    rw [hf₁eq, he₁eq, h, Sym2.eq_swap]
  have hx₂b : x₂ ≠ b := by
    intro h
    apply hf₂e₂
    rw [hf₂eq, he₂eq, h, Sym2.eq_swap]
  have hx₁b₃ : x₁ ≠ b₃ := by
    intro h
    exact no_triangle_of_bipartite hsub.2 hbb₁A.symm hbb₃A (h ▸ hb₁x₁)
  have hx₂b₃ : x₂ ≠ b₃ := by
    intro h
    exact no_triangle_of_bipartite hsub.2 hbb₂A.symm hbb₃A (h ▸ hb₂x₂)
  have hx₁x₂ : x₁ ≠ x₂ := by
    intro hxeq
    have hb₂x₁ : b₂ ≠ x₁ := by
      rw [hxeq]
      exact hb₂x₂.ne
    have hnd : [b₁, b, b₂, x₁].Nodup := by
      simp [hbb₁.symm, hb₁b₂, hb₁x₁.ne, hbb₂, hx₁b.symm, hb₂x₁]
    have hX₁ : s(b₁, b) ∈ extraEdges G H K φ Y y₁ := by
      simpa [he₁eq, Sym2.eq_swap] using he₁X₁
    have hX₂ : s(b, b₂) ∈ extraEdges G H K φ Y y₂ := by
      simpa [he₂eq] using he₂X₂
    have hX₃ : s(b₂, x₁) ∈ completeEdges G H K φ Y := by
      simpa [hf₂eq, hxeq] using hf₂X
    have hX₄ : s(x₁, b₁) ∈ completeEdges G H K φ Y := by
      simpa [hf₁eq, Sym2.eq_swap] using hf₁X
    exact thm_6_1_claim2 G hG H hsub.2 K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
      b₁ b b₂ x₁ hnd hbb₁A.symm hbb₂A (hxeq ▸ hb₂x₂) hb₁x₁.symm hbV
      hX₁ hX₂ hX₃ hX₄
  obtain ⟨-, -, ⟨g₁, hg₁, -⟩, ⟨g₂, hg₂, -⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₃ htriad₃
  have hg₁g₂ : MeetEdges g₁ g₂ := by
    intro hdisj
    exact hdisj b₃ ⟨hg₁.1.2, hg₂.1.2⟩
  have cross : ∀ (bi xi : Fin n) (f : Sym2 (Fin n)),
      H.Adj b bi → H.Adj bi xi → bi ≠ b₃ → xi ≠ b₃ →
      f = s(bi, xi) → f ∈ completeEdges G H K φ Y →
      H.Adj xi b₃ ∧ s(xi, b₃) ∉ completeEdges G H K φ Y := by
    intro bi xi f hbbi hbixi hbibr hxibr hfeq hfX
    have hm := thm_6_1_claim3 G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQodd
      g₁ g₂ f hg₁.2 hg₂.2 hg₁g₂ hfX
    have finish : ∀ (g : Sym2 (Fin n)), g ∈ incidentEdges H b₃ →
        g ∉ completeEdges G H K φ Y → MeetEdges f g →
        H.Adj xi b₃ ∧ s(xi, b₃) ∉ completeEdges G H K φ Y := by
      intro g hginc hgnotX hmeet
      obtain ⟨w, hwf, hwg⟩ := exists_common_end hmeet
      rw [hfeq] at hwf
      rcases Sym2.mem_iff.mp hwf with hwi | hwx
      · have hbi3 : H.Adj bi b₃ := by
          apply (SimpleGraph.mem_edgeSet H).mp
          have hge := hginc.1
          have hgeq : g = s(b₃, bi) := eq_sym2_of_mem_mem hbibr.symm hginc.2 (hwi ▸ hwg)
          rwa [hgeq, Sym2.eq_swap] at hge
        exact False.elim (no_triangle_of_bipartite hsub.2 hbbi.symm hbb₃A hbi3)
      · have hgeq : g = s(b₃, xi) :=
          eq_sym2_of_mem_mem hxibr.symm hginc.2 (hwx ▸ hwg)
        have hadj : H.Adj xi b₃ := by
          have hge := hginc.1
          rw [hgeq] at hge
          exact ((SimpleGraph.mem_edgeSet H).mp hge).symm
        refine ⟨hadj, ?_⟩
        simpa [hgeq, Sym2.eq_swap] using hgnotX
    rcases hm with hm | hm
    · exact finish g₁ hg₁.1 (Set.disjoint_right.mp hXX₁ hg₁.2) hm
    · exact finish g₂ hg₂.1 (Set.disjoint_right.mp hXX₂ hg₂.2) hm
  obtain ⟨hx₁b₃A, hx₁b₃X⟩ :=
    cross b₁ x₁ f₁ hbb₁A hb₁x₁ hb₁b₃ hx₁b₃ hf₁eq hf₁X
  obtain ⟨hx₂b₃A, hx₂b₃X⟩ :=
    cross b₂ x₂ f₂ hbb₂A hb₂x₂ hb₂b₃ hx₂b₃ hf₂eq hf₂X
  exact ⟨x₁, x₂, hf₁eq, hf₂eq, hx₁x₂, hb₁x₁, hb₂x₂,
    hx₁b₃A, hx₂b₃A, hx₁b₃X, hx₂b₃X⟩

/-- **Gap for the final sentence of 6.1(7), printed p. 31.**

PAPER: *"Since `H` is a subdivision of a 3-connected graph, `J = K_{3,3}`, and `L(H)` is a
degenerate appearance of `J`, and there is a `J`-enlargement that appears in the complement
of `G`, so the third outcome of the theorem holds."*

The hypotheses include the common configuration, the three one-edge conclusions supplied by
claims (5) and (6), both triad facts, and `hskeleton`, which is the preceding part of the
paragraph proved by `short_odd_skeleton`. -/
theorem short_odd_configuration_gives_third_outcome
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQodd : Odd (pathLength Q))
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (f₁ f₂ f₃ : Sym2 (Fin n))
    (hf : OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃)
    (htriad : Triad G H K φ Y b)
    (htriad₃ : Triad G H K φ Y b₃)
    (hB₁ : trackLength B₁ = 1) (hB₂ : trackLength B₂ = 1)
    (hB₃ : trackLength B₃ = 1)
    (hskeleton : ∃ x₁ x₂ : Fin n,
      ShortOddSkeleton G H K φ Y b₁ b₂ b₃ x₁ x₂ f₁ f₂) :
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧
      DegenerateAppearance J H ∧
      ∃ (m' : ℕ) (J' : SimpleGraph (Fin m')),
        IsJEnlargement J J' ∧ Appears Gᶜ J' := by
  classical
  obtain ⟨x₁, x₂, hf₁eq, hf₂eq, hx₁x₂, hb₁x₁, hb₂x₂, hx₁b₃, hx₂b₃, _, _⟩ := hskeleton
  let a : Fin 3 → Fin n := ![b, x₁, x₂]
  let c : Fin 3 → Fin n := ![b₁, b₂, b₃]
  obtain ⟨ha, hc, hcross, hta, htc⟩ := Thm61OddLabelled.labelled_configuration
    G hG m J hJ n H K hsub φ Y hYanti hYmajor hmin y₁ y₂ Q hQ hQY hy hQodd
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ f₃ hf htriad htriad₃
    hB₁ hB₂ hB₃ x₁ x₂ hf₁eq hf₂eq hx₁x₂ hb₁x₁ hb₂x₂ hx₁b₃ hx₂b₃
  have hda : ∀ i, (H.neighborSet (a i)).ncard = 3 := fun i =>
    (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy (a i) (hta i)).1
  have hdc : ∀ i, (H.neighborSet (c i)).ncard = 3 := fun i =>
    (triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy (c i) (htc i)).1
  have hident := Thm61OddK33.degenerate_of_cubic_bipartition J hJ H hsub
    a c ha hc hcross hda hdc
  obtain ⟨_, _, _, hd1, hd2, hd12, hs1, hs2⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  rcases hbc with ⟨_, _, _, he₁X₁, _, he₂X₂, _, _, _,
    _, he₁B₁, hfrom₁, _, he₂B₂, hfrom₂, _, _, _⟩
  have he₁eq : e₁ = s(b, b₁) := by
    rwa [trackEdges_eq_singleton_of_length_one hfrom₁ hB₁] at he₁B₁
  have he₂eq : e₂ = s(b, b₂) := by
    rwa [trackEdges_eq_singleton_of_length_one hfrom₂ hB₂] at he₂B₂
  have hclasses := Thm61OddEdgeClasses.edge_classes G H K φ Y y₁ y₂ a c ha hc
    hcross hta htc hd1 hd2 hd12 hs1 hs2
    (by simpa only [a, c, he₁eq] using he₁X₁)
    (by simpa only [a, c, he₂eq] using he₂X₂)
    (by simpa [a, c, hf₁eq, Sym2.eq_swap] using hf.1.1)
    (by simpa [a, c, hf₂eq, Sym2.eq_swap] using hf.2.1.1)
  refine ⟨hident.1, hident.2, 6, Thm61OddFiniteModel.enlarged,
    Thm61OddFiniteModel.is_enlargement J hident.1, ?_⟩
  exact Thm61OddComplement.appears_enlarged G H K φ Y
    (fun y hy => (hYmajor y hy).1) Q y₁ y₂ hQ hQY hQodd a c ha hc hcross hclasses

end Workspace.ProofLemmas.Thm61OddEndgame
