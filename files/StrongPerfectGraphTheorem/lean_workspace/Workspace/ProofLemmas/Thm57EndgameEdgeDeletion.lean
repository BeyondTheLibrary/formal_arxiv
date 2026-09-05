import Workspace.ProofLemmas.Thm55Structure
import Workspace.ProofLemmas.Thm55BranchReach
import Workspace.ProofLemmas.BranchClassification

/-! # The edge-end deletion used in 5.7

The paper says: "Since H is cyclically 3-connected and a₃,b₃ are adjacent, it follows
that H \\ {a₃,b₃} is connected." A component without a branch vertex would lie strictly
between the two deleted vertices on one subdividing track. Adjacency rules this out.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameEdgeDeletion

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch
open Workspace.ProofLemmas.Thm55Structure

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- Two adjacent vertices on a subdividing track are consecutive on that track. -/
theorem adjacent_indices {n : ℕ} {J : SimpleGraph (Fin n)} {H : SimpleGraph W}
    {ι : Fin n → W} {T : Fin n → Fin n → List W} (hS : SubData J H ι T)
    {a b : Fin n} (hab : J.Adj a b) {i j : ℕ}
    (hi : i < (T a b).length) (hj : j < (T a b).length)
    (hadj : H.Adj (T a b)[i] (T a b)[j]) : i + 1 = j ∨ j + 1 = i := by
  have he : s((T a b)[i], (T a b)[j]) ∈ H.edgeSet := hadj
  rw [hS.edges] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨c, d, hcd, he⟩ := he
  have hmem := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges he
  have heq := same_original_edge_of_two_common hS hab hcd hadj.ne
    (List.getElem_mem hi) (List.getElem_mem hj) hmem.1 hmem.2
  have het : s((T a b)[i], (T a b)[j]) ∈ trackEdges (T a b) := by
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact he
    · rwa [hS.rev a b hab, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] at he
  obtain ⟨k, hk, heq⟩ := het
  rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := (hS.track a b hab).1.2.1.getElem_inj_iff.mp h1
    have := (hS.track a b hab).1.2.1.getElem_inj_iff.mp h2
    omega
  · have := (hS.track a b hab).1.2.1.getElem_inj_iff.mp h1
    have := (hS.track a b hab).1.2.1.getElem_inj_iff.mp h2
    omega

/-- Every nonempty set closed outside the ends of an edge contains a branch vertex. -/
theorem closed_set_has_branch (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {u v : W} (huv : H.Adj u v) (E : Set W) (hne : E.Nonempty)
    (hES : E ⊆ ({u, v} : Set W)ᶜ)
    (hcl : ∀ x ∈ E, ∀ y ∈ ({u, v} : Set W)ᶜ, H.Adj x y → y ∈ E) :
    ∃ b ∈ E, b ∈ branchVertices H := by
  classical
  by_contra hnone
  have hnb : ∀ b ∈ E, b ∉ branchVertices H := by
    intro b hb hbb
    exact hnone ⟨b, hb, hbb⟩
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  obtain ⟨z, hz⟩ := hne
  obtain ⟨a, b, hab, hzint⟩ : ∃ a b, J.Adj a b ∧ z ∈ trackInterior (T a b) := by
    rcases hS.cover z with ⟨a, rfl⟩ | h
    · exact (hnb _ hz (by rw [branch_eq_range hJ hS]; exact ⟨a, rfl⟩)).elim
    · exact h
  obtain ⟨k, hk, hkz⟩ :=
    (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff (T a b) z).mp hzint
  obtain ⟨i, j, hi, hj, hik, hkj, his, hjs⟩ :=
    separator_hits_both_sides hJ hS {u, v} E hES hcl hnb hab hk (hkz ▸ hz)
  have hij : (T a b)[i]'hi ≠ (T a b)[j]'hj := by
    intro h
    have := (hS.track a b hab).1.2.1.getElem_inj_iff.mp h
    omega
  change (T a b)[i] = u ∨ (T a b)[i] = v at his
  change (T a b)[j] = u ∨ (T a b)[j] = v at hjs
  have hadj : H.Adj (T a b)[i] (T a b)[j] := by
    rcases his with his | his <;> rcases hjs with hjs | hjs
    · exact (hij (his.trans hjs.symm)).elim
    · simpa only [his, hjs] using huv
    · simpa only [his, hjs] using huv.symm
    · exact (hij (his.trans hjs.symm)).elim
  have := adjacent_indices hS hab hi hj hadj
  omega

/-- Deleting the ends of an edge of a cyclically 3-connected graph leaves a connected set. -/
theorem connected_compl_edge (H : SimpleGraph W) (hc3 : CyclicallyThreeConnected H)
    {u v : W} (huv : H.Adj u v) : ConnectedSet H (({u, v} : Set W)ᶜ) := by
  classical
  let S : Set W := ({u, v} : Set W)ᶜ
  have hreach : ∀ x ∈ S, ∃ b ∈ branchVertices H, RchIn H S x b := by
    intro x hx
    let E : Set W := {y | RchIn H S x y}
    have hES : E ⊆ S := fun _ h => h.mem_right
    have hcl : ∀ y ∈ E, ∀ z ∈ S, H.Adj y z → z ∈ E := by
      intro y hy z hz hyz
      exact hy.trans (RchIn.of_adj hy.mem_right hz hyz)
    obtain ⟨b, hb, hbb⟩ := closed_set_has_branch H hc3 huv E
      ⟨x, RchIn.refl hx⟩ hES hcl
    exact ⟨b, hbb, hb⟩
  intro x y
  obtain ⟨a, ha, hxa⟩ := hreach x x.2
  obtain ⟨b, hb, hyb⟩ := hreach y y.2
  have hab := Workspace.ProofLemmas.Thm55BranchReach.branch_rchIn_compl_pair
    hc3 ha hb hxa.mem_right hyb.mem_right
  exact (hxa.trans (hab.trans hyb.symm)).choose_spec.choose_spec

end Workspace.ProofLemmas.Thm57EndgameEdgeDeletion
