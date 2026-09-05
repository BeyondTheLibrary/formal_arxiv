import Workspace.ProofLemmas.Thm61Claim2
import Workspace.ProofLemmas.Thm61Claim3
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-! The triad and cross-edge steps in the last paragraph of 6.1(7). -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61OddTriads

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm84RungEndDictionary

/-- Paper, 6.1(7): "therefore `fᵢ` is the unique edge in `X` incident with `bᵢ`,
and `bᵢ` is a triad (`i = 1, 2`)." Any branch-vertex distinct from and nonadjacent
to a triad is itself a triad in the odd case. Two complete edges at that vertex
would form the four-cycle forbidden by (2), using (3) at the given triad. -/
theorem triad_of_nonadjacent_triad
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (hbip : H.IsBipartite) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Z : Set V, Z ⊂ Y → AnticonnectedSet G Z →
      SaturatesLineGraph H (completeEdges G H K φ Z))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ w : V, w ∈ Q ↔ w ∈ Y) (hy : y₁ ≠ y₂)
    (hodd : Odd (pathLength Q))
    {u v : Fin n} (hu : u ∈ branchVertices H) (hv : Triad G H K φ Y v)
    (huv : u ≠ v) (hnadj : ¬ H.Adj u v) : Triad G H K φ Y u := by
  classical
  obtain ⟨_, _, ⟨g₁, hg₁, _⟩, ⟨g₂, hg₂, _⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy v hv
  obtain ⟨a, _, hga⟩ := edge_track_from_incident hg₁.1
  obtain ⟨c, _, hgc⟩ := edge_track_from_incident hg₂.1
  have hva : H.Adj v a := by simpa [hga] using hg₁.1.1
  have hvc : H.Adj v c := by simpa [hgc] using hg₂.1.1
  have hac : a ≠ c := by
    intro h
    have hd := (X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy).2.2.2.2.2.1
    apply Set.disjoint_left.mp hd hg₁.2
    simpa [hga, hgc, h] using hg₂.2
  have hua : u ≠ a := fun h => hnadj (by rw [h]; exact hva.symm)
  have huc : u ≠ c := fun h => hnadj (by rw [h]; exact hvc.symm)
  have hmeet : MeetEdges g₁ g₂ := fun h => h v ⟨hg₁.1.2, hg₂.1.2⟩
  have form : ∀ f ∈ incidentEdges H u ∩ completeEdges G H K φ Y,
      f = s(u, a) ∨ f = s(u, c) := by
    intro f hf
    have identify : ∀ g z, u ≠ z → g = s(v, z) → MeetEdges f g → f = s(u, z) := by
      intro g z huz hgz hm
      obtain ⟨w, hwf, hwg⟩ := exists_common_end hm
      rw [hgz] at hwg
      rcases Sym2.mem_iff.mp hwg with hwv | hwz
      · have hfeq := eq_sym2_of_mem_mem huv hf.1.2 (hwv ▸ hwf)
        exact False.elim (hnadj (by simpa [hfeq] using hf.1.1))
      · exact eq_sym2_of_mem_mem huz hf.1.2 (hwz ▸ hwf)
    rcases Thm61Claim3.thm_6_1_claim3 G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hodd
      g₁ g₂ f hg₁.2 hg₂.2 hmeet hf.2 with hm | hm
    · exact Or.inl (identify g₁ a hua hga hm)
    · exact Or.inr (identify g₂ c huc hgc hm)
  refine ⟨hu, ?_⟩
  intro f hf g hg
  by_contra hfg
  have both : s(u, a) ∈ completeEdges G H K φ Y ∧
      s(u, c) ∈ completeEdges G H K φ Y := by
    rcases form f hf with rfl | rfl <;> rcases form g hg with rfl | rfl
    · exact False.elim (hfg rfl)
    · exact ⟨hf.2, hg.2⟩
    · exact ⟨hg.2, hf.2⟩
    · exact False.elim (hfg rfl)
  have huaA : H.Adj u a := both.1.choose
  have hucA : H.Adj u c := both.2.choose
  exact Thm61Claim2.thm_6_1_claim2 G hG H hbip K φ Y hYmajor hmin y₁ y₂ Q hQ hQY hy hodd
    a v c u (by simp [hva.ne.symm, hac, hua.symm, hvc.ne, huv.symm, huc.symm])
    hva.symm hvc hucA.symm huaA hv.1
    (by simpa [hga, Sym2.eq_swap] using hg₁.2)
    (by simpa [hgc] using hg₂.2) (by simpa [Sym2.eq_swap] using both.2) both.1

/-- Paper, 6.1(7): "By (3) applied to `f₂` and `b₁` we deduce that `b₁` is
adjacent to `x₂`, and, similarly, `x₁` is adjacent to `b₂`." The edge obtained
at the triad is outside `X`. -/
theorem adjacent_to_complete_end
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hmin : ∀ Z : Set V, Z ⊂ Y → AnticonnectedSet G Z →
      SaturatesLineGraph H (completeEdges G H K φ Z))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ w : V, w ∈ Q ↔ w ∈ Y) (hy : y₁ ≠ y₂)
    (hodd : Odd (pathLength Q))
    {u a c : Fin n} (hu : Triad G H K φ Y u)
    (hua : u ≠ a) (huc : u ≠ c) (hnadj : ¬ H.Adj u a)
    (hf : s(a, c) ∈ completeEdges G H K φ Y) :
    H.Adj u c ∧ s(u, c) ∉ completeEdges G H K φ Y := by
  obtain ⟨_, _, ⟨g₁, hg₁, _⟩, ⟨g₂, hg₂, _⟩⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy u hu
  have hm : MeetEdges g₁ g₂ := fun h => h u ⟨hg₁.1.2, hg₂.1.2⟩
  have finish : ∀ g, g ∈ incidentEdges H u →
      g ∉ completeEdges G H K φ Y → MeetEdges s(a, c) g →
      H.Adj u c ∧ s(u, c) ∉ completeEdges G H K φ Y := by
    intro g hg hgn hm
    obtain ⟨w, hwf, hwg⟩ := exists_common_end hm
    rcases Sym2.mem_iff.mp hwf with hwa | hwc
    · have heq := eq_sym2_of_mem_mem hua hg.2 (hwa ▸ hwg)
      exact False.elim (hnadj (by simpa [heq] using hg.1))
    · have heq := eq_sym2_of_mem_mem huc hg.2 (hwc ▸ hwg)
      exact ⟨by simpa [heq] using hg.1, by simpa [heq] using hgn⟩
  rcases Thm61Claim3.thm_6_1_claim3 G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hodd
      g₁ g₂ s(a, c) hg₁.2 hg₂.2 hm hf with hm | hm
  · exact finish g₁ hg₁.1 hg₁.2.2 hm
  · exact finish g₂ hg₂.1 hg₂.2.2 hm

/-- At a triad, an edge outside `X` has the opposite extra-edge class from
another incident edge outside `X`. This records the setup preceding 6.1(2). -/
theorem opposite_extra_class
    {V : Type*} {n : ℕ} {G : SimpleGraph V} {H : SimpleGraph (Fin n)}
    {K : Set V} (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y z : V)
    (hdisj : Disjoint (extraEdges G H K φ Y y) (extraEdges G H K φ Y z))
    (hsat : SaturatesLineGraph H (completeEdges G H K φ Y ∪ extraEdges G H K φ Y z))
    {v : Fin n} (hv : v ∈ branchVertices H) {e f : Sym2 (Fin n)}
    (he : e ∈ incidentEdges H v) (hf : f ∈ incidentEdges H v)
    (hey : e ∈ extraEdges G H K φ Y y) (hfn : f ∉ completeEdges G H K φ Y)
    (hne : f ≠ e) : f ∈ extraEdges G H K φ Y z := by
  by_contra h
  apply hne
  exact hsat v hv ⟨hf, fun hf => hf.elim hfn h⟩
    ⟨he, fun he => he.elim hey.2 (Set.disjoint_left.mp hdisj hey)⟩

end Workspace.ProofLemmas.Thm61OddTriads
