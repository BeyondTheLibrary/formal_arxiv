import Workspace.ProofLemmas.Thm61EvenFinalClosingEdges
import Workspace.ProofLemmas.Thm61EvenFinalBridge
import Workspace.ProofLemmas.Thm61Claim1

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenFinalClosing

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61Conclusion Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61Claim1Helpers Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenFinalK4 Workspace.ProofLemmas.Thm61EvenFinalBridge
open Workspace.ProofLemmas.Thm61EvenFinalDiagonals Workspace.ProofLemmas.Thm61EvenFinalClosingEdges

/-- The closing paragraph after (13). A long odd `B₅` gives an overshadowed appearance.
When `B₅` has one edge, the four-cycle and its diagonals give either (1) or the six-vertex outcome. -/
theorem even_final_closing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H) (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ x : V, x ∈ Q ↔ x ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ e₄ : Sym2 (Fin n)) (B₁ B₂ B₃ B₄ : List (Fin n))
    (b₁ b₂ b₃ b₄ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y)
    (hB₁even : Even (trackLength B₁)) (hB₂odd : Odd (trackLength B₂))
    (he₄ : e₄ ∈ incidentEdges H b₂) (hB₄ : IsBranch H B₄)
    (he₄B₄ : e₄ ∈ trackEdges B₄) (hfrom₄ : IsTrackFrom H B₄ b₂ b₄)
    (hb₄ : b₄ = b₃) (hB₃one : trackLength B₃ = 1)
    (hJiso : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (hB₄even : Even (trackLength B₄)) :
    Thm61Concl G m J n H K φ Y := by
  classical
  have htri₂ := b2_triad G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h9 hadj hXb hB₁even
  obtain ⟨hB₂one, he₂eq⟩ := b2_short G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy h10
    b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc h8 hadj hB₁even htri₂
  obtain ⟨hB₁pos, hB₂pos, hB₃pos, hbV, hb₁V, hb₂V, hb₃V,
    hbb₁, hbb₂, hbb₃, hb₁b₂, hb₁b₃, hb₂b₃⟩ :=
    branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc
  obtain ⟨-, -, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩ := hbc
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have he₃X := other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
    he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have he₃eq : e₃ = s(b, b₃) := by
    rw [trackEdges_eq_singleton_of_length_one hfrom₃ hB₃one] at he₃B₃
    exact he₃B₃
  have h03 : H.Adj b b₃ := H.mem_edgeSet.mp (he₃eq ▸ he₃inc.1)
  have h02 : H.Adj b b₂ := H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)
  obtain ⟨B₅, hB₅, hfrom₅, hpos₅⟩ := linked_of_k4 hJ hsub.1 hJiso hb₁V hb₃V hb₁b₃
  have hodd₅ : Odd (trackLength B₅) := by
    obtain ⟨col⟩ := BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
    have h01 := (BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁).mp hB₁even
    apply Nat.not_even_iff_odd.mp
    intro heven
    exact col.valid h03 (h01.trans ((BipartiteClosedWalkEven.even_trackLength_iff col hfrom₅).mp heven))
  by_cases hlong₅ : 3 ≤ trackLength B₅
  · have hy₁Y : y₁ ∈ Y := (hQY y₁).mp (List.mem_of_mem_head? hQ.2.1)
    have hover := overshadowed_of_major_branch φ hB₅ hfrom₅ hodd₅ hlong₅ hb₁V hb₃V
      (hYmajor y₁ hy₁Y)
    exact Or.inl ⟨Or.inr hJiso, n, H, K, φ, ⟨hsub, ⟨φ⟩⟩, hover⟩
  have hshort₅ : trackLength B₅ = 1 := by
    obtain ⟨k, hk⟩ := hodd₅
    omega
  have hlen₅ : B₅.length = 2 := by simp only [trackLength] at hshort₅; omega
  have hhead₅ : B₅[0]'(by omega) = b₁ := head_getElem hfrom₅.2.1 (by omega)
  have hlast₅ : B₅[1]'(by omega) = b₃ := (geq B₅ (show 1 = B₅.length - 1 by omega)
    (by omega) (by omega)).trans (last_getElem hfrom₅.2.2 (by omega))
  have h13 : H.Adj b₁ b₃ := by
    have h := hfrom₅.1.2.2 0 (by omega)
    simpa only [hhead₅, hlast₅] using h
  have hnd : [b, b₂, b₁, b₃].Nodup := by
    simp [hbb₂, hbb₁, hbb₃, hb₁b₂.symm, hb₂b₃, hb₁b₃]
  have hbvs := branchVertices_eq_four hJ hsub.1 hJiso hnd hbV hb₂V hb₁V hb₃V
  obtain ⟨C₁, C₄, hD⟩ := exists_diagonals hsub.1 hsub.2 hJiso hnd hbvs h02 hadj.symm h13 h03.symm
  have hC12 : 2 ≤ C₁.length := by have h := hD.pos₁; simp only [trackLength] at h; omega
  have hC42 : 2 ≤ C₄.length := by have h := hD.pos₄; simp only [trackLength] at h; omega
  have hE₁ := same_branch_edges hJ hsub.1 hB₁ hfrom₁ hB₁pos
    hD.branch₁ hD.track₁ (by have := hD.pos₁; omega) hbV hb₁V
  have he₁C₁ : e₁ ∈ trackEdges C₁ := hE₁ ▸ he₁B₁
  have he₁first := trackEdge_at_head hD.track₁ hC12 he₁C₁ he₁inc.2
  have hfirst₁ : s(C₁[0]'(by omega), C₁[1]'(by omega)) ∈ extraEdges G H K φ Y y₁ :=
    he₁first ▸ he₁X₁
  let f := s(C₄[0]'(by omega), C₄[1]'(by omega))
  have hfC : f ∈ trackEdges C₄ := ⟨0, by omega, rfl⟩
  have hfinc : f ∈ incidentEdges H b₂ := ⟨hD.track₄.1.2.2 0 (by omega), by
    dsimp [f]
    rw [head_getElem hD.track₄.2.1 (by omega)]
    simp⟩
  have hfb : b ∉ f := trackEdge_avoids (fun h => (hD.avoids₄ b h).1 rfl) hfC
  have hfb₁ : b₁ ∉ f := trackEdge_avoids (fun h => (hD.avoids₄ b₁ h).2 rfl) hfC
  have hfne₂ : f ≠ e₂ := fun h => hfb (by rw [h, he₂eq]; simp)
  have hfnotX : f ∉ completeEdges G H K φ Y := by
    intro hfX
    have hfeq := htri₂.2 ⟨hfinc, hfX⟩ ⟨⟨H.mem_edgeSet.mpr hadj, by simp⟩, hXb⟩
    exact hfb₁ (by rw [hfeq]; simp)
  have hfU : f ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    by_contra hn
    have he₂out : e₂ ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
      rintro (h | h)
      · exact he₂X₂.2 h
      · exact Set.disjoint_left.mp hX₁X₂ h he₂X₂
    exact hfne₂ (hsat₁ b₂ hb₂V ⟨hfinc, hn⟩ ⟨⟨he₂inc.1, by rw [he₂eq]; simp⟩, he₂out⟩)
  have hfirst₄ : f ∈ extraEdges G H K φ Y y₁ := hfU.resolve_left hfnotX
  have hX21 : s(b₂, b₁) ∈ completeEdges G H K φ Y := by rwa [Sym2.eq_swap]
  have hX03 : s(b, b₃) ∈ completeEdges G H K φ Y := he₃eq ▸ he₃X
  have hX₂ : s(b, b₂) ∈ extraEdges G H K φ Y y₂ := he₂eq ▸ he₂X₂
  rcases closing_edges h8 h9 h10 hnd hD h02 hadj.symm h03 hX21 hX03 hX₂
    hC12 hC42 hfirst₁ hfirst₄ with ⟨hXC, hXcard⟩ | ⟨hlen₁, hlen₄⟩
  · exact Thm61Claim1.thm_6_1_claim_1 G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
      y₁ y₂ Q hQ hQY hy b b₂ b₁ b₃ hnd hbvs h02 hadj.symm h13 h03.symm hXC hXcard
  · have hn := six_vertices hnd hD (exists_neighbor hJ hsub.1) hlen₁ hlen₄
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hJiso, hn⟩)))

end Workspace.ProofLemmas.Thm61EvenFinalClosing
