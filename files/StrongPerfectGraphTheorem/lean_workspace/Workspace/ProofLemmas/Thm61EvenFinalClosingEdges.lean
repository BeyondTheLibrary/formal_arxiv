import Workspace.ProofLemmas.Thm61EvenFinalFans

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenFinalClosingEdges

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61Claim1Helpers Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenFinalDiagonals Workspace.ProofLemmas.Thm61EvenFinalFans
open Workspace.ProofLemmas.Thm61EvenFinalTracks

/-- An internal edge of a track misses both ends of that track. -/
theorem internal_edge_misses_ends
    {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W}
    (hB : IsTrackFrom H B a b) (i : ℕ) (hi : 1 ≤ i) (hi' : i + 2 < B.length) :
    a ∉ s(B[i]'(by omega), B[i + 1]'(by omega)) ∧
      b ∉ s(B[i]'(by omega), B[i + 1]'(by omega)) := by
  have h0 := head_getElem hB.2.1 (show 0 < B.length by omega)
  have hl := last_getElem hB.2.2 (show 0 < B.length by omega)
  constructor
  · intro hm
    rcases Sym2.mem_iff.mp hm with h | h
    · have := hB.1.2.1.getElem_inj_iff.mp (h0.trans h)
      omega
    · have := hB.1.2.1.getElem_inj_iff.mp (h0.trans h)
      omega
  · intro hm
    rcases Sym2.mem_iff.mp hm with h | h
    · have := hB.1.2.1.getElem_inj_iff.mp (hl.trans h)
      omega
    · have := hB.1.2.1.getElem_inj_iff.mp (hl.trans h)
      omega

/-- Completeness in `Y` implies completeness after deleting one vertex of `Y`. -/
theorem complete_diff_of_complete
    {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V} {y : V} {e : Sym2 W}
    (he : e ∈ completeEdges G H K φ Y) : e ∈ completeEdges G H K φ (Y \ {y}) := by
  obtain ⟨he, hcomp⟩ := he
  exact ⟨he, fun x hx => hcomp x hx.1⟩

/-- The edge part of the closing paragraph. Either (1) applies to the four-cycle, or the
last application of (9) makes both diagonal branches have length two. -/
theorem closing_edges
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V} {y₁ y₂ : V}
    (h8 : Claim8 G H K φ Y y₁ y₂) (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    {b b₁ b₂ b₃ : Fin n} {C₁ C₄ : List (Fin n)}
    (hnd : [b, b₂, b₁, b₃].Nodup) (hD : Diagonals H b b₁ b₂ b₃ C₁ C₄)
    (h02 : H.Adj b b₂) (h21 : H.Adj b₂ b₁) (h03 : H.Adj b b₃)
    (hX21 : s(b₂, b₁) ∈ completeEdges G H K φ Y)
    (hX03 : s(b, b₃) ∈ completeEdges G H K φ Y)
    (hX₂ : s(b, b₂) ∈ extraEdges G H K φ Y y₂)
    (hC12 : 2 ≤ C₁.length) (hC42 : 2 ≤ C₄.length)
    (hfirst₁ : s(C₁[0]'(by omega), C₁[1]'(by omega)) ∈ extraEdges G H K φ Y y₁)
    (hfirst₄ : s(C₄[0]'(by omega), C₄[1]'(by omega)) ∈ extraEdges G H K φ Y y₁) :
    (completeEdges G H K φ Y ⊆
      ({s(b, b₂), s(b₂, b₁), s(b₁, b₃), s(b₃, b)} : Set (Sym2 (Fin n))) ∧
      (completeEdges G H K φ Y).ncard ≤ 3) ∨
    (trackLength C₁ = 2 ∧ trackLength C₄ = 2) := by
  classical
  have hX30 : s(b₃, b) ∈ completeEdges G H K φ Y := by rwa [Sym2.eq_swap]
  have hX12 : s(b₁, b₂) ∈ completeEdges G H K φ Y := by rwa [Sym2.eq_swap]
  have hb₂C₁ : b₂ ∉ C₁ := fun h => (hD.avoids₁ b₂ h).1 rfl
  have hb₃C₁ : b₃ ∉ C₁ := fun h => (hD.avoids₁ b₃ h).2 rfl
  have hbC₄ : b ∉ C₄ := fun h => (hD.avoids₄ b h).1 rfl
  have hb₁C₄ : b₁ ∉ C₄ := fun h => (hD.avoids₄ b₁ h).2 rfl
  have hb₃b₂ : b₃ ≠ b₂ := by intro h; simp [h] at hnd
  have hb₁b : b₁ ≠ b := by intro h; simp [h] at hnd
  by_cases hany : ∃ e ∈ trackEdges C₁, e ∈ completeEdges G H K φ Y
  · right
    have hterm₁ := complete_left_terminal h10 hnd hD h02 h21 h03 hX21 hX03 hX₂.2 hC12 hfirst₁.2
    have hterm₄ := complete_fourth_terminal h10 hD h02 h03 hX03 hX₂.2 hC12 hfirst₁.2 hany
    have hany₄ : ∃ e ∈ trackEdges C₄, e ∈ completeEdges G H K φ Y := by
      by_contra hn
      have hno : Disjoint (trackEdges C₄) (completeEdges G H K φ Y) := by
        exact Set.disjoint_left.mpr (fun e he hc => hn ⟨e, he, hc⟩)
      have hhit := complete_edge_hits_ends h9 hD.track₄ (by have := hD.pos₄; omega) hD.even₄
        h21.symm h03.symm hb₁C₄ hbC₄ hb₁b hX12 hX30 hno
      obtain ⟨e, he, heX⟩ := hany
      rcases hhit e heX with h | h
      · exact trackEdge_avoids hb₂C₁ he h
      · exact trackEdge_avoids hb₃C₁ he h
    have hlast₁ : s(C₁[C₁.length - 2]'(by omega), C₁[C₁.length - 1]'(by omega)) ∈
        completeEdges G H K φ Y := by
      obtain ⟨e, he, heX⟩ := hany
      have heq := trackEdge_at_last hD.track₁ hC12 he (hterm₁ e he heX)
      exact heq ▸ heX
    have hlast₄ : s(C₄[C₄.length - 2]'(by omega), C₄[C₄.length - 1]'(by omega)) ∈
        completeEdges G H K φ Y := by
      obtain ⟨e, he, heX⟩ := hany₄
      have heq := trackEdge_at_last hD.track₄ hC42 he (hterm₄ e he heX)
      exact heq ▸ heX
    have hint₁ : ∀ i, 1 ≤ i → ∀ hi : i + 2 < C₁.length,
        s(C₁[i]'(by omega), C₁[i + 1]'(by omega)) ∉ completeEdges G H K φ (Y \ {y₁}) := by
      intro i hi hi' hc
      let e := s(C₁[i]'(by omega), C₁[i + 1]'(by omega))
      have he : e ∈ trackEdges C₁ := ⟨i, by omega, rfl⟩
      have hmiss := internal_edge_misses_ends hD.track₁ i hi hi'
      by_cases heX : e ∈ completeEdges G H K φ Y
      · exact hmiss.2 (hterm₁ e he heX)
      have heX₁ : e ∈ extraEdges G H K φ Y y₁ := ⟨hc, heX⟩
      obtain ⟨w, hwe, hwp⟩ := exists_common_end (h8 e s(b, b₂) heX₁ hX₂)
      rcases Sym2.mem_iff.mp hwp with h | h
      · exact hmiss.1 (h ▸ hwe)
      · exact trackEdge_avoids hb₂C₁ he (h ▸ hwe)
    have hint₄ : ∀ i, 1 ≤ i → ∀ hi : i + 2 < C₄.length,
        s(C₄[i]'(by omega), C₄[i + 1]'(by omega)) ∉ completeEdges G H K φ (Y \ {y₁}) := by
      intro i hi hi' hc
      let e := s(C₄[i]'(by omega), C₄[i + 1]'(by omega))
      have he : e ∈ trackEdges C₄ := ⟨i, by omega, rfl⟩
      have hmiss := internal_edge_misses_ends hD.track₄ i hi hi'
      by_cases heX : e ∈ completeEdges G H K φ Y
      · exact hmiss.2 (hterm₄ e he heX)
      have heX₁ : e ∈ extraEdges G H K φ Y y₁ := ⟨hc, heX⟩
      obtain ⟨w, hwe, hwp⟩ := exists_common_end (h8 e s(b, b₂) heX₁ hX₂)
      rcases Sym2.mem_iff.mp hwp with h | h
      · exact trackEdge_avoids hbC₄ he (h ▸ hwe)
      · exact hmiss.1 (h ▸ hwe)
    have hmiss₁ : ∀ w ∈ trackInterior C₁, w ∉ s(b, b₃) := by
      intro w hw he
      rcases Sym2.mem_iff.mp he with h | h
      · exact (interior_ne_ends hD.track₁ hw).1 h
      · exact (hD.avoids₁ w (PathBasics.interior_subset hw)).2 h
    have hmiss₄ : ∀ w ∈ trackInterior C₄, w ∉ s(b, b₃) := by
      intro w hw he
      rcases Sym2.mem_iff.mp he with h | h
      · exact (hD.avoids₄ w (PathBasics.interior_subset hw)).1 h
      · exact (interior_ne_ends hD.track₄ hw).2 h
    exact ⟨length_two_of_claim9 h9 (Y \ {y₁}) (Or.inr (Or.inl rfl)) hD.track₁.1 hC12
      hD.even₁ hfirst₁.1 (complete_diff_of_complete hlast₁) hint₁
      (complete_diff_of_complete hX03) hmiss₁,
      length_two_of_claim9 h9 (Y \ {y₁}) (Or.inr (Or.inl rfl)) hD.track₄.1 hC42
      hD.even₄ hfirst₄.1 (complete_diff_of_complete hlast₄) hint₄
      (complete_diff_of_complete hX03) hmiss₄⟩
  · left
    have hno : Disjoint (trackEdges C₁) (completeEdges G H K φ Y) :=
      Set.disjoint_left.mpr (fun e he hc => hany ⟨e, he, hc⟩)
    have hhit := complete_edge_hits_ends h9 hD.track₁ (by have := hD.pos₁; omega) hD.even₁
      h03.symm h21.symm hb₃C₁ hb₂C₁ hb₃b₂ hX30 hX12 hno
    have hcycle : completeEdges G H K φ Y ⊆
        ({s(b, b₂), s(b₂, b₁), s(b₁, b₃), s(b₃, b)} : Set (Sym2 (Fin n))) := by
      intro e heX
      have he : e ∈ H.edgeSet := heX.choose
      rw [hD.edges] at he
      rcases he with (he | he) | he
      · exact he
      · rcases hhit e heX with h | h
        · exact False.elim (trackEdge_avoids hbC₄ he h)
        · exact False.elim (trackEdge_avoids hb₁C₄ he h)
      · exact False.elim (hany ⟨e, he, heX⟩)
    refine ⟨hcycle, ?_⟩
    have hsub : completeEdges G H K φ Y ⊆ ({s(b₂, b₁), s(b₁, b₃), s(b₃, b)} : Set (Sym2 (Fin n))) := by
      intro e he
      rcases hcycle he with h | h | h | h
      · exact False.elim (hX₂.2 (h ▸ he))
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hn := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hn1 := Set.ncard_insert_le s(b₂, b₁) ({s(b₁, b₃), s(b₃, b)} : Set (Sym2 (Fin n)))
    have hn2 := Set.ncard_insert_le s(b₁, b₃) ({s(b₃, b)} : Set (Sym2 (Fin n)))
    simp only [Set.ncard_singleton] at hn2
    omega

end Workspace.ProofLemmas.Thm61EvenFinalClosingEdges
