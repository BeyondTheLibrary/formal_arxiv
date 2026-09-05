import Workspace.ProofLemmas.Thm61EvenFinalDiagonals

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenFinalFans

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61Claim1Helpers Workspace.ProofLemmas.Thm61EvenFinalDiagonals

/-- Cut a track just after an edge which misses its far end. The prefix keeps the first
edge, contains the chosen edge, and omits the far end. -/
theorem prefix_with_edge
    {W : Type*} {H : SimpleGraph W} {B : List W} {a b : W}
    (hB : IsTrackFrom H B a b) (hB2 : 2 ≤ B.length)
    {e : Sym2 W} (he : e ∈ trackEdges B) (hb : b ∉ e) :
    ∃ P v, IsTrackFrom H P a v ∧ 2 ≤ P.length ∧ e ∈ trackEdges P ∧
      (∀ w ∈ P, w ∈ B ∧ w ≠ b) ∧
      ∀ hP2 : 2 ≤ P.length,
        s(P[0]'(by omega), P[1]'(by omega)) = s(B[0]'(by omega), B[1]'(by omega)) := by
  obtain ⟨i, hi, heq⟩ := he
  have hi' : i + 2 < B.length := by
    by_contra hn
    have hilast : i + 1 = B.length - 1 := by omega
    have hlast : B[i + 1]'hi = b := (geq B hilast hi (by omega)).trans
      (last_getElem hB.2.2 (by omega))
    exact hb (by rw [heq, hlast]; simp)
  let P := TrackSlice.slice B 0 (i + 1)
  have hlen : P.length = i + 2 := by
    simpa [P] using TrackSlice.length_slice B hi (show 0 ≤ i + 1 by omega)
  have hget : ∀ k (hk : k < P.length), P[k]'hk = B[k]'(by omega) := by
    intro k hk
    simpa [P] using TrackSlice.getElem_slice B hk (by omega)
  have hP : IsTrackFrom H P a (B[i + 1]'hi) := by
    have h := TrackSlice.isTrackFrom_slice hB.1 hi (show 0 ≤ i + 1 by omega)
    rw [head_getElem hB.2.1 (by omega)] at h
    exact h
  refine ⟨P, B[i + 1]'hi, hP, by omega, ?_, ?_, ?_⟩
  · refine ⟨i, by omega, ?_⟩
    rw [hget i (by omega), hget (i + 1) (by omega)]
    exact heq
  · intro w hw
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    have hBw : B[k]'(by omega) = w := (hget k hk).symm.trans hkw
    refine ⟨hBw ▸ List.getElem_mem (by omega), ?_⟩
    intro hwb
    have hEq : B[k]'(by omega) = B[B.length - 1]'(by omega) :=
      hBw.trans (hwb.trans (last_getElem hB.2.2 (by omega)).symm)
    have := hB.1.2.1.getElem_inj_iff.mp hEq
    omega
  · intro hP2
    rw [hget 0 (by omega), hget 1 (by omega)]

/-- The second application of (10) in the closing paragraph: the only possible complete
edge on the first diagonal is its edge at `b₁`. -/
theorem complete_left_terminal
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V}
    (h10 : Claim10 G H K φ Y)
    {b b₁ b₂ b₃ : Fin n} {C₁ C₄ : List (Fin n)}
    (hnd : [b, b₂, b₁, b₃].Nodup) (hD : Diagonals H b b₁ b₂ b₃ C₁ C₄)
    (h02 : H.Adj b b₂) (h21 : H.Adj b₂ b₁) (h03 : H.Adj b b₃)
    (hX21 : s(b₂, b₁) ∈ completeEdges G H K φ Y)
    (hX03 : s(b, b₃) ∈ completeEdges G H K φ Y)
    (hnot02 : s(b, b₂) ∉ completeEdges G H K φ Y)
    (hC2 : 2 ≤ C₁.length)
    (hfirst : s(C₁[0]'(by omega), C₁[1]'(by omega)) ∉ completeEdges G H K φ Y) :
    ∀ e ∈ trackEdges C₁, e ∈ completeEdges G H K φ Y → b₁ ∈ e := by
  classical
  intro e he heX
  by_contra hb₁
  obtain ⟨P, v, hP, hP2, heP, hPmem, hPfirst⟩ := prefix_with_edge hD.track₁ hC2 he hb₁
  have hbb₁ : b ≠ b₁ := by intro h; simp [h] at hnd
  have h3b : b₃ ≠ b := h03.ne.symm
  have h32 : b₃ ≠ b₂ := by intro h; simp [h] at hnd
  have h31 : b₃ ≠ b₁ := by intro h; simp [h] at hnd
  have hT : IsTrackFrom H [b, b₂, b₁] b b₁ := isTrackFrom_cons
    (HPrimeTracks.isTrackFrom_pair h21) h02 (by simp [h02.ne, hbb₁])
  have hE : IsTrackFrom H [b, b₃] b b₃ := HPrimeTracks.isTrackFrom_pair h03
  have h12 : ∀ w ∈ P, w ∈ [b, b₂, b₁] → w = b := by
    intro w hw hw'
    have hh := hPmem w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with h | h | h
    · exact h
    · exact False.elim ((hD.avoids₁ w hh.1).1 h)
    · exact False.elim (hh.2 h)
  have h13 : ∀ w ∈ P, w ∈ [b, b₃] → w = b := by
    intro w hw hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with h | h
    · exact h
    · exact False.elim ((hD.avoids₁ w (hPmem w hw).1).2 h)
  have h23 : ∀ w ∈ [b, b₂, b₁], w ∈ [b, b₃] → w = b := by
    intro w hw hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw hw'
    rcases hw' with h | h
    · exact h
    · rcases hw with h' | h' | h'
      · exact h'
      · exact False.elim (h32 (h.symm.trans h'))
      · exact False.elim (h31 (h.symm.trans h'))
  have h := h10 b v b₁ b₃ P [b, b₂, b₁] [b, b₃] hP hT hE hP2 (by simp) (by simp)
    h12 h13 h23 ⟨e, heP, heX⟩ ⟨s(b₂, b₁), ⟨1, by simp, rfl⟩, hX21⟩
    ⟨s(b, b₃), ⟨0, by simp, rfl⟩, hX03⟩
  have hn : s(P[0]'(by omega), P[1]'(by omega)) ∉ completeEdges G H K φ Y :=
    fun hx => hfirst (hPfirst hP2 ▸ hx)
  rcases h with h | h | h
  · exact hn h.1
  · exact hn h.1
  · exact hnot02 h.1

/-- The first application of (10) in the closing paragraph: if the first diagonal has a
complete edge, the only possible complete edge on the other diagonal is its edge at `b₃`. -/
theorem complete_fourth_terminal
    {V : Type*} {G : SimpleGraph V} {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    {φ : H.lineGraph ≃g G.induce K} {Y : Set V}
    (h10 : Claim10 G H K φ Y)
    {b b₁ b₂ b₃ : Fin n} {C₁ C₄ : List (Fin n)}
    (hD : Diagonals H b b₁ b₂ b₃ C₁ C₄)
    (h02 : H.Adj b b₂) (h03 : H.Adj b b₃)
    (hX03 : s(b, b₃) ∈ completeEdges G H K φ Y)
    (hnot02 : s(b, b₂) ∉ completeEdges G H K φ Y)
    (hC2 : 2 ≤ C₁.length)
    (hfirst : s(C₁[0]'(by omega), C₁[1]'(by omega)) ∉ completeEdges G H K φ Y)
    (hany : ∃ e ∈ trackEdges C₁, e ∈ completeEdges G H K φ Y) :
    ∀ e ∈ trackEdges C₄, e ∈ completeEdges G H K φ Y → b₃ ∈ e := by
  classical
  intro e he heX
  by_contra hb₃
  have hC₄2 : 2 ≤ C₄.length := by have h := hD.pos₄; simp only [trackLength] at h; omega
  obtain ⟨S, v, hS, hS2, heS, hSmem, -⟩ := prefix_with_edge hD.track₄ hC₄2 he hb₃
  have hbS : b ∉ S := fun h => (hD.avoids₄ b (hSmem b h).1).1 rfl
  have hP : IsTrackFrom H (b :: S) b v := isTrackFrom_cons hS h02 hbS
  have hP2 : 2 ≤ (b :: S).length := by simp; omega
  have heP : e ∈ trackEdges (b :: S) := by
    obtain ⟨i, hi, heq⟩ := heS
    exact ⟨i + 1, by simp; omega, by simpa using heq⟩
  have h12 : ∀ w ∈ C₁, w ∈ b :: S → w = b := by
    intro w hw hw'
    rcases List.mem_cons.mp hw' with h | h
    · exact h
    · exact False.elim (hD.disjoint w hw (hSmem w h).1)
  have h13 : ∀ w ∈ C₁, w ∈ [b, b₃] → w = b := by
    intro w hw hw'
    rcases List.mem_cons.mp hw' with h | h
    · exact h
    · exact False.elim ((hD.avoids₁ w hw).2 (List.eq_of_mem_singleton h))
  have h23 : ∀ w ∈ b :: S, w ∈ [b, b₃] → w = b := by
    intro w hw hw'
    rcases List.mem_cons.mp hw with h | h
    · exact h
    · rcases List.mem_cons.mp hw' with h' | h'
      · exact h'
      · exact False.elim ((hSmem w h).2 (List.eq_of_mem_singleton h'))
  have h := h10 b b₁ v b₃ C₁ (b :: S) [b, b₃] hD.track₁ hP
    (HPrimeTracks.isTrackFrom_pair h03) hC2 hP2 (by simp) h12 h13 h23 hany
    ⟨e, heP, heX⟩ ⟨s(b, b₃), ⟨0, by simp, rfl⟩, hX03⟩
  have hPfirst : s((b :: S)[0]'(by omega), (b :: S)[1]'(by omega)) = s(b, b₂) := by
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [head_getElem hS.2.1 (by omega)]
  rcases h with h | h | h
  · exact hfirst h.1
  · exact hfirst h.1
  · exact hnot02 (hPfirst ▸ h.1)

end Workspace.ProofLemmas.Thm61EvenFinalFans
