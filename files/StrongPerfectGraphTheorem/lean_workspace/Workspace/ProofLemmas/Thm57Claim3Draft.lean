import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm57Setup

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim3Draft

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem draft (H : SimpleGraph W) (X : Set (Sym2 W))
    (hnotrack : NoEvenTrack57 H X) :
    ¬ ∃ (b a₁ a₂ a₃ : W) (P₁ P₂ P₃ : List W)
        (_h₁ : 2 ≤ P₁.length) (_h₂ : 2 ≤ P₂.length) (_h₃ : 2 ≤ P₃.length),
      IsTrackFrom H P₁ b a₁ ∧ IsTrackFrom H P₂ b a₂ ∧ IsTrackFrom H P₃ b a₃ ∧
      (∀ v : W, v ∈ P₁ → v ∈ P₂ → v = b) ∧
      (∀ v : W, v ∈ P₁ → v ∈ P₃ → v = b) ∧
      (∀ v : W, v ∈ P₂ → v ∈ P₃ → v = b) ∧
      (∃ e ∈ trackEdges P₁, e ∈ X) ∧
      (∃ e ∈ trackEdges P₂, e ∈ X) ∧
      (∃ e ∈ trackEdges P₃, e ∈ X) ∧
      ((s(P₁[0], P₁[1]) ∉ X ∧ s(P₂[0], P₂[1]) ∉ X) ∨
       (s(P₁[0], P₁[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X) ∨
       (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)) := by
  classical
  rintro ⟨b, a₁, a₂, a₃, P₁, P₂, P₃, h₁, h₂, h₃,
    hP₁, hP₂, hP₃, hcommon₁₂, hcommon₁₃, hcommon₂₃,
    hX₁, hX₂, hX₃, hout⟩
  have clean : ∀ (P : List W), (∃ e ∈ trackEdges P, e ∈ X) →
      ∃ n : ℕ, ∃ hn : n + 1 < P.length,
        s(P[n], P[n + 1]) ∈ X ∧
        ∀ (j : ℕ), j < n → ∀ hj : j + 1 < P.length, s(P[j], P[j + 1]) ∉ X := by
    intro P hXP
    obtain ⟨e, ⟨i, hi, rfl⟩, heX⟩ := hXP
    let p : ℕ → Prop := fun j => ∃ hj : j + 1 < P.length, s(P[j], P[j + 1]) ∈ X
    have hex : ∃ j, p j := ⟨i, hi, heX⟩
    let n := Nat.find hex
    have hspec : p n := Nat.find_spec hex
    obtain ⟨hn, hnX⟩ := hspec
    refine ⟨n, hn, hnX, ?_⟩
    intro j hjn hjlen hjX
    exact (Nat.find_min hex hjn) ⟨hjlen, hjX⟩
  obtain ⟨n₁, hn₁, hnX₁, hmin₁⟩ := clean P₁ hX₁
  obtain ⟨n₂, hn₂, hnX₂, hmin₂⟩ := clean P₂ hX₂
  obtain ⟨n₃, hn₃, hnX₃, hmin₃⟩ := clean P₃ hX₃

  have pair_short : ∀ (P Q : List W) (n m : ℕ),
      IsTrackList H P → IsTrackList H Q →
      P.head? = some b → Q.head? = some b →
      (∀ v : W, v ∈ P → v ∈ Q → v = b) →
      (∃ hn : n + 1 < P.length, s(P[n], P[n + 1]) ∈ X) →
      (∃ hm : m + 1 < Q.length, s(Q[m], Q[m + 1]) ∈ X) →
      (∀ (j : ℕ), j < n → ∀ hj : j + 1 < P.length, s(P[j], P[j + 1]) ∉ X) →
      (∀ (j : ℕ), j < m → ∀ hj : j + 1 < Q.length, s(Q[j], Q[j + 1]) ∉ X) →
      Even ((n + 1) + (m + 1)) → n = 0 ∧ m = 0 := by
    intro P Q n m hPt hQt hPhead hQhead hcommon hnpack hmpack hminP hminQ heven
    obtain ⟨hn, hnX⟩ := hnpack
    obtain ⟨hm, hmX⟩ := hmpack
    let A := P.take (n + 2)
    let B := Q.take (m + 2)
    let R := A.reverse ++ B.tail
    have hAlen : A.length = n + 2 := by simp [A, List.length_take]; omega
    have hBlen : B.length = m + 2 := by simp [B, List.length_take]; omega
    have hRlen : R.length = n + m + 3 := by
      simp only [R, List.length_append, List.length_reverse, List.length_tail, hAlen, hBlen]
      omega
    have hAget : ∀ (k : ℕ) (hkR : k < R.length) (hk : k < n + 2),
        R[k]'hkR = P[n + 1 - k]'(by omega) := by
      intro k hkR hk
      simp only [R]
      rw [List.getElem_append_left (by simpa [hAlen] using hk), List.getElem_reverse]
      simp only [hAlen]
      rw [List.getElem_take]
      congr 1
    have hBget : ∀ (k : ℕ) (hkR : k < R.length), n + 1 ≤ k →
        R[k]'hkR = Q[k - (n + 1)]'(by omega) := by
      intro k hkR hk
      by_cases heq : k = n + 1
      · subst k
        simp only [R]
        rw [List.getElem_append_left (by simp [hAlen]), List.getElem_reverse]
        simp only [hAlen]
        rw [List.getElem_take]
        have hP0 : P[0]'(by omega) = b := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hPhead
          exact Option.some_injective _ hPhead
        have hQ0 : Q[0]'(by omega) = b := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hQhead
          exact Option.some_injective _ hQhead
        have hi : n + 2 - 1 - (n + 1) = 0 := by omega
        simpa only [hi, Nat.sub_self] using hP0.trans hQ0.symm
      · have hkA : A.length ≤ k := by rw [hAlen]; omega
        have hkAr : A.reverse.length ≤ k := by simpa using hkA
        have hArlen : A.reverse.length = n + 2 := by simpa using hAlen
        simp only [R]
        rw [List.getElem_append_right hkAr, List.getElem_tail]
        simp only [B]
        rw [List.getElem_take]
        congr 1
        rw [hArlen]
        omega
    have hAt : IsTrackList H A := by
      refine ⟨?_, hPt.2.1.sublist (List.take_sublist _ _), ?_⟩
      · intro hnil
        rw [hnil] at hAlen
        simp at hAlen
      · intro k hk
        rw [List.getElem_take, List.getElem_take]
        exact hPt.2.2 k (by rw [hAlen] at hk; omega)
    have hBt : IsTrackList H B := by
      refine ⟨?_, hQt.2.1.sublist (List.take_sublist _ _), ?_⟩
      · intro hnil
        rw [hnil] at hBlen
        simp at hBlen
      · intro k hk
        rw [List.getElem_take, List.getElem_take]
        exact hQt.2.2 k (by rw [hBlen] at hk; omega)
    have hAhead : A.head? = some b := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [List.getElem_take]
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hPhead
      exact hPhead
    have hBhead : B.head? = some b := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      rw [List.getElem_take]
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hQhead
      exact hQhead
    have hbnotBtail : b ∉ B.tail := by
      rcases hB : B with _ | ⟨z, zs⟩
      · simp [hB]
      · have hzb : z = b := by
          rw [hB] at hBhead
          simpa using hBhead
        rw [hB] at hBt
        simp only [List.tail_cons]
        rw [hzb] at hBt
        exact (List.nodup_cons.mp hBt.2.1).1
    have hRt : IsTrackList H R := by
      refine ⟨?_, ?_, ?_⟩
      · intro hnil
        rw [hnil] at hRlen
        simp at hRlen
      · simp only [R]
        rw [List.nodup_append]
        refine ⟨by simpa using hAt.2.1, hBt.2.1.tail, ?_⟩
        intro x hx y hy hxy
        have hxA : x ∈ A := by simpa using hx
        have hxP : x ∈ P := (List.take_sublist (n + 2) P).subset hxA
        have hyB : y ∈ B := List.mem_of_mem_tail hy
        have hyQ : y ∈ Q := (List.take_sublist (m + 2) Q).subset hyB
        have hxb : x = b := hcommon x hxP (by simpa [hxy] using hyQ)
        apply hbnotBtail
        have hyb : y = b := hxy.symm.trans hxb
        rw [hyb] at hy
        exact hy
      · intro k hk
        rw [hRlen] at hk
        by_cases hleft : k < n + 1
        · rw [hAget k (by omega) (by omega), hAget (k + 1) (by omega) (by omega)]
          simpa only [show n - k + 1 = n + 1 - k by omega,
            show n + 1 - (k + 1) = n - k by omega] using (hPt.2.2 (n - k) (by omega)).symm
        · rw [hBget k (by omega) (by omega), hBget (k + 1) (by omega) (by omega)]
          simpa only [show k - (n + 1) + 1 = k + 1 - (n + 1) by omega] using
            hQt.2.2 (k - (n + 1)) (by omega)
    have hfirstX : s(R[0]'(by omega), R[1]'(by omega)) ∈ X := by
      rw [hAget 0 (by omega) (by omega), hAget 1 (by omega) (by omega)]
      rw [Sym2.eq_swap]
      exact hnX
    have hlastX : s(R[R.length - 2]'(by omega), R[R.length - 1]'(by omega)) ∈ X := by
      rw [hBget (R.length - 2) (by omega) (by rw [hRlen]; omega),
        hBget (R.length - 1) (by omega) (by rw [hRlen]; omega)]
      have hi0 : R.length - 2 - (n + 1) = m := by omega
      have hi1 : R.length - 1 - (n + 1) = m + 1 := by omega
      simpa only [hi0, hi1] using hmX
    have hother : ∀ e ∈ trackEdges R,
        e ≠ s(R[0], R[1]) → e ≠ s(R[R.length - 2], R[R.length - 1]) → e ∉ X := by
      intro e he hneFirst hneLast
      obtain ⟨k, hk, rfl⟩ := he
      rw [hRlen] at hk
      by_cases hleft : k < n + 1
      · have hk0 : k ≠ 0 := by
          intro hk0
          subst k
          exact hneFirst rfl
        rw [hAget k (by omega) (by omega), hAget (k + 1) (by omega) (by omega)]
        rw [Sym2.eq_swap]
        simpa only [show n + 1 - k = n - k + 1 by omega,
          show n + 1 - (k + 1) = n - k by omega] using
            hminP (n - k) (by omega) (by omega)
      · have hklast : k ≠ R.length - 2 := by
          intro hkeq
          subst k
          have helem : R[R.length - 2 + 1]'(by omega) = R[R.length - 1]'(by omega) :=
            hRt.2.1.getElem_inj_iff.mpr (by omega)
          exact hneLast (by rw [helem])
        rw [hBget k (by omega) (by omega), hBget (k + 1) (by omega) (by omega)]
        simpa only [show k + 1 - (n + 1) = k - (n + 1) + 1 by omega] using
          hminQ (k - (n + 1)) (by omega) (by omega)
    have hevenR : Even (trackLength R) := by
      have hlen : trackLength R = (n + 1) + (m + 1) := by
        rw [trackLength, hRlen]
        omega
      rw [hlen]
      exact heven
    by_contra hzero
    have hlarge : 5 ≤ R.length := by
      rw [hRlen]
      have hpos : 0 < n ∨ 0 < m := by omega
      rcases heven with ⟨t, ht⟩
      omega
    exact hnotrack ⟨R, hlarge, hRt, hevenR, hfirstX, hlastX, hother⟩

  have hshort₁₂ : Even ((n₁ + 1) + (n₂ + 1)) → n₁ = 0 ∧ n₂ = 0 := by
    intro hp
    exact pair_short P₁ P₂ n₁ n₂ hP₁.1 hP₂.1 hP₁.2.1 hP₂.2.1 hcommon₁₂
      ⟨hn₁, hnX₁⟩ ⟨hn₂, hnX₂⟩ hmin₁ hmin₂ hp
  have hshort₁₃ : Even ((n₁ + 1) + (n₃ + 1)) → n₁ = 0 ∧ n₃ = 0 := by
    intro hp
    exact pair_short P₁ P₃ n₁ n₃ hP₁.1 hP₃.1 hP₁.2.1 hP₃.2.1 hcommon₁₃
      ⟨hn₁, hnX₁⟩ ⟨hn₃, hnX₃⟩ hmin₁ hmin₃ hp
  have hshort₂₃ : Even ((n₂ + 1) + (n₃ + 1)) → n₂ = 0 ∧ n₃ = 0 := by
    intro hp
    exact pair_short P₂ P₃ n₂ n₃ hP₂.1 hP₃.1 hP₂.2.1 hP₃.2.1 hcommon₂₃
      ⟨hn₂, hnX₂⟩ ⟨hn₃, hnX₃⟩ hmin₂ hmin₃ hp
  have hone₁ : n₁ = 0 → s(P₁[0], P₁[1]) ∈ X := by intro h; subst n₁; exact hnX₁
  have hone₂ : n₂ = 0 → s(P₂[0], P₂[1]) ∈ X := by intro h; subst n₂; exact hnX₂
  have hone₃ : n₃ = 0 → s(P₃[0], P₃[1]) ∈ X := by intro h; subst n₃; exact hnX₃
  have finish₁₂ (hz₁ : n₁ = 0) (hz₂ : n₂ = 0) : False := by
    have hx₁ := hone₁ hz₁
    have hx₂ := hone₂ hz₂
    rcases hout with h | h | h
    · exact h.1 hx₁
    · exact h.1 hx₁
    · exact h.1 hx₂
  have finish₁₃ (hz₁ : n₁ = 0) (hz₃ : n₃ = 0) : False := by
    have hx₁ := hone₁ hz₁
    have hx₃ := hone₃ hz₃
    rcases hout with h | h | h
    · exact h.1 hx₁
    · exact h.1 hx₁
    · exact h.2 hx₃
  have finish₂₃ (hz₂ : n₂ = 0) (hz₃ : n₃ = 0) : False := by
    have hx₂ := hone₂ hz₂
    have hx₃ := hone₃ hz₃
    rcases hout with h | h | h
    · exact h.2 hx₂
    · exact h.2 hx₃
    · exact h.1 hx₂
  rcases Nat.even_or_odd (n₁ + 1) with he₁ | ho₁
  · rcases Nat.even_or_odd (n₂ + 1) with he₂ | ho₂
    · exact (hshort₁₂ (he₁.add he₂)).elim finish₁₂
    · rcases Nat.even_or_odd (n₃ + 1) with he₃ | ho₃
      · exact (hshort₁₃ (he₁.add he₃)).elim finish₁₃
      · exact (hshort₂₃ (ho₂.add_odd ho₃)).elim finish₂₃
  · rcases Nat.even_or_odd (n₂ + 1) with he₂ | ho₂
    · rcases Nat.even_or_odd (n₃ + 1) with he₃ | ho₃
      · exact (hshort₂₃ (he₂.add he₃)).elim finish₂₃
      · exact (hshort₁₃ (ho₁.add_odd ho₃)).elim finish₁₃
    · exact (hshort₁₂ (ho₁.add_odd ho₂)).elim finish₁₂

end Workspace.ProofLemmas.Thm57Claim3Draft
