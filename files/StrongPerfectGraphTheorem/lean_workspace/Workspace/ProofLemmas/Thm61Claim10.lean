import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint

/-!
# 6.1, claim (10): three tracks with a common end, each meeting `X`

PAPER (proof of 6.1, printed p. 32):

> *"(10) If `P₁, P₂, P₃` are tracks in `H` with a common end `v`, say, and otherwise
> vertex-disjoint, each with an edge in `X`, then at least two of the three edges of
> `P₁ ∪ P₂ ∪ P₃` incident with `v` belong to `X`.*
>
> *For we may assume that for `i = 1,2,3`, `Pᵢ` is between `v` and `vᵢ` say, and the only edge
> of `Pᵢ` in `X` is the edge incident with `vᵢ`.  Some two of `P₁, P₂, P₃` have lengths of the
> same parity, say `P₁, P₂`, and so `P₁ ∪ P₂` is a track of even length.  If it has length 2
> then `P₁, P₂` both have length 1 and the claim holds, so we assume it has length `≥ 4`.  The
> edge of `P₃` incident with `v₃` is incident with a penultimate vertex of this track, by (9),
> and so `P₃` and one of `P₁, P₂` have length 1, and again the claim holds.  This proves
> (10)."*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm61Claim10

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61EvenClaims

/-! ### Small list utilities -/

section Aux

variable {α : Type*}

private theorem geq (l : List α) {i j : ℕ} (h : i = j) (hi : i < l.length)
    (hj : j < l.length) : l[i]'hi = l[j]'hj := by subst h; rfl

private theorem head_getElem {l : List α} {a : α} (h : l.head? = some a) (h0 : 0 < l.length) :
    l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simpa using h

private theorem last_getElem {l : List α} {a : α} (h : l.getLast? = some a)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = a := by
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (show l.length - 1 < l.length by omega)] at h
  exact Option.some_inj.mp h

private theorem nodup_index_eq {l : List α} (h : l.Nodup) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (hij : l[i]'hi = l[j]'hj) : i = j := by
  by_contra hne
  have := h.getElem_inj_iff (i := i) (j := j) (hi := hi) (hj := hj)
  exact hne (this.mp hij)

private theorem rev_getElem (l : List α) {i : ℕ} (h : i < l.reverse.length)
    (h' : l.length - 1 - i < l.length) : l.reverse[i]'h = l[l.length - 1 - i]'h' := by
  simp [List.getElem_reverse]

private theorem tl_getElem (l : List α) {i : ℕ} (h : i < l.tail.length)
    (h' : i + 1 < l.length) : l.tail[i]'h = l[i + 1]'h' := by
  simp [List.getElem_tail]

end Aux

/-! ### *"we may assume that … the only edge of `Pᵢ` in `X` is the edge incident with `vᵢ`"* -/

/-- The paper's reduction to a subtrack: replace a track carrying an edge of `X` by its initial
segment ending at the *first* edge of `X`.  The first edge is unchanged, so the conclusion of
(10) is unaffected. -/
private theorem truncate {W : Type*} {H : SimpleGraph W} {X : Set (Sym2 W)}
    {P : List W} {v w : W} (hP : IsTrackFrom H P v w) (hlen : 2 ≤ P.length)
    (hex : ∃ e ∈ trackEdges P, e ∈ X) :
    ∃ (P' : List W) (w' : W), IsTrackFrom H P' v w' ∧ ∃ _h2 : 2 ≤ P'.length,
      (∀ z, z ∈ P' → z ∈ P) ∧
      (P'[0]'(by omega) = P[0]'(by omega)) ∧ (P'[1]'(by omega) = P[1]'(by omega)) ∧
      s(P'[P'.length - 2]'(by omega), P'[P'.length - 1]'(by omega)) ∈ X ∧
      (∀ i : ℕ, ∀ _hi : i + 2 < P'.length,
        s(P'[i]'(by omega), P'[i + 1]'(by omega)) ∉ X) := by
  classical
  obtain ⟨e, ⟨i0, hi0, rfl⟩, heX⟩ := hex
  have hpex : ∃ i : ℕ, ∃ h : i + 1 < P.length,
      s(P[i]'(Nat.lt_of_succ_lt h), P[i + 1]'h) ∈ X := ⟨i0, hi0, heX⟩
  obtain ⟨hk1, hkX⟩ := Nat.find_spec hpex
  set k := Nat.find hpex with hkdef
  have hmin : ∀ j, j < k → ¬ (∃ h : j + 1 < P.length,
      s(P[j]'(Nat.lt_of_succ_lt h), P[j + 1]'h) ∈ X) := fun j hj => Nat.find_min hpex hj
  have hSlen : (TrackSlice.slice P 0 (k + 1)).length = k + 2 := by
    have := TrackSlice.length_slice P hk1 (Nat.zero_le (k + 1))
    omega
  have hSget : ∀ (m : ℕ) (hm : m < (TrackSlice.slice P 0 (k + 1)).length)
      (hm' : m < P.length), (TrackSlice.slice P 0 (k + 1))[m]'hm = P[m]'hm' := by
    intro m hm hm'
    rw [TrackSlice.getElem_slice P hm (show 0 + m < P.length by omega)]
    exact geq P (by omega) _ _
  have hfrom : IsTrackFrom H (TrackSlice.slice P 0 (k + 1)) (P[0]'(by omega))
      (P[k + 1]'hk1) := TrackSlice.isTrackFrom_slice hP.1 hk1 (Nat.zero_le (k + 1))
  have hP0 : P[0]'(show 0 < P.length by omega) = v := head_getElem hP.2.1 (by omega)
  refine ⟨TrackSlice.slice P 0 (k + 1), P[k + 1]'hk1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hP0]; exact hfrom
  · omega
  · intro z hz; exact TrackSlice.mem_of_mem_slice hz
  · exact hSget 0 (by omega) (by omega)
  · exact hSget 1 (by omega) (by omega)
  · have e1 : (TrackSlice.slice P 0 (k + 1))[(TrackSlice.slice P 0 (k + 1)).length - 2]'(by omega)
        = P[k]'(by omega) :=
      (geq (TrackSlice.slice P 0 (k + 1))
          (show (TrackSlice.slice P 0 (k + 1)).length - 2 = k by omega) _
          (show k < (TrackSlice.slice P 0 (k + 1)).length by omega)).trans
        (hSget k (by omega) (by omega))
    have e2 : (TrackSlice.slice P 0 (k + 1))[(TrackSlice.slice P 0 (k + 1)).length - 1]'(by omega)
        = P[k + 1]'hk1 :=
      (geq (TrackSlice.slice P 0 (k + 1))
          (show (TrackSlice.slice P 0 (k + 1)).length - 1 = k + 1 by omega) _
          (show k + 1 < (TrackSlice.slice P 0 (k + 1)).length by omega)).trans
        (hSget (k + 1) (by omega) (by omega))
    rw [e1, e2]; exact hkX
  · intro i hi
    have hik : i < k := by omega
    have e1 : (TrackSlice.slice P 0 (k + 1))[i]'(by omega) = P[i]'(by omega) :=
      hSget i (by omega) (by omega)
    have e2 : (TrackSlice.slice P 0 (k + 1))[i + 1]'(by omega) = P[i + 1]'(by omega) :=
      hSget (i + 1) (by omega) (by omega)
    rw [e1, e2]
    intro hcon
    exact hmin i hik ⟨by omega, hcon⟩

/-! ### The core of the printed argument -/

/-- *"Some two of `P₁, P₂, P₃` have lengths of the same parity, say `P₁, P₂`, and so `P₁ ∪ P₂`
is a track of even length. … The edge of `P₃` incident with `v₃` is incident with a penultimate
vertex of this track, by (9), and so `P₃` and one of `P₁, P₂` have length 1."*

Stated for three already-truncated tracks `A, B, C` (each carrying exactly one edge of `X`, at
its far end), with `A, B` the pair of equal length parity. -/
private theorem key {W : Type*} {H : SimpleGraph W} (X : Set (Sym2 W))
    (h9 : ∀ P : List W, IsTrackList H P → ∀ _hlen : 5 ≤ P.length, Even (trackLength P) →
      s(P[0]'(by omega), P[1]'(by omega)) ∈ X →
      s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega)) ∈ X →
      (∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
        s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ X) →
      ∀ f ∈ X, (P[1]'(by omega)) ∈ f ∨ (P[P.length - 2]'(by omega)) ∈ f)
    {v va vb vc : W} {A B C : List W}
    (hA : IsTrackFrom H A v va) (hB : IsTrackFrom H B v vb) (hC : IsTrackFrom H C v vc)
    (hA2 : 2 ≤ A.length) (hB2 : 2 ≤ B.length) (hC2 : 2 ≤ C.length)
    (hAB : ∀ z, z ∈ A → z ∈ B → z = v)
    (hAC : ∀ z, z ∈ A → z ∈ C → z = v)
    (hBC : ∀ z, z ∈ B → z ∈ C → z = v)
    (hAl : s(A[A.length - 2]'(by omega), A[A.length - 1]'(by omega)) ∈ X)
    (hBl : s(B[B.length - 2]'(by omega), B[B.length - 1]'(by omega)) ∈ X)
    (hCl : s(C[C.length - 2]'(by omega), C[C.length - 1]'(by omega)) ∈ X)
    (hAn : ∀ i : ℕ, ∀ _hi : i + 2 < A.length, s(A[i]'(by omega), A[i + 1]'(by omega)) ∉ X)
    (hBn : ∀ i : ℕ, ∀ _hi : i + 2 < B.length, s(B[i]'(by omega), B[i + 1]'(by omega)) ∉ X)
    (hpar : trackLength A % 2 = trackLength B % 2) :
    (s(A[0]'(by omega), A[1]'(by omega)) ∈ X ∧ s(B[0]'(by omega), B[1]'(by omega)) ∈ X) ∨
    (s(A[0]'(by omega), A[1]'(by omega)) ∈ X ∧ s(C[0]'(by omega), C[1]'(by omega)) ∈ X) ∨
    (s(B[0]'(by omega), B[1]'(by omega)) ∈ X ∧ s(C[0]'(by omega), C[1]'(by omega)) ∈ X) := by
  simp only [trackLength] at hpar
  have hAnd : A.Nodup := hA.1.2.1
  have hBnd : B.Nodup := hB.1.2.1
  have hCnd : C.Nodup := hC.1.2.1
  have hA0 : A[0]'(show 0 < A.length by omega) = v := head_getElem hA.2.1 (by omega)
  have hB0 : B[0]'(show 0 < B.length by omega) = v := head_getElem hB.2.1 (by omega)
  have hC0 : C[0]'(show 0 < C.length by omega) = v := head_getElem hC.2.1 (by omega)
  -- a track whose neighbour-of-the-far-end is the common end `v` has length 1
  have hAdeg : A[A.length - 2]'(by omega) = v → A.length = 2 := by
    intro h
    have := nodup_index_eq hAnd (show A.length - 2 < A.length by omega)
      (show 0 < A.length by omega) (by rw [h, hA0])
    omega
  have hBdeg : B[B.length - 2]'(by omega) = v → B.length = 2 := by
    intro h
    have := nodup_index_eq hBnd (show B.length - 2 < B.length by omega)
      (show 0 < B.length by omega) (by rw [h, hB0])
    omega
  have hCdeg : v ∈ s(C[C.length - 2]'(show C.length - 2 < C.length by omega),
      C[C.length - 1]'(show C.length - 1 < C.length by omega)) → C.length = 2 := by
    intro h
    rcases Sym2.mem_iff.mp h with h' | h'
    · have := nodup_index_eq hCnd (show C.length - 2 < C.length by omega)
        (show 0 < C.length by omega) (by rw [← h', hC0])
      omega
    · have := nodup_index_eq hCnd (show C.length - 1 < C.length by omega)
        (show 0 < C.length by omega) (by rw [← h', hC0])
      omega
  have hAfirst : A.length = 2 → s(A[0]'(by omega), A[1]'(by omega)) ∈ X := by
    intro h
    have e1 : A[A.length - 2]'(by omega) = A[0]'(show 0 < A.length by omega) :=
      geq A (by omega) _ _
    have e2 : A[A.length - 1]'(by omega) = A[1]'(show 1 < A.length by omega) :=
      geq A (by omega) _ _
    rw [e1, e2] at hAl; exact hAl
  have hBfirst : B.length = 2 → s(B[0]'(by omega), B[1]'(by omega)) ∈ X := by
    intro h
    have e1 : B[B.length - 2]'(by omega) = B[0]'(show 0 < B.length by omega) :=
      geq B (by omega) _ _
    have e2 : B[B.length - 1]'(by omega) = B[1]'(show 1 < B.length by omega) :=
      geq B (by omega) _ _
    rw [e1, e2] at hBl; exact hBl
  have hCfirst : C.length = 2 → s(C[0]'(by omega), C[1]'(by omega)) ∈ X := by
    intro h
    have e1 : C[C.length - 2]'(by omega) = C[0]'(show 0 < C.length by omega) :=
      geq C (by omega) _ _
    have e2 : C[C.length - 1]'(by omega) = C[1]'(show 1 < C.length by omega) :=
      geq C (by omega) _ _
    rw [e1, e2] at hCl; exact hCl
  -- *"`P₁ ∪ P₂` is a track"*
  have hAr : IsTrackFrom H A.reverse va v := TrackSlice.isTrackFrom_reverse hA
  have hcom : ∀ z, z ∈ A.reverse → z ∈ B → z = v := by
    intro z hz hzB; exact hAB z (List.mem_reverse.mp hz) hzB
  have hglue := TrackGlueAtCommonEndpoint H A.reverse B va v vb hAr hB hcom
  obtain ⟨hRfrom, -⟩ := hglue
  have hlenR : (A.reverse ++ B.tail).length = A.length + B.length - 1 := by
    simp only [List.length_append, List.length_reverse, List.length_tail]; omega
  -- *"If it has length 2 then `P₁, P₂` both have length 1 and the claim holds"*
  rcases Nat.lt_or_ge (A.length + B.length - 1) 5 with hsmall | hbig
  · have hAe : A.length = 2 := by omega
    have hBe : B.length = 2 := by omega
    exact Or.inl ⟨hAfirst hAe, hBfirst hBe⟩
  -- *"so we assume it has length ≥ 4"*
  have hR5 : 5 ≤ (A.reverse ++ B.tail).length := by omega
  -- index dictionary for the glued track
  have hRget1 : (A.reverse ++ B.tail)[1]'(by omega) = A[A.length - 2]'(by omega) := by
    rw [List.getElem_append_left (show 1 < A.reverse.length by
      simp only [List.length_reverse]; omega)]
    exact rev_getElem A _ (by omega)
  have hRget0 : (A.reverse ++ B.tail)[0]'(by omega) = A[A.length - 1]'(by omega) := by
    rw [List.getElem_append_left (show 0 < A.reverse.length by
      simp only [List.length_reverse]; omega)]
    exact rev_getElem A _ (by omega)
  have hRgetlast : (A.reverse ++ B.tail)[(A.reverse ++ B.tail).length - 1]'(by omega)
      = B[B.length - 1]'(by omega) := by
    rw [List.getElem_append_right (show A.reverse.length ≤ (A.reverse ++ B.tail).length - 1 by
      simp only [List.length_reverse]; omega)]
    rw [tl_getElem B (by simp only [List.length_tail, List.length_reverse]; omega)
      (show ((A.reverse ++ B.tail).length - 1) - A.reverse.length + 1 < B.length by
        simp only [List.length_reverse]; omega)]
    exact geq B (by simp only [List.length_reverse]; omega) _ _
  have hRgetpen : (A.reverse ++ B.tail)[(A.reverse ++ B.tail).length - 2]'(by omega)
      = B[B.length - 2]'(by omega) := by
    rcases Nat.lt_or_ge ((A.reverse ++ B.tail).length - 2) A.reverse.length with hlt | hge
    · -- `B` has length 2, and the penultimate vertex is the common end `v`
      have hBe : B.length = 2 := by
        simp only [List.length_reverse] at hlt; omega
      rw [List.getElem_append_left hlt]
      rw [rev_getElem A _ (show A.length - 1 - ((A.reverse ++ B.tail).length - 2) < A.length by
        omega)]
      rw [geq A (show A.length - 1 - ((A.reverse ++ B.tail).length - 2) = 0 by
        rw [hlenR]; omega) _ (show 0 < A.length by omega)]
      rw [geq B (show B.length - 2 = 0 by omega) _ (show 0 < B.length by omega)]
      rw [hA0, hB0]
    · rw [List.getElem_append_right hge]
      rw [tl_getElem B (by simp only [List.length_tail, List.length_reverse] at *; omega)
        (show ((A.reverse ++ B.tail).length - 2) - A.reverse.length + 1 < B.length by
          simp only [List.length_reverse] at *; omega)]
      exact geq B (by simp only [List.length_reverse] at *; omega) _ _
  -- the two end-edges of the glued track are the `X`-edges of `A` and of `B`
  have hRe0 : s((A.reverse ++ B.tail)[0]'(by omega), (A.reverse ++ B.tail)[1]'(by omega)) ∈ X := by
    rw [hRget0, hRget1, Sym2.eq_swap]; exact hAl
  have hRel : s((A.reverse ++ B.tail)[(A.reverse ++ B.tail).length - 2]'(by omega),
      (A.reverse ++ B.tail)[(A.reverse ++ B.tail).length - 1]'(by omega)) ∈ X := by
    rw [hRgetpen, hRgetlast]; exact hBl
  -- no internal edge of the glued track lies in `X`
  have hRint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < (A.reverse ++ B.tail).length,
      s((A.reverse ++ B.tail)[i]'(by omega),
        (A.reverse ++ B.tail)[i + 1]'(by omega)) ∉ X := by
    intro i hi1 hi
    rw [hlenR] at hi
    rcases Nat.lt_or_ge (i + 1) A.length with hcase | hcase
    · -- both endpoints inside the reversed `A`
      have e1 : (A.reverse ++ B.tail)[i]'(by omega)
          = A[A.length - 2 - i + 1]'(by omega) := by
        rw [List.getElem_append_left (show i < A.reverse.length by
          simp only [List.length_reverse]; omega)]
        rw [rev_getElem A _ (show A.length - 1 - i < A.length by omega)]
        exact geq A (by omega) _ _
      have e2 : (A.reverse ++ B.tail)[i + 1]'(by omega)
          = A[A.length - 2 - i]'(by omega) := by
        rw [List.getElem_append_left (show i + 1 < A.reverse.length by
          simp only [List.length_reverse]; omega)]
        rw [rev_getElem A _ (show A.length - 1 - (i + 1) < A.length by omega)]
        exact geq A (by omega) _ _
      rw [e1, e2, Sym2.eq_swap]
      exact hAn (A.length - 2 - i) (by omega)
    rcases Nat.lt_or_ge i A.length with hjunc | hjunc
    · -- the junction edge: it is the first edge of `B`
      have hiA : i = A.length - 1 := by omega
      have hB3 : 3 ≤ B.length := by omega
      have e1 : (A.reverse ++ B.tail)[i]'(by omega) = B[0]'(show 0 < B.length by omega) := by
        rw [List.getElem_append_left (show i < A.reverse.length by
          simp only [List.length_reverse]; omega)]
        rw [rev_getElem A _ (show A.length - 1 - i < A.length by omega)]
        rw [geq A (show A.length - 1 - i = 0 by omega) _ (show 0 < A.length by omega)]
        rw [hA0, hB0]
      have e2 : (A.reverse ++ B.tail)[i + 1]'(by omega)
          = B[1]'(show 1 < B.length by omega) := by
        rw [List.getElem_append_right (show A.reverse.length ≤ i + 1 by
          simp only [List.length_reverse]; omega)]
        rw [tl_getElem B (by simp only [List.length_tail, List.length_reverse]; omega)
          (show i + 1 - A.reverse.length + 1 < B.length by
            simp only [List.length_reverse]; omega)]
        exact geq B (by simp only [List.length_reverse]; omega) _ _
      rw [e1, e2]
      exact hBn 0 (by omega)
    · -- both endpoints inside `B`
      have e1 : (A.reverse ++ B.tail)[i]'(by omega)
          = B[i - A.length + 1]'(by omega) := by
        rw [List.getElem_append_right (show A.reverse.length ≤ i by
          simp only [List.length_reverse]; omega)]
        rw [tl_getElem B (by simp only [List.length_tail, List.length_reverse]; omega)
          (show i - A.reverse.length + 1 < B.length by
            simp only [List.length_reverse]; omega)]
        exact geq B (by simp only [List.length_reverse]) _ _
      have e2 : (A.reverse ++ B.tail)[i + 1]'(by omega)
          = B[i - A.length + 1 + 1]'(by omega) := by
        rw [List.getElem_append_right (show A.reverse.length ≤ i + 1 by
          simp only [List.length_reverse]; omega)]
        rw [tl_getElem B (by simp only [List.length_tail, List.length_reverse]; omega)
          (show i + 1 - A.reverse.length + 1 < B.length by
            simp only [List.length_reverse]; omega)]
        exact geq B (by simp only [List.length_reverse]; omega) _ _
      rw [e1, e2]
      exact hBn (i - A.length + 1) (by omega)
  have hReven : Even (trackLength (A.reverse ++ B.tail)) := by
    rw [trackLength, Nat.even_iff, hlenR]
    omega
  -- *"by (9)"*
  rcases h9 (A.reverse ++ B.tail) hRfrom.1 hR5 hReven hRe0 hRel hRint _ hCl with hpen | hpen
  · -- the penultimate vertex on the `A` side
    rw [hRget1] at hpen
    have hmemC : A[A.length - 2]'(show A.length - 2 < A.length by omega) ∈ C := by
      rcases Sym2.mem_iff.mp hpen with h' | h'
      · rw [h']; exact List.getElem_mem _
      · rw [h']; exact List.getElem_mem _
    have hv : A[A.length - 2]'(show A.length - 2 < A.length by omega) = v :=
      hAC _ (List.getElem_mem _) hmemC
    have hCe : C.length = 2 := hCdeg (by rw [← hv]; exact hpen)
    exact Or.inr (Or.inl ⟨hAfirst (hAdeg hv), hCfirst hCe⟩)
  · -- the penultimate vertex on the `B` side
    rw [hRgetpen] at hpen
    have hmemC : B[B.length - 2]'(show B.length - 2 < B.length by omega) ∈ C := by
      rcases Sym2.mem_iff.mp hpen with h' | h'
      · rw [h']; exact List.getElem_mem _
      · rw [h']; exact List.getElem_mem _
    have hv : B[B.length - 2]'(show B.length - 2 < B.length by omega) = v :=
      hBC _ (List.getElem_mem _) hmemC
    have hCe : C.length = 2 := hCdeg (by rw [← hv]; exact hpen)
    exact Or.inr (Or.inr ⟨hBfirst (hBdeg hv), hCfirst hCe⟩)

/-- **6.1(10)** *"If `P₁, P₂, P₃` are tracks in `H` with a common end `v`, say, and otherwise
vertex-disjoint, each with an edge in `X`, then at least two of the three edges of
`P₁ ∪ P₂ ∪ P₃` incident with `v` belong to `X`."* -/
theorem thm_6_1_claim10
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h9 : Claim9 G H K φ Y y₁ y₂) :
    Claim10 G H K φ Y := by
  intro v v₁ v₂ v₃ P₁ P₂ P₃ hP₁ hP₂ hP₃ hl₁ hl₂ hl₃ h₁₂ h₁₃ h₂₃ hX₁ hX₂ hX₃
  -- `X` is the set of `Y`-complete edges; (9) at `Y' = Y`
  have h9' : ∀ P : List (Fin n), IsTrackList H P → ∀ _hlen : 5 ≤ P.length,
      Even (trackLength P) →
      s(P[0]'(by omega), P[1]'(by omega)) ∈ completeEdges G H K φ Y →
      s(P[P.length - 2]'(by omega), P[P.length - 1]'(by omega)) ∈ completeEdges G H K φ Y →
      (∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
        s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y) →
      ∀ f ∈ completeEdges G H K φ Y,
        (P[1]'(by omega)) ∈ f ∨ (P[P.length - 2]'(by omega)) ∈ f :=
    fun P hP hlen he e0 el ei f hf => h9 Y (Or.inl rfl) P hP hlen he e0 el ei f hf
  -- *"we may assume … the only edge of `Pᵢ` in `X` is the edge incident with `vᵢ`"*
  obtain ⟨A, wa, hA, hA2, hAmem, hAe0, hAe1, hAl, hAn⟩ := truncate hP₁ hl₁ hX₁
  obtain ⟨B, wb, hB, hB2, hBmem, hBe0, hBe1, hBl, hBn⟩ := truncate hP₂ hl₂ hX₂
  obtain ⟨C, wc, hC, hC2, hCmem, hCe0, hCe1, hCl, hCn⟩ := truncate hP₃ hl₃ hX₃
  have hAB : ∀ z, z ∈ A → z ∈ B → z = v := fun z hz hz' => h₁₂ z (hAmem z hz) (hBmem z hz')
  have hAC : ∀ z, z ∈ A → z ∈ C → z = v := fun z hz hz' => h₁₃ z (hAmem z hz) (hCmem z hz')
  have hBC : ∀ z, z ∈ B → z ∈ C → z = v := fun z hz hz' => h₂₃ z (hBmem z hz) (hCmem z hz')
  have hBA : ∀ z, z ∈ B → z ∈ A → z = v := fun z hz hz' => hAB z hz' hz
  have hCA : ∀ z, z ∈ C → z ∈ A → z = v := fun z hz hz' => hAC z hz' hz
  have hCB : ∀ z, z ∈ C → z ∈ B → z = v := fun z hz hz' => hBC z hz' hz
  -- transport the conclusion back along the truncation
  have gA : s(A[0]'(by omega), A[1]'(by omega)) ∈ completeEdges G H K φ Y →
      s(P₁[0]'(by omega), P₁[1]'(by omega)) ∈ completeEdges G H K φ Y := by
    intro h; rw [hAe0, hAe1] at h; exact h
  have gB : s(B[0]'(by omega), B[1]'(by omega)) ∈ completeEdges G H K φ Y →
      s(P₂[0]'(by omega), P₂[1]'(by omega)) ∈ completeEdges G H K φ Y := by
    intro h; rw [hBe0, hBe1] at h; exact h
  have gC : s(C[0]'(by omega), C[1]'(by omega)) ∈ completeEdges G H K φ Y →
      s(P₃[0]'(by omega), P₃[1]'(by omega)) ∈ completeEdges G H K φ Y := by
    intro h; rw [hCe0, hCe1] at h; exact h
  -- *"Some two of `P₁, P₂, P₃` have lengths of the same parity"*
  have hpar : trackLength A % 2 = trackLength B % 2 ∨ trackLength A % 2 = trackLength C % 2 ∨
      trackLength B % 2 = trackLength C % 2 := by omega
  rcases hpar with hp | hp | hp
  · rcases key (completeEdges G H K φ Y) h9' hA hB hC hA2 hB2 hC2 hAB hAC hBC
      hAl hBl hCl hAn hBn hp with h | h | h
    · exact Or.inl ⟨gA h.1, gB h.2⟩
    · exact Or.inr (Or.inl ⟨gA h.1, gC h.2⟩)
    · exact Or.inr (Or.inr ⟨gB h.1, gC h.2⟩)
  · rcases key (completeEdges G H K φ Y) h9' hA hC hB hA2 hC2 hB2 hAC hAB hCB
      hAl hCl hBl hAn hCn hp with h | h | h
    · exact Or.inr (Or.inl ⟨gA h.1, gC h.2⟩)
    · exact Or.inl ⟨gA h.1, gB h.2⟩
    · exact Or.inr (Or.inr ⟨gB h.2, gC h.1⟩)
  · rcases key (completeEdges G H K φ Y) h9' hB hC hA hB2 hC2 hA2 hBC hBA hCA
      hBl hCl hAl hBn hCn hp with h | h | h
    · exact Or.inr (Or.inr ⟨gB h.1, gC h.2⟩)
    · exact Or.inl ⟨gA h.2, gB h.1⟩
    · exact Or.inr (Or.inl ⟨gA h.2, gC h.1⟩)

end Workspace.ProofLemmas.Thm61Claim10
