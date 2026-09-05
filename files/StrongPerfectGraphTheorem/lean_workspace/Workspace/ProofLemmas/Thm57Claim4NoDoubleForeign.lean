import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Thm57Claim4Basics
import Workspace.ProofLemmas.Thm57Claim4Config

/-!
# 5.7 (4): no end is joined in `K` to ends of both other marked edges

PAPER (printed p. 24):

> *"Also, by (3) it follows that `a₃` is not adjacent in `K` to both `b₁` and `b₂`, and five
> similar statements."*

The lemma below is the common form of all six statements, and it does not mention the
colouring: no end of `x k` is `K`-adjacent to an end of `x i` and to an end of `x j`, for
`i, j, k` distinct.  The reason is the paper's: the two tracks in `A`, each completed by the
marked edge at its far end, together with the one-edge track `x k`, would be three tracks with
a common end, otherwise disjoint, each carrying an edge of `X`, and with at most one of the
three edges at the common end in `X` — exactly what claim (3) forbids.

Two tracks of `A` out of the same vertex need not be disjoint, so the common end is not `u`
itself.  We take `t` to be the **last** vertex of `P` (counted from `u`) that also lies on
`Q`; then the part of `P` after `t` misses `Q` altogether, and the two parts of `Q` on either
side of `t` meet only in `t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm57Claim4NoDoubleForeign

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Claim4Config
open Workspace.ProofLemmas.Thm57Claim4Basics
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem no_double_foreign
    (H : SimpleGraph W) (X : Set (Sym2 W)) (A : Set W) (x : Fin 3 → Sym2 W)
    (hxX : ∀ i, x i ∈ X) (hxE : ∀ i, x i ∈ H.edgeSet)
    (hdisj : ∀ i j, i ≠ j → DisjointEdges (x i) (x j))
    (hclaim3 :
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
         (s(P₂[0], P₂[1]) ∉ X ∧ s(P₃[0], P₃[1]) ∉ X)))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {u v w : W} (hu : u ∈ x k) (hv : v ∈ x i) (hw : w ∈ x j)
    (h1 : KAdj H X A x u v) (h2 : KAdj H X A x u w) : False := by
  classical
  obtain ⟨P, hP, -, hPT⟩ := h1
  obtain ⟨Q, hQ, -, hQT⟩ := h2
  obtain ⟨u', hxk⟩ := Sym2.mem_iff_exists.mp hu
  obtain ⟨v', hxi⟩ := Sym2.mem_iff_exists.mp hv
  obtain ⟨w', hxj⟩ := Sym2.mem_iff_exists.mp hw
  have hu'x : u' ∈ x k := by rw [hxk]; exact Sym2.mem_mk_right _ _
  have hv'x : v' ∈ x i := by rw [hxi]; exact Sym2.mem_mk_right _ _
  have hw'x : w' ∈ x j := by rw [hxj]; exact Sym2.mem_mk_right _ _
  have hadjk : H.Adj u u' := by have h := hxE k; rw [hxk] at h; exact h
  have hadji : H.Adj v v' := by have h := hxE i; rw [hxi] at h; exact h
  have hadjj : H.Adj w w' := by have h := hxE j; rw [hxj] at h; exact h
  -- distinct terminals of distinct marked edges
  have hne : ∀ (a b : W) (p q : Fin 3), p ≠ q → a ∈ x p → b ∈ x q → a ≠ b := by
    intro a b p q hpq ha hb hab
    exact hdisj p q hpq a ⟨ha, hab ▸ hb⟩
  -- which terminals can appear on `P` and on `Q`
  have hPterm : ∀ z ∈ P, z ∈ Terminals x → z = u ∨ z = v := hPT
  have hQterm : ∀ z ∈ Q, z ∈ Terminals x → z = u ∨ z = w := hQT
  have hnotP : ∀ z : W, z ∈ Terminals x → z ≠ u → z ≠ v → z ∉ P := by
    intro z hz h1 h2 hzP
    rcases hPterm z hzP hz with h | h
    · exact h1 h
    · exact h2 h
  have hnotQ : ∀ z : W, z ∈ Terminals x → z ≠ u → z ≠ w → z ∉ Q := by
    intro z hz h1 h2 hzQ
    rcases hQterm z hzQ hz with h | h
    · exact h1 h
    · exact h2 h
  have hwP : w ∉ P := hnotP w ⟨j, hw⟩ (hne w u j k hjk hw hu) (hne w v j i hij.symm hw hv)
  have hw'P : w' ∉ P :=
    hnotP w' ⟨j, hw'x⟩ (hne w' u j k hjk hw'x hu) (hne w' v j i hij.symm hw'x hv)
  have hu'P : u' ∉ P :=
    hnotP u' ⟨k, hu'x⟩ hadjk.ne' (hne u' v k i (Ne.symm hik) hu'x hv)
  have hv'P : v' ∉ P :=
    hnotP v' ⟨i, hv'x⟩ (hne v' u i k hik hv'x hu) hadji.ne'
  have hvQ : v ∉ Q := hnotQ v ⟨i, hv⟩ (hne v u i k hik hv hu) (hne v w i j hij hv hw)
  have hv'Q : v' ∉ Q :=
    hnotQ v' ⟨i, hv'x⟩ (hne v' u i k hik hv'x hu) (hne v' w i j hij hv'x hw)
  have hu'Q : u' ∉ Q := hnotQ u' ⟨k, hu'x⟩ hadjk.ne' (hne u' w k j (Ne.symm hjk) hu'x hw)
  have hw'Q : w' ∉ Q := hnotQ w' ⟨j, hw'x⟩ (hne w' u j k hjk hw'x hu) hadjj.ne'
  -- endpoints by index
  have hPne : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  have hQne : 0 < Q.length := List.length_pos_of_ne_nil hQ.1.1
  have hP0 : P[0]'hPne = u := getElem_zero_of_head? hP.2.1 hPne
  have hPl : P[P.length - 1]'(by omega) = v := getElem_last_of_getLast? hP.2.2 hPne
  have hQ0 : Q[0]'hQne = u := getElem_zero_of_head? hQ.2.1 hQne
  have hQl : Q[Q.length - 1]'(by omega) = w := getElem_last_of_getLast? hQ.2.2 hQne
  have huQ : u ∈ Q := by
    rw [← hQ0]; exact List.getElem_mem hQne
  -- the last vertex of `P` that lies on `Q`
  obtain ⟨p, hplt, htQ, hgreat⟩ :
      ∃ p, ∃ h : p < P.length, P[p]'h ∈ Q ∧ ∀ r (hr : r < P.length), p < r → P[r]'hr ∉ Q := by
    classical
    set pred : ℕ → Prop := fun r => ∃ h : r < P.length, P[r]'h ∈ Q with hpreddef
    have hpred0 : pred 0 := ⟨hPne, by rw [hP0]; exact huQ⟩
    have hspec : pred (Nat.findGreatest pred (P.length - 1)) :=
      Nat.findGreatest_spec (Nat.zero_le _) hpred0
    obtain ⟨hlt, hmem⟩ := hspec
    refine ⟨Nat.findGreatest pred (P.length - 1), hlt, hmem, ?_⟩
    intro r hr hgt hrQ
    exact Nat.findGreatest_is_greatest hgt (by omega) ⟨hr, hrQ⟩
  obtain ⟨mq, hmqlt, hQmq⟩ := List.mem_iff_getElem.mp htQ
  -- the three tracks out of `t`
  set t : W := P[p]'hplt with htdef
  have hR₁ : IsTrackFrom (H.deleteEdges X) (slice P p (P.length - 1)) t v := by
    rw [htdef]
    have h := isTrackFrom_slice (i := p) (j := P.length - 1) hP.1
      (show P.length - 1 < P.length by omega) (by omega)
    rwa [hPl] at h
  have hR₂ : IsTrackFrom (H.deleteEdges X) (slice Q mq (Q.length - 1)) t w := by
    rw [← hQmq]
    have h := isTrackFrom_slice (i := mq) (j := Q.length - 1) hQ.1
      (show Q.length - 1 < Q.length by omega) (by omega)
    rwa [hQl] at h
  have hR₃ : IsTrackFrom (H.deleteEdges X) (slice Q 0 mq).reverse t u := by
    rw [← hQmq]
    have h := isTrackFrom_slice (i := 0) (j := mq) hQ.1 hmqlt (Nat.zero_le _)
    rw [hQ0] at h
    exact isTrackFrom_reverse h
  -- lengths of the three pieces
  have hL₁ : (slice P p (P.length - 1)).length = P.length - 1 - p + 1 :=
    length_slice P (show P.length - 1 < P.length by omega) (by omega)
  have hL₂ : (slice Q mq (Q.length - 1)).length = Q.length - 1 - mq + 1 :=
    length_slice Q (show Q.length - 1 < Q.length by omega) (by omega)
  have hL₃ : (slice Q 0 mq).length = mq + 1 := by
    have := length_slice Q hmqlt (Nat.zero_le mq)
    simpa using this
  -- membership dictionaries
  have hR₁P : ∀ z ∈ slice P p (P.length - 1), z ∈ P := fun z hz => mem_of_mem_slice hz
  have hR₂Q : ∀ z ∈ slice Q mq (Q.length - 1), z ∈ Q := fun z hz => mem_of_mem_slice hz
  have hR₃Q : ∀ z ∈ (slice Q 0 mq).reverse, z ∈ Q := fun z hz =>
    mem_of_mem_slice (List.mem_reverse.mp hz)
  -- the part of `P` beyond `t` misses `Q`
  have hR₁Q : ∀ z ∈ slice P p (P.length - 1), z ∈ Q → z = t := by
    intro z hz hzQ
    obtain ⟨r, hr, hpr, hrl, hrz⟩ :=
      (mem_slice_iff (show P.length - 1 < P.length by omega) (show p ≤ P.length - 1 by omega)).mp hz
    rcases eq_or_lt_of_le hpr with h | h
    · rw [htdef, ← hrz]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P h.symm hr hplt
    · exact absurd (hrz ▸ hzQ) (hgreat r hr h)
  -- the two parts of `Q` meet only at `t`
  have hR₂₃ : ∀ z ∈ slice Q mq (Q.length - 1), z ∈ (slice Q 0 mq).reverse → z = t := by
    intro z h2 h3
    obtain ⟨r₁, hr₁, hle₁, hle₁', he₁⟩ :=
      (mem_slice_iff (show Q.length - 1 < Q.length by omega)
        (show mq ≤ Q.length - 1 by omega)).mp h2
    obtain ⟨r₂, hr₂, hle₂, hle₂', he₂⟩ :=
      (mem_slice_iff hmqlt (Nat.zero_le mq)).mp (List.mem_reverse.mp h3)
    have hrr : r₁ = r₂ := hQ.1.2.1.getElem_inj_iff.mp (he₁.trans he₂.symm)
    have : r₁ = mq := by omega
    rw [← hQmq, ← he₁]
    exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q this hr₁ hmqlt
  -- the pendant vertices are new
  have hv'nR₁ : v' ∉ slice P p (P.length - 1) := fun h => hv'P (hR₁P _ h)
  have hw'nR₂ : w' ∉ slice Q mq (Q.length - 1) := fun h => hw'Q (hR₂Q _ h)
  have hu'nR₃ : u' ∉ (slice Q 0 mq).reverse := fun h => hu'Q (hR₃Q _ h)
  -- the three tracks
  have hT₁ : IsTrackFrom H (slice P p (P.length - 1) ++ [v']) t v' :=
    isTrackFrom_concat (isTrackFrom_of_delete hR₁) hadji hv'nR₁
  have hT₂ : IsTrackFrom H (slice Q mq (Q.length - 1) ++ [w']) t w' :=
    isTrackFrom_concat (isTrackFrom_of_delete hR₂) hadjj hw'nR₂
  have hT₃ : IsTrackFrom H ((slice Q 0 mq).reverse ++ [u']) t u' :=
    isTrackFrom_concat (isTrackFrom_of_delete hR₃) hadjk hu'nR₃
  have hlen₁ : 2 ≤ (slice P p (P.length - 1) ++ [v']).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hL₁]; omega
  have hlen₂ : 2 ≤ (slice Q mq (Q.length - 1) ++ [w']).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, hL₂]; omega
  have hlen₃ : 2 ≤ ((slice Q 0 mq).reverse ++ [u']).length := by
    simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse, hL₃]
    omega
  -- the marked edge at the far end of each track
  have hE₁ : s(v, v') ∈ trackEdges (slice P p (P.length - 1) ++ [v']) := by
    have hlast := getElem_last_of_getLast? hR₁.2.2 (show 0 < (slice P p (P.length - 1)).length by omega)
    have h := last_edge_mem_concat (show 0 < (slice P p (P.length - 1)).length by omega) v'
    rwa [hlast] at h
  have hE₂ : s(w, w') ∈ trackEdges (slice Q mq (Q.length - 1) ++ [w']) := by
    have hlast := getElem_last_of_getLast? hR₂.2.2 (show 0 < (slice Q mq (Q.length - 1)).length by omega)
    have h := last_edge_mem_concat (show 0 < (slice Q mq (Q.length - 1)).length by omega) w'
    rwa [hlast] at h
  have hE₃ : s(u, u') ∈ trackEdges ((slice Q 0 mq).reverse ++ [u']) := by
    have hlast := getElem_last_of_getLast? hR₃.2.2
      (show 0 < ((slice Q 0 mq).reverse).length by simp only [List.length_reverse, hL₃]; omega)
    have h := last_edge_mem_concat
      (show 0 < ((slice Q 0 mq).reverse).length by simp only [List.length_reverse, hL₃]; omega) u'
    rwa [hlast] at h
  have hXi : s(v, v') ∈ X := by rw [← hxi]; exact hxX i
  have hXj : s(w, w') ∈ X := by rw [← hxj]; exact hxX j
  have hXk : s(u, u') ∈ X := by rw [← hxk]; exact hxX k
  -- pairwise disjointness away from `t`
  have hd12 : ∀ z : W, z ∈ slice P p (P.length - 1) ++ [v'] →
      z ∈ slice Q mq (Q.length - 1) ++ [w'] → z = t := by
    intro z hz1 hz2
    rcases mem_concat_iff.mp hz1 with h1 | h1 <;> rcases mem_concat_iff.mp hz2 with h2 | h2
    · exact hR₁Q z h1 (hR₂Q z h2)
    · exact absurd (h2 ▸ hR₁P z h1) hw'P
    · exact absurd (h1 ▸ hR₂Q z h2) hv'Q
    · exact absurd (h1.symm.trans h2) (hne v' w' i j hij hv'x hw'x)
  have hd13 : ∀ z : W, z ∈ slice P p (P.length - 1) ++ [v'] →
      z ∈ (slice Q 0 mq).reverse ++ [u'] → z = t := by
    intro z hz1 hz3
    rcases mem_concat_iff.mp hz1 with h1 | h1 <;> rcases mem_concat_iff.mp hz3 with h3 | h3
    · exact hR₁Q z h1 (hR₃Q z h3)
    · exact absurd (h3 ▸ hR₁P z h1) hu'P
    · exact absurd (h1 ▸ hR₃Q z h3) hv'Q
    · exact absurd (h1.symm.trans h3) (hne v' u' i k hik hv'x hu'x)
  have hd23 : ∀ z : W, z ∈ slice Q mq (Q.length - 1) ++ [w'] →
      z ∈ (slice Q 0 mq).reverse ++ [u'] → z = t := by
    intro z hz2 hz3
    rcases mem_concat_iff.mp hz2 with h2 | h2 <;> rcases mem_concat_iff.mp hz3 with h3 | h3
    · exact hR₂₃ z h2 h3
    · exact absurd (h3 ▸ hR₂Q z h2) hu'Q
    · exact absurd (h2 ▸ hR₃Q z h3) hw'Q
    · exact absurd (h2.symm.trans h3) (hne w' u' j k hjk hw'x hu'x)
  -- `t ≠ w`, so the second track starts with an edge of `A`
  have htP : t ∈ P := by rw [htdef]; exact List.getElem_mem hplt
  have hmqne : mq ≠ Q.length - 1 := by
    intro h
    apply hwP
    have htw : t = w := by
      rw [← hQmq, ← hQl]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q h hmqlt (by omega)
    exact htw ▸ htP
  have h2first : s((slice Q mq (Q.length - 1) ++ [w'])[0]'(by omega),
      (slice Q mq (Q.length - 1) ++ [w'])[1]'(by omega)) ∉ X := by
    have hlen : 2 ≤ (slice Q mq (Q.length - 1)).length := by rw [hL₂]; omega
    rw [first_edge_concat hlen]
    have e0 : (slice Q mq (Q.length - 1))[0]'(by omega) = Q[mq]'hmqlt := by
      rw [getElem_slice Q (by omega) (show mq + 0 < Q.length by omega)]
      exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q (by omega) _ _
    have e1 : (slice Q mq (Q.length - 1))[1]'(by omega) = Q[mq + 1]'(by omega) := by
      rw [getElem_slice Q (by omega) (show mq + 1 < Q.length by omega)]
    rw [e0, e1]
    exact edge_not_mem_of_delete hQ.1 (show mq + 1 < Q.length by omega)
  have hdisjunct :
      (s((slice P p (P.length - 1) ++ [v'])[0]'(by omega),
          (slice P p (P.length - 1) ++ [v'])[1]'(by omega)) ∉ X ∧
        s((slice Q mq (Q.length - 1) ++ [w'])[0]'(by omega),
          (slice Q mq (Q.length - 1) ++ [w'])[1]'(by omega)) ∉ X) ∨
      (s((slice P p (P.length - 1) ++ [v'])[0]'(by omega),
          (slice P p (P.length - 1) ++ [v'])[1]'(by omega)) ∉ X ∧
        s(((slice Q 0 mq).reverse ++ [u'])[0]'(by omega),
          ((slice Q 0 mq).reverse ++ [u'])[1]'(by omega)) ∉ X) ∨
      (s((slice Q mq (Q.length - 1) ++ [w'])[0]'(by omega),
          (slice Q mq (Q.length - 1) ++ [w'])[1]'(by omega)) ∉ X ∧
        s(((slice Q 0 mq).reverse ++ [u'])[0]'(by omega),
          ((slice Q 0 mq).reverse ++ [u'])[1]'(by omega)) ∉ X) := by
    by_cases hpv : p = P.length - 1
    · -- `t = v`: the first track is just the marked edge, but the third starts inside `A`
      have htv : t = v := by
        rw [htdef, ← hPl]
        exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P hpv hplt (by omega)
      have hmq0 : mq ≠ 0 := by
        intro h
        have hnu : t = u := by
          rw [← hQmq, ← hQ0]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q h hmqlt hQne
        exact (hne v u i k hik hv hu) (htv ▸ hnu)
      have hlen : 2 ≤ ((slice Q 0 mq).reverse).length := by
        simp only [List.length_reverse, hL₃]; omega
      have h3first : s(((slice Q 0 mq).reverse ++ [u'])[0]'(by omega),
          ((slice Q 0 mq).reverse ++ [u'])[1]'(by omega)) ∉ X := by
        rw [first_edge_concat hlen]
        have e0 : ((slice Q 0 mq).reverse)[0]'(by omega) = Q[mq]'hmqlt := by
          rw [List.getElem_reverse]
          rw [getElem_slice Q (show (slice Q 0 mq).length - 1 - 0 < (slice Q 0 mq).length by
              rw [hL₃]; omega)
            (show 0 + ((slice Q 0 mq).length - 1 - 0) < Q.length by rw [hL₃]; omega)]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q
            (by rw [hL₃]; omega) _ _
        have e1 : ((slice Q 0 mq).reverse)[1]'(by omega) = Q[mq - 1]'(by omega) := by
          rw [List.getElem_reverse]
          rw [getElem_slice Q (show (slice Q 0 mq).length - 1 - 1 < (slice Q 0 mq).length by
              rw [hL₃]; omega)
            (show 0 + ((slice Q 0 mq).length - 1 - 1) < Q.length by rw [hL₃]; omega)]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q
            (by rw [hL₃]; omega) _ _
        rw [e0, e1, Sym2.eq_swap]
        have hnot := edge_not_mem_of_delete hQ.1 (n := mq - 1) (show mq - 1 + 1 < Q.length by omega)
        have hidx : Q[mq - 1 + 1]'(show mq - 1 + 1 < Q.length by omega) = Q[mq]'hmqlt :=
          Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq Q (by omega) _ _
        rwa [hidx] at hnot
      exact Or.inr (Or.inr ⟨h2first, h3first⟩)
    · have hlen : 2 ≤ (slice P p (P.length - 1)).length := by rw [hL₁]; omega
      have h1first : s((slice P p (P.length - 1) ++ [v'])[0]'(by omega),
          (slice P p (P.length - 1) ++ [v'])[1]'(by omega)) ∉ X := by
        rw [first_edge_concat hlen]
        have e0 : (slice P p (P.length - 1))[0]'(by omega) = P[p]'hplt := by
          rw [getElem_slice P (by omega) (show p + 0 < P.length by omega)]
          exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq P (by omega) _ _
        have e1 : (slice P p (P.length - 1))[1]'(by omega) = P[p + 1]'(by omega) := by
          rw [getElem_slice P (by omega) (show p + 1 < P.length by omega)]
        rw [e0, e1]
        exact edge_not_mem_of_delete hP.1 (show p + 1 < P.length by omega)
      exact Or.inl ⟨h1first, h2first⟩
  exact hclaim3 ⟨t, v', w', u',
    slice P p (P.length - 1) ++ [v'],
    slice Q mq (Q.length - 1) ++ [w'],
    (slice Q 0 mq).reverse ++ [u'],
    hlen₁, hlen₂, hlen₃, hT₁, hT₂, hT₃, hd12, hd13, hd23,
    ⟨_, hE₁, hXi⟩, ⟨_, hE₂, hXj⟩, ⟨_, hE₃, hXk⟩, hdisjunct⟩


end Workspace.ProofLemmas.Thm57Claim4NoDoubleForeign
