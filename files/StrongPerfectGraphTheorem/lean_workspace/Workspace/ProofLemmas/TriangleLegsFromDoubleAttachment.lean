import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Workspace.Types.TriangleLegsFromDoubleAttachment

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm244Shapes
open Workspace.ProofLemmas

private theorem getElem_congr_idx {V : Type*} {l : List V} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h
  rfl

private theorem mem_take_iff {V : Type*} {l : List V} {k : ℕ} {x : V} :
    x ∈ l.take k ↔ ∃ (m : ℕ) (h : m < l.length), m < k ∧ l[m]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_take] at hi
    exact ⟨i, by omega, by omega, by simp⟩
  · rintro ⟨m, hm, hmk, rfl⟩
    exact ⟨m, by rw [List.length_take]; omega, by simp⟩

private theorem mem_drop_iff {V : Type*} {l : List V} {k : ℕ} {x : V} :
    x ∈ l.drop k ↔ ∃ (m : ℕ) (h : m < l.length), k ≤ m ∧ l[m]'h = x := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rw [List.length_drop] at hi
    exact ⟨k + i, by omega, by omega, by simp⟩
  · rintro ⟨m, hm, hkm, rfl⟩
    refine ⟨m - k, by rw [List.length_drop]; omega, ?_⟩
    simp only [List.getElem_drop]
    exact getElem_congr_idx _ _ (by omega)

private theorem isPathFrom_take {V : Type*} {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) {k : ℕ} (hk : k < p.length) :
    IsPathFrom G (p.take (k + 1)) (p[0]'(by omega)) (p[k]'hk) := by
  refine ⟨PathBasics.isPathList_take hp (Nat.succ_pos k), ?_, ?_⟩
  · rw [List.head?_take]
    simp only [Nat.succ_ne_zero, if_false]
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  · rw [List.getLast?_take]
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    rw [List.getElem?_eq_getElem hk]
    rfl

private theorem isPathFrom_drop {V : Type*} {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) {k : ℕ} (hk : k < p.length) :
    IsPathFrom G (p.drop k) (p[k]'hk) (p[p.length - 1]'(by omega)) := by
  refine ⟨PathBasics.isPathList_drop hp hk, ?_, ?_⟩
  · rw [List.head?_drop, List.getElem?_eq_getElem hk]
  · rw [List.getLast?_drop]
    simp only [Nat.not_le.mpr hk, if_false]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]

private theorem connectedSet_take {V : Type*} {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) {k : ℕ} (hk : 0 < k) :
    ConnectedSet G {z : V | z ∈ p.take k} :=
  InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (PathBasics.isPathList_take hp hk)

private theorem connectedSet_drop {V : Type*} {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) {k : ℕ} (hk : k < p.length) :
    ConnectedSet G {z : V | z ∈ p.drop k} :=
  InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (PathBasics.isPathList_drop hp hk)

private theorem connectedSet_drop' {V : Type*} {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) (k : ℕ) : ConnectedSet G {z : V | z ∈ p.drop k} := by
  rcases Nat.lt_or_ge k p.length with h | h
  · exact connectedSet_drop hp h
  · have hnil : p.drop k = [] := List.drop_eq_nil_of_le h
    rw [hnil]
    intro a b
    exact absurd a.2 (by simp)

private theorem connectedSet_union' {V : Type*} {G : SimpleGraph V} {X Y : Set V}
    (hX : ConnectedSet G X) (hY : ConnectedSet G Y)
    (hlink : Y = ∅ ∨ ∃ a ∈ X, ∃ b ∈ Y, G.Adj a b) : ConnectedSet G (X ∪ Y) := by
  rcases hlink with rfl | h
  · simpa using hX
  · exact ConnectedSetUnionAttach.connectedSet_union hX hY (Or.inr h)

private theorem fin3_cases {motive : Fin 3 → Prop} (h0 : motive 0) (h1 : motive 1)
    (h2 : motive 2) (i : Fin 3) : motive i := by
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

private theorem fin3_pairs {motive : Fin 3 → Fin 3 → Prop}
    (hsymm : ∀ i j : Fin 3, motive i j → motive j i)
    (h01 : motive 0 1) (h02 : motive 0 2) (h12 : motive 1 2) :
    ∀ i j : Fin 3, i ≠ j → motive i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hij
      | exact h01
      | exact h02
      | exact h12
      | exact hsymm _ _ h01
      | exact hsymm _ _ h02
      | exact hsymm _ _ h12

private theorem uniq_of_connected_diff {V : Type*} {G : SimpleGraph V} {F : Set V}
    {N : Fin 3 → Set V} {v : Fin 3 → V}
    (hvF : ∀ i, v i ∈ F) (hvN : ∀ i, v i ∈ N i)
    (hpair : ∀ i j : Fin 3, i ≠ j → v i ≠ v j)
    (hminEq : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → S = F)
    (i : Fin 3) (hconn : ConnectedSet G (F \ {v i})) :
    ∀ w ∈ F, w ∈ N i → w = v i := by
  intro w hwF hwN
  by_contra hne
  have hmeet : ∀ j : Fin 3, ∃ x ∈ F \ {v i}, x ∈ N j := by
    intro j
    by_cases hji : j = i
    · subst j
      exact ⟨w, ⟨hwF, hne⟩, hwN⟩
    · exact ⟨v j, ⟨hvF j, hpair j i hji⟩, hvN j⟩
  have heq := hminEq (F \ {v i}) Set.diff_subset hconn hmeet
  have hmem : v i ∈ F \ {v i} := by
    rw [heq]
    exact hvF i
  exact hmem.2 rfl

private theorem isPathFrom_congr {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y x' y' : V} (h : IsPathFrom G l x y) (hx : x = x') (hy : y = y') :
    IsPathFrom G l x' y' :=
  ⟨h.1, hx ▸ h.2.1, hy ▸ h.2.2⟩

private def triple {α : Type*} (a b c : α) (i : Fin 3) : α :=
  if i = 0 then a else if i = 1 then b else c

private theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
private theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
private theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

theorem triangleLegsFromDoubleAttachment
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V) (v : Fin 3 → V)
    (hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i)
    (hpair : ∀ i j : Fin 3, i ≠ j → v i ≠ v j)
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → F.ncard ≤ S.ncard)
    (hfixed : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, v i ∈ S) → S = F)
    (Q R : List V) (z : V) (s : ℕ)
    (hQ : IsPathFrom G Q (v 0) (v 1))
    (hQF : ∀ w ∈ Q, w ∈ F)
    (hR : IsPathFrom G R (v 2) z)
    (hRF : ∀ w ∈ R, w ∈ F)
    (hv2Q : v 2 ∉ Q)
    (hzQ : z ∈ Q)
    (hRlen : 2 ≤ R.length)
    (hinter : {w : V | w ∈ R} ∩ {w : V | w ∈ Q} = {z})
    (hcover : F = {w : V | w ∈ Q} ∪ {w : V | w ∈ R})
    (hclean : ∀ (t d : ℕ) (ht : t + 2 < R.length) (hd : d < Q.length),
      ¬ G.Adj (R[t]'(by omega)) (Q[d]'hd))
    (hs : s + 1 < Q.length)
    (hz : z = Q[s]'(by omega) ∨ z = Q[s + 1]'hs)
    (hattach : ∀ (d : ℕ) (hd : d < Q.length),
      G.Adj (R[R.length - 2]'(by omega)) (Q[d]'hd) ↔ d = s ∨ d = s + 1) :
    ∃ (u : Fin 3 → V) (P : Fin 3 → List V), TriangleLegs G F N v u P := by
  classical
  have hQl : IsPathList G Q := hQ.1
  have hQnd : Q.Nodup := PathBasics.path_nodup hQl
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQl
  have hQ0 : Q[0]'hQpos = v 0 := PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = v 1 :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQconn : ConnectedSet G {w : V | w ∈ Q} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQl

  have hRl : IsPathList G R := hR.1
  have hRnd : R.Nodup := PathBasics.path_nodup hRl
  have hRpos : 0 < R.length := PathBasics.path_length_pos hRl
  have hR0 : R[0]'hRpos = v 2 := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRlast : R[R.length - 1]'(by omega) = z :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hRpos

  let T : List V := R.take (R.length - 1)
  let y : V := R[R.length - 2]'(by omega)
  have hTlen : T.length = R.length - 1 := by simp [T]
  have hTpos : 0 < T.length := by omega
  have hTl : IsPathList G T := by
    dsimp [T]
    exact PathBasics.isPathList_take hRl (by omega)
  have hTnd : T.Nodup := PathBasics.path_nodup hTl
  have hT0 : T[0]'hTpos = v 2 := by
    simp only [T, List.getElem_take]
    exact hR0
  have hTfrom : IsPathFrom G T (v 2) y := by
    have h := isPathFrom_take hRl (k := R.length - 2) (by omega)
    have heq : R.length - 2 + 1 = R.length - 1 := by omega
    rw [heq] at h
    exact isPathFrom_congr h hR0 rfl
  have hTlast : T[T.length - 1]'(by omega) = y :=
    PathBasics.getElem_last_of_getLast? hTfrom.2.2 hTpos
  have hTconn : ConnectedSet G {w : V | w ∈ T} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hTl
  have hTmem : ∀ w ∈ T, w ∈ F ∧ w ∉ Q := by
    intro w hwT
    have hwR : w ∈ R := List.mem_of_mem_take hwT
    refine ⟨hRF w hwR, ?_⟩
    intro hwQ
    have hwz : w = z := by
      have hw : w ∈ ({x : V | x ∈ R} ∩ {x : V | x ∈ Q}) := ⟨hwR, hwQ⟩
      rw [hinter] at hw
      simpa using hw
    obtain ⟨m, hm, hmlt, rfl⟩ := mem_take_iff.mp hwT
    have heq : R[m]'hm = R[R.length - 1]'(by omega) := by
      rw [hRlast]
      exact hwz
    have := (List.Nodup.getElem_inj_iff hRnd).mp heq
    omega

  have hFeq : {w : V | w ∈ Q} ∪ {w : V | w ∈ T} = F := by
    rw [hcover]
    ext w
    simp only [Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hwQ | hwT)
      · exact Or.inl hwQ
      · exact Or.inr (List.mem_of_mem_take hwT)
    · rintro (hwQ | hwR)
      · exact Or.inl hwQ
      · obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hwR
        by_cases hmlast : m = R.length - 1
        · left
          rw [getElem_congr_idx hm (by omega) hmlast, hRlast]
          exact hzQ
        · right
          exact mem_take_iff.mpr ⟨m, hm, by omega, rfl⟩

  have hminEq : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → S = F := by
    intro S hSF hSconn hSmeet
    exact (Set.subset_iff_eq_of_ncard_le (hmin S hSF hSconn hSmeet)).mp hSF

  have hcrossQT : ∀ (m : ℕ) (hm : m < Q.length), ∀ w ∈ T,
      (G.Adj (Q[m]'hm) w ↔ ((m = s ∨ m = s + 1) ∧ w = y)) := by
    intro m hm w hwT
    obtain ⟨t, ht, htlt, rfl⟩ := mem_take_iff.mp hwT
    constructor
    · intro hadj
      by_cases hty : t = R.length - 2
      · subst t
        exact ⟨(hattach m hm).mp hadj.symm, rfl⟩
      · exact False.elim ((hclean t m (by omega) hm) hadj.symm)
    · rintro ⟨hmidx, hwy⟩
      rw [hwy]
      exact ((hattach m hm).mpr hmidx).symm

  have hyT : y ∈ T := PathBasics.getLast_mem hTfrom.2.2
  have hys : G.Adj y (Q[s]'(by omega)) := (hattach s (by omega)).mpr (Or.inl rfl)
  have hysucc : G.Adj y (Q[s + 1]'hs) := (hattach (s + 1) hs).mpr (Or.inr rfl)

  have hdiff0 : ConnectedSet G (F \ {v 0}) := by
    have hset : F \ {v 0} = {w : V | w ∈ Q.drop 1} ∪ {w : V | w ∈ T} := by
      rw [← hFeq]
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwQ | hwT, hwne⟩
        · refine Or.inl ?_
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hwQ
          refine mem_drop_iff.mpr ⟨m, hm, ?_, rfl⟩
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · exact absurd hQ0 hwne
          · omega
        · exact Or.inr hwT
      · rintro (hwQ | hwT)
        · refine ⟨Or.inl (List.mem_of_mem_drop hwQ), ?_⟩
          obtain ⟨m, hm, h1m, hme⟩ := mem_drop_iff.mp hwQ
          rw [← hme, ← hQ0]
          intro he
          have := (List.Nodup.getElem_inj_iff hQnd).mp he
          omega
        · exact ⟨Or.inr hwT, fun he => (hTmem w hwT).2 (by rw [he]; exact PathBasics.head_mem hQ.2.1)⟩
    rw [hset]
    exact ConnectedSetUnionAttach.connectedSet_union (connectedSet_drop hQl (by omega)) hTconn
      (Or.inr ⟨Q[s + 1]'hs, mem_drop_iff.mpr ⟨s + 1, hs, by omega, rfl⟩,
        y, hyT, hysucc.symm⟩)

  have hdiff1 : ConnectedSet G (F \ {v 1}) := by
    have hset : F \ {v 1} = {w : V | w ∈ Q.take (Q.length - 1)} ∪ {w : V | w ∈ T} := by
      rw [← hFeq]
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwQ | hwT, hwne⟩
        · refine Or.inl ?_
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hwQ
          refine mem_take_iff.mpr ⟨m, hm, ?_, rfl⟩
          rcases Nat.lt_or_ge m (Q.length - 1) with h | h
          · exact h
          · exact absurd ((getElem_congr_idx hm (by omega) (by omega)).trans hQlast) hwne
        · exact Or.inr hwT
      · rintro (hwQ | hwT)
        · refine ⟨Or.inl (List.mem_of_mem_take hwQ), ?_⟩
          obtain ⟨m, hm, hmlt, hme⟩ := mem_take_iff.mp hwQ
          rw [← hme, ← hQlast]
          intro he
          have := (List.Nodup.getElem_inj_iff hQnd).mp he
          omega
        · exact ⟨Or.inr hwT, fun he => (hTmem w hwT).2 (by rw [he]; exact PathBasics.getLast_mem hQ.2.2)⟩
    rw [hset]
    exact ConnectedSetUnionAttach.connectedSet_union (connectedSet_take hQl (by omega)) hTconn
      (Or.inr ⟨Q[s]'(by omega), mem_take_iff.mpr ⟨s, by omega, by omega, rfl⟩,
        y, hyT, hys.symm⟩)

  have hdiff2 : ConnectedSet G (F \ {v 2}) := by
    have hset : F \ {v 2} = {w : V | w ∈ Q} ∪ {w : V | w ∈ T.drop 1} := by
      rw [← hFeq]
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hwQ | hwT, hwne⟩
        · exact Or.inl hwQ
        · refine Or.inr ?_
          obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hwT
          refine mem_drop_iff.mpr ⟨m, hm, ?_, rfl⟩
          rcases Nat.eq_zero_or_pos m with rfl | hpos
          · exact absurd hT0 hwne
          · omega
      · rintro (hwQ | hwT)
        · exact ⟨Or.inl hwQ, fun he => hv2Q (by rw [← he]; exact hwQ)⟩
        · refine ⟨Or.inr (List.mem_of_mem_drop hwT), ?_⟩
          obtain ⟨m, hm, h1m, hme⟩ := mem_drop_iff.mp hwT
          rw [← hme, ← hT0]
          intro he
          have := (List.Nodup.getElem_inj_iff hTnd).mp he
          omega
    rw [hset]
    refine connectedSet_union' hQconn (connectedSet_drop' hTl 1) ?_
    rcases Nat.lt_or_ge 1 T.length with h | h
    · refine Or.inr ⟨Q[s]'(by omega), List.getElem_mem (by omega), y, ?_, hys.symm⟩
      exact mem_drop_iff.mpr ⟨T.length - 1, by omega, by omega, hTlast⟩
    · refine Or.inl ?_
      have hnil : T.drop 1 = [] := List.drop_eq_nil_of_le h
      ext w
      simp [hnil]

  refine ⟨triple (Q[s]'(by omega)) (Q[s + 1]'hs) y,
    triple (Q.take (s + 1)) ((Q.drop (s + 1)).reverse) T, (fun i => (hv i).2), ?_, ?_, ?_, ?_, ?_⟩
  · refine fin3_cases ?_ ?_ ?_
    · exact uniq_of_connected_diff (fun i => (hv i).1) (fun i => (hv i).2) hpair hminEq 0 hdiff0
    · exact uniq_of_connected_diff (fun i => (hv i).1) (fun i => (hv i).2) hpair hminEq 1 hdiff1
    · exact uniq_of_connected_diff (fun i => (hv i).1) (fun i => (hv i).2) hpair hminEq 2 hdiff2
  · refine fin3_cases ?_ ?_ ?_
    · rw [triple_zero, triple_zero]
      exact isPathFrom_congr (isPathFrom_take hQl (by omega)) hQ0 rfl
    · rw [triple_one, triple_one]
      exact isPathFrom_congr (PathBasics.isPathFrom_reverse (isPathFrom_drop hQl hs)) hQlast rfl
    · rw [triple_two, triple_two]
      exact hTfrom
  · refine fin3_cases ?_ ?_ ?_
    · rw [triple_zero]
      exact fun w hw => hQF w (List.mem_of_mem_take hw)
    · rw [triple_one]
      exact fun w hw => hQF w (List.mem_of_mem_drop (List.mem_reverse.mp hw))
    · rw [triple_two]
      exact fun w hw => (hTmem w hw).1
  · refine fin3_pairs (fun i j h a ha b hb => h b hb a ha |>.symm) ?_ ?_ ?_
    · rw [triple_zero, triple_one]
      intro a ha b hb
      obtain ⟨m, hm, hmle, rfl⟩ := mem_take_iff.mp ha
      obtain ⟨m', hm', hm'ge, rfl⟩ := mem_drop_iff.mp (List.mem_reverse.mp hb)
      intro he
      have := (List.Nodup.getElem_inj_iff hQnd).mp he
      omega
    · rw [triple_zero, triple_two]
      exact fun a ha b hb he => (hTmem b hb).2 (by rw [← he]; exact List.mem_of_mem_take ha)
    · rw [triple_one, triple_two]
      exact fun a ha b hb he => (hTmem b hb).2
        (by rw [← he]; exact List.mem_of_mem_drop (List.mem_reverse.mp ha))
  · refine fin3_pairs
      (fun i j h a ha b hb => ((SimpleGraph.adj_comm G a b).trans (h b hb a ha)).trans and_comm)
      ?_ ?_ ?_
    · rw [triple_zero, triple_one, triple_zero, triple_one]
      intro a ha b hb
      obtain ⟨m, hm, hmle, rfl⟩ := mem_take_iff.mp ha
      obtain ⟨m', hm', hm'ge, rfl⟩ := mem_drop_iff.mp (List.mem_reverse.mp hb)
      rw [PathBasics.path_adj_iff hQl hm hm']
      constructor
      · intro hmm
        exact ⟨getElem_congr_idx _ _ (by omega), getElem_congr_idx _ _ (by omega)⟩
      · rintro ⟨h1, h2⟩
        have e1 := (List.Nodup.getElem_inj_iff hQnd).mp h1
        have e2 := (List.Nodup.getElem_inj_iff hQnd).mp h2
        omega
    · rw [triple_zero, triple_two, triple_zero, triple_two]
      intro a ha b hb
      obtain ⟨m, hm, hmle, rfl⟩ := mem_take_iff.mp ha
      rw [hcrossQT m hm b hb]
      constructor
      · rintro ⟨hmidx, rfl⟩
        exact ⟨getElem_congr_idx _ _ (by omega), rfl⟩
      · rintro ⟨h1, rfl⟩
        have e1 := (List.Nodup.getElem_inj_iff hQnd).mp h1
        exact ⟨Or.inl e1, rfl⟩
    · rw [triple_one, triple_two, triple_one, triple_two]
      intro a ha b hb
      obtain ⟨m, hm, hmge, rfl⟩ := mem_drop_iff.mp (List.mem_reverse.mp ha)
      rw [hcrossQT m hm b hb]
      constructor
      · rintro ⟨hmidx, rfl⟩
        exact ⟨getElem_congr_idx _ _ (by omega), rfl⟩
      · rintro ⟨h1, rfl⟩
        have e1 := (List.Nodup.getElem_inj_iff hQnd).mp h1
        exact ⟨Or.inr e1, rfl⟩

end Workspace.Types.TriangleLegsFromDoubleAttachment
