import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false

namespace Workspace.Types.NearestPathAttachment

open Workspace.Types.Core.SPGT

private def IsChainToList {V : Type*} (G : SimpleGraph V) (F : Set V) (Q p : List V)
    (x : V) : Prop :=
  p.head? = some x ∧
  (∃ z : V, p.getLast? = some z ∧ z ∈ Q) ∧
  (∀ z ∈ p, z ∈ F) ∧
  List.IsChain G.Adj p

private theorem chain_length_pos {V : Type*} {G : SimpleGraph V} {F : Set V}
    {Q p : List V} {x : V} (h : IsChainToList G F Q p x) : 0 < p.length := by
  rcases p with _ | ⟨a, l⟩
  · simp [IsChainToList] at h
  · simp

private theorem chain_getElem_last {V : Type*} {G : SimpleGraph V} {F : Set V}
    {Q p : List V} {x z : V} (h : IsChainToList G F Q p x)
    (hz : p.getLast? = some z) :
    p[p.length - 1]'(by have := chain_length_pos h; omega) = z := by
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by have := chain_length_pos h; omega)] at hz
  exact Option.some_inj.mp hz

private theorem chain_take {V : Type*} {G : SimpleGraph V} {F : Set V}
    {Q p : List V} {x : V} (h : IsChainToList G F Q p x)
    {i : ℕ} (hi : i < p.length) (hiQ : p[i]'hi ∈ Q) :
    IsChainToList G F Q (p.take (i + 1)) x ∧ (p.take (i + 1)).length = i + 1 := by
  refine ⟨⟨?_, ?_, ?_, h.2.2.2.take _⟩, by rw [List.length_take]; omega⟩
  · rw [List.head?_take, if_neg (by omega)]
    exact h.1
  · refine ⟨p[i]'hi, ?_, hiQ⟩
    rw [List.getLast?_take, if_neg (by omega)]
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, Option.some_or]
  · exact fun z hz => h.2.2.1 z (List.take_subset _ _ hz)

private theorem chain_splice {V : Type*} {G : SimpleGraph V} {F : Set V}
    {Q p : List V} {x : V} (h : IsChainToList G F Q p x)
    {i k : ℕ} (hik : i + 1 < k) (hk : k < p.length)
    (hadj : G.Adj (p[i]'(by omega)) (p[k]'hk)) :
    IsChainToList G F Q (p.take (i + 1) ++ p.drop k) x ∧
      (p.take (i + 1) ++ p.drop k).length < p.length := by
  have hip : i < p.length := by omega
  have hqlen : (p.take (i + 1) ++ p.drop k).length = (i + 1) + (p.length - k) := by
    rw [List.length_append, List.length_take, List.length_drop]
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
  · rw [List.head?_append, List.head?_take, if_neg (by omega), h.1]
    rfl
  · obtain ⟨z, hzlast, hzQ⟩ := h.2.1
    refine ⟨z, ?_, hzQ⟩
    rw [List.getLast?_append, List.getLast?_drop, if_neg (by omega), hzlast]
    rfl
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h.2.2.1 z (List.take_subset _ _ hz)
    · exact h.2.2.1 z (List.drop_subset _ _ hz)
  · refine List.IsChain.append (h.2.2.2.take _) (h.2.2.2.drop _) ?_
    intro a ha b hb
    rw [List.getLast?_take, if_neg (by omega)] at ha
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hip, Option.some_or,
      Option.mem_some_iff] at ha
    rw [List.head?_drop, List.getElem?_eq_getElem hk, Option.mem_some_iff] at hb
    rw [← ha, ← hb]
    exact hadj

private theorem chain_attach {V : Type*} {G : SimpleGraph V} {F : Set V}
    {Q p : List V} {x q : V} (h : IsChainToList G F Q p x)
    {i : ℕ} (hi : i < p.length) (hqQ : q ∈ Q) (hqF : q ∈ F)
    (hadj : G.Adj (p[i]'hi) q) :
    IsChainToList G F Q (p.take (i + 1) ++ [q]) x ∧
      (p.take (i + 1) ++ [q]).length = i + 2 := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by simp [List.length_take]; omega⟩
  · rw [List.head?_append, List.head?_take, if_neg (by omega), h.1]
    rfl
  · exact ⟨q, by simp, hqQ⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h.2.2.1 z (List.take_subset _ _ hz)
    · simp only [List.mem_singleton] at hz
      simpa [hz] using hqF
  · refine List.IsChain.append (h.2.2.2.take _) (by simp) ?_
    intro a ha b hb
    simp only [List.head?_cons, Option.mem_some_iff] at hb
    subst b
    rw [List.getLast?_take, if_neg (by omega)] at ha
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, Option.some_or,
      Option.mem_some_iff] at ha
    rw [← ha]
    exact hadj

theorem nearestPathAttachment
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (Q : List V) (x : V)
    (hF : ConnectedSet G F)
    (hQ : IsPathList G Q)
    (hQF : ∀ w ∈ Q, w ∈ F)
    (hxF : x ∈ F) (hxQ : x ∉ Q) :
    ∃ (R : List V) (z : V),
      IsPathFrom G R x z ∧
      (∀ w ∈ R, w ∈ F) ∧
      z ∈ Q ∧
      2 ≤ R.length ∧
      {w : V | w ∈ R} ∩ {w : V | w ∈ Q} = {z} ∧
      ∀ (t d : ℕ) (ht : t + 2 < R.length) (hd : d < Q.length),
        ¬ G.Adj (R[t]'(by omega)) (Q[d]'hd) := by
  classical
  have hQne : Q ≠ [] := hQ.1
  let q : V := Q.head hQne
  have hqQ : q ∈ Q := by
    exact List.head_mem hQne
  obtain ⟨p, hpPath, hpF⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
      hF hxF (hQF q hqQ)
  have hex : ∃ n : ℕ, ∃ p : List V, IsChainToList G F Q p x ∧ p.length = n := by
    refine ⟨p.length, p, ?_, rfl⟩
    exact ⟨hpPath.2.1, ⟨q, hpPath.2.2, hqQ⟩, hpF,
      Workspace.ProofLemmas.InducedPathExtraction.isChain_of_isPathList hpPath.1⟩
  obtain ⟨R, hR, hRlen⟩ := Nat.find_spec hex
  have hmin : ∀ p : List V, IsChainToList G F Q p x → R.length ≤ p.length := by
    intro p hp
    rw [hRlen]
    exact Nat.find_min' hex ⟨p, hp, rfl⟩
  obtain ⟨z, hzlast, hzQ⟩ := hR.2.1
  have hpos : 0 < R.length := chain_length_pos hR
  have hlast : R[R.length - 1]'(by omega) = z := chain_getElem_last hR hzlast
  have hfirst : R[0]'(by omega) = x := by
    have hxhead := hR.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hxhead
    exact Option.some_inj.mp hxhead
  have hchord : ∀ (i j : ℕ) (hi : i < R.length) (hj : j < R.length), i + 1 < j →
      ¬ G.Adj (R[i]'hi) (R[j]'hj) := by
    intro i j hi hj hij hadj
    obtain ⟨hsp, hlt⟩ := chain_splice hR hij hj hadj
    exact absurd (hmin _ hsp) (by omega)
  have hnodup : R.Nodup := by
    refine List.pairwise_iff_getElem.mpr ?_
    intro i j hi hj hij heq
    by_cases hjl : j + 1 = R.length
    · have hiQ : R[i]'hi ∈ Q := by
        have hjlast : j = R.length - 1 := by omega
        subst hjlast
        rw [heq, hlast]
        exact hzQ
      obtain ⟨hct, hctlen⟩ := chain_take hR hi hiQ
      have := hmin _ hct
      omega
    · have hj1 : j + 1 < R.length := by omega
      have hadj : G.Adj (R[i]'hi) (R[j + 1]'hj1) := by
        rw [heq]
        exact hR.2.2.2.getElem j hj1
      obtain ⟨hsp, hlt⟩ := chain_splice hR (by omega : i + 1 < j + 1) hj1 hadj
      exact absurd (hmin _ hsp) (by omega)
  have hpath : IsPathFrom G R x z := by
    refine ⟨⟨?_, hnodup, ?_⟩, hR.1, hzlast⟩
    · intro hnil
      rw [hnil] at hpos
      simp at hpos
    · intro i j hi hj
      constructor
      · intro hadj
        by_contra hcon
        push Not at hcon
        obtain ⟨h1, h2⟩ := hcon
        rcases lt_trichotomy i j with hlt | heq | hgt
        · exact hchord i j hi hj (by omega) hadj
        · subst heq
          exact G.irrefl hadj
        · exact hchord j i hj hi (by omega) hadj.symm
      · rintro (rfl | rfl)
        · exact hR.2.2.2.getElem i hj
        · exact (hR.2.2.2.getElem j hi).symm
  have hlen : 2 ≤ R.length := by
    by_contra hlt
    have hone : R.length = 1 := by omega
    have hidx : R.length - 1 = 0 := by omega
    have hz0 : R[0]'(by omega) = z := by
      simpa [hidx] using hlast
    apply hxQ
    rw [← hfirst, hz0]
    exact hzQ
  have hinter : {w : V | w ∈ R} ∩ {w : V | w ∈ Q} = {z} := by
    ext w
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hwR, hwQ⟩
      obtain ⟨i, hi, hiw⟩ := List.getElem_of_mem hwR
      obtain ⟨hct, hctlen⟩ := chain_take hR hi (hiw ▸ hwQ)
      have hle := hmin _ hct
      have hilast : i = R.length - 1 := by omega
      rw [← hiw]
      subst i
      exact hlast
    · rintro rfl
      exact ⟨by rw [← hlast]; exact List.getElem_mem _, hzQ⟩
  have hclean : ∀ (t d : ℕ) (ht : t + 2 < R.length) (hd : d < Q.length),
      ¬ G.Adj (R[t]'(by omega)) (Q[d]'hd) := by
    intro t d ht hd hadj
    obtain ⟨hatt, hattlen⟩ := chain_attach hR (by omega) (List.getElem_mem hd)
      (hQF _ (List.getElem_mem hd)) hadj
    have := hmin _ hatt
    omega
  exact ⟨R, z, hpath, hR.2.2.1, hzQ, hlen, hinter, hclean⟩

end Workspace.Types.NearestPathAttachment
