import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Workspace.Types.AttachmentIndicesAreLocal

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h
  rfl

private theorem mem_take_iff {W : Type*} (l : List W) (m : ℕ) (z : W) :
    z ∈ l.take m ↔ ∃ (c : ℕ) (hc : c < l.length), c < m ∧ l[c]'hc = z := by
  constructor
  · intro h
    obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem h
    rw [List.length_take] at hc
    exact ⟨c, by omega, by omega, by rw [← hcz]; simp⟩
  · rintro ⟨c, hc, hcm, hcz⟩
    refine List.mem_iff_getElem.mpr ⟨c, by rw [List.length_take]; omega, ?_⟩
    rw [← hcz]
    simp

private theorem mem_drop_iff {W : Type*} (l : List W) (m : ℕ) (z : W) :
    z ∈ l.drop m ↔ ∃ (c : ℕ) (hc : c < l.length), m ≤ c ∧ l[c]'hc = z := by
  constructor
  · intro h
    obtain ⟨c, hc, hcz⟩ := List.getElem_of_mem h
    rw [List.length_drop] at hc
    refine ⟨m + c, by omega, by omega, ?_⟩
    rw [← hcz]
    simp
  · rintro ⟨c, hc, hcm, hcz⟩
    refine List.mem_iff_getElem.mpr ⟨c - m, by rw [List.length_drop]; omega, ?_⟩
    rw [← hcz, List.getElem_drop]
    exact gidx l (by omega) (by omega) hc

theorem attachmentIndicesAreLocal
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V) (v : Fin 3 → V)
    (hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i)
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → F.ncard ≤ S.ncard)
    (Q R : List V) (z : V)
    (hQ : IsPathFrom G Q (v 0) (v 1))
    (hR : IsPathFrom G R (v 2) z)
    (hv2Q : v 2 ∉ Q) (hzQ : z ∈ Q) (hRlen : 2 ≤ R.length)
    (hinter : {x : V | x ∈ R} ∩ {x : V | x ∈ Q} = {z})
    (hcover : F = {x : V | x ∈ Q} ∪ {x : V | x ∈ R}) :
    ∃ s : ℕ, s < Q.length ∧
      Xor'
        (∀ (d : ℕ) (hd : d < Q.length),
          G.Adj (R[R.length - 2]'(by omega)) (Q[d]'hd) ↔ d = s)
        (s + 1 < Q.length ∧
          ∀ (d : ℕ) (hd : d < Q.length),
            G.Adj (R[R.length - 2]'(by omega)) (Q[d]'hd) ↔
              d = s ∨ d = s + 1) := by
  classical
  let y : V := R[R.length - 2]'(by omega)
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hQnd : Q.Nodup := PathBasics.path_nodup hQ.1
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  have hQ0 : Q[0]'hQpos = v 0 :=
    PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = v 1 :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hR0 : R[0]'(by omega) = v 2 :=
    PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hRlast : R[R.length - 1]'(by omega) = z :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  have hclose : ∀ (p q : ℕ) (hp : p < Q.length) (hq : q < Q.length),
      p < q → G.Adj y (Q[p]'hp) → G.Adj y (Q[q]'hq) → q ≤ p + 1 := by
    intro p q hp hq hpq hyp hyq
    by_contra hfar
    have hp2q : p + 2 ≤ q := by omega
    let x : V := Q[p + 1]'(by omega)
    let A : Set V := {w : V | w ∈ Q.take (p + 1)}
    let C : Set V := {w : V | w ∈ R.take (R.length - 1)}
    let B : Set V := {w : V | w ∈ Q.drop (p + 2)}
    let S : Set V := (A ∪ C) ∪ B
    have hAconn : ConnectedSet G A := by
      dsimp [A]
      exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_take hQ.1 (by omega))
    have hCconn : ConnectedSet G C := by
      dsimp [C]
      exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_take hR.1 (by omega))
    have hBconn : ConnectedSet G B := by
      dsimp [B]
      exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_drop hQ.1 (by omega))
    have hQpA : Q[p]'hp ∈ A := by
      exact (mem_take_iff Q (p + 1) _).mpr ⟨p, hp, by omega, rfl⟩
    have hyC : y ∈ C := by
      exact (mem_take_iff R (R.length - 1) _).mpr
        ⟨R.length - 2, by omega, by omega, rfl⟩
    have hQqB : Q[q]'hq ∈ B := by
      exact (mem_drop_iff Q (p + 2) _).mpr ⟨q, hq, hp2q, rfl⟩
    have hACconn : ConnectedSet G (A ∪ C) :=
      ConnectedSetUnionAttach.connectedSet_union hAconn hCconn
        (Or.inr ⟨Q[p]'hp, hQpA, y, hyC, hyp.symm⟩)
    have hSconn : ConnectedSet G S := by
      dsimp [S]
      exact ConnectedSetUnionAttach.connectedSet_union hACconn hBconn
        (Or.inr ⟨y, Or.inr hyC, Q[q]'hq, hQqB, hyq⟩)
    have hSF : S ⊆ F := by
      intro w hw
      rw [hcover]
      rcases hw with (hwA | hwC) | hwB
      · exact Or.inl (List.mem_of_mem_take hwA)
      · exact Or.inr (List.mem_of_mem_take hwC)
      · exact Or.inl (List.mem_of_mem_drop hwB)
    have hxF : x ∈ F := by
      rw [hcover]
      exact Or.inl (List.getElem_mem (l := Q) (by omega))
    have hxA : x ∉ A := by
      intro hxA
      obtain ⟨c, hc, hcp, hcx⟩ := (mem_take_iff Q (p + 1) x).mp hxA
      have : c = p + 1 := hQnd.getElem_inj_iff.mp hcx
      omega
    have hxB : x ∉ B := by
      intro hxB
      obtain ⟨c, hc, hpc, hcx⟩ := (mem_drop_iff Q (p + 2) x).mp hxB
      have : c = p + 1 := hQnd.getElem_inj_iff.mp hcx
      omega
    have hxC : x ∉ C := by
      intro hxC
      obtain ⟨c, hc, hcR, hcx⟩ := (mem_take_iff R (R.length - 1) x).mp hxC
      have hxR : x ∈ R := by simpa [hcx] using List.getElem_mem hc
      have hxQ : x ∈ Q := List.getElem_mem (l := Q) (by omega)
      have hxint : x ∈ {w : V | w ∈ R} ∩ {w : V | w ∈ Q} := ⟨hxR, hxQ⟩
      rw [hinter] at hxint
      have hxz : x = z := by simpa using hxint
      have heq : R[c]'hc = R[R.length - 1]'(by omega) := by
        rw [hcx, hxz, hRlast]
      have : c = R.length - 1 := hRnd.getElem_inj_iff.mp heq
      omega
    have hxS : x ∉ S := by
      rintro ((hxA' | hxC') | hxB')
      · exact hxA hxA'
      · exact hxC hxC'
      · exact hxB hxB'
    have hv0S : v 0 ∈ S := by
      apply Or.inl
      apply Or.inl
      rw [← hQ0]
      exact (mem_take_iff Q (p + 1) _).mpr ⟨0, hQpos, by omega, rfl⟩
    have hv1S : v 1 ∈ S := by
      apply Or.inr
      rw [← hQlast]
      exact (mem_drop_iff Q (p + 2) _).mpr
        ⟨Q.length - 1, by omega, by omega, rfl⟩
    have hv2S : v 2 ∈ S := by
      apply Or.inl
      apply Or.inr
      rw [← hR0]
      exact (mem_take_iff R (R.length - 1) _).mpr
        ⟨0, by omega, by omega, rfl⟩
    have hmeet : ∀ i : Fin 3, ∃ w ∈ S, w ∈ N i := by
      intro i
      fin_cases i
      · exact ⟨v 0, hv0S, (hv 0).2⟩
      · exact ⟨v 1, hv1S, (hv 1).2⟩
      · exact ⟨v 2, hv2S, (hv 2).2⟩
    have hcard : F.ncard ≤ S.ncard := hmin S hSF hSconn hmeet
    have heq : S = F := Set.eq_of_subset_of_ncard_le hSF hcard
    exact hxS (heq ▸ hxF)
  have hyz : G.Adj y z := by
    have h := (hR.1.2.2 (R.length - 2) (R.length - 1) (by omega) (by omega)).2
      (Or.inl (by omega))
    simpa [y, hRlast] using h
  obtain ⟨t, ht, htz⟩ := List.getElem_of_mem hzQ
  have hyQt : G.Adj y (Q[t]'ht) := by simpa [htz] using hyz
  have hex : ∃ d : ℕ, ∃ hd : d < Q.length, G.Adj y (Q[d]'hd) :=
    ⟨t, ht, hyQt⟩
  let s : ℕ := Nat.find hex
  obtain ⟨hs, hys⟩ := Nat.find_spec hex
  have hsmin : ∀ (d : ℕ) (hd : d < Q.length), G.Adj y (Q[d]'hd) → s ≤ d := by
    intro d hd hyd
    exact Nat.find_min' hex ⟨hd, hyd⟩
  have hclass : ∀ (d : ℕ) (hd : d < Q.length),
      G.Adj y (Q[d]'hd) → d = s ∨ d = s + 1 := by
    intro d hd hyd
    have hsd : s ≤ d := hsmin d hd hyd
    by_cases hds : d = s
    · exact Or.inl hds
    · have hslt : s < d := by omega
      have hle := hclose s d hs hd hslt hys hyd
      exact Or.inr (by omega)
  by_cases hnext : ∃ hsucc : s + 1 < Q.length, G.Adj y (Q[s + 1]'hsucc)
  · obtain ⟨hsucc, hynext⟩ := hnext
    refine ⟨s, hs, Or.inr ⟨?_, ?_⟩⟩
    · refine ⟨hsucc, ?_⟩
      intro d hd
      constructor
      · exact hclass d hd
      · rintro (rfl | rfl)
        · exact hys
        · exact hynext
    · intro hsingle
      have := (hsingle (s + 1) hsucc).mp hynext
      omega
  · refine ⟨s, hs, Or.inl ⟨?_, ?_⟩⟩
    · intro d hd
      constructor
      · intro hyd
        rcases hclass d hd hyd with hds | hds
        · exact hds
        · subst d
          exact False.elim (hnext ⟨hd, hyd⟩)
      · rintro rfl
        exact hys
    · rintro ⟨hsucc, hdouble⟩
      have hySucc : G.Adj y (Q[s + 1]'hsucc) :=
        (hdouble (s + 1) hsucc).mpr (Or.inr rfl)
      exact hnext ⟨hsucc, hySucc⟩

end Workspace.Types.AttachmentIndicesAreLocal

