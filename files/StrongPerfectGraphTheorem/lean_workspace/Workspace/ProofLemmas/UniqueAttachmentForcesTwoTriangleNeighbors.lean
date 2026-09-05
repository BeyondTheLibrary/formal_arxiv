import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_4
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.Types.UniqueAttachmentForcesTwoTriangleNeighbors

open Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT

private theorem isPathList_cons {V : Type*} {G : SimpleGraph V} {r : List V} {v x : V}
    (hr : IsPathList G r) (hhead : r.head? = some x) (hv : v ∉ r)
    (hadj : ∀ y ∈ r, (G.Adj v y ↔ y = x)) :
    IsPathList G (v :: r) := by
  have hrlen : 0 < r.length := Workspace.ProofLemmas.PathBasics.path_length_pos hr
  have hr0 : r[0]'hrlen = x :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hrlen
  refine ⟨by simp, List.nodup_cons.mpr ⟨hv, hr.2.1⟩, ?_⟩
  intro i j hi hj
  rcases i with _ | s <;> rcases j with _ | t
  · simp
  · have ht : t < r.length := by simpa using hj
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [hadj (r[t]'ht) (List.getElem_mem ht), ← hr0, hr.2.1.getElem_inj_iff]
    omega
  · have hs : s < r.length := by simpa using hi
    simp only [List.getElem_cons_zero, List.getElem_cons_succ]
    rw [SimpleGraph.adj_comm, hadj (r[s]'hs) (List.getElem_mem hs), ← hr0,
      hr.2.1.getElem_inj_iff]
    omega
  · have hs : s < r.length := by simpa using hi
    have ht : t < r.length := by simpa using hj
    simp only [List.getElem_cons_succ]
    rw [Workspace.ProofLemmas.PathBasics.path_adj_iff hr hs ht]
    omega

private theorem mem_take_index {V : Type*} {l : List V} {k : ℕ} {x : V}
    (hx : x ∈ l.take k) :
    ∃ (i : ℕ) (hi : i < l.length), i < k ∧ l[i]'hi = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_take] at hi
  have hil : i < l.length := by omega
  refine ⟨i, hil, ?_, ?_⟩
  · omega
  · simpa only [List.getElem_take] using hix

private theorem mem_drop_index {V : Type*} {l : List V} {k : ℕ} {x : V}
    (hx : x ∈ l.drop k) :
    ∃ (i : ℕ) (hi : i < l.length), k ≤ i ∧ l[i]'hi = x := by
  obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
  simp only [List.length_drop] at hj
  have hi : k + j < l.length := by
    omega
  refine ⟨k + j, hi, by omega, ?_⟩
  simpa only [List.getElem_drop] using hjx

private theorem getElem_congr_idx {V : Type*} {l : List V} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst j
  rfl

theorem uniqueAttachmentForcesTwoTriangleNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (A F : Set V) (a₁ a₂ a₃ b₁ b₂ b₃ : V)
    (hA : IsTriangle G A)
    (hAeq : A = {a₁, a₂, a₃})
    (haDistinct : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hbDistinct : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃)
    (hbF : b₁ ∈ F ∧ b₂ ∈ F ∧ b₃ ∈ F)
    (hdisj : Disjoint F A)
    (hadj : ∀ f ∈ F,
      (G.Adj a₁ f ↔ f = b₁) ∧
      (G.Adj a₂ f ↔ f = b₂) ∧
      (G.Adj a₃ f ↔ f = b₃))
    (P R : List V) (w y : V)
    (hP : IsPathFrom G P b₁ b₂)
    (hPF : ∀ p ∈ P, p ∈ F)
    (hR : IsPathFrom G R b₃ w)
    (hRF : ∀ r ∈ R, r ∈ F)
    (hb₃P : b₃ ∉ P)
    (hwP : w ∈ P)
    (hRlen : 2 ≤ R.length)
    (hinter : {v : V | v ∈ R} ∩ {v : V | v ∈ P} = {w})
    (hclean : ∀ (t d : ℕ) (ht : t + 2 < R.length) (hd : d < P.length),
      ¬ G.Adj (R[t]'(by omega)) (P[d]'hd))
    (hyP : y ∈ P)
    (hattach : ∀ p ∈ P,
      G.Adj (R[R.length - 2]'(by omega)) p ↔ p = y) :
    2 ≤ (G.neighborSet y ∩ A).ncard := by
  classical
  open Workspace.ProofLemmas in
    obtain ⟨s, hs, hsy⟩ := List.getElem_of_mem hyP
  have hPl : IsPathList G P := hP.1
  have hRl : IsPathList G R := hR.1
  have hPnd : P.Nodup := Workspace.ProofLemmas.PathBasics.path_nodup hPl
  have hRnd : R.Nodup := Workspace.ProofLemmas.PathBasics.path_nodup hRl
  have hPpos : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hPl
  have hRpos : 0 < R.length := Workspace.ProofLemmas.PathBasics.path_length_pos hRl
  have hP0 : P[0]'hPpos = b₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hPpos
  have hPlast : P[P.length - 1]'(by omega) = b₂ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
  have hR0 : R[0]'hRpos = b₃ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRlast : R[R.length - 1]'(by omega) = w :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.2.2 hRpos

  have ha₁A : a₁ ∈ A := by rw [hAeq]; simp
  have ha₂A : a₂ ∈ A := by rw [hAeq]; simp
  have ha₃A : a₃ ∈ A := by rw [hAeq]; simp
  have ha₁F : a₁ ∉ F := fun h => Set.disjoint_left.mp hdisj h ha₁A
  have ha₂F : a₂ ∉ F := fun h => Set.disjoint_left.mp hdisj h ha₂A
  have ha₃F : a₃ ∉ F := fun h => Set.disjoint_left.mp hdisj h ha₃A

  let L : List V := P.take s
  let Q : List V := (P.drop (s + 1)).reverse
  let T : List V := R.take (R.length - 1)

  have hLidx : ∀ {x : V}, x ∈ L →
      ∃ (i : ℕ) (hi : i < P.length), i < s ∧ P[i]'hi = x := by
    intro x hx
    exact mem_take_index (l := P) (k := s) (by simpa [L] using hx)
  have hQidx : ∀ {x : V}, x ∈ Q →
      ∃ (i : ℕ) (hi : i < P.length), s + 1 ≤ i ∧ P[i]'hi = x := by
    intro x hx
    have hx' : x ∈ P.drop (s + 1) := by simpa [Q] using hx
    exact mem_drop_index hx'
  have hTidx : ∀ {x : V}, x ∈ T →
      ∃ (i : ℕ) (hi : i < R.length), i < R.length - 1 ∧ R[i]'hi = x := by
    intro x hx
    exact mem_take_index (l := R) (k := R.length - 1) (by simpa [T] using hx)
  have hLF : ∀ x ∈ L, x ∈ F := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hLidx hx
    exact hPF _ (List.getElem_mem hi)
  have hQF : ∀ x ∈ Q, x ∈ F := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hQidx hx
    exact hPF _ (List.getElem_mem hi)
  have hTF : ∀ x ∈ T, x ∈ F := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hTidx hx
    exact hRF _ (List.getElem_mem hi)
  have hLP : ∀ x ∈ L, x ∈ P := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hLidx hx
    exact List.getElem_mem hi
  have hQP : ∀ x ∈ Q, x ∈ P := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hQidx hx
    exact List.getElem_mem hi
  have hTR : ∀ x ∈ T, x ∈ R := by
    intro x hx
    obtain ⟨i, hi, -, rfl⟩ := hTidx hx
    exact List.getElem_mem hi

  have hTnotP : ∀ x ∈ T, x ∉ P := by
    intro x hxT hxP
    have hxinter : x ∈ ({v : V | v ∈ R} ∩ {v : V | v ∈ P}) :=
      ⟨hTR x hxT, hxP⟩
    rw [hinter] at hxinter
    have hxw : x = w := by simpa using hxinter
    obtain ⟨i, hi, hiT, hix⟩ := hTidx hxT
    have heq : R[i]'hi = R[R.length - 1]'(by omega) := by
      rw [hix, hxw, hRlast]
    have := (List.Nodup.getElem_inj_iff hRnd).mp heq
    omega
  have hLQdisj : ∀ x ∈ L, x ∉ Q := by
    intro x hxL hxQ
    obtain ⟨i, hi, his, hix⟩ := hLidx hxL
    obtain ⟨j, hj, hsj, hjx⟩ := hQidx hxQ
    have heq : P[i]'hi = P[j]'hj := hix.trans hjx.symm
    have := (List.Nodup.getElem_inj_iff hPnd).mp heq
    omega
  have hyL : y ∉ L := by
    intro hy
    obtain ⟨i, hi, his, hiy⟩ := hLidx hy
    have heq : P[i]'hi = P[s]'hs := hiy.trans hsy.symm
    have := (List.Nodup.getElem_inj_iff hPnd).mp heq
    omega
  have hyQ : y ∉ Q := by
    intro hy
    obtain ⟨i, hi, hsi, hiy⟩ := hQidx hy
    have heq : P[i]'hi = P[s]'hs := hiy.trans hsy.symm
    have := (List.Nodup.getElem_inj_iff hPnd).mp heq
    omega
  have hb₁Q : b₁ ∉ Q := by
    intro hb
    obtain ⟨i, hi, hsi, hib⟩ := hQidx hb
    have heq : P[i]'hi = P[0]'hPpos := hib.trans hP0.symm
    have := (List.Nodup.getElem_inj_iff hPnd).mp heq
    omega
  have hb₂L : b₂ ∉ L := by
    intro hb
    obtain ⟨i, hi, his, hib⟩ := hLidx hb
    have heq : P[i]'hi = P[P.length - 1]'(by omega) := hib.trans hPlast.symm
    have := (List.Nodup.getElem_inj_iff hPnd).mp heq
    omega
  have hb₃L : b₃ ∉ L := fun hb => hb₃P (hLP b₃ hb)
  have hb₃Q : b₃ ∉ Q := fun hb => hb₃P (hQP b₃ hb)
  have hb₁T : b₁ ∉ T := fun hb => hTnotP b₁ hb (Workspace.ProofLemmas.PathBasics.head_mem hP.2.1)
  have hb₂T : b₂ ∉ T := fun hb => hTnotP b₂ hb (Workspace.ProofLemmas.PathBasics.getLast_mem hP.2.2)

  have hLpath : IsPathList G (a₁ :: L) := by
    by_cases hs0 : s = 0
    · subst s
      simpa [L] using Workspace.ProofLemmas.PathBasics.isPathList_singleton G a₁
    · have hLp : IsPathList G L := by
        simpa [L] using Workspace.ProofLemmas.PathBasics.isPathList_take hPl (by omega)
      have hLhead : L.head? = some b₁ := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem
          (show 0 < L.length by simp [L]; omega)]
        simp only [L, List.getElem_take]
        exact congrArg some hP0
      apply isPathList_cons hLp hLhead
      · intro ha
        exact ha₁F (hLF a₁ ha)
      · intro x hx
        exact (hadj x (hLF x hx)).1
  have hQpath : IsPathList G (a₂ :: Q) := by
    by_cases hslast : s + 1 = P.length
    · have hQnil : Q = [] := by simp [Q, hslast]
      rw [hQnil]
      exact Workspace.ProofLemmas.PathBasics.isPathList_singleton G a₂
    · have hsnext : s + 1 < P.length := by omega
      have hQp : IsPathList G Q := by
        simpa [Q] using Workspace.ProofLemmas.PathBasics.isPathList_reverse
          (Workspace.ProofLemmas.PathBasics.isPathList_drop hPl hsnext)
      have hQhead : Q.head? = some b₂ := by
        simp only [Q, List.head?_reverse, List.getLast?_drop]
        simp only [Nat.not_le.mpr hsnext, if_false]
        exact hP.2.2
      apply isPathList_cons hQp hQhead
      · intro ha
        exact ha₂F (hQF a₂ ha)
      · intro x hx
        exact (hadj x (hQF x hx)).2.1
  have hTpath : IsPathList G (a₃ :: T) := by
    have hTp : IsPathList G T := by
      simpa [T] using Workspace.ProofLemmas.PathBasics.isPathList_take hRl (by omega)
    have hTpos : 0 < T.length := by simp [T]; omega
    have hThead : T.head? = some b₃ := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hTpos]
      simp only [T, List.getElem_take]
      exact congrArg some hR0
    apply isPathList_cons hTp hThead
    · intro ha
      exact ha₃F (hTF a₃ ha)
    · intro x hx
      exact (hadj x (hTF x hx)).2.2

  have hdisj12 : ∀ x ∈ a₁ :: L, x ∉ a₂ :: Q := by
    intro x hx
    rcases List.mem_cons.mp hx with hxHead | hxL
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hzQ
      · exact haDistinct.1 (hxHead.symm.trans hzHead)
      · exact ha₁F (hxHead ▸ hQF x hzQ)
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hxQ
      · exact ha₂F (hzHead ▸ hLF x hxL)
      · exact hLQdisj x hxL hxQ
  have hdisj13 : ∀ x ∈ a₁ :: L, x ∉ a₃ :: T := by
    intro x hx
    rcases List.mem_cons.mp hx with hxHead | hxL
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hzT
      · exact haDistinct.2.1 (hxHead.symm.trans hzHead)
      · exact ha₁F (hxHead ▸ hTF x hzT)
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hxT
      · exact ha₃F (hzHead ▸ hLF x hxL)
      · exact hTnotP x hxT (hLP x hxL)
  have hdisj23 : ∀ x ∈ a₂ :: Q, x ∉ a₃ :: T := by
    intro x hx
    rcases List.mem_cons.mp hx with hxHead | hxQ
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hzT
      · exact haDistinct.2.2 (hxHead.symm.trans hzHead)
      · exact ha₂F (hxHead ▸ hTF x hzT)
    · intro hx
      rcases List.mem_cons.mp hx with hzHead | hxT
      · exact ha₃F (hzHead ▸ hQF x hxQ)
      · exact hTnotP x hxT (hQP x hxQ)

  have hLQno : ∀ x ∈ L, ∀ z ∈ Q, ¬ G.Adj x z := by
    intro x hx z hz had
    obtain ⟨i, hi, his, hix⟩ := hLidx hx
    obtain ⟨j, hj, hsj, hjz⟩ := hQidx hz
    have hpAdj : G.Adj (P[i]'hi) (P[j]'hj) := by simpa [hix, hjz] using had
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hPl hi hj).mp hpAdj with h | h <;> omega
  have hPTno : ∀ p ∈ P, p ≠ y → ∀ z ∈ T, ¬ G.Adj p z := by
    intro p hp hpy z hz had
    obtain ⟨d, hd, hdp⟩ := List.getElem_of_mem hp
    obtain ⟨t, ht, htT, htz⟩ := hTidx hz
    by_cases hearly : t + 2 < R.length
    · exact hclean t d hearly hd (by simpa [hdp, htz] using had.symm)
    · have htpen : t = R.length - 2 := by omega
      subst t
      have hpen : G.Adj (R[R.length - 2]'(by omega)) p := by
        rw [htz]
        exact had.symm
      exact hpy ((hattach p hp).mp hpen)

  have hcross12 : ∀ x ∈ a₁ :: L, ∀ z ∈ a₂ :: Q,
      (G.Adj x z ↔ (x = a₁ ∧ z = a₂)) := by
    intro x hx z hz
    rcases List.mem_cons.mp hx with hxHead | hxL
    · rcases List.mem_cons.mp hz with hzHead | hzQ
      · subst x
        subst z
        constructor
        · intro _
          exact ⟨rfl, rfl⟩
        · intro _
          exact hA.2 a₁ ha₁A a₂ ha₂A haDistinct.1
      · constructor
        · intro had
          have hzb : z = b₁ := (hadj z (hQF z hzQ)).1.mp (hxHead ▸ had)
          exact False.elim (hb₁Q (hzb ▸ hzQ))
        · rintro ⟨-, hzEq⟩
          exact absurd (hzEq ▸ hQF z hzQ) ha₂F
    · rcases List.mem_cons.mp hz with hzHead | hzQ
      · constructor
        · intro had
          have hxb : x = b₂ := (hadj x (hLF x hxL)).2.1.mp (hzHead ▸ had.symm)
          exact False.elim (hb₂L (hxb ▸ hxL))
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hLF x hxL) ha₁F
      · constructor
        · intro had
          exact False.elim ((hLQno x hxL z hzQ) had)
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hLF x hxL) ha₁F
  have hcross13 : ∀ x ∈ a₁ :: L, ∀ z ∈ a₃ :: T,
      (G.Adj x z ↔ (x = a₁ ∧ z = a₃)) := by
    intro x hx z hz
    rcases List.mem_cons.mp hx with hxHead | hxL
    · rcases List.mem_cons.mp hz with hzHead | hzT
      · subst x
        subst z
        constructor
        · intro _
          exact ⟨rfl, rfl⟩
        · intro _
          exact hA.2 a₁ ha₁A a₃ ha₃A haDistinct.2.1
      · constructor
        · intro had
          have hzb : z = b₁ := (hadj z (hTF z hzT)).1.mp (hxHead ▸ had)
          exact False.elim (hb₁T (hzb ▸ hzT))
        · rintro ⟨-, hzEq⟩
          exact absurd (hzEq ▸ hTF z hzT) ha₃F
    · rcases List.mem_cons.mp hz with hzHead | hzT
      · constructor
        · intro had
          have hxb : x = b₃ := (hadj x (hLF x hxL)).2.2.mp (hzHead ▸ had.symm)
          exact False.elim (hb₃L (hxb ▸ hxL))
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hLF x hxL) ha₁F
      · constructor
        · intro had
          exact False.elim ((hPTno x (hLP x hxL) (fun h => hyL (h ▸ hxL)) z hzT) had)
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hLF x hxL) ha₁F
  have hcross23 : ∀ x ∈ a₂ :: Q, ∀ z ∈ a₃ :: T,
      (G.Adj x z ↔ (x = a₂ ∧ z = a₃)) := by
    intro x hx z hz
    rcases List.mem_cons.mp hx with hxHead | hxQ
    · rcases List.mem_cons.mp hz with hzHead | hzT
      · subst x
        subst z
        constructor
        · intro _
          exact ⟨rfl, rfl⟩
        · intro _
          exact hA.2 a₂ ha₂A a₃ ha₃A haDistinct.2.2
      · constructor
        · intro had
          have hzb : z = b₂ := (hadj z (hTF z hzT)).2.1.mp (hxHead ▸ had)
          exact False.elim (hb₂T (hzb ▸ hzT))
        · rintro ⟨-, hzEq⟩
          exact absurd (hzEq ▸ hTF z hzT) ha₃F
    · rcases List.mem_cons.mp hz with hzHead | hzT
      · constructor
        · intro had
          have hxb : x = b₃ := (hadj x (hQF x hxQ)).2.2.mp (hzHead ▸ had.symm)
          exact False.elim (hb₃Q (hxb ▸ hxQ))
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hQF x hxQ) ha₂F
      · constructor
        · intro had
          exact False.elim ((hPTno x (hQP x hxQ) (fun h => hyQ (h ▸ hxQ)) z hzT) had)
        · rintro ⟨hxEq, -⟩
          exact absurd (hxEq ▸ hQF x hxQ) ha₂F

  have hn₁ : ∃ x ∈ a₁ :: L, G.Adj y x := by
    by_cases hs0 : s = 0
    · have hyb : y = b₁ := by
        calc
          y = P[s]'hs := hsy.symm
          _ = P[0]'hPpos := getElem_congr_idx hs hPpos hs0
          _ = b₁ := hP0
      refine ⟨a₁, by simp, ?_⟩
      rw [hyb]
      exact ((hadj b₁ hbF.1).1.mpr rfl).symm
    · let x : V := P[s - 1]'(by omega)
      have hxL : x ∈ L := by
        apply List.mem_iff_getElem.mpr
        refine ⟨s - 1, ?_, ?_⟩
        · simp [L]
          omega
        · simp [x, L]
      refine ⟨x, by simp [hxL], ?_⟩
      have had := Workspace.ProofLemmas.PathBasics.path_adj_succ hPl
        (i := s - 1) (by omega : s - 1 + 1 < P.length)
      have helem : P[s - 1 + 1]'(by omega) = P[s]'hs :=
        getElem_congr_idx _ _ (by omega)
      exact hsy ▸ helem ▸ (by simpa [x] using had.symm)
  have hn₂ : ∃ x ∈ a₂ :: Q, G.Adj y x := by
    by_cases hslast : s + 1 = P.length
    · have hsidx : s = P.length - 1 := by omega
      have hyb : y = b₂ := by
        calc
          y = P[s]'hs := hsy.symm
          _ = P[P.length - 1]'(by omega) := getElem_congr_idx hs (by omega) hsidx
          _ = b₂ := hPlast
      refine ⟨a₂, by simp, ?_⟩
      rw [hyb]
      exact ((hadj b₂ hbF.2.1).2.1.mpr rfl).symm
    · have hsnext : s + 1 < P.length := by omega
      let x : V := P[s + 1]'hsnext
      have hxdrop : x ∈ P.drop (s + 1) := by
        apply List.mem_iff_getElem.mpr
        refine ⟨0, by simp; omega, ?_⟩
        simp [x]
      have hxQ : x ∈ Q := by simpa [Q] using hxdrop
      refine ⟨x, by simp [hxQ], ?_⟩
      have had := Workspace.ProofLemmas.PathBasics.path_adj_succ hPl (i := s) hsnext
      rw [← hsy]
      simpa [x] using had
  have hn₃ : ∃ x ∈ a₃ :: T, G.Adj y x := by
    let x : V := R[R.length - 2]'(by omega)
    have hxT : x ∈ T := by
      apply List.mem_iff_getElem.mpr
      refine ⟨R.length - 2, ?_, ?_⟩
      · simp [T]
        omega
      · simp [x, T]
    refine ⟨x, by simp [hxT], ?_⟩
    exact ((hattach y hyP).mpr rfl).symm

  have hlink : VertexCanBeLinkedOntoTriangle G y a₁ a₂ a₃ := by
    refine ⟨a₁ :: L, a₂ :: Q, a₃ :: T,
      ⟨hLpath, hQpath, hTpath⟩,
      ⟨hdisj12, hdisj13, hdisj23⟩, ?_,
      ⟨hcross12, hcross13, hcross23⟩,
      ⟨hn₁, hn₂, hn₃⟩⟩
    simp
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG y a₁ a₂ a₃ hlink with
    h12 | h13 | h23
  · have hsub : ({a₁, a₂} : Set V) ⊆ G.neighborSet y ∩ A := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h12.1, ha₁A⟩
      · have : x = a₂ := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h12.2, ha₂A⟩
    have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
    simpa [Set.ncard_pair haDistinct.1] using hc
  · have hsub : ({a₁, a₃} : Set V) ⊆ G.neighborSet y ∩ A := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h13.1, ha₁A⟩
      · have : x = a₃ := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h13.2, ha₃A⟩
    have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
    simpa [Set.ncard_pair haDistinct.2.1] using hc
  · have hsub : ({a₂, a₃} : Set V) ⊆ G.neighborSet y ∩ A := by
      intro x hx
      rcases Set.mem_insert_iff.mp hx with rfl | hx
      · exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h23.1, ha₂A⟩
      · have : x = a₃ := Set.mem_singleton_iff.mp hx
        subst x
        exact ⟨by simpa only [SimpleGraph.mem_neighborSet] using h23.2, ha₃A⟩
    have hc := Set.ncard_le_ncard hsub (Set.toFinite _)
    simpa [Set.ncard_pair haDistinct.2.2] using hc

end Workspace.Types.UniqueAttachmentForcesTwoTriangleNeighbors

