import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Workspace.Types.DoubleAttachmentForcesTriangleReflection

open Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.Types.Prisms.SPGT
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

private theorem isPathFrom_congr {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y x' y' : V} (h : IsPathFrom G l x y) (hx : x = x') (hy : y = y') :
    IsPathFrom G l x' y' :=
  ⟨h.1, hx ▸ h.2.1, hy ▸ h.2.2⟩

private def triple {α : Type*} (a b c : α) (i : Fin 3) : α :=
  if i = 0 then a else if i = 1 then b else c

private theorem triple_zero {α : Type*} (a b c : α) : triple a b c 0 = a := rfl
private theorem triple_one {α : Type*} (a b c : α) : triple a b c 1 = b := rfl
private theorem triple_two {α : Type*} (a b c : α) : triple a b c 2 = c := rfl

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

private theorem isPathFrom_cons {V : Type*} {G : SimpleGraph V} {p : List V}
    {a b c : V} (hp : IsPathFrom G p b c) (ha : a ∉ p)
    (hadj : ∀ x ∈ p, G.Adj a x ↔ x = b) : IsPathFrom G (a :: p) a c := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hzero : p[0]'hpos = b := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  refine ⟨?_, rfl, ?_⟩
  · refine ⟨by simp, List.nodup_cons.mpr ⟨ha, PathBasics.path_nodup hp.1⟩, ?_⟩
    intro i j hi hj
    cases i with
    | zero =>
        cases j with
        | zero => simp
        | succ j =>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ]
            rw [hadj _ (List.getElem_mem _), ← hzero,
              List.Nodup.getElem_inj_iff (PathBasics.path_nodup hp.1)]
            omega
    | succ i =>
        cases j with
        | zero =>
            simp only [List.getElem_cons_zero, List.getElem_cons_succ]
            rw [SimpleGraph.adj_comm, hadj _ (List.getElem_mem _), ← hzero,
              List.Nodup.getElem_inj_iff (PathBasics.path_nodup hp.1)]
            omega
        | succ j =>
            simp only [List.getElem_cons_succ]
            rw [PathBasics.path_adj_iff hp.1]
            omega
  · rw [List.getLast?_cons_of_ne_nil (PathBasics.path_ne_nil hp.1)]
    exact hp.2.2

private theorem cross_cons {V : Type*} {G : SimpleGraph V} {L M : List V}
    {a c b d : V}
    (hac : G.Adj a c)
    (haM : ∀ v ∈ M, ¬ G.Adj a v)
    (hLc : ∀ u ∈ L, ¬ G.Adj u c)
    (hLM : ∀ u ∈ L, ∀ v ∈ M, G.Adj u v ↔ u = b ∧ v = d)
    (hab : a ≠ b) (hcd : c ≠ d) (haL : a ∉ L) (hcM : c ∉ M) :
    ∀ u ∈ a :: L, ∀ v ∈ c :: M,
      G.Adj u v ↔ (u = a ∧ v = c) ∨ (u = b ∧ v = d) := by
  intro u huAll v hvAll
  rcases List.mem_cons.mp huAll with rfl | huL
  · rcases List.mem_cons.mp hvAll with rfl | hvM
    · exact ⟨fun _ => Or.inl ⟨rfl, rfl⟩, fun _ => hac⟩
    · constructor
      · exact fun h => False.elim (haM v hvM h)
      · rintro (⟨_, rfl⟩ | ⟨h, -⟩)
        · exact False.elim (hcM hvM)
        · exact False.elim (hab h)
  · rcases List.mem_cons.mp hvAll with rfl | hvM
    · constructor
      · exact fun h => False.elim (hLc u huL h)
      · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
        · exact False.elim (haL huL)
        · exact False.elim (hcd h)
    · rw [hLM u huL v hvM]
      constructor
      · exact fun h => Or.inr h
      · rintro (⟨rfl, -⟩ | h)
        · exact False.elim (haL huL)
        · exact h

private theorem ends_eq_of_length_one {V : Type*} {G : SimpleGraph V} {p : List V}
    {a b : V} (hp : IsPathFrom G p a b) (hlen : p.length = 1) : a = b := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  rw [← h0, ← hl]
  exact getElem_congr_idx _ _ (by omega)

theorem doubleAttachmentForcesTriangleReflection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF7 G)
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
    (P R : List V) (w : V)
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
    (s : ℕ) (y z : V)
    (hs : s + 1 < P.length)
    (hy : y = P[s]'(by omega))
    (hz : z = P[s + 1]'hs)
    (hattach : ∀ p ∈ P,
      G.Adj (R[R.length - 2]'(by omega)) p ↔ p = y ∨ p = z) :
    ({b₁, b₂, b₃} : Set V) ⊆ F ∧
      IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃ := by
  classical
  let x : V := R[R.length - 2]'(by omega)
  let L₁ : List V := P.take (s + 1)
  let L₂ : List V := (P.drop (s + 1)).reverse
  let L₃ : List V := R.take (R.length - 1)
  have hPl : IsPathList G P := hP.1
  have hPnd : P.Nodup := PathBasics.path_nodup hPl
  have hPpos : 0 < P.length := PathBasics.path_length_pos hPl
  have hP0 : P[0]'hPpos = b₁ := PathBasics.getElem_zero_of_head? hP.2.1 hPpos
  have hPlast : P[P.length - 1]'(by omega) = b₂ :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hPpos
  have hRl : IsPathList G R := hR.1
  have hRnd : R.Nodup := PathBasics.path_nodup hRl
  have hRpos : 0 < R.length := PathBasics.path_length_pos hRl
  have hR0 : R[0]'hRpos = b₃ := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRlast : R[R.length - 1]'(by omega) = w :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  have hL₁ : IsPathFrom G L₁ b₁ y := by
    dsimp [L₁]
    exact isPathFrom_congr (isPathFrom_take hPl (by omega)) hP0 hy.symm
  have hL₂ : IsPathFrom G L₂ b₂ z := by
    dsimp [L₂]
    exact isPathFrom_congr
      (PathBasics.isPathFrom_reverse (isPathFrom_drop hPl hs)) hPlast hz.symm
  have hL₃ : IsPathFrom G L₃ b₃ x := by
    dsimp [L₃, x]
    have h := isPathFrom_take hRl (k := R.length - 2) (by omega)
    have heq : R.length - 2 + 1 = R.length - 1 := by omega
    rw [heq] at h
    exact isPathFrom_congr h hR0 rfl
  have hL₁F : ∀ v ∈ L₁, v ∈ F := fun v hv => hPF v (List.mem_of_mem_take hv)
  have hL₂F : ∀ v ∈ L₂, v ∈ F := fun v hv =>
    hPF v (List.mem_of_mem_drop (List.mem_reverse.mp hv))
  have hL₃F : ∀ v ∈ L₃, v ∈ F := fun v hv => hRF v (List.mem_of_mem_take hv)
  have hL₃notP : ∀ v ∈ L₃, v ∉ P := by
    intro v hvL hvP
    have hvR : v ∈ R := List.mem_of_mem_take hvL
    have hvw : v = w := by
      have hv : v ∈ ({q : V | q ∈ R} ∩ {q : V | q ∈ P}) := ⟨hvR, hvP⟩
      rw [hinter] at hv
      simpa using hv
    obtain ⟨m, hm, hmlt, rfl⟩ := mem_take_iff.mp hvL
    have heq : R[m]'hm = R[R.length - 1]'(by omega) := by rw [hRlast]; exact hvw
    have := (List.Nodup.getElem_inj_iff hRnd).mp heq
    omega
  have hcrossPL₃ : ∀ (m : ℕ) (hm : m < P.length), ∀ v ∈ L₃,
      (G.Adj (P[m]'hm) v ↔ ((m = s ∨ m = s + 1) ∧ v = x)) := by
    intro m hm v hvL
    obtain ⟨t, ht, htlt, rfl⟩ := mem_take_iff.mp hvL
    constructor
    · intro hedge
      by_cases htx : t = R.length - 2
      · subst t
        refine ⟨?_, rfl⟩
        have hp := (hattach (P[m]'hm) (List.getElem_mem hm)).mp hedge.symm
        rcases hp with hp | hp
        · left
          rw [hy] at hp
          exact (List.Nodup.getElem_inj_iff hPnd).mp hp
        · right
          rw [hz] at hp
          exact (List.Nodup.getElem_inj_iff hPnd).mp hp
      · exact False.elim ((hclean t m (by omega) hm) hedge.symm)
    · rintro ⟨hmidx, hvx⟩
      rw [hvx]
      apply SimpleGraph.Adj.symm
      apply (hattach (P[m]'hm) (List.getElem_mem hm)).mpr
      rcases hmidx with rfl | rfl
      · exact Or.inl hy.symm
      · exact Or.inr hz.symm
  have hL₁L₂disj : ∀ u ∈ L₁, ∀ v ∈ L₂, u ≠ v := by
    intro u hu v hv he
    obtain ⟨m, hm, hmle, hmu⟩ := mem_take_iff.mp hu
    obtain ⟨n, hn, hnge, hnv⟩ := mem_drop_iff.mp (List.mem_reverse.mp hv)
    have hmn : P[m]'hm = P[n]'hn := by rw [hmu, hnv, he]
    have := (List.Nodup.getElem_inj_iff hPnd).mp hmn
    omega
  have hL₁L₃disj : ∀ u ∈ L₁, ∀ v ∈ L₃, u ≠ v := by
    intro u hu v hv he
    exact hL₃notP v hv (by rw [← he]; exact List.mem_of_mem_take hu)
  have hL₂L₃disj : ∀ u ∈ L₂, ∀ v ∈ L₃, u ≠ v := by
    intro u hu v hv he
    exact hL₃notP v hv (by rw [← he]; exact List.mem_of_mem_drop (List.mem_reverse.mp hu))
  have hcross₁₂ : ∀ u ∈ L₁, ∀ v ∈ L₂,
      (G.Adj u v ↔ u = y ∧ v = z) := by
    intro u hu v hv
    obtain ⟨m, hm, hmle, rfl⟩ := mem_take_iff.mp hu
    obtain ⟨n, hn, hnge, rfl⟩ := mem_drop_iff.mp (List.mem_reverse.mp hv)
    rw [PathBasics.path_adj_iff hPl hm hn]
    constructor
    · intro hmn
      constructor
      · rw [hy]
        exact getElem_congr_idx _ _ (by omega)
      · rw [hz]
        exact getElem_congr_idx _ _ (by omega)
    · rintro ⟨hmy, hnz⟩
      rw [hy] at hmy
      rw [hz] at hnz
      have hm' := (List.Nodup.getElem_inj_iff hPnd).mp hmy
      have hn' := (List.Nodup.getElem_inj_iff hPnd).mp hnz
      omega
  have hcross₁₃ : ∀ u ∈ L₁, ∀ v ∈ L₃,
      (G.Adj u v ↔ u = y ∧ v = x) := by
    intro u hu v hv
    obtain ⟨m, hm, hmle, rfl⟩ := mem_take_iff.mp hu
    rw [hcrossPL₃ m hm v hv]
    constructor
    · rintro ⟨hmidx, hvx⟩
      refine ⟨?_, hvx⟩
      rw [hy]
      rcases hmidx with rfl | hbad
      · rfl
      · omega
    · rintro ⟨hmy, hvx⟩
      rw [hy] at hmy
      have hm' := (List.Nodup.getElem_inj_iff hPnd).mp hmy
      exact ⟨Or.inl hm', hvx⟩
  have hcross₂₃ : ∀ u ∈ L₂, ∀ v ∈ L₃,
      (G.Adj u v ↔ u = z ∧ v = x) := by
    intro u hu v hv
    obtain ⟨m, hm, hmge, rfl⟩ := mem_drop_iff.mp (List.mem_reverse.mp hu)
    rw [hcrossPL₃ m hm v hv]
    constructor
    · rintro ⟨hmidx, hvx⟩
      refine ⟨?_, hvx⟩
      rw [hz]
      rcases hmidx with hbad | rfl
      · omega
      · rfl
    · rintro ⟨hmz, hvx⟩
      rw [hz] at hmz
      have hm' := (List.Nodup.getElem_inj_iff hPnd).mp hmz
      exact ⟨Or.inr hm', hvx⟩
  have ha₁A : a₁ ∈ A := by rw [hAeq]; simp
  have ha₂A : a₂ ∈ A := by rw [hAeq]; simp
  have ha₃A : a₃ ∈ A := by rw [hAeq]; simp
  have hnotAF : ∀ a ∈ A, ∀ v ∈ F, a ≠ v := by
    intro a ha v hv hav
    subst v
    exact (Set.disjoint_left.mp hdisj) hv ha
  have hxF : x ∈ F := hL₃F x (PathBasics.getLast_mem hL₃.2.2)
  have hyF : y ∈ F := hL₁F y (PathBasics.getLast_mem hL₁.2.2)
  have hzF : z ∈ F := hL₂F z (PathBasics.getLast_mem hL₂.2.2)
  have hpath₁ : IsPathFrom G (a₁ :: L₁) a₁ y := by
    apply isPathFrom_cons hL₁
    · exact fun ha => (hnotAF a₁ ha₁A _ (hL₁F a₁ ha)) rfl
    · intro v hv
      exact (hadj v (hL₁F v hv)).1
  have hpath₂ : IsPathFrom G (a₂ :: L₂) a₂ z := by
    apply isPathFrom_cons hL₂
    · exact fun ha => (hnotAF a₂ ha₂A _ (hL₂F a₂ ha)) rfl
    · intro v hv
      exact (hadj v (hL₂F v hv)).2.1
  have hpath₃ : IsPathFrom G (a₃ :: L₃) a₃ x := by
    apply isPathFrom_cons hL₃
    · exact fun ha => (hnotAF a₃ ha₃A _ (hL₃F a₃ ha)) rfl
    · intro v hv
      exact (hadj v (hL₃F v hv)).2.2
  let aa : Fin 3 → V := triple a₁ a₂ a₃
  let bb : Fin 3 → V := triple y z x
  have hAA : ∀ i j : Fin 3, i ≠ j → G.Adj (aa i) (aa j) := by
    refine fin3_pairs (fun _ _ h => h.symm) ?_ ?_ ?_
    · dsimp [aa]; rw [triple_zero, triple_one]
      exact hA.2 a₁ ha₁A a₂ ha₂A haDistinct.1
    · dsimp [aa]; rw [triple_zero, triple_two]
      exact hA.2 a₁ ha₁A a₃ ha₃A haDistinct.2.1
    · dsimp [aa]; rw [triple_one, triple_two]
      exact hA.2 a₂ ha₂A a₃ ha₃A haDistinct.2.2
  have hyz : G.Adj y z := by
    rw [hy, hz]
    exact PathBasics.path_adj_succ hPl hs
  have hyx : G.Adj y x := by
    rw [SimpleGraph.adj_comm]
    dsimp [x]
    apply (hattach y (by rw [hy]; exact List.getElem_mem (by omega))).mpr
    exact Or.inl rfl
  have hzx : G.Adj z x := by
    rw [SimpleGraph.adj_comm]
    dsimp [x]
    apply (hattach z (by rw [hz]; exact List.getElem_mem hs)).mpr
    exact Or.inr rfl
  have hBB : ∀ i j : Fin 3, i ≠ j → G.Adj (bb i) (bb j) := by
    refine fin3_pairs (fun _ _ h => h.symm) ?_ ?_ ?_
    · dsimp [bb]; rw [triple_zero, triple_one]; exact hyz
    · dsimp [bb]; rw [triple_zero, triple_two]; exact hyx
    · dsimp [bb]; rw [triple_one, triple_two]; exact hzx
  have haabb : ∀ i j : Fin 3, aa i ≠ bb j := by
    intro i j
    fin_cases i <;> fin_cases j
    · exact hnotAF a₁ ha₁A y hyF
    · exact hnotAF a₁ ha₁A z hzF
    · exact hnotAF a₁ ha₁A x hxF
    · exact hnotAF a₂ ha₂A y hyF
    · exact hnotAF a₂ ha₂A z hzF
    · exact hnotAF a₂ ha₂A x hxF
    · exact hnotAF a₃ ha₃A y hyF
    · exact hnotAF a₃ ha₃A z hzF
    · exact hnotAF a₃ ha₃A x hxF
  have hcrossA₁L₂ : ∀ v ∈ L₂, ¬ G.Adj a₁ v := by
    intro v hv hedge
    have hvb : v = b₁ := ((hadj v (hL₂F v hv)).1).mp hedge
    exact hL₁L₂disj b₁ (PathBasics.head_mem hL₁.2.1) v hv hvb.symm
  have hcrossL₁A₂ : ∀ u ∈ L₁, ¬ G.Adj u a₂ := by
    intro u hu hedge
    have hub : u = b₂ := ((hadj u (hL₁F u hu)).2.1).mp hedge.symm
    exact hL₁L₂disj u hu b₂ (PathBasics.head_mem hL₂.2.1) hub
  have hcrossA₁L₃ : ∀ v ∈ L₃, ¬ G.Adj a₁ v := by
    intro v hv hedge
    have hvb : v = b₁ := ((hadj v (hL₃F v hv)).1).mp hedge
    exact hL₁L₃disj b₁ (PathBasics.head_mem hL₁.2.1) v hv hvb.symm
  have hcrossL₁A₃ : ∀ u ∈ L₁, ¬ G.Adj u a₃ := by
    intro u hu hedge
    have hub : u = b₃ := ((hadj u (hL₁F u hu)).2.2).mp hedge.symm
    exact hb₃P (by rw [← hub]; exact List.mem_of_mem_take hu)
  have hcrossA₂L₃ : ∀ v ∈ L₃, ¬ G.Adj a₂ v := by
    intro v hv hedge
    have hvb : v = b₂ := ((hadj v (hL₃F v hv)).2.1).mp hedge
    exact hL₂L₃disj b₂ (PathBasics.head_mem hL₂.2.1) v hv hvb.symm
  have hcrossL₂A₃ : ∀ u ∈ L₂, ¬ G.Adj u a₃ := by
    intro u hu hedge
    have hub : u = b₃ := ((hadj u (hL₂F u hu)).2.2).mp hedge.symm
    exact hb₃P (by rw [← hub]; exact List.mem_of_mem_drop (List.mem_reverse.mp hu))
  have hcrossC₁₂ : ∀ u ∈ a₁ :: L₁, ∀ v ∈ a₂ :: L₂,
      G.Adj u v ↔ (u = a₁ ∧ v = a₂) ∨ (u = y ∧ v = z) :=
    cross_cons (hA.2 a₁ ha₁A a₂ ha₂A haDistinct.1)
      hcrossA₁L₂ hcrossL₁A₂ hcross₁₂
      (hnotAF a₁ ha₁A y hyF) (hnotAF a₂ ha₂A z hzF)
      (fun h => (hnotAF a₁ ha₁A _ (hL₁F a₁ h)) rfl)
      (fun h => (hnotAF a₂ ha₂A _ (hL₂F a₂ h)) rfl)
  have hcrossC₁₃ : ∀ u ∈ a₁ :: L₁, ∀ v ∈ a₃ :: L₃,
      G.Adj u v ↔ (u = a₁ ∧ v = a₃) ∨ (u = y ∧ v = x) :=
    cross_cons (hA.2 a₁ ha₁A a₃ ha₃A haDistinct.2.1)
      hcrossA₁L₃ hcrossL₁A₃ hcross₁₃
      (hnotAF a₁ ha₁A y hyF) (hnotAF a₃ ha₃A x hxF)
      (fun h => (hnotAF a₁ ha₁A _ (hL₁F a₁ h)) rfl)
      (fun h => (hnotAF a₃ ha₃A _ (hL₃F a₃ h)) rfl)
  have hcrossC₂₃ : ∀ u ∈ a₂ :: L₂, ∀ v ∈ a₃ :: L₃,
      G.Adj u v ↔ (u = a₂ ∧ v = a₃) ∨ (u = z ∧ v = x) :=
    cross_cons (hA.2 a₂ ha₂A a₃ ha₃A haDistinct.2.2)
      hcrossA₂L₃ hcrossL₂A₃ hcross₂₃
      (hnotAF a₂ ha₂A z hzF) (hnotAF a₃ ha₃A x hxF)
      (fun h => (hnotAF a₂ ha₂A _ (hL₂F a₂ h)) rfl)
      (fun h => (hnotAF a₃ ha₃A _ (hL₃F a₃ h)) rfl)
  have hprism : FormPrism G aa bb (a₁ :: L₁) (a₂ :: L₂) (a₃ :: L₃) := by
    refine ⟨hAA, hBB, haabb, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [aa, bb, triple_zero] using hpath₁
    · simpa only [aa, bb, triple_one] using hpath₂
    · simpa only [aa, bb, triple_two] using hpath₃
    · simpa only [aa, bb, triple_zero, triple_one] using hcrossC₁₂
    · simpa only [aa, bb, triple_zero, triple_two] using hcrossC₁₃
    · simpa only [aa, bb, triple_one, triple_two] using hcrossC₂₃
  have hlen₁ : L₁.length ≤ 1 := by
    by_contra hlong
    apply hG.1.1.2.1
    exact ⟨aa, bb, a₁ :: L₁, a₂ :: L₂, a₃ :: L₃, hprism,
      Or.inl (by rw [PathBasics.pathLength_cons]; omega)⟩
  have hlen₂ : L₂.length ≤ 1 := by
    by_contra hlong
    apply hG.1.1.2.1
    exact ⟨aa, bb, a₁ :: L₁, a₂ :: L₂, a₃ :: L₃, hprism,
      Or.inr (Or.inl (by rw [PathBasics.pathLength_cons]; omega))⟩
  have hlen₃ : L₃.length ≤ 1 := by
    by_contra hlong
    apply hG.1.1.2.1
    exact ⟨aa, bb, a₁ :: L₁, a₂ :: L₂, a₃ :: L₃, hprism,
      Or.inr (Or.inr (by rw [PathBasics.pathLength_cons]; omega))⟩
  have hlen₁' : L₁.length = 1 := by
    have := PathBasics.path_length_pos hL₁.1
    omega
  have hlen₂' : L₂.length = 1 := by
    have := PathBasics.path_length_pos hL₂.1
    omega
  have hlen₃' : L₃.length = 1 := by
    have := PathBasics.path_length_pos hL₃.1
    omega
  have hb₁y : b₁ = y := ends_eq_of_length_one hL₁ hlen₁'
  have hb₂z : b₂ = z := ends_eq_of_length_one hL₂ hlen₂'
  have hb₃x : b₃ = x := ends_eq_of_length_one hL₃ hlen₃'
  refine ⟨?_, ?_⟩
  · intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact hbF.1
    · exact hbF.2.1
    · exact hbF.2.2
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hAeq] using hA
    · refine ⟨?_, ?_⟩
      · simp [hbDistinct.1, hbDistinct.2.1, hbDistinct.2.2]
      · intro u hu v hv huv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        all_goals try { exact False.elim (huv rfl) }
        · rw [hb₁y, hb₂z]; exact hyz
        · rw [hb₁y, hb₃x]; exact hyx
        · rw [hb₂z, hb₁y]; exact hyz.symm
        · rw [hb₂z, hb₃x]; exact hzx
        · rw [hb₃x, hb₁y]; exact hyx.symm
        · rw [hb₃x, hb₂z]; exact hzx.symm
    · apply Set.disjoint_left.mpr
      intro v hvA hvB
      have hvA' : v ∈ A := by rw [hAeq]; exact hvA
      apply (Set.disjoint_left.mp hdisj) ?_ hvA'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvB
      rcases hvB with rfl | rfl | rfl
      · exact hbF.1
      · exact hbF.2.1
      · exact hbF.2.2
    · intro u hu v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
      · simpa only [hu, hv, true_and, true_or, and_self] using (hadj b₁ hbF.1).1
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.1,
          Ne.symm hbDistinct.1] using (hadj b₂ hbF.2.1).1
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.1,
          Ne.symm haDistinct.2.1, Ne.symm hbDistinct.2.1, Ne.symm hbDistinct.2.2] using
          (hadj b₃ hbF.2.2).1
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.1,
          Ne.symm hbDistinct.1] using (hadj b₁ hbF.1).2.1
      · simpa [hu, hv, haDistinct, hbDistinct] using (hadj b₂ hbF.2.1).2.1
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.1,
          Ne.symm hbDistinct.2.1, Ne.symm hbDistinct.2.2] using (hadj b₃ hbF.2.2).2.1
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.2.1,
          Ne.symm hbDistinct.2.1] using (hadj b₁ hbF.1).2.2
      · simpa [hu, hv, haDistinct, hbDistinct, Ne.symm haDistinct.2.2,
          Ne.symm haDistinct.2.1, Ne.symm hbDistinct.1,
          Ne.symm hbDistinct.2.2] using (hadj b₂ hbF.2.1).2.2
      · simpa [hu, hv, haDistinct, hbDistinct] using (hadj b₃ hbF.2.2).2.2

end Workspace.Types.DoubleAttachmentForcesTriangleReflection
