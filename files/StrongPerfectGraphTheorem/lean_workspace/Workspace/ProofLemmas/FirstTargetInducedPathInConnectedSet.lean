import Workspace.Types.Core
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.ConnectedSetUnionAttach
open Workspace.ProofLemmas.InducedPathExtraction
open Workspace.ProofLemmas.PathBasics

theorem firstTargetInducedPathInConnectedSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B : Set V) (v : V)
    (hA : ConnectedSet G A)
    (hvA : ∃ a ∈ A, G.Adj v a)
    (hAB : (A ∩ B).Nonempty)
    (hvB : v ∉ B) :
    ∃ p ∈ A ∩ B, ∃ P : List V,
      IsPathFrom G P v p ∧
      0 < pathLength P ∧
      (∀ w ∈ P, w ≠ v → w ∈ A) ∧
      (∀ w ∈ P, (w ∈ B ↔ w = p)) := by
  classical
  have hS : ConnectedSet G (A ∪ {v}) :=
    connectedSet_union_singleton hA hvA
  obtain ⟨p0, hp0A, hp0B⟩ := hAB
  obtain ⟨P0, hP0, hP0mem⟩ :=
    exists_isPathFrom_of_connected (G := G) hS (Or.inr rfl) (Or.inl hp0A)
  have hex : ∃ n : ℕ, ∃ p : V, p ∈ A ∩ B ∧ ∃ P : List V,
      IsPathFrom G P v p ∧ (∀ w ∈ P, w ∈ A ∪ {v}) ∧ P.length = n := by
    exact ⟨P0.length, p0, ⟨hp0A, hp0B⟩, P0, hP0, hP0mem, rfl⟩
  obtain ⟨p, hpAB, P, hP, hPmem, hPlen⟩ := Nat.find_spec hex
  have hmin : ∀ (q : V) (Q : List V), q ∈ A ∩ B → IsPathFrom G Q v q →
      (∀ w ∈ Q, w ∈ A ∪ {v}) → P.length ≤ Q.length := by
    intro q Q hq hQ hQmem
    rw [hPlen]
    exact Nat.find_min' hex ⟨q, hq, Q, hQ, hQmem, rfl⟩
  have hPne : P ≠ [] := hP.1.1
  have hPpos : 0 < P.length := List.length_pos_of_ne_nil hPne
  have hlast : P[P.length - 1]'(by omega) = p := by
    have hlastopt := hP.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega)] at hlastopt
    exact Option.some_inj.mp hlastopt
  have hpne : p ≠ v := by
    intro hpv
    apply hvB
    simpa [hpv] using hpAB.2
  have hPtwo : 1 < P.length := by
    by_contra hnot
    have hle : P.length ≤ 1 := Nat.le_of_not_gt hnot
    have hone : P.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
    have hhead : some x = some v := by
      simpa [hx] using hP.2.1
    have hlast' : some x = some p := by
      simpa [hx] using hP.2.2
    apply hpne
    exact (Option.some_inj.mp hlast').symm.trans (Option.some_inj.mp hhead)
  refine ⟨p, hpAB, P, hP, ?_, ?_, ?_⟩
  · simp only [pathLength]
    omega
  · intro w hw hwne
    rcases hPmem w hw with hwA | hwv
    · exact hwA
    · exfalso
      apply hwne
      simpa only [Set.mem_singleton_iff] using hwv
  · intro w hw
    constructor
    · intro hwB
      obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
      have hwA : w ∈ A := by
        rcases hPmem w hw with hwA | hwv
        · exact hwA
        · exfalso
          apply hvB
          exact (by simpa only [Set.mem_singleton_iff] using hwv) ▸ hwB
      have hilast : i = P.length - 1 := by
        by_contra hne
        have hi_lt : i + 1 < P.length := by omega
        have hpre : IsPathFrom G (P.take (i + 1)) v w := by
          refine ⟨isPathList_take hP.1 (by omega), ?_, ?_⟩
          · rw [List.head?_take, if_neg (by omega)]
            exact hP.2.1
          · rw [List.getLast?_take, if_neg (by omega)]
            simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, hwi,
              Option.some_or]
        have hpremem : ∀ z ∈ P.take (i + 1), z ∈ A ∪ {v} := by
          intro z hz
          exact hPmem z (List.take_subset _ _ hz)
        have hle := hmin w (P.take (i + 1)) ⟨hwA, hwB⟩ hpre hpremem
        rw [List.length_take] at hle
        omega
      subst i
      exact hwi.symm.trans hlast
    · intro hwp
      rw [hwp]
      exact hpAB.2

end Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
