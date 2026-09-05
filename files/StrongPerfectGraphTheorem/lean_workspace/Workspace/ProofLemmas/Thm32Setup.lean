import Workspace.Statements.S02.Thm_2_9
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # The first, double-Roussel--Rubio reduction in Theorem 3.2 -/

namespace Workspace.ProofLemmas.Thm32Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem mem_take_index {p : List V} {k : ℕ} {z : V} (hz : z ∈ p.take k) :
    ∃ i : ℕ, ∃ hi : i < p.length, i < k ∧ p[i]'hi = z := by
  obtain ⟨i, hi, hieq⟩ := List.mem_iff_getElem.mp hz
  have hip : i < p.length := lt_of_lt_of_le hi (by
    simp only [List.length_take]
    exact Nat.min_le_right _ _)
  have hik : i < k := by
    have : i < (p.take k).length := hi
    rw [List.length_take] at this
    omega
  refine ⟨i, hip, hik, ?_⟩
  rw [← hieq]
  exact (List.getElem_take ..).symm

private theorem mem_drop_index {p : List V} {k : ℕ} {z : V} (hz : z ∈ p.drop k) :
    ∃ i : ℕ, ∃ hi : i < p.length, k ≤ i ∧ p[i]'hi = z := by
  obtain ⟨j, hj, hjeq⟩ := List.mem_iff_getElem.mp hz
  have hjlen : j < p.length - k := by simpa using hj
  refine ⟨k + j, by omega, by omega, ?_⟩
  rw [← hjeq]
  simp

/-- Applying 2.9 in the complement yields one of the two antipaths used by the
printed proof of 3.2. -/
theorem initial_configuration
    (G : SimpleGraph V) (hG : Berge G) (m n s : ℕ) (p q : List V)
    (hp : IsPathList G p) (hpm : p.length = m)
    (hs1 : 2 ≤ s) (hs2 : s ≤ m - 2)
    (hqn : q.length = n) (hn2 : 2 ≤ n) (hnodd : Odd n)
    (hQ : IsAntipathFrom G (p[s - 1] :: (q ++ [p[s]])) p[s - 1] p[s])
    (hqleft : ∀ x ∈ q, ∃ y ∈ p.take (s - 1), G.Adj x y)
    (hqright : ∀ x ∈ q, ∃ y ∈ p.drop (s + 1), G.Adj x y) :
    (∃ u ∈ p.take (s - 1), ∃ v ∈ p.take (s - 1),
        ¬ Gᶜ.Adj u v ∧
          IsPathList Gᶜ (u :: ((p[s - 1] :: q) ++ [v]))) ∨
      (∃ w ∈ p.drop (s + 1), ∃ x ∈ p.drop (s + 1),
        ¬ Gᶜ.Adj w x ∧
          IsPathList Gᶜ (w :: ((q ++ [p[s]]) ++ [x]))) := by
  classical
  have hn3 : 3 ≤ n := by
    obtain ⟨k, hk⟩ := hnodd
    omega
  have hslt : s < p.length := by omega
  have hsm1lt : s - 1 < p.length := by omega
  have hsp1lt : s + 1 < p.length := by omega
  let L : Set V := {z : V | z ∈ p.take (s - 1)}
  let R : Set V := {z : V | z ∈ p.drop (s + 1)}
  let P : List V := p[s - 1] :: (q ++ [p[s]])
  have hplen : P.length = n + 2 := by simp [P, hqn]
  have hLne : L.Nonempty := by
    refine ⟨p[0]'(by omega), ?_⟩
    exact List.mem_take_iff_getElem.mpr ⟨0, by omega, rfl⟩
  have hRne : R.Nonempty := by
    refine ⟨p[s + 1]'hsp1lt, ?_⟩
    exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
  have hRL : Disjoint R L := by
    rw [Set.disjoint_left]
    intro z hzR hzL
    obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzR
    obtain ⟨j, hj, hjs, hjz⟩ := mem_take_index hzL
    have hij : i = j := hp.2.1.getElem_inj_iff.mp (hiz.trans hjz.symm)
    omega
  have hanti : Anticomplete G R L := by
    intro x hxR y hyL hadj
    obtain ⟨i, hi, his, hix⟩ := mem_drop_index hxR
    obtain ⟨j, hj, hjs, hjy⟩ := mem_take_index hyL
    rw [← hix, ← hjy] at hadj
    rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hp hi hj).mp hadj with h | h <;>
      omega
  have hRLcomp : Complete Gᶜ R L := by
    intro x hx y hy
    refine (G.compl_adj x y).2 ⟨?_, hanti x hx y hy⟩
    intro he
    subst y
    exact Set.disjoint_left.mp hRL hx hy
  have hLa : AnticonnectedSet Gᶜ L := by
    unfold AnticonnectedSet
    simpa only [compl_compl] using
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (Workspace.ProofLemmas.PathBasics.isPathList_take hp (by omega))
  have hRa : AnticonnectedSet Gᶜ R := by
    unfold AnticonnectedSet
    simpa only [compl_compl] using
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (Workspace.ProofLemmas.PathBasics.isPathList_drop hp (by omega))
  have hpsL : p[s - 1] ∉ L := by
    intro hz
    obtain ⟨j, hj, hjs, he⟩ := mem_take_index hz
    exact (by
      have := hp.2.1.getElem_inj_iff.mp (he.trans rfl)
      omega)
  have hpsR : p[s - 1] ∉ R := by
    intro hz
    obtain ⟨i, hi, his, he⟩ := mem_drop_index hz
    exact (by
      have := hp.2.1.getElem_inj_iff.mp (he.trans rfl)
      omega)
  have hptL : p[s] ∉ L := by
    intro hz
    obtain ⟨j, hj, hjs, he⟩ := mem_take_index hz
    exact (by
      have := hp.2.1.getElem_inj_iff.mp (he.trans rfl)
      omega)
  have hptR : p[s] ∉ R := by
    intro hz
    obtain ⟨i, hi, his, he⟩ := mem_drop_index hz
    exact (by
      have := hp.2.1.getElem_inj_iff.mp (he.trans rfl)
      omega)
  have hPout : ∀ z ∈ P, z ∉ R ∪ L := by
    intro z hz hside
    simp [P] at hz
    rcases hz with hz | hz | hz
    · subst z
      exact hside.elim hpsR hpsL
    · rcases hside with hzR | hzL
      · obtain ⟨y, hyL, hzy⟩ := hqleft z hz
        exact hanti z hzR y hyL hzy
      · obtain ⟨y, hyR, hzy⟩ := hqright z hz
        exact hanti y hyR z hzL hzy.symm
    · subst z
      exact hside.elim hptR hptL
  have hpsRcomp : VertexComplete Gᶜ p[s - 1] R := by
    intro z hzR
    obtain ⟨i, hi, his, hiz⟩ := mem_drop_index hzR
    have hne : p[s - 1] ≠ z := by
      intro he
      have := hp.2.1.getElem_inj_iff.mp (he.trans hiz.symm)
      omega
    refine (G.compl_adj _ _).2 ⟨hne, ?_⟩
    rw [← hiz]
    exact Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hp hsm1lt hi (by omega) (by omega)
  have hptLcomp : VertexComplete Gᶜ p[s] L := by
    intro z hzL
    obtain ⟨j, hj, hjs, hjz⟩ := mem_take_index hzL
    have hne : p[s] ≠ z := by
      intro he
      have := hp.2.1.getElem_inj_iff.mp (he.trans hjz.symm)
      omega
    refine (G.compl_adj _ _).2 ⟨hne, ?_⟩
    rw [← hjz]
    exact Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hp hslt hj (by omega) (by omega)
  have hRuniq : ∀ z ∈ P, (VertexComplete Gᶜ z R ↔ z = p[s - 1]) := by
    intro z hz
    constructor
    · intro hc
      simp [P] at hz
      rcases hz with hz | hz | hz
      · exact hz
      · obtain ⟨y, hyR, hzy⟩ := hqright z hz
        exact False.elim ((hc y hyR).2 hzy)
      · subst z
        have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hp (i := s) (by omega)
        have hmem : p[s + 1] ∈ R := by
          exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
        exact False.elim ((hc (p[s + 1]) hmem).2 hadj)
    · rintro rfl
      exact hpsRcomp
  have hLuniq : ∀ z ∈ P, (VertexComplete Gᶜ z L ↔ z = p[s]) := by
    intro z hz
    constructor
    · intro hc
      simp [P] at hz
      rcases hz with hz | hz | hz
      · subst z
        have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hp (i := s - 2) (by omega)
        have hmem : p[s - 2] ∈ L := by
          exact List.mem_take_iff_getElem.mpr ⟨s - 2, by omega, rfl⟩
        have heq : s - 2 + 1 = s - 1 := by omega
        exact False.elim ((hc (p[s - 2]) hmem).2
          (by simpa only [heq] using hadj.symm))
      · obtain ⟨y, hyL, hzy⟩ := hqleft z hz
        exact False.elim ((hc y hyL).2 hzy)
      · exact hz
    · rintro rfl
      exact hptLcomp
  have hPeven : Even (pathLength P) := by
    obtain ⟨k, hk⟩ := hnodd
    refine ⟨k + 1, ?_⟩
    simp [P, pathLength, hqn]
    omega
  have hPpos : 0 < pathLength P := by simp [P, pathLength, hqn]
  have h29 := Workspace.Statements.S02.SPGT.thm_2_9 Gᶜ
    (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) R L hRL hRne hLne hRa hLa
      hRLcomp P p[s - 1] p[s] hQ.1 hPout hPeven hPpos hQ.2.1 hQ.2.2 hRuniq hLuniq
  rcases h29.1 with hright | hleft | hshort
  · obtain ⟨-, w, hwR, x, hxR, hwx, hpath⟩ := hright
    exact Or.inr ⟨w, hwR, x, hxR, hwx, by simpa [P, List.append_assoc] using hpath⟩
  · obtain ⟨-, u, huL, v, hvL, huv, hpath⟩ := hleft
    have hdrop : P.dropLast = p[s - 1] :: q := by
      change ((p[s - 1] :: q) ++ [p[s]]).dropLast = _
      exact List.dropLast_concat
    rw [hdrop] at hpath
    exact Or.inl ⟨u, huL, v, hvL, huv, by
      simpa [List.append_assoc] using hpath⟩
  · have : pathLength P = n + 1 := by simp [P, pathLength, hqn]
    omega

end Workspace.ProofLemmas.Thm32Setup
