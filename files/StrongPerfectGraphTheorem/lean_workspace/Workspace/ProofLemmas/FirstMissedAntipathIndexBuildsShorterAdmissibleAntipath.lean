import Workspace.Types.Core
import Workspace.ProofLemmas.PathAttach

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

theorem FirstMissedAntipathIndexBuildsShorterAdmissibleAntipath
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (Y : Set V)
    (a0 a1 a2 : V) (q Q : List V) (j : ℕ)
    (hQshape : Q = a0 :: (q ++ [a1]))
    (hQantipath : IsAntipathFrom G Q a0 a1)
    (ha0a2 : G.Adj a0 a2)
    (ha2notY : a2 ∉ Y)
    (hqY : ∀ x ∈ q, x ∈ Y)
    (hj : j < q.length)
    (hjplus : j + 1 < q.length)
    (hmiss : ¬ G.Adj a2 (q[j]'hj))
    (hfirst : ∀ (k : ℕ) (hk : k < j),
      G.Adj a2 (q[k]'(Nat.lt_trans hk hj))) :
    let S := a0 :: (q.take (j + 1) ++ [a2])
    IsAntipathFrom G S a0 a2 ∧
    (∀ x ∈ interior S, x ∈ Y) ∧
    ¬ VertexComplete G a2 Y ∧
    pathLength S < pathLength Q := by
  classical
  dsimp
  have hjY : q[j]'hj ∈ Y := hqY _ (List.getElem_mem hj)
  have hQlen : Q.length = q.length + 2 := by
    simp [hQshape]
  have hprefixeq : Q.take (j + 2) = a0 :: q.take (j + 1) := by
    rw [hQshape, show j + 2 = (j + 1) + 1 by omega, List.take_succ_cons]
    congr 1
    exact List.take_eq_left_iff.mpr (Or.inr (by omega))
  have hp : IsPathFrom Gᶜ (Q.take (j + 2)) a0 (q[j]'hj) := by
    have hs := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hQantipath.1
      (i := 0) (j := j + 1) (by omega) (by omega)
    simpa [hQshape, hj] using hs
  have hendpoint : Gᶜ.Adj a2 (q[j]'hj) := by
    exact (G.compl_adj _ _).mpr ⟨fun heq => ha2notY (heq ▸ hjY), hmiss⟩
  have ha2notprefix : a2 ∉ Q.take (j + 2) := by
    rw [hprefixeq]
    intro hm
    rcases List.mem_cons.mp hm with heq | hmq
    · exact ha0a2.ne heq.symm
    · exact ha2notY (hqY _ (List.mem_of_mem_take hmq))
  have hother : ∀ z ∈ Q.take (j + 2), z ≠ q[j]'hj → ¬ Gᶜ.Adj a2 z := by
    rw [hprefixeq]
    intro z hz hzj hcz
    rcases List.mem_cons.mp hz with hza0 | hzq
    · subst z
      exact ((G.compl_adj _ _).mp hcz).2 ha0a2.symm
    · obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hzq
      have hkq : k < q.length := by
        have hle : (q.take (j + 1)).length ≤ q.length := by
          simp only [List.length_take]
          omega
        exact lt_of_lt_of_le hk hle
      have hkle : k ≤ j := by
        have hle : (q.take (j + 1)).length ≤ j + 1 := by
          simp only [List.length_take]
          omega
        have hlt : k < j + 1 := lt_of_lt_of_le hk hle
        omega
      have hklt : k < j := by
        by_contra hknot
        have hkj : k = j := by omega
        subst k
        have hqjz : q[j]'hj = z := by
          simpa only [List.getElem_take] using hkz
        exact hzj hqjz.symm
      have ha : G.Adj a2 z := by
        rw [← hkz]
        simp only [List.getElem_take]
        exact hfirst k hklt
      exact ((G.compl_adj _ _).mp hcz).2 ha
  have hS : IsAntipathFrom G (a0 :: (q.take (j + 1) ++ [a2])) a0 a2 := by
    have ha := Workspace.ProofLemmas.PathAttach.isPathFrom_concat hp hendpoint ha2notprefix hother
    simpa [hprefixeq] using ha
  refine ⟨hS, ?_, ?_, ?_⟩
  · intro z hz
    have hSpath : IsPathFrom Gᶜ (a0 :: (q.take (j + 1) ++ [a2])) a0 a2 := hS
    have hzall := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hSpath).mp hz
    rcases List.mem_cons.mp hzall.1 with hza0 | hzrest
    · exact (hzall.2.1 hza0).elim
    · rcases List.mem_append.mp hzrest with hztake | hza2
      · exact hqY z (List.mem_of_mem_take hztake)
      · exact (hzall.2.2 (by simpa using hza2)).elim
  · intro hc
    exact hmiss (hc _ hjY)
  · simp [hQshape, pathLength, List.length_take] <;> omega

end Workspace.ProofLemmas
