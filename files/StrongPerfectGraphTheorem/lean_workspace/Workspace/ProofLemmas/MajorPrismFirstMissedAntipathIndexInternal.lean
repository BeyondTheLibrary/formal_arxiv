import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

theorem MajorPrismFirstMissedAntipathIndexInternal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y : Set V)
    (alpha beta : Fin 3 -> V) (q Q : List V) (x : V)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G alpha beta y)
    (hQshape : Q = alpha 0 :: (q ++ [alpha 1]))
    (hQantipath : IsAntipathFrom G Q (alpha 0) (alpha 1))
    (hqY : ∀ y ∈ q, y ∈ Y)
    (hxq : x ∈ q)
    (hxmiss : ¬ G.Adj (alpha 2) x) :
    ∃ (j : ℕ) (hj : j < q.length),
      0 < j ∧
      j + 1 < q.length ∧
      ¬ G.Adj (alpha 2) (q[j]'hj) ∧
      ∀ (k : ℕ) (hk : k < j),
        G.Adj (alpha 2) (q[k]'(Nat.lt_trans hk hj)) := by
  classical
  subst Q
  let Q : List V := alpha 0 :: (q ++ [alpha 1])
  have hQantipath' : IsAntipathFrom G Q (alpha 0) (alpha 1) := by
    simpa only [Q] using hQantipath
  have hmajor02 : ∀ y ∈ Y, ¬ G.Adj (alpha 0) y → ¬ G.Adj (alpha 2) y → False := by
    intro y hy h0 h2
    have hsat := (hYmajor y hy).1
    have hsub : (({alpha 0, alpha 1, alpha 2} : Set V) ∩ G.neighborSet y) ⊆ {alpha 1} := by
      rintro z ⟨hz, hzy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · exact (h0 (by simpa [SimpleGraph.mem_neighborSet] using hzy.symm)).elim
      · rfl
      · exact (h2 (by simpa [SimpleGraph.mem_neighborSet] using hzy.symm)).elim
    have hn := Set.ncard_le_ncard hsub (Set.finite_singleton (alpha 1))
    have : (({alpha 0, alpha 1, alpha 2} : Set V) ∩ G.neighborSet y).ncard ≤ 1 := by
      simpa using hn
    omega
  have hmajor12 : ∀ y ∈ Y, ¬ G.Adj (alpha 1) y → ¬ G.Adj (alpha 2) y → False := by
    intro y hy h1 h2
    have hsat := (hYmajor y hy).1
    have hsub : (({alpha 0, alpha 1, alpha 2} : Set V) ∩ G.neighborSet y) ⊆ {alpha 0} := by
      rintro z ⟨hz, hzy⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
      rcases hz with rfl | rfl | rfl
      · rfl
      · exact (h1 (by simpa [SimpleGraph.mem_neighborSet] using hzy.symm)).elim
      · exact (h2 (by simpa [SimpleGraph.mem_neighborSet] using hzy.symm)).elim
    have hn := Set.ncard_le_ncard hsub (Set.finite_singleton (alpha 0))
    have : (({alpha 0, alpha 1, alpha 2} : Set V) ∩ G.neighborSet y).ncard ≤ 1 := by
      simpa using hn
    omega
  let Bad : ℕ → Prop := fun j => ∃ hj : j < q.length, ¬ G.Adj (alpha 2) (q[j]'hj)
  have hbad_exists : ∃ j, Bad j := by
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxq
    refine ⟨i, hi, ?_⟩
    rw [hix]
    exact hxmiss
  let j := Nat.find hbad_exists
  have hjbad : Bad j := Nat.find_spec hbad_exists
  obtain ⟨hjlt, hjmiss⟩ := hjbad
  have hjmin : ∀ k, Bad k → j ≤ k := by
    intro k hk
    exact Nat.find_min' hbad_exists hk
  have hQlen : Q.length = q.length + 2 := by simp [Q]
  have hQzero : Q[0]'(by omega) = alpha 0 := by simp [Q]
  have hQsucc : ∀ k (hk : k < q.length), Q[k + 1]'(by omega) = q[k]'hk := by
    intro k hk
    simp only [Q]
    simp only [List.getElem_cons_succ]
    rw [List.getElem_append_left hk]
  have hfirstmiss : ¬ G.Adj (alpha 0) (q[0]'(by omega)) := by
    have hc : Gᶜ.Adj (alpha 0) (q[0]'(by omega)) := by
      rw [← hQzero, ← hQsucc 0 (by omega)]
      exact (PathBasics.path_adj_iff hQantipath'.1 (by omega) (by omega)).mpr (Or.inl rfl)
    exact ((G.compl_adj _ _).mp hc).2
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    have hjmiss0 : ¬ G.Adj (alpha 2) (q[0]'(by omega)) := by simpa [hj0] using hjmiss
    exact hmajor02 _ (hqY _ (List.getElem_mem (by omega))) hfirstmiss hjmiss0
  have hlastmiss : ¬ G.Adj (alpha 1) (q[q.length - 1]'(by omega)) := by
    have hc : Gᶜ.Adj (alpha 1) (q[q.length - 1]'(by omega)) := by
      have hqone : 1 ≤ q.length := by omega
      have hlast : Q[q.length]'(by omega) = q[q.length - 1]'(by omega) := by
        simpa only [Nat.sub_add_cancel hqone] using hQsucc (q.length - 1) (by omega)
      have hend : Q[q.length + 1]'(by omega) = alpha 1 := by
        simp only [Q]
        simp only [List.getElem_cons_succ]
        rw [List.getElem_append_right (le_refl q.length)]
        simp
      rw [← hend, ← hlast]
      exact (PathBasics.path_adj_iff hQantipath'.1 (by omega) (by omega)).mpr (Or.inr (by omega))
    exact ((G.compl_adj _ _).mp hc).2
  have hjnotlast : j ≠ q.length - 1 := by
    intro heq
    have hjmiss' : ¬ G.Adj (alpha 2) (q[q.length - 1]'(by omega)) := by
      simpa [heq] using hjmiss
    exact hmajor12 _ (hqY _ (List.getElem_mem (by omega))) hlastmiss hjmiss'
  have hjplus : j + 1 < q.length := by omega
  refine ⟨j, hjlt, hjpos, hjplus, hjmiss, ?_⟩
  intro k hk
  by_contra hkmiss
  have hle := hjmin k ⟨Nat.lt_trans hk hjlt, hkmiss⟩
  omega

end Workspace.ProofLemmas
