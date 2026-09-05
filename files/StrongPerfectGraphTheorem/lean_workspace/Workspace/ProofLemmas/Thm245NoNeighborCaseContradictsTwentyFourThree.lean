import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S24.Thm_24_3

set_option autoImplicit false

namespace Workspace.Types.Thm245NoNeighborCaseContradictsTwentyFourThree

open Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT

theorem thm245NoNeighborCaseContradictsTwentyFourThree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF11 G)
    (X Y : Set V)
    (hXne : X.Nonempty) (hX : AnticonnectedSet G X)
    (hYne : Y.Nonempty) (hXY : Disjoint X Y)
    (hcomp : Complete G X Y)
    (Q : List V) (z p₁ q : V)
    (hQ : IsPathFrom G Q z p₁)
    (hsnd : Q.tail.head? = some q)
    (hQX : ∀ w ∈ Q, w ∉ X)
    (hzXcomp : VertexComplete G z X)
    (hp₁Xcomp : VertexComplete G p₁ X)
    (hint : ∀ w ∈ interior Q, ¬ VertexComplete G w X)
    (hzY : z ∉ Y) (hp₁Y : p₁ ∉ Y)
    (hzYcomp : VertexComplete G z Y)
    (hqYcomp : VertexComplete G q Y)
    (hzp₁ : ¬ G.Adj z p₁) (hqp₁ : ¬ G.Adj q p₁) :
    False := by
  have hqtail : q ∈ Q.tail := List.mem_of_mem_head? hsnd
  have htailpos : 0 < Q.tail.length := List.length_pos_of_mem hqtail
  have hQlen2 : 2 ≤ Q.length := by
    simp only [List.length_tail] at htailpos
    omega
  have hQpos : 0 < Q.length := by omega
  have hQ0 : Q[0]'hQpos = z :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQ1 : Q[1]'(by omega) = q := by
    have h := hsnd
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)] at h
    have h' : Q.tail[0]'(by simp; omega) = q := Option.some_inj.mp h
    rw [← h']
    simp [List.getElem_tail]
  have hQlast : Q[Q.length - 1]'(by omega) = p₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQlen4 : 4 ≤ Q.length := by
    by_contra hlen
    have hcases : Q.length = 2 ∨ Q.length = 3 := by omega
    rcases hcases with hlen2 | hlen3
    · have hqeq : q = p₁ := by
        rw [← hQ1, ← hQlast]
        congr 1
        omega
      have hzq : G.Adj z q := by
        rw [← hQ0, ← hQ1]
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hQ.1 (by omega) (by omega)).mpr
          (Or.inl rfl)
      exact hzp₁ (hqeq ▸ hzq)
    · have hlast2 : Q[2]'(by omega) = p₁ := by
        rw [← hQlast]
        congr 1
        omega
      have hqend : G.Adj q p₁ := by
        rw [← hQ1, ← hlast2]
        exact (Workspace.ProofLemmas.PathBasics.path_adj_iff hQ.1 (by omega) (by omega)).mpr
          (Or.inl rfl)
      exact hqp₁ hqend
  obtain ⟨y, hyY⟩ := hYne
  have hyX : y ∉ X := by
    intro hyX
    exact Set.disjoint_left.mp hXY hyX hyY
  have hyXcomp : VertexComplete G y X := by
    intro x hx
    exact (hcomp x hx y hyY).symm
  have hyQ : y ∉ Q := by
    intro hyQ
    by_cases hyz : y = z
    · exact hzY (hyz ▸ hyY)
    by_cases hyp₁ : y = p₁
    · exact hp₁Y (hyp₁ ▸ hyY)
    exact hint y
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mpr
        ⟨hyQ, hyz, hyp₁⟩) hyXcomp
  exact (_root_.Workspace.Statements.S24.SPGT.thm_24_3
    G hG X hXne hX Q z q p₁ hQ.1 hQX hQlen4 hQ.2.1 hsnd hQ.2.2
    hzXcomp hp₁Xcomp hint)
    ⟨y, hyX, hyQ, hyXcomp, (hzYcomp y hyY).symm, (hqYcomp y hyY).symm⟩

end Workspace.Types.Thm245NoNeighborCaseContradictsTwentyFourThree
