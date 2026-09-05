import Workspace.Types.Core
import Workspace.ProofLemmas.ComponentsOfSetBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- A finite vertex set that is not connected splits into two nonempty
anticomplete parts. -/
theorem DisconnectedSetAnticompleteSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (A : Set V)
    (hA : ¬ ConnectedSet K A) :
    ∃ X Y : Set V,
      X.Nonempty ∧ Y.Nonempty ∧ Disjoint X Y ∧ X ∪ Y = A ∧
        Anticomplete K X Y := by
  classical
  have hAne : A.Nonempty := by
    by_contra hAempty
    rw [Set.not_nonempty_iff_eq_empty] at hAempty
    subst A
    apply hA
    intro x y
    exact (Set.notMem_empty x.1 x.2).elim
  obtain ⟨P, Q, hP, hQ, hPQ⟩ :=
    ComponentsOfSetBasics.exists_two_isComponent K hAne hA
  have hPne : P.Nonempty :=
    ComponentsOfSetBasics.nonempty_of_isComponent K hAne hP
  have hQne : Q.Nonempty :=
    ComponentsOfSetBasics.nonempty_of_isComponent K hAne hQ
  have hPQdisj : Disjoint P Q :=
    ComponentsOfSetBasics.disjoint_of_isComponent K hP hQ hPQ
  refine ⟨P, A \ P, hPne, ?_, ?_, ?_, ?_⟩
  · obtain ⟨q, hqQ⟩ := hQne
    refine ⟨q, hQ.1 hqQ, ?_⟩
    intro hqP
    exact (Set.disjoint_left.mp hPQdisj hqP hqQ).elim
  · rw [Set.disjoint_left]
    intro z hzP hzY
    exact hzY.2 hzP
  · ext z
    simp only [Set.mem_union, Set.mem_diff]
    constructor
    · rintro (hzP | ⟨hzA, _⟩)
      · exact hP.1 hzP
      · exact hzA
    · intro hzA
      by_cases hzP : z ∈ P
      · exact Or.inl hzP
      · exact Or.inr ⟨hzA, hzP⟩
  · intro x hx y hy hxy
    obtain ⟨hyA, hyP⟩ := hy
    obtain ⟨C, hC, hyC⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem K A hyA
    have hPC : P ≠ C := by
      intro hPC
      apply hyP
      rw [hPC]
      exact hyC
    exact ComponentsOfSetBasics.anticomplete_of_isComponent K hP hC hPC x hx y hyC hxy

end Workspace.ProofLemmas
