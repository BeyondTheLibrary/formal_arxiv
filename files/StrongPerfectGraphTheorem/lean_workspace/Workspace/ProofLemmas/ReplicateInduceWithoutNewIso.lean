import Workspace.Types.Replication

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Replication.SPGT

theorem ReplicateInduceWithoutNewIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X : Set (V ⊕ Unit))
    (hw : Sum.inr () ∉ X) :
    ∃ e : (replicateVertex G v).induce X ≃g G.induce {a : V | Sum.inl a ∈ X},
      ∀ (a : V) (ha : Sum.inl a ∈ X),
        e ⟨Sum.inl a, ha⟩ = ⟨a, ha⟩ := by
  classical
  let e : (replicateVertex G v).induce X ≃g G.induce {a : V | Sum.inl a ∈ X} :=
    { toFun := fun x =>
        match x with
        | ⟨Sum.inl a, ha⟩ => ⟨a, ha⟩
        | ⟨Sum.inr u, hu⟩ => (hw hu).elim
      invFun := fun y => ⟨Sum.inl y.1, y.2⟩
      left_inv := by
        rintro ⟨(a | u), ha⟩
        · rfl
        · exact (hw ha).elim
      right_inv := by
        rintro ⟨a, ha⟩
        rfl
      map_rel_iff' := by
        rintro ⟨(a | u), ha⟩ ⟨(b | w), hb⟩
        · rfl
        · exact (hw hb).elim
        · exact (hw ha).elim
        · exact (hw ha).elim }
  refine ⟨e, ?_⟩
  intro a ha
  rfl

end Workspace.ProofLemmas
