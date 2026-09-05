import Workspace.Types.Replication

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Replication.SPGT

/-- Replacing the lone new twin by the old vertex identifies the corresponding
induced replicated graph with an induced subgraph of the original graph. -/
theorem ReplicateInduceOnlyNewIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X : Set (V ⊕ Unit))
    (hw : Sum.inr () ∈ X) (hOldv : Sum.inl v ∉ X) :
    ∃ e : (replicateVertex G v).induce X ≃g
        G.induce (insert v {a : V | Sum.inl a ∈ X}),
      e ⟨Sum.inr (), hw⟩ = ⟨v, by simp⟩ ∧
        ∀ (a : V) (ha : Sum.inl a ∈ X),
          e ⟨Sum.inl a, ha⟩ = ⟨a, by simp [ha]⟩ := by
  let f : X → ↥(insert v {a : V | Sum.inl a ∈ X}) := fun x =>
    match x with
    | ⟨Sum.inl a, ha⟩ => ⟨a, Set.mem_insert_iff.mpr (Or.inr ha)⟩
    | ⟨Sum.inr _, _⟩ => ⟨v, Set.mem_insert v _⟩
  have hf_injective : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    rcases x with ⟨a | u, ha⟩
    · rcases y with ⟨b | t, hb⟩
      · exact congrArg Sum.inl (by simpa [f] using congrArg Subtype.val hxy)
      · have hav : a = v := by simpa [f] using congrArg Subtype.val hxy
        exact False.elim (hOldv (hav ▸ ha))
    · rcases y with ⟨b | t, hb⟩
      · have hvb : v = b := by simpa [f] using congrArg Subtype.val hxy
        exact False.elim (hOldv (hvb ▸ hb))
      · cases u
        cases t
        rfl
  have hf_surjective : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [Set.mem_insert_iff] at ha
    rcases ha with rfl | ha
    · exact ⟨⟨Sum.inr (), hw⟩, rfl⟩
    · exact ⟨⟨Sum.inl a, ha⟩, rfl⟩
  let e : (replicateVertex G v).induce X ≃g
      G.induce (insert v {a : V | Sum.inl a ∈ X}) :=
    { toEquiv := Equiv.ofBijective f ⟨hf_injective, hf_surjective⟩
      map_rel_iff' := by
        rintro ⟨a | u, ha⟩ ⟨b | t, hb⟩
        · rfl
        · have hav : a ≠ v := fun hav => hOldv (hav ▸ ha)
          simp [f, replicateVertex, hav]
        · have hbv : b ≠ v := fun hbv => hOldv (hbv ▸ hb)
          simp [f, replicateVertex, hbv, SimpleGraph.adj_comm]
        · cases u
          cases t
          simp [f, replicateVertex] }
  refine ⟨e, ?_, ?_⟩
  · rfl
  · intro a ha
    rfl

end Workspace.ProofLemmas
