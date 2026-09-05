import Workspace.Types.Core
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.StripSystemNeighbourhood

set_option autoImplicit false

namespace Workspace.Types.AnticompleteUnionComponents

open Workspace.Types.Core.SPGT

theorem anticompleteUnionComponents
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) (S T : Set V)
    (hdisjoint : Disjoint S T) (hS : S.Nonempty) (hT : T.Nonempty)
    (hanticomplete : Anticomplete H S T) :
    ¬ ConnectedSet H (S ∪ T) ∧
      ∃ C_S C_T : Set V,
        IsComponent H (S ∪ T) C_S ∧ C_S ⊆ S ∧
        IsComponent H (S ∪ T) C_T ∧ C_T ⊆ T := by
  obtain ⟨s, hs⟩ := hS
  obtain ⟨t, ht⟩ := hT
  have hnotConnected : ¬ ConnectedSet H (S ∪ T) := by
    intro hconnected
    have hsub : S ∪ T ⊆ S :=
      Workspace.ProofLemmas.StripSystemNeighbourhood.connectedSet_subset_of_anticomplete
        hanticomplete hconnected (Set.Subset.rfl) (Or.inl hs) hs
    exact Set.disjoint_left.mp hdisjoint (hsub (Or.inr ht)) ht
  obtain ⟨C_S, hC_S, hsC_S⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem H (S ∪ T) (Or.inl hs)
  obtain ⟨C_T, hC_T, htC_T⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem H (S ∪ T) (Or.inr ht)
  have hC_S_sub : C_S ⊆ S :=
    Workspace.ProofLemmas.StripSystemNeighbourhood.connectedSet_subset_of_anticomplete
      hanticomplete hC_S.2.1 hC_S.1 hsC_S hs
  have hanticomplete_symm : Anticomplete H T S := by
    intro y hy x hx hadj
    exact hanticomplete x hx y hy hadj.symm
  have hC_T_union : C_T ⊆ T ∪ S := by
    intro x hx
    exact (hC_T.1 hx).symm
  have hC_T_sub : C_T ⊆ T :=
    Workspace.ProofLemmas.StripSystemNeighbourhood.connectedSet_subset_of_anticomplete
      hanticomplete_symm hC_T.2.1 hC_T_union htC_T ht
  exact ⟨hnotConnected, C_S, C_T, hC_S, hC_S_sub, hC_T, hC_T_sub⟩

end Workspace.Types.AnticompleteUnionComponents
