import Workspace.Types.Core
import Workspace.ProofLemmas.MinimalThreeTerminalWitnesses

set_option autoImplicit false

namespace Workspace.Types.DeletedWitnessIsUnique

open Workspace.Types.Core.SPGT

theorem deletedWitnessIsUnique
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V) (v : Fin 3 → V)
    (hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i)
    (hpair : ∀ i j : Fin 3, i ≠ j → v i ≠ v j)
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ j : Fin 3, ∃ x ∈ S, x ∈ N j) → F.ncard ≤ S.ncard)
    (i : Fin 3) (hconnected : ConnectedSet G (F \ {v i})) :
    ∀ w ∈ F, w ∈ N i → w = v i := by
  classical
  intro w hwF hwN
  by_contra hwi
  have hmeet : ∀ j : Fin 3, ∃ x ∈ F \ {v i}, x ∈ N j := by
    intro j
    by_cases hji : j = i
    · subst j
      exact ⟨w, ⟨hwF, by simpa using hwi⟩, hwN⟩
    · exact ⟨v j, ⟨(hv j).1, by simpa using hpair j i hji⟩, (hv j).2⟩
  have hcard : F.ncard ≤ (F \ {v i}).ncard :=
    hmin (F \ {v i}) Set.diff_subset hconnected hmeet
  have heq : F \ {v i} = F :=
    Set.eq_of_subset_of_ncard_le Set.diff_subset hcard
  have hmem : v i ∈ F \ {v i} := by
    rw [heq]
    exact (hv i).1
  exact hmem.2 (by simp)

end Workspace.Types.DeletedWitnessIsUnique
