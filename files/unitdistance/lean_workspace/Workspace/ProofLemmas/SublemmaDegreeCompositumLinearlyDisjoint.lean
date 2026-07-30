import Mathlib

set_option maxHeartbeats 2000000

theorem SublemmaDegreeCompositumLinearlyDisjoint {ℓ : ℕ}
    (L : Fin ℓ → IntermediateField ℚ ℂ) [∀ i, FiniteDimensional ℚ ↥(L i)]
    [∀ i, IsGalois ℚ ↥(L i)]
    (hindep : iSupIndep (fun i => (L i).toSubalgebra))
    (hdisj : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥) :
    Module.finrank ℚ ↥(⨆ i, L i) = ∏ i, Module.finrank ℚ ↥(L i) := by
  have key : ∀ s : Finset (Fin ℓ),
      Module.finrank ℚ ↥(⨆ i ∈ s, L i) = ∏ i ∈ s, Module.finrank ℚ ↥(L i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        haveI : FiniteDimensional ℚ ↥(⨆ i ∈ s, L i) :=
          IntermediateField.finiteDimensional_iSup_of_finset
        have hsub : (⨆ i ∈ s, L i) ≤ (⨆ j, ⨆ (_ : j ≠ a), L j) := by
          refine iSup_le (fun i => iSup_le (fun his => ?_))
          have hia : i ≠ a := fun h => ha (h ▸ his)
          exact le_iSup_of_le i (le_iSup_of_le hia le_rfl)
        have hinf : L a ⊓ (⨆ i ∈ s, L i) = ⊥ :=
          le_bot_iff.mp (le_trans (inf_le_inf_left (L a) hsub) (le_of_eq (hdisj a)))
        have hga : IsGalois ℚ ↥(L a) := ‹∀ i, IsGalois ℚ ↥(L i)› a
        have hld : (L a).LinearDisjoint ↥(⨆ i ∈ s, L i) :=
          (@IntermediateField.LinearDisjoint.iff_inf_eq_bot ℚ ℂ _ _ _ (L a)
            (⨆ i ∈ s, L i) hga _ _).mpr hinf
        rw [Finset.iSup_insert, Finset.prod_insert ha,
          IntermediateField.LinearDisjoint.finrank_sup hld, ih]
  have h := key Finset.univ
  have huniv : (⨆ i, L i) = ⨆ i ∈ Finset.univ, L i := by simp
  rw [huniv]; exact h
