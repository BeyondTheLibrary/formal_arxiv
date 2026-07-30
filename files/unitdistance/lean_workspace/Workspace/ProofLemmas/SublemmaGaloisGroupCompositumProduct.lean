import Mathlib
import Workspace.ProofLemmas.SublemmaCompositumGalois
import Workspace.ProofLemmas.SublemmaDegreeCompositumLinearlyDisjoint

set_option maxHeartbeats 4000000

theorem SublemmaGaloisGroupCompositumProduct {ℓ : ℕ} (L : Fin ℓ → IntermediateField ℚ ℂ)
    [∀ i, IsGalois ℚ ↥(L i)] [∀ i, FiniteDimensional ℚ ↥(L i)]
    (hindep : iSupIndep (fun i => (L i).toSubalgebra))
    (hdisj : ∀ i, L i ⊓ (⨆ j, ⨆ (_ : j ≠ i), L j) = ⊥)
    [∀ i, Algebra ↥(L i) ↥(⨆ i, L i)] [∀ i, IsScalarTower ℚ ↥(L i) ↥(⨆ i, L i)] :
    ∃ e : (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) ≃* (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)),
      ∀ (σ : ↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) (i : Fin ℓ),
        e σ i = AlgEquiv.restrictNormal σ ↥(L i) := by
  haveI hn : ∀ i, Normal ℚ ↥(L i) := fun i => IsGalois.to_normal
  haveI hgalM : IsGalois ℚ ↥(⨆ i, L i) := (SublemmaCompositumGalois L).1
  haveI hfdM : FiniteDimensional ℚ ↥(⨆ i, L i) :=
    IntermediateField.finiteDimensional_iSup_of_finite (t := L)
  -- the restriction map as a MonoidHom
  set ρ : (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i)) →* (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)) :=
    Pi.monoidHom (fun i => AlgEquiv.restrictNormalHom ↥(L i)) with hρ
  -- injectivity
  have hinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hσi : ∀ i, σ.restrictNormal ↥(L i) = 1 := by
      intro i
      have h := congrFun hσ i
      simpa [hρ, Pi.monoidHom_apply] using h
    have hgen : (⨆ i, (IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange)
        = (⊤ : IntermediateField ℚ ↥(⨆ i, L i)) := by
      apply IntermediateField.map_injective (IntermediateField.val (⨆ i, L i))
      have hR : IntermediateField.map (IntermediateField.val (⨆ i, L i))
          (⊤ : IntermediateField ℚ ↥(⨆ i, L i)) = ⨆ i, L i :=
        (AlgHom.fieldRange_eq_map _).symm.trans (IntermediateField.fieldRange_val _)
      have hL : IntermediateField.map (IntermediateField.val (⨆ i, L i))
          (⨆ i, (IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange) = ⨆ i, L i := by
        simp only [IntermediateField.map_iSup]
        refine iSup_congr (fun i => ?_)
        exact (AlgHom.map_fieldRange _ _).trans
          (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ (L i) (hn i) _)
      exact hL.trans hR.symm
    have hadj : Algebra.adjoin ℚ
        (⋃ i, ((IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange : Set ↥(⨆ i, L i))) = ⊤ := by
      apply IntermediateField.adjoin_eq_top_iff.mp
      rw [← IntermediateField.iSup_eq_adjoin]
      exact hgen
    have hEqOn : Set.EqOn (σ.toAlgHom) (AlgHom.id ℚ ↥(⨆ i, L i))
        (⋃ i, ((IsScalarTower.toAlgHom ℚ ↥(L i) ↥(⨆ i, L i)).fieldRange : Set ↥(⨆ i, L i))) := by
      intro x hx
      simp only [Set.mem_iUnion, SetLike.mem_coe, AlgHom.mem_fieldRange] at hx
      obtain ⟨i, y, hy⟩ := hx
      have hc := AlgEquiv.restrictNormal_commutes σ ↥(L i) y
      rw [hσi i, AlgEquiv.one_apply] at hc
      show σ.toAlgHom x = AlgHom.id ℚ _ x
      rw [AlgHom.id_apply, ← hy]
      exact hc.symm
    have hEq : σ.toAlgHom = AlgHom.id ℚ ↥(⨆ i, L i) := AlgHom.ext_of_adjoin_eq_top hadj hEqOn
    ext x
    simpa using AlgHom.ext_iff.mp hEq x
  -- cardinality
  have hcard : Nat.card (↥(⨆ i, L i) ≃ₐ[ℚ] ↥(⨆ i, L i))
      = Nat.card (∀ i, ↥(L i) ≃ₐ[ℚ] ↥(L i)) := by
    rw [Nat.card_pi, (SublemmaCompositumGalois L).2,
      SublemmaDegreeCompositumLinearlyDisjoint L hindep hdisj]
    exact Finset.prod_congr rfl (fun i _ => (IsGalois.card_aut_eq_finrank ℚ ↥(L i)).symm)
  have hbij : Function.Bijective ρ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard
  refine ⟨MulEquiv.ofBijective ρ hbij, fun σ i => ?_⟩
  rfl
