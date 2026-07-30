import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.SublemmaCutOutChangeLevelInvariant
import Workspace.ProofLemmas.SublemmaCutOutFieldCubicChar
import Workspace.ProofLemmas.SublemmaCutOutProductClosure

open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaFsubsetM
    (ℓ : ℕ) (r : Fin ℓ → ℕ+) (D : ℕ+)
    (hp : ∀ i, (r i : ℕ).Prime)
    (hm : ∀ i, (r i : ℕ) % 3 = 1)
    (hrd : ∀ i, (r i : ℕ) ∣ (D : ℕ))
    (ψ : ∀ i, DirichletCharacter ℂ (r i : ℕ))
    (hψord : ∀ i, orderOf (ψ i) = 3)
    (χ : Fin ℓ → DirichletCharacter ℂ (D : ℕ))
    (hχ : ∀ i, χ i = (DirichletCharacter.changeLevel (hrd i)) (ψ i))
    (chi : DirichletCharacter ℂ (D : ℕ))
    (hchi : chi = ∏ i, χ i) :
    cutOutField D chi ≤ ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) := by
  set M := ⨆ i, cyclicCubicSubfield (r i) (hp i) (hm i) with hM
  -- Each factor's cut-out field equals a cyclic cubic subfield.
  have hcut : ∀ i, cutOutField D (χ i) = cyclicCubicSubfield (r i) (hp i) (hm i) := by
    intro i
    rw [hχ i, SublemmaCutOutChangeLevelInvariant (r i) D (ψ i) (hrd i),
        SublemmaCutOutFieldCubicChar (r i) (hp i) (hm i) (ψ i) (hψord i)]
  -- Each factor's cut-out field is ≤ M.
  have hfac : ∀ i, cutOutField D (χ i) ≤ M := by
    intro i
    rw [hcut i]
    exact le_iSup (fun i => cyclicCubicSubfield (r i) (hp i) (hm i)) i
  -- The trivial character cuts out ⊥.
  have h1 : cutOutField D (1 : DirichletCharacter ℂ (D : ℕ)) = ⊥ := by
    unfold cutOutField
    have hker : ((1 : DirichletCharacter ℂ (D : ℕ)).toUnitHom.comp
        (galToUnits D).toMonoidHom).ker = ⊤ := by
      rw [MonoidHom.ker_eq_top_iff]
      ext σ
      simp
    rw [hker]
    exact (congrArg IntermediateField.lift
      (IsGalois.fixedField_top (F := ℚ) (E := ↥(cyclotomicField' D)))).trans
        (IntermediateField.lift_bot ℚ (cyclotomicField' D))
  rw [hchi]
  refine Finset.prod_induction χ (fun x => cutOutField D x ≤ M) ?_ ?_ (fun i _ => hfac i)
  · intro a b ha hb
    exact le_trans (SublemmaCutOutProductClosure D a b) (sup_le ha hb)
  · show cutOutField D 1 ≤ M
    rw [h1]; exact bot_le
