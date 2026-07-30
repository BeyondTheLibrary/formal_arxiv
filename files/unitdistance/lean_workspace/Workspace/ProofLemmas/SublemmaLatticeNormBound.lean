import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaNormProduct

set_option maxHeartbeats 4000000

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaLatticeNormBound (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD) :
    ∀ v ∈ lattice sel DD, v ≠ 0 → (DD : ℝ)⁻¹ ≤ ‖v‖ := by
  intro v hv hne
  obtain ⟨β, hβ⟩ := hv
  -- `β ≠ 0` since `v ≠ 0`.
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβ
    exact hne hβ.symm
  -- Coordinate-wise, `v_r = σ_r β · DD⁻¹`.
  have hcoord : ∀ r, v r = sel.sigma r (β : K) * ((DD : ℂ))⁻¹ := by
    intro r
    have hr := congr_fun hβ r
    rw [← hr]
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hnorm : ∀ r, ‖v r‖ = ‖sel.sigma r (β : K)‖ * (DD : ℝ)⁻¹ := by
    intro r
    rw [hcoord r, norm_mul, norm_inv, Complex.norm_natCast]
  have hprod : (∏ r, ‖v r‖) = (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f := by
    rw [Finset.prod_congr rfl (fun r _ => hnorm r), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hnp := (Workspace.ProofLemmas.SublemmaNormProduct hcm sel β hβ0).2
  have hpow_nonneg : (0 : ℝ) ≤ ((DD : ℝ)⁻¹) ^ f := by positivity
  have hprodge : ((DD : ℝ)⁻¹) ^ f ≤ (∏ r, ‖v r‖) := by
    rw [hprod]
    calc ((DD : ℝ)⁻¹) ^ f = 1 * ((DD : ℝ)⁻¹) ^ f := (one_mul _).symm
      _ ≤ (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f :=
          mul_le_mul_of_nonneg_right hnp hpow_nonneg
  -- Sup-norm lower bound by contradiction.
  by_contra hcon
  replace hcon : ‖v‖ < (DD : ℝ)⁻¹ := not_le.mp hcon
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    exact hne (funext (fun i => i.elim0))
  · have hle : (∏ r, ‖v r‖) ≤ ‖v‖ ^ f := by
      calc (∏ r, ‖v r‖) ≤ ∏ _r : Fin f, ‖v‖ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun r _ => norm_le_pi_norm _ r)
        _ = ‖v‖ ^ f := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlt : ‖v‖ ^ f < ((DD : ℝ)⁻¹) ^ f :=
      pow_lt_pow_left₀ hcon (norm_nonneg _) hfpos.ne'
    exact absurd hprodge (not_le.mpr (lt_of_le_of_lt hle hlt))

end MinkowskiLemmas
