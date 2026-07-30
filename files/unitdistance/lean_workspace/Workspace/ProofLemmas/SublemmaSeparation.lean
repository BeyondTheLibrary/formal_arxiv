import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaNormProduct

open scoped NumberField
open Workspace.Types.MinkowskiWindow Workspace.Types.CMAdjoinI

namespace Workspace.ProofLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem SublemmaSeparation (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (a : Fin f → ℂ) :
    ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      ‖x - x'‖ ≥ (DD : ℝ)⁻¹ := by
  intro x hx x' hx' hne
  -- `x - x'` is a lattice vector, hence `= latticeHom sel DD β` for some `β ∈ 𝓞 K`.
  have hlat : x - x' ∈ lattice sel DD := by
    have h1 : x - a ∈ lattice sel DD := hx.1
    have h2 : x' - a ∈ lattice sel DD := hx'.1
    have h3 := AddSubgroup.sub_mem _ h1 h2
    simpa [sub_sub_sub_cancel_right] using h3
  obtain ⟨β, hβ⟩ := hlat
  -- `β ≠ 0` since `x ≠ x'`.
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hβ
    exact hne (sub_eq_zero.mp hβ.symm)
  -- Coordinate-wise, `(x - x')_r = σ_r β · DD⁻¹`.
  have hcoord : ∀ r, (x - x') r = sel.sigma r (β : K) * ((DD : ℂ))⁻¹ := by
    intro r
    have hr := congr_fun hβ r
    rw [← hr]
    simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
      AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply, minkowskiMap, Pi.ringHom_apply,
      map_mul, map_inv₀, map_natCast]
  have hnorm : ∀ r, ‖(x - x') r‖ = ‖sel.sigma r (β : K)‖ * (DD : ℝ)⁻¹ := by
    intro r
    rw [hcoord r, norm_mul, norm_inv, Complex.norm_natCast]
  -- Product of coordinate moduli.
  have hprod : (∏ r, ‖(x - x') r‖)
      = (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f := by
    rw [Finset.prod_congr rfl (fun r _ => hnorm r), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  -- Lower bound `≥ DD^{-f}` from `SublemmaNormProduct`.
  have hnp := (Workspace.ProofLemmas.SublemmaNormProduct hcm sel β hβ0).2
  have hpow_nonneg : (0 : ℝ) ≤ ((DD : ℝ)⁻¹) ^ f := by positivity
  have hprodge : ((DD : ℝ)⁻¹) ^ f ≤ (∏ r, ‖(x - x') r‖) := by
    rw [hprod]
    calc ((DD : ℝ)⁻¹) ^ f = 1 * ((DD : ℝ)⁻¹) ^ f := (one_mul _).symm
      _ ≤ (∏ r, ‖sel.sigma r (β : K)‖) * ((DD : ℝ)⁻¹) ^ f :=
          mul_le_mul_of_nonneg_right hnp hpow_nonneg
  -- Separation by contradiction.
  by_contra hcon
  replace hcon : ‖x - x'‖ < (DD : ℝ)⁻¹ := not_le.mp hcon
  rcases Nat.eq_zero_or_pos f with hf0 | hfpos
  · subst hf0
    exact hne (funext (fun i => i.elim0))
  · have hle : (∏ r, ‖(x - x') r‖) ≤ ‖x - x'‖ ^ f := by
      calc (∏ r, ‖(x - x') r‖) ≤ ∏ _r : Fin f, ‖x - x'‖ :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun r _ => norm_le_pi_norm _ r)
        _ = ‖x - x'‖ ^ f := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hlt : ‖x - x'‖ ^ f < ((DD : ℝ)⁻¹) ^ f :=
      pow_lt_pow_left₀ hcon (norm_nonneg _) hfpos.ne'
    exact absurd hprodge (not_le.mpr (lt_of_le_of_lt hle hlt))

end Workspace.ProofLemmas
