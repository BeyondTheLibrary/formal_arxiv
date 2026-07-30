import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.SublemmaSeparation
import Workspace.ProofLemmas.SublemmaPacking

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- **Lemma 2.6 (size bound / packing).** With `R > 1/2` and denominator `DD ≥ 1`, the number
of coset points in the window is bounded: `N_a ≤ (4·R·DD)^{2f} = e^{Bf}`, `B = 2 log(4RD)`. -/
theorem Lemma26SizeBound (hcm : IsAdjoinI L K)
    (sel : EmbeddingSelection L K f) (DD : ℕ) (hDD : 1 ≤ DD)
    (R : ℝ) (hR : 1 / 2 < R) (a : Fin f → ℂ) :
    (Ncount sel DD R a : ℝ) ≤ (4 * R * (DD : ℝ)) ^ (2 * f) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hDD1 : (1 : ℝ) ≤ (DD : ℝ) := by exact_mod_cast hDD
  -- Separation of distinct window points.
  have hsep : ∀ x ∈ Xset sel DD R a, ∀ x' ∈ Xset sel DD R a, x ≠ x' →
      (DD : ℝ)⁻¹ ≤ ‖x - x'‖ := by
    intro x hx x' hx' hne
    exact Workspace.ProofLemmas.SublemmaSeparation hcm sel DD hDD R a x hx x' hx' hne
  -- Packing bound.
  have hpack := SublemmaPacking sel DD hDD R hR0 a hsep
  have hbound : (Ncount sel DD R a : ℝ) ≤ (1 + 2 * R * (DD : ℝ)) ^ (2 * f) := hpack.2
  -- Monotonicity of the base.
  have hbase : 1 + 2 * R * (DD : ℝ) ≤ 4 * R * (DD : ℝ) := by
    have h1 : (1 : ℝ) ≤ 2 * R * (DD : ℝ) := by nlinarith [hR, hDD1]
    nlinarith [h1]
  have hnonneg : (0 : ℝ) ≤ 1 + 2 * R * (DD : ℝ) := by positivity
  have hmono : (1 + 2 * R * (DD : ℝ)) ^ (2 * f) ≤ (4 * R * (DD : ℝ)) ^ (2 * f) :=
    pow_le_pow_left₀ hnonneg hbase (2 * f)
  exact le_trans hbound hmono

end MinkowskiLemmas
