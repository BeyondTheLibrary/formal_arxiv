import Mathlib
import Workspace.Types.DiscriminantsClassNumber
import Workspace.ProofLemmas.PrimesOneModThreeLogSum

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

theorem BaseRootDiscriminantBound :
    ∃ C : ℝ, 0 < C ∧ ∃ ℓ₀ : ℕ, ∀ ℓ : ℕ, ℓ₀ ≤ ℓ →
      ∀ (F : Type) [Field F] [NumberField F],
        NumberField.IsTotallyReal F →
        Module.finrank ℚ F = 3 →
        (NumberField.discr F).natAbs =
            (∏ i ∈ Finset.range ℓ, Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i) ^ 2 →
        Real.log (rootDiscriminant F) =
              (2 / 3) * ∑ i ∈ Finset.range ℓ,
                Real.log ((Nat.nth (fun n => n.Prime ∧ n % 3 = 1) i : ℝ)) ∧
            Real.log (rootDiscriminant F) ≤ C * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by
  obtain ⟨A, hA, hbound⟩ := PrimesOneModThreeLogSum
  refine ⟨(2 / 3) * A, by positivity, 2, ?_⟩
  intro ℓ hℓ F _ _ _ hfin hdisc
  set pred := fun n => n.Prime ∧ n % 3 = 1 with hpred
  set P := ∏ i ∈ Finset.range ℓ, Nat.nth pred i with hP
  -- discriminant is nonzero, so P ≠ 0
  have hdne : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero (K := F)
  have hPsq : (NumberField.discr F).natAbs = P ^ 2 := hdisc
  have hPne : P ≠ 0 := by
    have h2 : P ^ 2 ≠ 0 := by
      rw [← hPsq]; exact Int.natAbs_ne_zero.mpr hdne
    intro h0; exact h2 (by simp [h0])
  have hrne : ∀ i ∈ Finset.range ℓ, Nat.nth pred i ≠ 0 :=
    Finset.prod_ne_zero_iff.mp (hP ▸ hPne)
  have hPposR : (0 : ℝ) < (P : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hPne)
  have hPpos : (0 : ℝ) < (P : ℝ) ^ 2 := pow_pos hPposR 2
  -- finrank cast
  have hfinr : (Module.finrank ℚ F : ℝ) = 3 := by rw [hfin]; norm_num
  -- |discr| as (P:ℝ)^2
  have habs : |(NumberField.discr F : ℝ)| = (P : ℝ) ^ 2 := by
    have h1 : |(NumberField.discr F : ℝ)| = ((NumberField.discr F).natAbs : ℝ) := by
      rw [Int.cast_natAbs, Int.cast_abs]
    rw [h1, hPsq]; push_cast; ring
  -- rootDiscriminant explicit
  have hrd : rootDiscriminant F = ((P : ℝ) ^ 2) ^ ((1 : ℝ) / 3) := by
    rw [rootDiscriminant, habs, hfinr]
  -- log of product = sum of logs
  have hsum : Real.log ((P : ℝ)) =
      ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ)) := by
    rw [hP]; push_cast
    rw [Real.log_prod (fun i hi => Nat.cast_ne_zero.mpr (hrne i hi))]
  -- the log identity
  have hlog : Real.log (rootDiscriminant F) =
      (2 / 3) * ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ)) := by
    rw [hrd, Real.log_rpow hPpos, Real.log_pow, ← hsum]
    push_cast; ring
  refine ⟨hlog, ?_⟩
  rw [hlog]
  have hb := hbound ℓ hℓ
  calc (2 / 3) * ∑ i ∈ Finset.range ℓ, Real.log ((Nat.nth pred i : ℝ))
      ≤ (2 / 3) * (A * (ℓ : ℝ) * Real.log (ℓ : ℝ)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = (2 / 3) * A * (ℓ : ℝ) * Real.log (ℓ : ℝ) := by ring
