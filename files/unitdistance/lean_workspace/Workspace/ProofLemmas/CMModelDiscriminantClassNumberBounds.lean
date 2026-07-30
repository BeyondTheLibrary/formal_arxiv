import Mathlib
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.ClassNumberRootDiscriminantBound
import Workspace.ProofLemmas.CMLayerAdjoinIRootDiscriminantBound

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.CMAdjoinI
open Polynomial

theorem CMModelDiscriminantClassNumberBounds
    (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (L : Type) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
    (hrd : rootDiscriminant L = rootDiscriminant F)
    (C_class : ℝ) (hCpos : 0 < C_class)
    (hCbound : ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ)
        ≤ (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ)))
    (H : ℝ) (hH : H = (2 * rootDiscriminant F) ^ (2 * C_class)) :
    0 < H ∧
      ∀ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra L K),
        IsAdjoinI L K →
          rootDiscriminant K ≤ 2 * rootDiscriminant F ∧
          (classNumber K : ℝ) ≤ H ^ (Module.finrank ℚ L) := by
  -- Root discriminant of `F` is at least `1` (since `|D_F| ≥ 1`).
  have hrdF_ge_one : (1 : ℝ) ≤ rootDiscriminant F := by
    have hDF : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero (K := F)
    have h1 : (1 : ℝ) ≤ |(NumberField.discr F : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hDF
    have hexp : (0 : ℝ) ≤ 1 / (Module.finrank ℚ F : ℝ) := by positivity
    unfold rootDiscriminant
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / (Module.finrank ℚ F : ℝ)) := by rw [Real.one_rpow]
      _ ≤ |(NumberField.discr F : ℝ)| ^ (1 / (Module.finrank ℚ F : ℝ)) :=
          Real.rpow_le_rpow (by norm_num) h1 hexp
  have hrdF_pos : (0 : ℝ) < rootDiscriminant F := by linarith
  have h2rdF_pos : (0 : ℝ) < 2 * rootDiscriminant F := by linarith
  have h2rdF_ge_two : (2 : ℝ) ≤ 2 * rootDiscriminant F := by linarith
  refine ⟨?_, ?_⟩
  · -- `0 < H`
    rw [hH]
    exact Real.rpow_pos_of_pos h2rdF_pos _
  · intro K fK nfK algLK hadj
    letI := fK
    letI := nfK
    letI := algLK
    -- Scalar tower `ℚ → L → K`.
    haveI hstL : IsScalarTower ℚ L K := by
      apply IsScalarTower.of_algebraMap_eq'
      exact Subsingleton.elim _ _
    haveI hfdLK : FiniteDimensional L K := by
      have : FiniteDimensional ℚ K := inferInstance
      exact FiniteDimensional.right ℚ L K
    -- Extract the generator `iota`.
    obtain ⟨iota, hsq, hadjT⟩ := hadj
    have hint : IsIntegral L iota := by
      refine ⟨X ^ 2 + 1, ?_, ?_⟩
      · monicity!
      · simp [hsq]
    have hmonic : (X ^ 2 + 1 : L[X]).Monic := by monicity!
    have hdvd : minpoly L iota ∣ (X ^ 2 + 1 : L[X]) := by
      apply minpoly.dvd
      simp [hsq]
    have hnd : (X ^ 2 + 1 : L[X]).natDegree = 2 := by compute_degree!
    -- `[K : L] ≤ 2`.
    have hfL : Module.finrank L K ≤ 2 := by
      have hadjfin := IntermediateField.adjoin.finrank hint
      rw [hadjT] at hadjfin
      rw [IntermediateField.topEquiv.toLinearEquiv.finrank_eq] at hadjfin
      have hle := Polynomial.natDegree_le_of_dvd hdvd hmonic.ne_zero
      rw [hnd] at hle
      rw [hadjfin]; exact hle
    -- `[K : ℚ] ≤ 2 [L : ℚ]`.
    have htower : Module.finrank ℚ L * Module.finrank L K = Module.finrank ℚ K :=
      Module.finrank_mul_finrank ℚ L K
    have hdeg_le : Module.finrank ℚ K ≤ 2 * Module.finrank ℚ L := by
      rw [← htower]
      calc Module.finrank ℚ L * Module.finrank L K
            ≤ Module.finrank ℚ L * 2 := by
              apply Nat.mul_le_mul_left; exact hfL
        _ = 2 * Module.finrank ℚ L := by ring
    -- The relative-discriminant bound (paper tex 806–818).
    have hdisc : rootDiscriminant K ≤ 2 * rootDiscriminant F := by
      rw [← hrd]
      exact CMLayerAdjoinIRootDiscriminantBound L K ⟨iota, hsq, hadjT⟩
    refine ⟨hdisc, ?_⟩
    -- Class-number bound.
    have hcn := hCbound K
    have hmax : max 2 (rootDiscriminant K) ≤ 2 * rootDiscriminant F :=
      max_le h2rdF_ge_two hdisc
    have hmax_nonneg : (0 : ℝ) ≤ max 2 (rootDiscriminant K) :=
      le_trans (by norm_num) (le_max_left _ _)
    have hexp_nonneg : (0 : ℝ) ≤ C_class * (Module.finrank ℚ K : ℝ) := by positivity
    have step2 : (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ))
        ≤ (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ)) :=
      Real.rpow_le_rpow hmax_nonneg hmax hexp_nonneg
    have hbase_ge_one : (1 : ℝ) ≤ 2 * rootDiscriminant F := by linarith
    have hexp_le : C_class * (Module.finrank ℚ K : ℝ)
        ≤ C_class * (2 * (Module.finrank ℚ L : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hCpos)
      have : (Module.finrank ℚ K : ℝ) ≤ 2 * (Module.finrank ℚ L : ℝ) := by
        exact_mod_cast hdeg_le
      linarith
    have step3 : (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ))
        ≤ (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexp_le
    have hrhs : (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ)))
        = H ^ (Module.finrank ℚ L) := by
      rw [hH]
      rw [← Real.rpow_natCast ((2 * rootDiscriminant F) ^ (2 * C_class)) (Module.finrank ℚ L)]
      rw [← Real.rpow_mul (le_of_lt h2rdF_pos)]
      congr 1
      ring
    calc (classNumber K : ℝ)
          ≤ (max 2 (rootDiscriminant K)) ^ (C_class * (Module.finrank ℚ K : ℝ)) := hcn
      _ ≤ (2 * rootDiscriminant F) ^ (C_class * (Module.finrank ℚ K : ℝ)) := step2
      _ ≤ (2 * rootDiscriminant F) ^ (C_class * (2 * (Module.finrank ℚ L : ℝ))) := step3
      _ = H ^ (Module.finrank ℚ L) := hrhs
