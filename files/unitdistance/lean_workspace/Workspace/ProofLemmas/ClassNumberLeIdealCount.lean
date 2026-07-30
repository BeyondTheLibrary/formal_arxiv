import Mathlib
import Workspace.Types.DiscriminantsClassNumber

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

/--
`ClassNumberLeIdealCount`:  the class number of a number field `K` is bounded above
by the number of *nonzero integral ideals of `𝓞 K` whose absolute norm is at most the
Minkowski bound* `MB K`, where
`MB K = (4/π)^{r₂} · (n! / nⁿ) · √|D_K|`,   `n = [K:ℚ]`,  `r₂ = nrComplexPlaces K`.

This is the Minkowski ideal-class reduction, proved purely from Mathlib:
every ideal class of `𝓞 K` contains an integral representative of absolute norm `≤ MB K`
(`NumberField.exists_ideal_in_class_of_norm_le`), so the map sending each class to such a
representative injects `ClassGroup (𝓞 K)` into the (finite, by
`Ideal.finite_setOf_absNorm_le`) set of bounded-norm ideals.
-/
theorem ClassNumberLeIdealCount (K : Type) [Field K] [NumberField K] :
    (classNumber K : ℝ) ≤
      (Nat.card {I : Ideal (𝓞 K) //
        I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤
          (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
            ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
              Real.sqrt |(NumberField.discr K : ℝ)|)} : ℝ) := by
  classical
  set MB : ℝ := (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
      ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K : ℝ) ^ Module.finrank ℚ K *
        Real.sqrt |(NumberField.discr K : ℝ)|) with hMBdef
  have hMBnonneg : 0 ≤ MB := by rw [hMBdef]; positivity
  -- The counting set is finite: it embeds into ideals of absNorm ≤ ⌊MB⌋₊.
  have hfin : {I : Ideal (𝓞 K) | I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB}.Finite := by
    apply Set.Finite.subset (Ideal.finite_setOf_absNorm_le (Nat.floor MB))
    intro I hI
    simp only [Set.mem_setOf_eq]
    exact Nat.le_floor hI.2
  haveI : Finite {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB} :=
    hfin.to_subtype
  -- The class-to-representative map injects into the counting set.
  have hcard : classNumber K ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB} := by
    show Fintype.card (ClassGroup (𝓞 K)) ≤
      Nat.card {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB}
    have hinj : Function.Injective
        (fun C : ClassGroup (𝓞 K) =>
          (⟨((NumberField.exists_ideal_in_class_of_norm_le C).choose : Ideal (𝓞 K)),
            ⟨mem_nonZeroDivisors_iff_ne_zero.mp (NumberField.exists_ideal_in_class_of_norm_le C).choose.2,
             (NumberField.exists_ideal_in_class_of_norm_le C).choose_spec.2⟩⟩ :
            {I : Ideal (𝓞 K) // I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ MB})) := by
      intro C₁ C₂ hC
      have hval := congrArg Subtype.val hC
      simp only at hval
      have h1 := (NumberField.exists_ideal_in_class_of_norm_le C₁).choose_spec.1
      have h2 := (NumberField.exists_ideal_in_class_of_norm_le C₂).choose_spec.1
      have heq : (NumberField.exists_ideal_in_class_of_norm_le C₁).choose
               = (NumberField.exists_ideal_in_class_of_norm_le C₂).choose := Subtype.ext hval
      rw [← h1, ← h2, heq]
    have hle := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_eq_fintype_card] at hle
  exact_mod_cast hcard
