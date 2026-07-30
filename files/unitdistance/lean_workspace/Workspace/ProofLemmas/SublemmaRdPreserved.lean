import Mathlib
import Workspace.Types.SplittingRamification
import Workspace.Types.DiscriminantsClassNumber

open scoped NumberField

open Workspace.Types.SplittingRamification Workspace.Types.DiscriminantsClassNumber

/-- **Proposition 3.8 Step 3 (P3): root discriminant is preserved under a finite
everywhere-unramified extension.** -/
theorem SublemmaRdPreserved
    (F : Type*) [Field F] [NumberField F]
    (E : Type*) [Field E] [NumberField E]
    [Algebra F E] [FiniteDimensional F E]
    (hur : UnramifiedAtFinitePrimes F E) :
    rootDiscriminant E = rootDiscriminant F := by
  -- Step 1: every nonzero prime of `𝓞 E` is unramified over `𝓞 F`.
  have key : ∀ (P : Ideal (𝓞 E)) [hP : P.IsPrime], P ≠ ⊥ →
      Algebra.IsUnramifiedAt (𝓞 F) P := by
    intro P hP hPne
    have hpne : Ideal.under (𝓞 F) P ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hPne
    haveI hpprime : (Ideal.under (𝓞 F) P).IsPrime := inferInstance
    have hmem : P ∈ Ideal.primesOver (Ideal.under (𝓞 F) P) (𝓞 E) := ⟨hP, ⟨rfl⟩⟩
    have hram : Ideal.ramificationIdx (Ideal.under (𝓞 F) P) P = 1 :=
      hur (Ideal.under (𝓞 F) P) hpne hpprime P hmem
    rw [Algebra.isUnramifiedAt_iff_of_isDedekindDomain hPne]
    exact hram
  -- Step 2: the relative different ideal is the whole ring.
  have hdiff : differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    haveI : M.IsPrime := hM.isPrime
    have hbot : differentIdeal (𝓞 F) (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
    have hM_ne : M ≠ ⊥ := by
      rintro rfl; exact hbot (le_bot_iff.mp hle)
    have hdvd : M ∣ differentIdeal (𝓞 F) (𝓞 E) := Ideal.dvd_iff_le.mpr hle
    rw [dvd_differentIdeal_iff] at hdvd
    exact hdvd (key M hM_ne)
  -- Step 3: discriminant tower formula.
  have htower :
      (NumberField.discr E).natAbs
        = Ideal.absNorm (differentIdeal (𝓞 F) (𝓞 E))
          * (NumberField.discr F).natAbs ^ Module.finrank F E :=
    NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow F (𝓞 F) E (𝓞 E)
  rw [hdiff, Ideal.absNorm_top, one_mul] at htower
  -- Step 4: rpow arithmetic.
  have cast_eq : ∀ (n : ℤ), ((n.natAbs : ℝ)) = |(n : ℝ)| :=
    fun n => by rw [Int.cast_natAbs, Int.cast_abs]
  have haEF : |(NumberField.discr E : ℝ)|
      = |(NumberField.discr F : ℝ)| ^ Module.finrank F E := by
    rw [← cast_eq, ← cast_eq, htower]; push_cast; ring
  have haF_nonneg : (0 : ℝ) ≤ |(NumberField.discr F : ℝ)| := abs_nonneg _
  have hmpos : 0 < Module.finrank F E := Module.finrank_pos
  have hnFpos : 0 < Module.finrank ℚ F := Module.finrank_pos
  have hm : (Module.finrank F E : ℝ) ≠ 0 := by exact_mod_cast hmpos.ne'
  have hnF : (Module.finrank ℚ F : ℝ) ≠ 0 := by exact_mod_cast hnFpos.ne'
  have hn : (Module.finrank ℚ E : ℝ)
      = (Module.finrank ℚ F : ℝ) * (Module.finrank F E : ℝ) := by
    rw [← Module.finrank_mul_finrank ℚ F E]; push_cast; ring
  simp only [rootDiscriminant]
  rw [haEF, ← Real.rpow_natCast |(NumberField.discr F : ℝ)| (Module.finrank F E),
      ← Real.rpow_mul haF_nonneg]
  congr 1
  rw [hn]
  field_simp
