import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.KwayCircModulusStep
open scoped Real Complex
set_option maxHeartbeats 4000000
namespace KModEnvBound
open KFoldConvolutionTheorem
open CircConvInfra
open KwayCircModulusStep

/-- The per-factor / iterated real envelope of the moduli of the Fourier transforms. -/
noncomputable def kModEnv (f : ℕ → (ℤ → ℂ)) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => fun η => ‖FT (f 0) η‖
  | (k + 2) => fun ξ => circConvR (kModEnv f (k + 1)) (fun η => ‖FT (f (k + 1)) η‖) ξ

@[simp] lemma kModEnv_one (f : ℕ → (ℤ → ℂ)) :
    kModEnv f 1 = fun η => ‖FT (f 0) η‖ := rfl

lemma kModEnv_succ_succ (f : ℕ → (ℤ → ℂ)) (k : ℕ) :
    kModEnv f (k + 2) = fun ξ => circConvR (kModEnv f (k + 1)) (fun η => ‖FT (f (k + 1)) η‖) ξ :=
  rfl

/-- `kConv f k` is continuous for `k ≥ 1`. -/
theorem kConv_continuous (f : ℕ → (ℤ → ℂ))
    (hcont : ∀ j, Continuous (fun η => FT (f j) η)) :
    ∀ k, 1 ≤ k → Continuous (fun ξ => kConv f k ξ) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simpa [kConv_one] using hcont 0
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kConv_succ_succ]
      exact circConv_continuous _ _ (ih (by omega)) (hcont (k' + 1))

/-- `kConv f k` is `2π`-periodic for `k ≥ 1`. -/
theorem kConv_periodic (f : ℕ → (ℤ → ℂ))
    (hper : ∀ j, ∀ x, FT (f j) (x + 2 * Real.pi) = FT (f j) x) :
    ∀ k, 1 ≤ k → ∀ ξ, kConv f k (ξ + 2 * Real.pi) = kConv f k ξ := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simpa [kConv_one] using hper 0 ξ
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kConv_succ_succ]
      simp only
      exact circConv_periodic (kConv f (k' + 1)) (FT (f (k' + 1))) (hper (k' + 1)) ξ

/-- `kModEnv f k` is continuous for `k ≥ 1`. -/
theorem kModEnv_continuous (f : ℕ → (ℤ → ℂ))
    (hcont : ∀ j, Continuous (fun η => FT (f j) η)) :
    ∀ k, 1 ≤ k → Continuous (fun ξ => kModEnv f k ξ) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [kModEnv_one]
      exact (hcont 0).norm
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kModEnv_succ_succ]
      exact circConvR_continuous _ _ (ih (by omega)) ((hcont (k' + 1)).norm)

/-- `kModEnv f k` is nonnegative. -/
theorem kModEnv_nonneg (f : ℕ → (ℤ → ℂ)) :
    ∀ k, ∀ ξ, 0 ≤ kModEnv f k ξ := by
  intro k
  induction k with
  | zero => intro ξ; simp [kModEnv]
  | succ k ih =>
    intro ξ
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [kModEnv_one]
      exact norm_nonneg _
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kModEnv_succ_succ]
      exact circConvR_nonneg _ _ (fun x => ih x) (fun x => norm_nonneg _) ξ

/-- `kModEnv f k` is integrable on `[-π, π]` for `k ≥ 1`. -/
theorem kModEnv_integrableOn (f : ℕ → (ℤ → ℂ))
    (hcont : ∀ j, Continuous (fun η => FT (f j) η)) :
    ∀ k, 1 ≤ k →
      MeasureTheory.IntegrableOn (fun ξ => kModEnv f k ξ) (Set.Icc (-Real.pi) Real.pi) := by
  intro k hk
  exact (kModEnv_continuous f hcont k hk).continuousOn.integrableOn_compact isCompact_Icc

/-- **The iterated circular-convolution modulus envelope bound (Lemma 7, step G3).** -/
theorem kConv_modulus_le_kModEnv (f : ℕ → (ℤ → ℂ))
    (hcont : ∀ j, Continuous (fun η => FT (f j) η))
    (hper : ∀ j, ∀ x, FT (f j) (x + 2 * Real.pi) = FT (f j) x) :
    ∀ k, 1 ≤ k → ∀ ξ : ℝ, ‖kConv f k ξ‖ ≤ kModEnv f k ξ := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [kConv_one, kModEnv_one]
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      have ih' : ∀ η, ‖kConv f (k' + 1) η‖ ≤ kModEnv f (k' + 1) η := ih (by omega)
      rw [kConv_succ_succ, kModEnv_succ_succ]
      simp only
      have hbound := circConv_modulus_envelope
        (kConv f (k' + 1)) (FT (f (k' + 1))) (kModEnv f (k' + 1))
        (kConv_periodic f hper (k' + 1) (by omega))
        (hper (k' + 1))
        ((kConv_continuous f hcont (k' + 1) (by omega)).continuousOn.integrableOn_compact
          isCompact_Icc)
        (hcont (k' + 1))
        (kModEnv_integrableOn f hcont (k' + 1) (by omega))
        ih'
        ξ
      -- hbound RHS is defeq to circConvR (kModEnv f (k'+1)) (fun x => ‖FT (f (k'+1)) x‖) ξ.
      exact hbound

end KModEnvBound
