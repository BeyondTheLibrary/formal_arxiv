import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem
import Workspace.ProofLemmas.CircConvInfra
import Workspace.ProofLemmas.CircConvMono
import Workspace.ProofLemmas.KModEnvBound

open scoped Real Complex

set_option maxHeartbeats 4000000

/-!
# Domination of the iterated modulus envelope by a single envelope (Lemma 7, G4)

The G4 step bounds the iterated *circular*-convolution modulus envelope
`kModEnv f k` (the k-fold circular convolution of the per-factor Fourier moduli
`‖FT(f j)‖`) by the k-fold circular convolution of a SINGLE dominating envelope
`e : ℝ → ℝ` that majorises every `‖FT(f j)‖` pointwise.

This is the structural reduction "many different per-factor envelopes ⟹ one common
envelope" that lets the final periodisation comparison
(`CircularConvolutionAsPeriodisation`) be applied to a single base function.

We define `kEnvOf e` as the k-fold circular self-convolution of `e`:
`kEnvOf e 1 = e`, `kEnvOf e (k+2) = circConvR (kEnvOf e (k+1)) e`, and prove,
sorry-free, the monotone domination

  `kModEnv f k ξ ≤ kEnvOf e k ξ`   for every `k ≥ 1` and `ξ : ℝ`,

assuming each `‖FT(f j)‖ ≤ e`, with `e` non-negative and continuous (and each
`FT(f j)` continuous and `2π`-periodic, which the parent supplies via finite
support).
-/

namespace KModEnvSingleDominated

open KFoldConvolutionTheorem
open CircConvInfra
open CircConvMono
open KModEnvBound

/-- The k-fold circular self-convolution of a single envelope `e : ℝ → ℝ`.
`kEnvOf e 0 = 0`, `kEnvOf e 1 = e`, `kEnvOf e (k+2) = circConvR (kEnvOf e (k+1)) e`. -/
noncomputable def kEnvOf (e : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | 1 => e
  | (k + 2) => fun ξ => circConvR (kEnvOf e (k + 1)) e ξ

@[simp] lemma kEnvOf_one (e : ℝ → ℝ) : kEnvOf e 1 = e := rfl

lemma kEnvOf_succ_succ (e : ℝ → ℝ) (k : ℕ) :
    kEnvOf e (k + 2) = fun ξ => circConvR (kEnvOf e (k + 1)) e ξ := rfl

/-- `kEnvOf e k` is non-negative for non-negative `e`. -/
theorem kEnvOf_nonneg (e : ℝ → ℝ) (he_nn : ∀ x, 0 ≤ e x) :
    ∀ k, ∀ ξ, 0 ≤ kEnvOf e k ξ := by
  intro k
  induction k with
  | zero => intro ξ; simp [kEnvOf]
  | succ k ih =>
    intro ξ
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [kEnvOf_one]; exact he_nn ξ
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kEnvOf_succ_succ]
      exact circConvR_nonneg _ _ (fun x => ih x) he_nn ξ

/-- `kEnvOf e k` is continuous for continuous `e` and `k ≥ 1`. -/
theorem kEnvOf_continuous (e : ℝ → ℝ) (he : Continuous e) :
    ∀ k, 1 ≤ k → Continuous (fun ξ => kEnvOf e k ξ) := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [kEnvOf_one]; exact he
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      rw [kEnvOf_succ_succ]
      exact circConvR_continuous _ _ (ih (by omega)) he

/-- **Iterated single-envelope domination (Lemma 7, step G4).** If each per-factor
Fourier modulus `‖FT(f j)‖` is pointwise `≤` a single non-negative continuous
envelope `e`, then the k-fold circular-convolution modulus envelope `kModEnv f k`
is dominated by the k-fold circular self-convolution `kEnvOf e k`:

  `kModEnv f k ξ ≤ kEnvOf e k ξ`   for every `k ≥ 1` and `ξ`. -/
theorem kModEnv_le_kEnvOf (f : ℕ → (ℤ → ℂ)) (e : ℝ → ℝ)
    (hcont : ∀ j, Continuous (fun η => FT (f j) η))
    (hper : ∀ j, ∀ x, FT (f j) (x + 2 * Real.pi) = FT (f j) x)
    (he_nn : ∀ x, 0 ≤ e x) (he : Continuous e)
    (hdom : ∀ j, ∀ η, ‖FT (f j) η‖ ≤ e η) :
    ∀ k, 1 ≤ k → ∀ ξ : ℝ, kModEnv f k ξ ≤ kEnvOf e k ξ := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
    intro _ ξ
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      rw [kModEnv_one, kEnvOf_one]
      exact hdom 0 ξ
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
      have ih' : ∀ η, kModEnv f (k' + 1) η ≤ kEnvOf e (k' + 1) η := ih (by omega)
      rw [kModEnv_succ_succ, kEnvOf_succ_succ]
      simp only
      -- circConvR (kModEnv f (k'+1)) ‖FT(f(k'+1))‖ ≤ circConvR (kEnvOf e (k'+1)) e
      apply circConvR_mono
      · exact fun x => kModEnv_nonneg f (k' + 1) x
      · exact fun x => kEnvOf_nonneg e he_nn (k' + 1) x
      · exact fun x => norm_nonneg _
      · exact fun x => he_nn x
      · exact kModEnv_continuous f hcont (k' + 1) (by omega)
      · exact kEnvOf_continuous e he (k' + 1) (by omega)
      · exact (hcont (k' + 1)).norm
      · exact he
      · exact fun η _ => ih' η
      · exact fun η _ => hdom (k' + 1) (ξ - η)

end KModEnvSingleDominated
