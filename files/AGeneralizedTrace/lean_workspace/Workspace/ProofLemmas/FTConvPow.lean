import Mathlib
import Workspace.ProofLemmas.KFoldConvolutionTheorem

open scoped Real Complex

set_option maxHeartbeats 4000000

namespace FTConvPow

open KFoldConvolutionTheorem

/-- Circular convolution on `ℝ/(2πℤ)` of two complex functions `F G : ℝ → ℂ`
(alias of `KFoldConvolutionTheorem.circConv`). -/
noncomputable def circConvC (F G : ℝ → ℂ) (ξ : ℝ) : ℂ := circConv F G ξ

/-- `b`-fold circular self-convolution of `F : ℝ → ℂ`.
`circPow F 0 = 0` (placeholder; only `b ≥ 1` is used);
`circPow F 1 = F`;
`circPow F (b+2) = circConvC (circPow F (b+1)) F`. -/
noncomputable def circPow (F : ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => fun _ => 0
  | 1 => F
  | (b + 2) => fun ξ => circConvC (circPow F (b + 1)) F ξ

@[simp] lemma circPow_one (F : ℝ → ℂ) : circPow F 1 = F := rfl

lemma circPow_succ_succ (F : ℝ → ℂ) (b : ℕ) :
    circPow F (b + 2) = fun ξ => circConvC (circPow F (b + 1)) F ξ := rfl

/-- The constant family `fun _ => g`'s `k`-fold convolution of FTs is exactly
`circPow (FT g) k`. -/
lemma kConv_const_eq_circPow (g : ℤ → ℂ) :
    ∀ k : ℕ, kConv (fun _ => g) k = circPow (FT g) k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    match k with
    | 0 => rfl
    | (k + 1) =>
      rw [kConv_succ_succ, circPow_succ_succ, ih]
      funext ξ
      rfl

/-- The constant family `fun _ => g`'s partial product is the pointwise power. -/
lemma partialProd_const (g : ℤ → ℂ) (k : ℕ) :
    partialProd (fun _ => g) k = fun n => (g n) ^ k := by
  funext n
  simp [partialProd]

/--
**FT of a pointwise power = circular power of the FT.**

For `g : ℤ → ℂ` whose every power `g^m` (for `1 ≤ m ≤ b`) is summable in modulus,
the discrete Fourier transform of the `b`-fold pointwise power `g^b` equals the
`b`-fold circular self-convolution of `FT g`:

  `FT (fun n => (g n)^b) ξ = circPow (FT g) b ξ`   for every `ξ`, whenever `1 ≤ b`.

This is the self-power specialization of `kFoldConvolutionTheorem` (all `k`
factors equal `g`). -/
theorem ft_pow_eq_circPow
    (g : ℤ → ℂ)
    (hpow_sum : ∀ m : ℕ, 1 ≤ m → Summable (fun n : ℤ => ‖(g n) ^ m‖)) :
    ∀ (b : ℕ), 1 ≤ b → ∀ ξ : ℝ,
      FT (fun n => (g n) ^ b) ξ = circPow (FT g) b ξ := by
  intro b hb ξ
  -- Instantiate the k-fold theorem at the constant family `fun _ => g`.
  have hf_sum : ∀ j : ℕ, Summable (fun n : ℤ => ‖(fun _ => g) j n‖) := by
    intro j
    simpa using hpow_sum 1 (le_refl 1)
  have hpp_sum : ∀ m : ℕ, 1 ≤ m →
      Summable (fun n : ℤ => ‖partialProd (fun _ => g) m n‖) := by
    intro m hm
    rw [partialProd_const]
    exact hpow_sum m hm
  have hmain := kFoldConvolutionTheorem (fun _ => g) hf_sum hpp_sum b hb ξ
  rw [partialProd_const] at hmain
  rw [hmain, kConv_const_eq_circPow]

end FTConvPow
