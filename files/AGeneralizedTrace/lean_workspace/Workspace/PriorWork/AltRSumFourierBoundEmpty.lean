-- NOW A PROVED THEOREM (previously admitted as an axiom).
-- Paper: k=0 / empty-ℓ case of Lemma 8 (Rivkin–Valiant–Valiant 2024,
--   arXiv:2412.00674v1, §3, lines 369-381).
-- The full discrete-Fourier-convolution region-split modulus estimate is
-- discharged in `AltRSumEmptyOuterBound` (and its dependencies
-- `AltRSumEmptyAtomBounds`, `AltRSumEmptyInnerModulusBound`,
-- `AltRSumEmptyInnerPointwise`, `AltRSumEmptyRegionDecay`,
-- `CleanFTOuterModulusBound`, `AltRSumEmptyFourierAssembly`,
-- `AltRSumEmptyRegionSplit`). The only remaining admitted analytic input is the
-- standard circular-convolution triangle inequality
-- `ModulusOfCircularConvolutionTriangle`.
-- NL statement: Let n ∈ ℕ with n ≥ 10^12 and n % 8 = 1. Let δ ∈ (0, 1/2], α = c'·√n where c' = 1/(4 e²√(2π)). For z₋, z₊ ∈ {0, ..., ⌊n/2⌋}, the inner alternating r-sum altRSum n δ α z₋ z₊ ∅ (with empty ℓ, so the ellFactor product is 1) admits a discrete-Fourier-convolution representation at ξ = π whose modulus is bounded by |altRSum n δ α z₋ z₊ ∅| ≤ B_exp + B_Fou, where B_exp = (n+1)·(2π-2)·(2π)²/(1-δ)² · M with M = max{exp(-δz₋/20)/(1-δ), exp(-δz₊/20)/(1-δ), exp(-n/150)} and B_Fou = 4·(2π)²·exp(-√n)/(1-δ)².
import Mathlib
import Workspace.Types.AlternatingSumExpression
import Workspace.PriorWork.AltRSumEmptyOuterBound

/--
**Discrete Fourier convolution bound on altRSum (k = 0 / empty ℓ case).**
Specialization of the standard discrete-Fourier-convolution-theorem +
sign-encoding identity `(-1)^r = e^{iπr}` to the empty-ℓ case of the
alternating r-sum `altRSum n δ α z₋ z₊ ∅`.

For `n ≥ 10^12` with `n ≡ 1 (mod 8)`, `δ ∈ (0, 1/2]`, `α := c' · √n` with
`c' := 1/(4 e² √(2π))`, and every `z₋, z₊ ∈ {0, ..., ⌊n/2⌋}`:

  |altRSum n δ α z₋ z₊ ∅| ≤ B_exp(n, δ, z₋, z₊) + B_Fou(n, δ).

The empty product `∏ j ∈ ∅, ellFactor n α r j = 1` collapses the
4-fold convolution of `AltRSumFourierBound` to a 3-fold convolution
at `ξ = π`; the same Fourier-decay bound shape is preserved.
-/
theorem AltRSumFourierBoundEmpty :
    ∀ (n : ℕ), (10 ^ 12 : ℕ) ≤ n → n % 8 = 1 →
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1/2 →
    let c' : ℝ := 1 / (4 * Real.exp 2 * Real.sqrt (2 * Real.pi))
    let α : ℝ := c' * Real.sqrt n
    ∀ (zMinus zPlus : ℕ), zMinus < n / 2 + 1 → zPlus < n / 2 + 1 →
        |Workspace.Types.AlternatingSumExpression.altRSum n δ α zMinus zPlus ∅|
          ≤
          ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 *
            (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                      (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                 (Real.exp (-((n : ℝ) / 150))))
          +
          4 * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 * Real.exp (-Real.sqrt n) := by
  intro n hn hmod δ hδ0 hδ
  intro c' α zMinus zPlus _hzm _hzp
  have hn1 : 1 ≤ n := le_trans (by norm_num) hn
  -- Upstream gives a TIGHTER bound whose third max-term is exp(-(n/2)/73).
  have hup := Workspace.PriorWork.AltRSumEmptyOuterBound.altRSum_empty_abs_le_axiomRHS
    n hn1 δ hδ0 hδ α zMinus zPlus
  -- We bound the upstream RHS by this file's RHS (with exp(-n/150) in its max).
  -- Step 1: exp(-(n/2)/73) ≤ exp(-n/150), via monotonicity of exp.
  have hexp : Real.exp (-((n / 2 : ℕ) : ℝ) / 73) ≤ Real.exp (-((n : ℝ) / 150)) := by
    apply Real.exp_le_exp.mpr
    -- need: -↑(n/2)/73 ≤ -(n/150), i.e. n/150 ≤ (n/2)/73
    -- with n % 8 = 1: n = 8t+1, n/2 = 4t; need (8t+1)/150 ≤ 4t/73, i.e. 73 ≤ 16t, true for n ≥ 10^12.
    have hhalf : 2 * (n / 2 : ℕ) + 1 = n := by omega
    have hcast : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      have h := congrArg (Nat.cast : ℕ → ℝ) hhalf
      push_cast at h
      linarith [h]
    -- from hcast: ((n/2:ℕ):ℝ) = ((n:ℝ) - 1)/2
    have hbig : (41 : ℝ) ≤ (n : ℝ) := by
      have : (10 ^ 12 : ℕ) ≤ n := hn
      have : (41 : ℕ) ≤ n := le_trans (by norm_num) hn
      exact_mod_cast this
    nlinarith [hcast, hbig]
  -- Step 2: the only difference between the two RHS is the third max-term; bound via monotonicity.
  refine le_trans hup ?_
  have hcoef : (0:ℝ) ≤ ((n : ℝ) + 1) * (2 * Real.pi - 2) * (2 * Real.pi) ^ 2 / (1 - δ) ^ 2 := by
    have hpi : (2:ℝ) ≤ 2 * Real.pi - 2 := by nlinarith [Real.pi_gt_three]
    have hD : (0:ℝ) < 1 - δ := by linarith
    positivity
  have hmax : (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                        (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                   (Real.exp (-((n / 2 : ℕ) : ℝ) / 73)))
              ≤ (max (max (Real.exp (-(δ * (zMinus : ℝ) / 20)) / (1 - δ))
                          (Real.exp (-(δ * (zPlus : ℝ) / 20)) / (1 - δ)))
                     (Real.exp (-((n : ℝ) / 150)))) := by
    apply max_le_max (le_refl _) hexp
  gcongr
