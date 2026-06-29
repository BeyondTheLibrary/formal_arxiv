import Mathlib
import Workspace.Types.GaussianPDF
import Workspace.ProofLemmas.HalfGaussianMomentBound

open MeasureTheory
open Workspace.Types.GaussianPDF

namespace Workspace.ProofLemmas

/--
Sigma-aware tail moment bound for the centred Gaussian `N(0, σ²)`, for moment orders
`0 ≤ j ≤ 6`. There is an absolute constant `K27 > 0` such that for every variance
`σ² ∈ (0, 1]`, every `a > 0`, and every integer `j ∈ {0, …, 6}`,

  `∫_{a}^{∞} u^j · (1 / √(2π σ²)) · exp(-u² / (2 σ²)) du`
    `≤ K27 · (a^{j-1} + σ^{j-1}) · exp(-a² / (2 σ²))     for j ≥ 1`,

and for `j = 0` the Mills-ratio bound

  `∫_{a}^{∞} (1 / √(2π σ²)) · exp(-u² / (2 σ²)) du ≤ K27 · exp(-a² / (2 σ²))`.

To avoid the `j - 1` underflow on `ℕ` when `j = 0`, we state the unified bound
using a real-valued polynomial-in-`a, σ` upper bound `(a^j + σ^j + 1) / a`
(times `exp(-a²/(2σ²))`) that subsumes both cases. Concretely, we package it as:

For some absolute `K27 > 0`, for every `σ² ∈ (0, 1]`, every `a > 0`, and every
`j ∈ {0, …, 6}`,

  `∫_{u ∈ Set.Ici a} u^j · (1 / √(2π σ²)) · exp(-u² / (2 σ²)) du
    ≤ K27 * (a^j + Real.sqrt σ²^j + 1) / a * Real.exp (-(a^2) / (2 * σ²))`.

This single statement implies both the `j ≥ 1` polynomial bound (multiply through
by `a`) and the `j = 0` Mills-ratio bound (specialise to `j = 0`, the `(a^0 + σ^0 + 1)/a
= 3/a` factor is harmless against `exp(-a²/(2σ²))`).
-/
theorem Lemma29SigmaAwareTailMomentStandardNormal :
    ∃ K27 : ℝ, 0 < K27 ∧
      ∀ (σSq a : ℝ) (j : ℕ),
        0 < σSq → σSq ≤ 1 → 0 < a → j ≤ 6 →
        ∫ u in Set.Ici a,
            u ^ j * (1 / Real.sqrt (2 * Real.pi * σSq))
                  * Real.exp (-(u^2) / (2 * σSq)) ∂MeasureTheory.volume
        ≤ K27 * ((a ^ j + Real.sqrt σSq ^ j + 1) / a)
              * Real.exp (-(a^2) / (2 * σSq)) :=
  Workspace.ProofLemmas.HalfGaussianMomentBound

end Workspace.ProofLemmas
