-- Cited from: Hummel-Gidas, Theorem 2.1 in reference [13] of Moitra-Valiant
-- Paper label: Theorem 8 of Moitra-Valiant
-- NL statement: For any f : ℝ → ℝ that is analytic on ℝ AND bounded (∃ C, ∀ x, |f x| ≤ C),
-- and has at most n zeros, and any σ² > 0, the function
-- g(x) := (f * N(0,σ²))(x) = ∫ y, f(y) · N(0,σ²)(x − y) dy has at most n zeros.
-- The boundedness hypothesis matches the paper (Hummel–Gidas: Section I 'Let f(x) be a
-- bounded function'; Theorem 2.1 is stated for 'a nonzero bounded solution'). Cited from:
-- Hummel–Gidas, Theorem 2.1 in reference [13] of Moitra–Valiant ('Zero Crossings and the
-- Heat Equation', Technical Report 111, Courant Institute, NYU, 1984). Paper label:
-- Theorem 8 of Moitra–Valiant (Thm 2.1 in [13]).
--
-- NOTE: The boundedness hypothesis `(∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C)` is REQUIRED: the
-- Hummel–Gidas result only holds for bounded functions, so it is included as an explicit
-- antecedent of the axiom.

import Mathlib
import Workspace.Types.ZeroCount
import Workspace.Types.GaussianConvolution

namespace Workspace.PriorWork

axiom HummelGidasZeroCount :
    ∀ (f : ℝ → ℝ), AnalyticOnNhd ℝ f Set.univ →
    (∃ C : ℝ, ∀ x : ℝ, |f x| ≤ C) →
    ∀ (n : ℕ), Workspace.Types.ZeroCount.hasAtMostNZeros f n →
    ∀ (σSq : ℝ) (h_pos : 0 < σSq),
        Workspace.Types.ZeroCount.hasAtMostNZeros
            (Workspace.Types.GaussianConvolution.convolveWithGaussian f σSq h_pos) n

end Workspace.PriorWork
