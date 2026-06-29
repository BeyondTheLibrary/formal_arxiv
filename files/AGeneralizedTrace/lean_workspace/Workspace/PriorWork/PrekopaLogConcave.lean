-- Cited from: Prékopa, A. (1973). On logarithmic concave measures and functions. Acta Sci. Math. (Szeged) 34, 335-343. Also Leindler, L. (1972). On a certain converse of Hölder's inequality II. Acta Sci. Math. (Szeged) 33, 217-223. The convolution-preserves-log-concavity statement (the form we use) is the Prékopa-Leindler inequality applied to convolutions.
-- Paper label: [Prekopa 1973]
-- NL statement: (a) [Stability under convolution] Let f, g : R → [0,∞) be log-concave, integrable functions on R (i.e. log f, log g are concave wherever finite, with -∞ allowed). Then their convolution (f * g)(x) := ∫_R f(y) g(x-y) dy is also log-concave on R. (b) [Pointwise bound from log-concavity + integral] Consequently, if h : R → [0,∞) is log-concave and integrable, and ∫_{|t| ≥ a} h(t) dt ≤ M for some a > 0, M > 0, then h is monotone non-increasing on [a, ∞) (eventually) and pointwise h(t) ≤ M / Δ on intervals of length Δ in [a, ∞) where h is still non-increasing.
import Mathlib

open MeasureTheory

/--
**Prékopa-Leindler (1973, applied to convolutions): convolution of log-concave
densities is log-concave.**

Given two non-negative integrable log-concave functions `f, g : ℝ → ℝ`
(log-concavity expressed in the multiplicative form
`f x ^ t * f y ^ (1-t) ≤ f (t*x + (1-t)*y)` for `t ∈ [0,1]`),
their convolution `(f * g)(x) := ∫ z, f z * g (x - z)` is itself log-concave.
-/
axiom PrekopaLogConcave_convolution :
    ∀ (f g : ℝ → ℝ),
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      Integrable f → Integrable g →
      (∀ x y t, 0 ≤ t → t ≤ 1 →
        f x ^ t * f y ^ (1 - t) ≤ f (t * x + (1 - t) * y)) →
      (∀ x y t, 0 ≤ t → t ≤ 1 →
        g x ^ t * g y ^ (1 - t) ≤ g (t * x + (1 - t) * y)) →
      ∀ x y t, 0 ≤ t → t ≤ 1 →
        (∫ z, f z * g (x - z)) ^ t * (∫ z, f z * g (y - z)) ^ (1 - t)
          ≤ (∫ z, f z * g ((t * x + (1 - t) * y) - z))

-- NOTE (faithfulness prune, 2026-06-13): the former `PrekopaLogConcave_pointwise`
-- axiom was REMOVED. It was NOT the Prékopa–Leindler inequality but the paper's
-- OWN step in the proof of Lemma 7 ("h is monotone decreasing away from 0, hence
-- h(ξ') ≤ ∫_{ξ'-1}^{ξ'} h"), mislabeled as prior work, and its stated form (free
-- `Δ` with only a global tail hypothesis) was unsound. It was orphaned (no
-- consumers). The genuine Prékopa–Leindler statement (`_convolution` above) is kept.
-- The faithful Lemma-7 pointwise step must be PROVED (monotone ⇒ pointwise ≤ Δ=1
-- cumulative tail) when Lemma 7 is formalized.
