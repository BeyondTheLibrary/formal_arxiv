-- Cited from: this is NOT external prior work. It is the paper's OWN "unwrapping"
-- step in the proof of Lemma 7 (arXiv:2412.00674v1, lines 331-339: "We first show
-- that h is an 'unwrapped' version of f, in that |f(ξ)| ≤ Σ_s h(ξ+2πs)").
-- Faithfulness fix (2026-06-13): the previous statement asserted an EQUALITY
-- (`Hcirc B ξ = Σ_s Hlin B (ξ+2π s)`). The paper neither states nor uses an
-- equality here; it proves and uses the INEQUALITY `|f(ξ)| ≤ Σ_s h(ξ+2π s)`, which
-- arises from |f| ≤ (the periodised circular-modulus envelope) ≤ Σ_s h(ξ+2π s)
-- (the last step replaces circular convolution by ordinary convolution on ℝ, an
-- enlargement). The statement below is restated to that faithful inequality form.
-- Background references for the periodisation phenomenon: Folland, Real Analysis
-- (2nd ed.) §8.4; Stein-Shakarchi, Fourier Analysis Ch. 4 §4.
-- Paper label: Lemma 7 "unwrapping" / periodisation inequality
-- NL statement: Let H : ℝ → ℝ be non-negative, integrable, and supported on
-- [-π, π]. For every B ∈ ℕ with B ≥ 1, the B-fold circular convolution H^{⊛B}
-- (on ℝ/(2πℤ)) and B-fold linear convolution H^{*B} (on ℝ) satisfy: for every
-- ξ ∈ [-π, π], H^{⊛B}(ξ) ≤ ∑_{s ∈ ℤ} H^{*B}(ξ + 2π·s).
import Mathlib

/--
**Periodisation INEQUALITY for B-fold convolutions of a compactly-supported
function** (the paper's "unwrapping" step in Lemma 7).

For a non-negative, integrable function `H : ℝ → ℝ` supported on
`[-π, π]`, and for every `B ≥ 1`, the `B`-fold circular convolution
`Hcirc B = H ⊛ H ⊛ ⋯ ⊛ H` on `ℝ/(2πℤ)` and the `B`-fold linear convolution
`Hlin B = H * H * ⋯ * H` on `ℝ` satisfy the periodisation **bound**
  `Hcirc B (ξ) ≤ ∑_{s ∈ ℤ} Hlin B (ξ + 2π s)`
for every `ξ ∈ [-π, π]`.

This is exactly the form the paper proves and uses (arXiv:2412.00674v1, lines
331-339: `|f(ξ)| ≤ ∑_s h(ξ+2πs)`); it is NOT an equality. The non-negativity of
`H` (hence of every iterate) makes the periodised series an upper bound for the
circular convolution.

NOTE (faithfulness, 2026-06-13): restated from the previous unfaithful EQUALITY
form to the paper's actual INEQUALITY. It remains an `axiom`: a full proof is the
Poisson-summation / periodisation argument for compactly-supported iterated
convolutions, which is multi-day infrastructure not currently in the workspace.
It MUST be proved when the periodisation machinery is built; do NOT revert to the
equality form.

SATISFIABILITY FIX (2026-06-13): the previous statement quantified the two
recurrence premises over ALL `B : ℕ` with NO lower-bound guard. At `B = 0` this
forced `Hcirc 1 ξ = (1/2π)∫ Hcirc 0 · H` and `Hlin 1 ξ = ∫ Hlin 0 · H`, which —
combined with the bases `Hcirc 1 = H`, `Hlin 1 = H` — would require `Hcirc 0`
(resp. `Hlin 0`) to act as a circular (resp. linear) Dirac identity, impossible
for an honest `ℝ → ℝ` function. The premises were therefore UNSATISFIABLE and the
axiom could never be instantiated. The recurrences are now guarded by `1 ≤ B`, so
they only constrain `B ≥ 1` (matching the base at `B = 1`). This is the faithful
form: the convolution-power recurrence naturally starts from the 1-fold base, and
the guard does NOT weaken the conclusion in any way.
-/
axiom CircularConvolutionAsPeriodisation :
    ∀ (H : ℝ → ℝ),
      (∀ x, 0 ≤ H x) →
      MeasureTheory.Integrable H →
      (∀ x, |x| > Real.pi → H x = 0) →
      ∀ (Hcirc Hlin : ℕ → ℝ → ℝ),
        -- B-fold circular convolution: base case and recurrence on R/(2πZ).
        -- The recurrence is guarded by `1 ≤ B` (so it links level B≥1 to B+1
        -- and never constrains the meaningless level 0); see SATISFIABILITY FIX.
        (Hcirc 1 = H) →
        (∀ B : ℕ, 1 ≤ B → ∀ ξ : ℝ,
            Hcirc (B + 1) ξ
              = (1 / (2 * Real.pi)) *
                  ∫ η in (-Real.pi)..Real.pi, Hcirc B η * H (ξ - η)) →
        -- B-fold linear convolution: base case and recurrence on R (also `1 ≤ B`).
        (Hlin 1 = H) →
        (∀ B : ℕ, 1 ≤ B → ∀ ξ : ℝ,
            Hlin (B + 1) ξ = ∫ η, Hlin B η * H (ξ - η)) →
        ∀ (B : ℕ), 1 ≤ B →
          ∀ ξ : ℝ, |ξ| ≤ Real.pi →
            Hcirc B ξ ≤ ∑' s : ℤ, Hlin B (ξ + 2 * Real.pi * (s : ℝ))
