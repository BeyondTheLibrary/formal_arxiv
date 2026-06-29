import Mathlib
import Workspace.ProofLemmas.SublemmaGenericSimpleZerosPaper

/-!
# Paper §6.1 — First reduction: an arbitrarily small coefficient perturbation
makes all real zeros simple.

This file formalizes the *first reduction* of Proposition 7's proof in
Moitra–Valiant (§6.1):

> "WLOG all zeros have multiplicity 1. (If some zero is tangent to the axis,
> perturb `a₁ ↦ a₁ − ε` for small ε: by sign-counting, all zeros of odd
> multiplicity remain (now of multiplicity 1) and each tangent zero with
> positive concavity splits into two simple zeros, so the total count does
> not decrease.)"

The analytic backbone of this reduction is the **genericity of simple zeros**:
for the one-parameter analytic family obtained by varying the first coefficient
`a₁` of a finite real Gaussian combination, the set of parameter values that
produce a *non-simple* real zero is countable
(`Workspace.ProofLemmas.SublemmaGenericSimpleZerosPaper`). Since any nondegenerate
open interval of reals is uncountable, every such interval contains a value
making all real zeros simple — in particular we can stay within an arbitrarily
small tolerance `ε` of any chosen base coefficient.

The combination is written in the *bare-exponential* normalization
`g(x) = a₁·exp(-(x-μ₀)²/(2τ₀)) + Σ_{i} a_rest(i)·exp(-(x-μ_{i+1})²/(2τ_{i+1}))`,
which matches the genericity statement exactly (the `1/√(2πσ²)` normalization
constants of a `SignedGaussianCombination` are absorbed into the coefficients,
so no generality is lost).

What is delivered here (Mathlib-only, no `sorry`, no new axioms beyond the
already-present genericity prior-work entry):
* `SignedGaussianFirstReduction` — existence of a perturbed first coefficient
  `a₁' ∈ (a₀, a₀+ε)` for which the perturbed family has only simple real zeros.

The *count-non-decreasing* half of the paper sentence is supplied separately by
`Workspace.PriorWork.SublemmaCoefficientPerturbationPreservesZeroCountPaper`
(Rolle / sign-counting), which gives `zeroCount S.density ≤ zeroCount S'.density`
for perturbations `a' ∈ [a_i, a_i + ε]` of a combination whose zeros are already
simple. Composing the two yields the full reduction; this file proves the
genericity half.
-/

namespace Workspace.ProofLemmas

open Workspace.PriorWork

/-- A nondegenerate open real interval `Ioo a₀ b` (`a₀ < b`) cannot be covered by
a countable set: there is always a point of the interval outside the set.

Uses `Cardinal.Real.Ioo_countable_iff : (Set.Ioo x y).Countable ↔ y ≤ x`. -/
theorem ioo_not_subset_of_countable
    {a₀ b : ℝ} (hab : a₀ < b) {B : Set ℝ} (hB : B.Countable) :
    ∃ y ∈ Set.Ioo a₀ b, y ∉ B := by
  by_contra h
  push_neg at h
  have hsub : Set.Ioo a₀ b ⊆ B := fun y hy => h y hy
  have hcc : (Set.Ioo a₀ b).Countable := hB.mono hsub
  rw [Cardinal.Real.Ioo_countable_iff] at hcc
  linarith

/-- **Paper §6.1 first reduction (genericity / all-zeros-simple form).**

For the analytic family `g` (a finite real Gaussian combination in the
bare-exponential normalization the paper uses) parameterized by its first
coefficient `a₁`, given ANY base value `a₀` and ANY tolerance `ε > 0`, there is
a perturbed first coefficient `a₁' ∈ (a₀, a₀ + ε)` (hence with
`0 < a₁' - a₀ < ε`, so within `ε` of `a₀`) for which the perturbed combination
has ONLY SIMPLE real zeros: every real zero `x` of `g` satisfies
`deriv g x ≠ 0`.

This is precisely the "make all zeros simple by a small coefficient
perturbation" step of the first reduction. It is obtained by intersecting the
*countable* bad-parameter set (from `SublemmaGenericSimpleZerosPaper`) with the
*uncountable* interval `(a₀, a₀ + ε)`. -/
theorem SignedGaussianFirstReduction
    (n : ℕ) (hn : 1 ≤ n)
    (μ τ : Fin n → ℝ)
    (h_τ_ne : ∀ i : Fin n, τ i ≠ 0)
    (a_rest : Fin (n - 1) → ℝ)
    (a₀ : ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ a₁' : ℝ, a₁' ∈ Set.Ioo a₀ (a₀ + ε) ∧
      ∀ x : ℝ,
        (a₁' * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
          + (Finset.univ : Finset (Fin (n - 1))).sum
              (fun i => a_rest i *
                Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                          (2 * τ ⟨i.val + 1, by omega⟩)))) = 0 →
        deriv (fun x : ℝ =>
          a₁' * Real.exp (-(x - μ ⟨0, by omega⟩)^2 / (2 * τ ⟨0, by omega⟩))
          + (Finset.univ : Finset (Fin (n - 1))).sum
              (fun i => a_rest i *
                Real.exp (-(x - μ ⟨i.val + 1, by omega⟩)^2 /
                          (2 * τ ⟨i.val + 1, by omega⟩)))) x ≠ 0 := by
  have hcount := SublemmaGenericSimpleZerosPaper n hn μ τ h_τ_ne a_rest
  have hab : a₀ < a₀ + ε := by linarith
  obtain ⟨a₁', hmem, hnot⟩ := ioo_not_subset_of_countable hab hcount
  refine ⟨a₁', hmem, ?_⟩
  -- `hnot : a₁' ∉ {a_1 | ∃ x, g x = 0 ∧ deriv g x = 0}` (the `let g` reduces
  -- definitionally to our explicit family), i.e. `¬ ∃ x, g x = 0 ∧ deriv g x = 0`.
  intro x hgx hderiv
  exact hnot ⟨x, hgx, hderiv⟩

end Workspace.ProofLemmas
