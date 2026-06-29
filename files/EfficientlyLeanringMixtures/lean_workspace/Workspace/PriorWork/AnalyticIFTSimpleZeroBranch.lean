-- Cited from: S. G. Krantz and H. R. Parks, *The Implicit Function Theorem:
-- History, Theory, and Applications*, Birkhäuser, 2002, Chapter 6
-- (real-analytic case of the Implicit Function Theorem).
-- Paper label: Krantz–Parks 2002, Implicit Function Theorem, Ch. 6 (real-analytic IFT)
-- NL statement: Real-analytic Implicit Function Theorem for simple zeros of a
-- one-parameter family. For a parametrized family `f : ℝ × ℝ → ℝ` that is jointly
-- continuous together with its partial derivative in the second variable
-- `(c, x) ↦ ∂f/∂x (c, x)`, if `f(0, x₀) = 0` and `(∂f/∂x)(0, x₀) ≠ 0` (a simple
-- zero at parameter `c = 0`), then there exist `δ > 0` and a continuous branch
-- `φ : {c : ℝ | |c| < δ} → ℝ` with `φ(0) = x₀`, `f(c, φ(c)) = 0` for all `|c| < δ`,
-- and `(∂f/∂x)(c, φ(c)) ≠ 0` (the simple-zero property is preserved along the
-- branch). The branch is the unique continuous local solution of `f(c, x) = 0`
-- near `(0, x₀)`. This is the textbook real-analytic IFT specialised to a
-- 1-parameter / 1-unknown setting.

import Mathlib

namespace Workspace.PriorWork

/--
**Prior work** (real-analytic Implicit Function Theorem; Krantz–Parks 2002,
*The Implicit Function Theorem*, Ch. 6).

For a parametrized family `f : ℝ × ℝ → ℝ` that is jointly continuous together
with its partial `x`-derivative `D : ℝ × ℝ → ℝ` (i.e. `D (c, x)` is the value
of `(∂/∂x) f(c, ·) x`), if at parameter `c = 0` there is a *simple* zero
`x₀` (meaning `f(0, x₀) = 0` and `D(0, x₀) ≠ 0`), then for all sufficiently
small `|c|` there is a continuous local branch `φ(c)` of zeros of `f(c, ·)`
with `φ(0) = x₀`, and the simple-zero property `D(c, φ(c)) ≠ 0` is preserved.

Moreover the branch is **locally unique**: there is a neighbourhood radius
`ε > 0` such that for every `|c| < δ`, `φ(c)` is the ONLY zero of `f(c, ·)`
within distance `ε` of `x₀`. This local-uniqueness clause is an intrinsic part
of the textbook real-analytic Implicit Function Theorem — the implicit solution
of `f(c, x) = 0` near `(0, x₀)` is, by construction, the unique solution in a
fixed product neighbourhood `{|c| < δ} × {|x − x₀| < ε}` (Krantz–Parks 2002,
*The Implicit Function Theorem*, Thm 6.1.2: existence AND uniqueness of the
implicit function on a product neighbourhood).

This is the textbook real-analytic IFT in 1 parameter / 1 unknown.
-/
axiom AnalyticIFTSimpleZeroBranch
    (f D : ℝ → ℝ → ℝ)
    (hf_cont : Continuous (fun p : ℝ × ℝ => f p.1 p.2))
    (hD_cont : Continuous (fun p : ℝ × ℝ => D p.1 p.2))
    (hD_eq : ∀ c x : ℝ, D c x = deriv (fun y => f c y) x)
    (x₀ : ℝ) (hzero : f 0 x₀ = 0) (hsimple : D 0 x₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Ioo (-δ) δ) ∧
      φ 0 = x₀ ∧
      (∀ c : ℝ, |c| < δ → f c (φ c) = 0) ∧
      (∀ c : ℝ, |c| < δ → D c (φ c) ≠ 0) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ c : ℝ, |c| < δ → ∀ x : ℝ,
        f c x = 0 → |x - x₀| < ε → x = φ c)

end Workspace.PriorWork
