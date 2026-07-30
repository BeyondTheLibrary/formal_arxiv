import Mathlib
import Workspace.Types.CMAdjoinI
import Workspace.Types.AdmissibleDatum

/-!
# Minkowski-embedding window setup (Section 2.1)

This file formalises the Minkowski-embedding *window* setup of Section 2.1 of the paper,
relative to a totally real number field `L` of degree `f` and its CM extension
`K = L(i)` (as bundled in `CMAdjoinI` / an `AdmissibleDatum`), together with a positive
integer denominator `DD` (in the paper `DD = D = Q ^ 2`).

Ingredients (definitions only — Lemmas 2.4–2.6 are stated elsewhere against these):

* `EmbeddingSelection L K f` : a choice of one complex embedding `σ_r : K → ℂ` per real
  embedding of `L`; the restrictions `σ_r|_L` form a bijection onto the (all real)
  embeddings of `L` into `ℂ`.
* `minkowskiMap sel : K →+* (Fin f → ℂ)` : the Minkowski map `Φ(x) = (σ_1 x, …, σ_f x)`.
* `lattice sel DD : AddSubgroup (Fin f → ℂ)` : the lattice `Λ = Φ(DD⁻¹ 𝓞_K)`.
* `supNorm z = ‖z‖` : the sup norm `‖z‖_∞ = max_r |z_r|` (the default `Pi` norm).
* `window R` : the polydisc `B_R = {z | ∀ r, |z_r| ≤ R}`.
* `Xset sel DD R a = (a + Λ) ∩ B_R`, `Ncount = |X_a|`, `Ecount U a = #{(x,x') ∈ X_a² | x'-x ∈ U}`.
* `discArea R = π R²`, `overlapArea R` = area of the intersection of two radius-`R` discs at
  centre distance `1`, `rho R = overlapArea R / discArea R`.
-/

open scoped NumberField
open MeasureTheory

namespace Workspace.Types.MinkowskiWindow

set_option maxHeartbeats 400000

/-! ## The embedding selection -/

section EmbeddingSelection

variable (L K : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K]

/-- An **embedding selection** of size `f`: a choice, for each of the `f` real embeddings of
the totally real field `L`, of one complex embedding `σ_r : K → ℂ` of `K` extending it.

The defining property is that the restriction map `r ↦ σ_r|_L` is a *bijection* onto the set
of all embeddings `L → ℂ` (there are exactly `f = [L : ℚ]` of them since `L` is totally real),
and each restriction has real image (`IsReal`, i.e. it is fixed by complex conjugation).  This
captures "one extension chosen per real place of `L`". -/
structure EmbeddingSelection (f : ℕ) where
  /-- The chosen complex embedding of `K` for each `r`. -/
  sigma : Fin f → (K →+* ℂ)
  /-- The restrictions to `L` biject onto the embeddings `L → ℂ`. -/
  restrict_bijective :
    Function.Bijective (fun r : Fin f => (sigma r).comp (algebraMap L K))
  /-- Each restriction to `L` has real image (`L` is totally real). -/
  restrict_isReal :
    ∀ r : Fin f, NumberField.ComplexEmbedding.IsReal ((sigma r).comp (algebraMap L K))

end EmbeddingSelection

/-! ## The Minkowski map and lattice -/

section Maps

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- The **Minkowski map** `Φ : K → ℂ^f`, `Φ(x) = (σ_1 x, …, σ_f x)`, as a ring homomorphism
into the product `Fin f → ℂ`. -/
noncomputable def minkowskiMap (sel : EmbeddingSelection L K f) : K →+* (Fin f → ℂ) :=
  Pi.ringHom sel.sigma

/-- The additive homomorphism `𝓞_K → ℂ^f`, `y ↦ Φ(y / DD)`, whose range is the lattice
`Λ = Φ(DD⁻¹ 𝓞_K)`. -/
noncomputable def latticeHom (sel : EmbeddingSelection L K f) (DD : ℕ) :
    (𝓞 K) →+ (Fin f → ℂ) :=
  (minkowskiMap sel).toAddMonoidHom.comp
    ((AddMonoidHom.mulRight ((DD : K)⁻¹)).comp (algebraMap (𝓞 K) K).toAddMonoidHom)

/-- The **lattice** `Λ = Φ(DD⁻¹ 𝓞_K)`, the image under the Minkowski map of the fractional
`𝓞_K`-module `DD⁻¹ 𝓞_K = {x : K | ∃ y ∈ 𝓞_K, x = y / DD}`, as an additive subgroup of
`ℂ^f`. -/
noncomputable def lattice (sel : EmbeddingSelection L K f) (DD : ℕ) :
    AddSubgroup (Fin f → ℂ) :=
  (latticeHom sel DD).range

end Maps

/-! ## Sup norm and window -/

section Window

variable {f : ℕ}

/-- The **window** `B_R = {z | ∀ r, |z_r| ≤ R}`, a product of `f` closed discs of radius `R`. -/
def window (R : ℝ) : Set (Fin f → ℂ) := {z | ∀ r, ‖z r‖ ≤ R}

end Window

/-! ## Coset point counts -/

section Counts

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

/-- The point set `X_a = (a + Λ) ∩ B_R` of a coset `a + Λ` intersected with the window. -/
def Xset (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ) (a : Fin f → ℂ) :
    Set (Fin f → ℂ) :=
  {z | z - a ∈ lattice sel DD} ∩ window R

/-- The count `N_a = |X_a|` of lattice-coset points in the window. -/
noncomputable def Ncount (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (a : Fin f → ℂ) : ℕ :=
  (Xset sel DD R a).ncard

/-- The count `E_a(U) = #{(x, x') ∈ X_a × X_a : x' - x ∈ U}` of ordered pairs in `X_a` whose
difference lies in the finite set `U`. -/
noncomputable def Ecount (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (U : Finset (Fin f → ℂ)) (a : Fin f → ℂ) : ℕ :=
  {p : (Fin f → ℂ) × (Fin f → ℂ) |
      p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U}.ncard

end Counts

/-! ## Disc-overlap areas -/

section Areas

/-- The area `b(R) = π R²` of a disc of radius `R`. -/
noncomputable def discArea (R : ℝ) : ℝ := Real.pi * R ^ 2

/-- The area `a(R)` of the intersection of two closed discs of radius `R` whose centres are at
distance `1` (via the 2-dimensional Lebesgue/volume measure on `ℂ`). -/
noncomputable def overlapArea (R : ℝ) : ℝ :=
  (volume (Metric.closedBall (0 : ℂ) R ∩ Metric.closedBall (1 : ℂ) R)).toReal

/-- The ratio `ρ_R = a(R) / b(R)`. -/
noncomputable def rho (R : ℝ) : ℝ := overlapArea R / discArea R

end Areas

end Workspace.Types.MinkowskiWindow
