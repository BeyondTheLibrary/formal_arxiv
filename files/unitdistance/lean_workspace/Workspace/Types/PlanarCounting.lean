import Mathlib

/-!
# PlanarCounting

Unit-distance counting functions of the paper "Planar Point Sets with Many Unit
Distances".

* `nu P` counts, for a finite set `P` of points in a (pseudo-)metric space, the
  number of **unordered** pairs `{x, y}` of **distinct** points of `P` at distance
  exactly `1`.
* `nuMax n` is the maximum of `nu P` over all `n`-point subsets `P` of the Euclidean
  plane `EuclideanSpace ℝ (Fin 2)`.
* `toPlane` / `embedFinset` provide the standard isometric identification of the
  complex plane `ℂ` with `EuclideanSpace ℝ (Fin 2)`, so that `nu` computed on a
  `Finset ℂ` agrees with `nu` on its image in the Euclidean plane.
-/

open scoped Classical

namespace Workspace.Types.PlanarCounting

variable {X : Type*} [PseudoMetricSpace X]

/-- The symmetric distance function packaged as a map out of `Sym2`, so that it can
be evaluated on an *unordered* pair. -/
noncomputable def distSym2 : Sym2 X → ℝ :=
  Sym2.lift ⟨dist, fun x y => dist_comm x y⟩

@[simp] lemma distSym2_mk (x y : X) : distSym2 (s(x, y)) = dist x y :=
  Sym2.lift_mk _ _ _

/-- `nu P` is the number of unordered pairs `{x, y}` of distinct points of `P` at
distance exactly `1`. Encoded as the number of non-diagonal elements of `Finset.sym2 P`
(each unordered pair drawn from `P` occurs exactly once there) whose two endpoints are
at distance `1`. -/
noncomputable def nu (P : Finset X) : ℕ :=
  (P.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1)).card

/-- The maximum number of unit distances realized by an `n`-point set in the Euclidean
plane `ℝ² = EuclideanSpace ℝ (Fin 2)`. Defined as the supremum, over all `n`-point
subsets `P`, of `nu P`. Because `nu P ≤ P.card.choose 2 = n.choose 2` the set of values
is bounded above, and it is nonempty for every `n` (the plane is infinite), so this
supremum is attained and finite. -/
noncomputable def nuMax (n : ℕ) : ℕ :=
  sSup {k : ℕ | ∃ P : Finset (EuclideanSpace ℝ (Fin 2)), P.card = n ∧ nu P = k}

/-- The standard linear isometry identifying the complex plane `ℂ` with the Euclidean
plane `EuclideanSpace ℝ (Fin 2)`, sending `z` to `(z.re, z.im)`. It preserves distances,
so it carries unit-distance configurations to unit-distance configurations. -/
noncomputable def toPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.isometryOfOrthonormal (EuclideanSpace.basisFun (Fin 2) ℝ)

/-- Transport a finite set of complex numbers to a finite set of points of the Euclidean
plane via the isometry `toPlane`. Bridges `nu` on `Finset ℂ` with `nu` on
`Finset (EuclideanSpace ℝ (Fin 2))`. -/
noncomputable def embedFinset (P : Finset ℂ) : Finset (EuclideanSpace ℝ (Fin 2)) :=
  P.image toPlane

end Workspace.Types.PlanarCounting
