import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.CutOutFieldEqCyclicCubic

open Workspace.Types.CyclotomicCharacterFields

/-- The field cut out by an order-3 Dirichlet character of prime conductor
`r ≡ 1 (mod 3)` is the cyclic cubic subfield of `ℚ(ζ_r)`. -/
theorem SublemmaCutOutFieldCubicChar
    (r : ℕ+) (hr : (r : ℕ).Prime) (hr3 : (r : ℕ) % 3 = 1)
    (ψ : DirichletCharacter ℂ (r : ℕ)) (hψ : orderOf ψ = 3) :
    cutOutField r ψ = cyclicCubicSubfield r hr hr3 :=
  CutOutFieldEqCyclicCubic r hr hr3 ψ hψ
