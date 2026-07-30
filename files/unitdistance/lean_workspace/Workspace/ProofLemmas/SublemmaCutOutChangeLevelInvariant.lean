import Mathlib
import Workspace.Types.CyclotomicCharacterFields
import Workspace.ProofLemmas.CutOutFieldLevelInvariant

open Complex
open Workspace.Types.CyclotomicCharacterFields

theorem SublemmaCutOutChangeLevelInvariant
    (r D : ℕ+) (ψ : DirichletCharacter ℂ (r : ℕ)) (hr : (r : ℕ) ∣ (D : ℕ)) :
    cutOutField D (DirichletCharacter.changeLevel hr ψ) = cutOutField r ψ :=
  CutOutFieldLevelInvariant r D ψ hr
