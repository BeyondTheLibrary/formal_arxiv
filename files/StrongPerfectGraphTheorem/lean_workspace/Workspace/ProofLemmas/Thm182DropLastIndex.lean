import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# `pₙ₋₁` and `pₙ₋₂` as indices

The numbered statements of §18 pin down the paper's `pₙ₋₁`, `pₙ₋₂` by
`p.dropLast.getLast?` and `p.dropLast.dropLast.getLast?` (the subscript minus is not
a Lean identifier character).  Every *proof* wants them as `p[p.length - 2]` and
`p[p.length - 3]`, because path adjacency and injectivity are stated by index.  The
two translations are recorded here once.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm182DropLastIndex

variable {V : Type*}

/-- The last vertex of `p.dropLast` is `p[p.length - 2]`. -/
theorem dropLast_getLast?_eq (p : List V) (h : 2 ≤ p.length) :
    p.dropLast.getLast? = some (p[p.length - 2]'(by omega)) := by
  have hlen : p.dropLast.length = p.length - 1 := by simp
  have hlt : p.dropLast.length - 1 < p.dropLast.length := by omega
  have hidx : p.dropLast.length - 1 = p.length - 2 := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlt, List.getElem_dropLast]
  simp only [hidx]

/-- The last vertex of `p.dropLast.dropLast` is `p[p.length - 3]`. -/
theorem dropLast_dropLast_getLast?_eq (p : List V) (h : 3 ≤ p.length) :
    p.dropLast.dropLast.getLast? = some (p[p.length - 3]'(by omega)) := by
  have hlen : p.dropLast.length = p.length - 1 := by simp
  have h2 : 2 ≤ p.dropLast.length := by omega
  have hstep := dropLast_getLast?_eq p.dropLast h2
  have hidx : p.dropLast.length - 2 = p.length - 3 := by omega
  rw [hstep, List.getElem_dropLast]
  simp only [hidx]

end Workspace.ProofLemmas.Thm182DropLastIndex
