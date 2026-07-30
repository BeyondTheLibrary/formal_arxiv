import Mathlib
import Workspace.Types.DiscriminantsClassNumber
import Workspace.ProofLemmas.ClassNumberLeIdealCount
import Workspace.ProofLemmas.IdealCountByNormBound

open scoped NumberField
open Workspace.Types.DiscriminantsClassNumber

/--
`ClassNumberRootDiscriminantBound` (Proposition 3.7 / A.13):  there is an absolute
constant `C > 0` such that every number field `K` satisfies
`h(K) ≤ max{2, rd(K)}^{C · [K:ℚ]}`,  where `rd(K) = |D_K|^{1/[K:ℚ]}`.

Proved by composing the Minkowski reduction `ClassNumberLeIdealCount` (class number ≤ count of
nonzero ideals up to the Minkowski bound) with `IdealCountByNormBound` (that ideal count is
≤ `max{2, rd(K)}^{C·[K:ℚ]}`, the divisor-sum ideal-counting core).
-/
theorem ClassNumberRootDiscriminantBound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K],
      (classNumber K : ℝ)
        ≤ (max 2 (rootDiscriminant K)) ^ (C * (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := IdealCountByNormBound
  refine ⟨C, hC, ?_⟩
  intro K _ _
  exact le_trans (ClassNumberLeIdealCount K) (hbound K)
