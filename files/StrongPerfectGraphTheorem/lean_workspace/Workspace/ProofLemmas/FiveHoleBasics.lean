import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.HoleBasics

/-!
# Five-vertex holes

The printed proof of 14.1 (pp. 87–88) exhibits four separate five-vertex cycles

```
v-a-c-d-b-v      v-c₂-d₂-b₂-d₁-v      v-a₁-c₂-d₂-b₁-v      v-a₁-a₂-b₂-d₁-v
```

and each time concludes *"is an odd hole"*, i.e. a contradiction with `Berge G`.  This module
packages that step: `isHoleList_five` is the five-vertex analogue of
`CubeExtraction.isHoleList_four`, and `five_hole_absurd` is the one-shot form used at each of the
four call sites.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.FiveHoleBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

theorem nodup_five {x y z w t : V}
    (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w) (h4 : x ≠ t)
    (h5 : y ≠ z) (h6 : y ≠ w) (h7 : y ≠ t)
    (h8 : z ≠ w) (h9 : z ≠ t) (h10 : w ≠ t) :
    ([x, y, z, w, t] : List V).Nodup := by
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]

theorem nodup_four {x y z w : V} (h1 : x ≠ y) (h2 : x ≠ z) (h3 : x ≠ w)
    (h4 : y ≠ z) (h5 : y ≠ w) (h6 : z ≠ w) : ([x, y, z, w] : List V).Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

/-- The four-vertex analogue of `isHoleList_five`.  (Same statement as
`CubeExtraction.isHoleList_four`, repeated here because `CubeExtraction` imports 14.1 and this
module is used *in the proof of* 14.1.) -/
theorem isHoleList_four {G : SimpleGraph V} {x y z w : V}
    (hnd : ([x, y, z, w] : List V).Nodup)
    (e1 : G.Adj x y) (e2 : G.Adj y z) (e3 : G.Adj z w) (e4 : G.Adj w x)
    (n1 : ¬ G.Adj x z) (n2 : ¬ G.Adj y w) : IsHoleList G [x, y, z, w] := by
  have n1' : ¬ G.Adj z x := fun h => n1 h.symm
  have n2' : ¬ G.Adj w y := fun h => n2 h.symm
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [e1, e2, e3, e4, e1.symm, e2.symm, e3.symm, e4.symm, n1, n2, n1', n2']

/-- The five-vertex list `[x, y, z, w, t]` is a hole as soon as the five cyclically consecutive
pairs are edges and the five remaining pairs are non-edges. -/
theorem isHoleList_five {G : SimpleGraph V} {x y z w t : V}
    (hnd : ([x, y, z, w, t] : List V).Nodup)
    (e1 : G.Adj x y) (e2 : G.Adj y z) (e3 : G.Adj z w) (e4 : G.Adj w t) (e5 : G.Adj t x)
    (n1 : ¬ G.Adj x z) (n2 : ¬ G.Adj x w) (n3 : ¬ G.Adj y w) (n4 : ¬ G.Adj y t)
    (n5 : ¬ G.Adj z t) :
    IsHoleList G [x, y, z, w, t] := by
  have n1' : ¬ G.Adj z x := fun h => n1 h.symm
  have n2' : ¬ G.Adj w x := fun h => n2 h.symm
  have n3' : ¬ G.Adj w y := fun h => n3 h.symm
  have n4' : ¬ G.Adj t y := fun h => n4 h.symm
  have n5' : ¬ G.Adj t z := fun h => n5 h.symm
  refine ⟨by simp, hnd, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [e1, e2, e3, e4, e5, e1.symm, e2.symm, e3.symm, e4.symm, e5.symm,
      n1, n2, n3, n4, n5, n1', n2', n3', n4', n5']

/-- A Berge graph has no five-vertex hole: this is the paper's *"… is an odd hole"*. -/
theorem five_hole_absurd {G : SimpleGraph V} (hB : Berge G) {x y z w t : V}
    (hnd : ([x, y, z, w, t] : List V).Nodup)
    (e1 : G.Adj x y) (e2 : G.Adj y z) (e3 : G.Adj z w) (e4 : G.Adj w t) (e5 : G.Adj t x)
    (n1 : ¬ G.Adj x z) (n2 : ¬ G.Adj x w) (n3 : ¬ G.Adj y w) (n4 : ¬ G.Adj y t)
    (n5 : ¬ G.Adj z t) : False := by
  have h := hB.1 [x, y, z, w, t] (isHoleList_five hnd e1 e2 e3 e4 e5 n1 n2 n3 n4 n5)
  have h5 : holeLength ([x, y, z, w, t] : List V) = 5 := by simp [holeLength]
  rw [h5] at h
  exact (by decide : ¬ Even 5) h

end Workspace.ProofLemmas.FiveHoleBasics
