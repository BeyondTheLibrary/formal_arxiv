import Mathlib
import Workspace.Types.Core
import Workspace.Statements.S02.Thm_2_3

/-!
# A hole cannot carry an odd number `≥ 3` of `Y`-complete edges

Sections 18 and 16 end an argument with *"there is an odd number (`≥ 3`) of `Y`-complete edges
in `C`, contrary to 2.3"* over and over: it is the last sentence of the proof of 18.4, it
appears inside the proof of 18.5 (*"it follows that there is an odd number (`≥ 3`) of
`Y`-complete edges in `C`, contrary to 2.3"*), and it appears **three** times in the proof of
18.6 — once in claim (1), once in the first case of claim (2), and once in the closing
paragraph.

The step is not immediate from 2.3, which offers a disjunction:

> if `P` is a hole, then either there are an even number of `X`-complete edges in `P`, or there
> are exactly two `X`-complete vertices and they are adjacent.

An odd count kills the first alternative, so the second holds; but then *every* `Y`-complete
edge has both ends among those two vertices, so there is at most one such edge — and `3 ≤` the
count is contradicted.  `not_odd_ge_three_yEdges` packages exactly that.

`yEdges` is the paper's *number of `Y`-complete edges*, in the `Set (Sym2 V)` form used by
every §2 and §18 statement, so a caller can hand its goal over unchanged.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HoleYEdgeParity

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set of `Y`-complete edges of a list of vertices, in the form every §2/§18 statement
uses.  For a path or hole `C` this is the paper's set of `Y`-complete edges of `C`, each
counted once (the entries are *unordered* pairs). -/
def yEdges (G : SimpleGraph V) (Y : Set V) (C : List V) : Set (Sym2 V) :=
  {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}

/-- If a hole has exactly two `Y`-complete vertices then it has at most one `Y`-complete
edge. -/
theorem yEdges_ncard_le_one_of_pair {G : SimpleGraph V} {Y : Set V} {C : List V}
    {c d : V} (hset : {w : V | w ∈ C ∧ VertexComplete G w Y} = {c, d}) :
    (yEdges G Y C).ncard ≤ 1 := by
  have hsub : yEdges G Y C ⊆ {s(c, d)} := by
    rintro e ⟨u, hu, v, hv, rfl, hadj, huY, hvY⟩
    have hum : u ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hu, huY⟩
    have hvm : v ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hv, hvY⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hum hvm
    have huv : u ≠ v := hadj.ne
    rcases hum with rfl | rfl <;> rcases hvm with rfl | rfl
    · exact absurd rfl huv
    · exact rfl
    · exact Set.mem_singleton_iff.mpr (Sym2.eq_swap)
    · exact absurd rfl huv
  calc (yEdges G Y C).ncard ≤ ({s(c, d)} : Set (Sym2 V)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 1 := Set.ncard_singleton _

/-- **The engine behind *"contrary to 2.3"*.**  In a Berge graph, a hole disjoint from an
anticonnected set `Y` cannot carry an odd number of `Y`-complete edges once that number is at
least three: 2.3 forces "exactly two `Y`-complete vertices, and they are adjacent", which
leaves at most one `Y`-complete edge. -/
theorem not_odd_ge_three_yEdges {G : SimpleGraph V} (hBerge : Berge G) {Y : Set V}
    (hY : AnticonnectedSet G Y) {C : List V} (hC : IsHoleList G C)
    (hCY : ∀ w ∈ C, w ∉ Y)
    (hodd : (yEdges G Y C).ncard % 2 = 1) (h3 : 3 ≤ (yEdges G Y C).ncard) : False := by
  have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hY C
    (Or.inr hC) hCY).2 hC
  rcases h23 with heven | ⟨c, d, hset, -, -⟩
  · obtain ⟨m, hm⟩ := heven
    simp only [yEdges] at hodd hm
    omega
  · have := yEdges_ncard_le_one_of_pair (G := G) (Y := Y) (C := C) hset
    omega

/-- The same statement with the hypothesis phrased as `Odd`, which is the shape 18.4 and 18.6
deliver. -/
theorem not_odd_ge_three_yEdges' {G : SimpleGraph V} (hBerge : Berge G) {Y : Set V}
    (hY : AnticonnectedSet G Y) {C : List V} (hC : IsHoleList G C)
    (hCY : ∀ w ∈ C, w ∉ Y)
    (hodd : Odd (yEdges G Y C).ncard) (h3 : 3 ≤ (yEdges G Y C).ncard) : False :=
  not_odd_ge_three_yEdges hBerge hY hC hCY (Nat.odd_iff.mp hodd) h3

/-- Unfolding `yEdges` at a call site whose goal is written out in full. -/
theorem yEdges_eq (G : SimpleGraph V) (Y : Set V) (C : List V) :
    yEdges G Y C =
      {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v} := rfl

end Workspace.ProofLemmas.HoleYEdgeParity
