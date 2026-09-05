import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HyperprismBasics

/-!
# Rung structure of a hyperprism (P2 of the 10.6 decomposition)

The proof of **10.6** builds a *strictly larger* hyperprism three separate times — once in
the `X ∩ C₁ ≠ ∅` block, once in the `n` even block and once in the `n` odd block — and each
time the verification runs through the same paragraph:

> *"Let `C'ᵢ` be the union of the interiors of the `i`-rungs between `A'ᵢ` and `B'ᵢ`, and
> `C''ᵢ` the union of the interiors of the `i`-rungs between `A''ᵢ` and `B''ᵢ`.  We observe
> that `Cᵢ = C'ᵢ ∪ C''ᵢ`.  Moreover, `C'ᵢ ∩ C''ᵢ = ∅`, for **otherwise there would be an
> `i`-rung between `A'ᵢ` and `B''ᵢ`**.  For the same reason there are no edges between
> `A'ᵢ ∪ C'ᵢ` and `C''ᵢ ∪ B''ᵢ`, and no edges between `A''ᵢ ∪ C''ᵢ` and `C'ᵢ ∪ B'ᵢ`."*
> (printed p. 61; repeated verbatim on p. 62)

The bold clause is the only real content, and it is what this module supplies.

* `exists_rung_of_connected` — *if `W ⊆ Sᵢ` is connected, meets `Aᵢ` only in `x` and `Bᵢ`
  only in `w`, then there is an `i`-rung from `x` to `w`.*  (Extract an induced path inside
  `W`; its interior avoids `Aᵢ` and `Bᵢ`, hence lies in `Cᵢ`.)
* `rung_dropLast_*` / `rung_tail_*` — the two halves of a rung that the paper glues:
  `V(P) \ {B-end}` misses `Bᵢ` entirely and meets `Aᵢ` only in the `A`-end, and dually.
* **`exists_rung_join`** — the packaged move: two `i`-rungs `P` (ends `x,y`) and `Q` (ends
  `z,w`) whose `A`-half and `B`-half are *linked* (share a vertex, or are joined by an edge)
  yield an `i`-rung from `x` to `w`.  All five instances of the paragraph above — the
  `C' ∩ C'' = ∅` one and the four `Anticomplete` ones — are this lemma with a different link.
* `exists_rung_from_A` / `exists_rung_from_B` — *every vertex of `Aᵢ` is the `A`-end of some
  `i`-rung* — and `mem_C_iff` — *`Cᵢ` is exactly the union of the rung interiors*.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismRungStructure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-! ### `dropLast` and `tail` of a path -/

theorem mem_tail_iff_of_pathFrom {p : List V} {u v : V} (h : IsPathFrom G p u v) {x : V} :
    x ∈ p.tail ↔ (x ∈ p ∧ x ≠ u) := by
  cases p with
  | nil => exact absurd rfl h.1.1
  | cons a t =>
    have ha : a = u := by simpa using h.2.1
    have hnd : (a :: t).Nodup := PathBasics.path_nodup h.1
    simp only [List.tail_cons]
    constructor
    · intro hx
      refine ⟨List.mem_cons_of_mem _ hx, ?_⟩
      intro hxu
      have hxa : x = a := hxu.trans ha.symm
      rw [hxa] at hx
      exact (List.nodup_cons.mp hnd).1 hx
    · rintro ⟨hx, hxu⟩
      rcases List.mem_cons.mp hx with hxa | hx'
      · exact absurd (hxa.trans ha) hxu
      · exact hx'

theorem mem_dropLast_iff_of_pathFrom {p : List V} {u v : V} (h : IsPathFrom G p u v) {x : V} :
    x ∈ p.dropLast ↔ (x ∈ p ∧ x ≠ v) := by
  have hne : p ≠ [] := h.1.1
  rw [PathBasics.mem_dropLast_iff (PathBasics.path_nodup h.1) hne]
  have hv : p.getLast hne = v := by
    have hg := h.2.2
    rw [List.getLast?_eq_some_getLast hne] at hg
    exact Option.some_injective _ hg
  rw [hv]

theorem isPathList_dropLast {p : List V} (h : IsPathList G p) (hlen : 2 ≤ p.length) :
    IsPathList G p.dropLast := by
  rw [List.dropLast_eq_take]
  exact PathBasics.isPathList_take h (by omega)

theorem isPathList_tail {p : List V} (h : IsPathList G p) (hlen : 2 ≤ p.length) :
    IsPathList G p.tail := by
  rw [← List.drop_one]
  exact PathBasics.isPathList_drop h (by omega)

/-! ### Extracting a rung from a connected set -/

/-- **The engine.**  A connected subset of `Sᵢ` that meets `Aᵢ` only in `x` and `Bᵢ` only in
`w` contains an `i`-rung from `x` to `w`. -/
theorem exists_rung_of_connected (i : Fin 3) {W : Set V}
    (hWconn : ConnectedSet G W) (hWS : ∀ z ∈ W, z ∈ A i ∪ B i ∪ C i)
    {x w : V} (hx : x ∈ W) (hxA : x ∈ A i) (hw : w ∈ W) (hwB : w ∈ B i)
    (hWA : ∀ z ∈ W, z ∈ A i → z = x) (hWB : ∀ z ∈ W, z ∈ B i → z = w) :
    ∃ p : List V, IsRungFrom G A B C i p x w := by
  obtain ⟨p, hp, hpW⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hWconn hx hw
  refine ⟨p, hxA, hwB, hp, ?_⟩
  intro z hz
  rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hz
  obtain ⟨hzp, hzx, hzw⟩ := hz
  rcases hWS z (hpW z hzp) with (hzA | hzB) | hzC
  · exact absurd (hWA z (hpW z hzp) hzA) hzx
  · exact absurd (hWB z (hpW z hzp) hzB) hzw
  · exact hzC

/-! ### The two halves of a rung -/

section Halves

variable {i : Fin 3} {P : List V} {x y : V}

theorem rung_dropLast_connected (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) : ConnectedSet G {z : V | z ∈ P.dropLast} :=
  InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (isPathList_dropLast hP.2.2.1.1 (rung_two_le_length hH hP))

theorem rung_tail_connected (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) : ConnectedSet G {z : V | z ∈ P.tail} :=
  InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
    (isPathList_tail hP.2.2.1.1 (rung_two_le_length hH hP))

theorem mem_of_mem_dropLast (hP : IsRungFrom G A B C i P x y) {z : V}
    (hz : z ∈ P.dropLast) : z ∈ P := ((mem_dropLast_iff_of_pathFrom hP.2.2.1).mp hz).1

theorem mem_of_mem_tail (hP : IsRungFrom G A B C i P x y) {z : V}
    (hz : z ∈ P.tail) : z ∈ P := ((mem_tail_iff_of_pathFrom hP.2.2.1).mp hz).1

/-- The `A`-half of a rung misses `Bᵢ` altogether. -/
theorem rung_dropLast_notMem_B (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) {z : V} (hz : z ∈ P.dropLast) : z ∉ B i := by
  intro hzB
  exact ((mem_dropLast_iff_of_pathFrom hP.2.2.1).mp hz).2
    (rung_eq_B hH hP (mem_of_mem_dropLast hP hz) hzB)

/-- The `B`-half of a rung misses `Aᵢ` altogether. -/
theorem rung_tail_notMem_A (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) {z : V} (hz : z ∈ P.tail) : z ∉ A i := by
  intro hzA
  exact ((mem_tail_iff_of_pathFrom hP.2.2.1).mp hz).2
    (rung_eq_A hH hP (mem_of_mem_tail hP hz) hzA)

theorem mem_dropLast_A_end (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) : x ∈ P.dropLast :=
  (mem_dropLast_iff_of_pathFrom hP.2.2.1).mpr
    ⟨(PathBasics.isPathFrom_ends_mem hP.2.2.1).1, rung_ends_ne hH hP⟩

theorem mem_tail_B_end (hH : IsHyperprism G A B C)
    (hP : IsRungFrom G A B C i P x y) : y ∈ P.tail :=
  (mem_tail_iff_of_pathFrom hP.2.2.1).mpr
    ⟨(PathBasics.isPathFrom_ends_mem hP.2.2.1).2, fun h => rung_ends_ne hH hP h.symm⟩

theorem mem_dropLast_of_mem_interior (hP : IsRungFrom G A B C i P x y) {z : V}
    (hz : z ∈ SPGT.interior P) : z ∈ P.dropLast := by
  rw [PathBasics.mem_interior_iff_of_pathFrom hP.2.2.1] at hz
  exact (mem_dropLast_iff_of_pathFrom hP.2.2.1).mpr ⟨hz.1, hz.2.2⟩

theorem mem_tail_of_mem_interior (hP : IsRungFrom G A B C i P x y) {z : V}
    (hz : z ∈ SPGT.interior P) : z ∈ P.tail := by
  rw [PathBasics.mem_interior_iff_of_pathFrom hP.2.2.1] at hz
  exact (mem_tail_iff_of_pathFrom hP.2.2.1).mpr ⟨hz.1, hz.2.1⟩

end Halves

/-! ### Joining the `A`-half of one rung to the `B`-half of another -/

/-- **The packaged form of the paper's *"otherwise there would be an `i`-rung between `A'ᵢ`
and `B''ᵢ`"*.**  Two `i`-rungs whose `A`-half and `B`-half are linked — they share a vertex,
or an edge joins them — yield an `i`-rung from the first one's `A`-end to the second one's
`B`-end. -/
theorem exists_rung_join (hH : IsHyperprism G A B C) {i : Fin 3} {P Q : List V}
    {x y z w : V} (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C i Q z w)
    (hlink : (∃ v, v ∈ P.dropLast ∧ v ∈ Q.tail) ∨
      (∃ s ∈ P.dropLast, ∃ t ∈ Q.tail, G.Adj s t)) :
    ∃ p : List V, IsRungFrom G A B C i p x w := by
  refine exists_rung_of_connected i
    (W := {u : V | u ∈ P.dropLast} ∪ {u : V | u ∈ Q.tail}) ?_ ?_ ?_ hP.1 ?_ hQ.2.1 ?_ ?_
  · refine ConnectedSetUnionAttach.connectedSet_union (rung_dropLast_connected hH hP)
      (rung_tail_connected hH hQ) ?_
    rcases hlink with ⟨v, hv1, hv2⟩ | ⟨s, hs, t, ht, hadj⟩
    · exact Or.inl ⟨v, hv1, hv2⟩
    · exact Or.inr ⟨s, hs, t, ht, hadj⟩
  · rintro u (hu | hu)
    · exact rung_mem_S hP u (mem_of_mem_dropLast hP hu)
    · exact rung_mem_S hQ u (mem_of_mem_tail hQ hu)
  · exact Or.inl (mem_dropLast_A_end hH hP)
  · exact Or.inr (mem_tail_B_end hH hQ)
  · rintro u (hu | hu) huA
    · exact rung_eq_A hH hP (mem_of_mem_dropLast hP hu) huA
    · exact absurd huA (rung_tail_notMem_A hH hQ hu)
  · rintro u (hu | hu) huB
    · exact absurd huB (rung_dropLast_notMem_B hH hP hu)
    · exact rung_eq_B hH hQ (mem_of_mem_tail hQ hu) huB

/-- The paper's *"`C'ᵢ ∩ C''ᵢ = ∅`, for otherwise there would be an `i`-rung between `A'ᵢ` and
`B''ᵢ`"*: a vertex interior to two rungs splices them. -/
theorem exists_rung_splice (hH : IsHyperprism G A B C) {i : Fin 3} {P Q : List V}
    {x y z w : V} (hP : IsRungFrom G A B C i P x y) (hQ : IsRungFrom G A B C i Q z w)
    {v : V} (hvP : v ∈ SPGT.interior P) (hvQ : v ∈ SPGT.interior Q) :
    ∃ p : List V, IsRungFrom G A B C i p x w :=
  exists_rung_join hH hP hQ
    (Or.inl ⟨v, mem_dropLast_of_mem_interior hP hvP, mem_tail_of_mem_interior hQ hvQ⟩)

/-! ### Rungs through prescribed vertices, and `Cᵢ` as a union of interiors -/

theorem exists_rung_from_A (hH : IsHyperprism G A B C) (i : Fin 3) {x : V} (hx : x ∈ A i) :
    ∃ (p : List V) (y : V), IsRungFrom G A B C i p x y := by
  obtain ⟨p, x', y, hp, hxp⟩ := exists_rung_through hH i (Or.inl (Or.inl hx))
  refine ⟨p, y, ?_⟩
  rw [rung_eq_A hH hp hxp hx]
  exact hp

theorem exists_rung_from_B (hH : IsHyperprism G A B C) (i : Fin 3) {w : V} (hw : w ∈ B i) :
    ∃ (p : List V) (z : V), IsRungFrom G A B C i p z w := by
  obtain ⟨p, z, w', hp, hwp⟩ := exists_rung_through hH i (Or.inl (Or.inr hw))
  refine ⟨p, z, ?_⟩
  rw [rung_eq_B hH hp hwp hw]
  exact hp

/-- `Cᵢ` is exactly the union of the interiors of the `i`-rungs. -/
theorem mem_C_iff (hH : IsHyperprism G A B C) (i : Fin 3) {v : V} :
    v ∈ C i ↔ ∃ (p : List V) (x y : V), IsRungFrom G A B C i p x y ∧ v ∈ SPGT.interior p := by
  constructor
  · intro hv
    obtain ⟨p, x, y, hp, hvp⟩ := exists_rung_through hH i (Or.inr hv)
    refine ⟨p, x, y, hp, ?_⟩
    rw [PathBasics.mem_interior_iff_of_pathFrom hp.2.2.1]
    refine ⟨hvp, ?_, ?_⟩
    · intro hvx
      exact Set.disjoint_left.mp (hH.2.2.1 i i) (by rw [hvx]; exact hp.1) hv
    · intro hvy
      exact Set.disjoint_left.mp (hH.2.2.2.1 i i) (by rw [hvy]; exact hp.2.1) hv
  · rintro ⟨p, x, y, hp, hvp⟩
    exact hp.2.2.2 v hvp

/-- Converse of `interior_subset_C`: a vertex of an `i`-rung that lies in `Cᵢ` is **internal**
to it.  This is what turns the paper's *"there exists `x₁ ∈ X ∩ C₁`"* into the hypothesis
`x₁ ∈ V(R₁)*` that `thm_10_3` demands. -/
theorem mem_interior_of_mem_C (hH : IsHyperprism G A B C) {i : Fin 3} {p : List V}
    {x y v : V} (hp : IsRungFrom G A B C i p x y) (hv : v ∈ p) (hvC : v ∈ C i) :
    v ∈ SPGT.interior p := by
  rw [PathBasics.mem_interior_iff_of_pathFrom hp.2.2.1]
  refine ⟨hv, ?_, ?_⟩
  · intro hvx
    exact Set.disjoint_left.mp (hH.2.2.1 i i) (by rw [hvx]; exact hp.1) hvC
  · intro hvy
    exact Set.disjoint_left.mp (hH.2.2.2.1 i i) (by rw [hvy]; exact hp.2.1) hvC

/-- Every vertex of an `i`-rung that is neither of its ends lies in `Cᵢ`; combined with
`mem_C_iff` this is the paper's *"`Cᵢ = C'ᵢ ∪ C''ᵢ`"* once the rungs are split into two
kinds. -/
theorem interior_subset_C {i : Fin 3} {P : List V} {x y : V}
    (hP : IsRungFrom G A B C i P x y) : ∀ v ∈ SPGT.interior P, v ∈ C i := hP.2.2.2

end Workspace.ProofLemmas.HyperprismRungStructure
