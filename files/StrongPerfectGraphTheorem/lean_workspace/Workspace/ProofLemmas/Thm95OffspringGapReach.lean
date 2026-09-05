import Workspace.ProofLemmas.Thm95OffspringSplit
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# Joining two antirungs of `Tⱼ` through `Zⱼ`

PAPER (9.5(1), printed p. 52): *"there are no nonedges between `Mⱼ` and `Nⱼ` except possibly
between `Mⱼ ∩ Xⱼ` and `Nⱼ ∩ Xⱼ`, or between `Mⱼ ∩ Yⱼ` and `Nⱼ ∩ Yⱼ`"*.

The paper gives no argument for this sentence, and the argument is the following surgery on
antirungs.  Take a nonedge of `G` — that is, an edge of `Ḡ` — between a vertex `u` of one
`Tⱼ`-antirung and a vertex `v` of another, and suppose the two are not both in `Xⱼ` and not
both in `Yⱼ`.  Then `u` is joined to one end of its antirung by a piece of that antirung whose
other vertices lie in `Zⱼ`, and `v` is joined to an end of the other antirung in the same way,
and the two ends can be chosen so that one lies in `Xⱼ` and the other in `Yⱼ`.  Gluing the two
pieces along the edge `uv` gives a set consisting of those two ends and vertices of `Zⱼ` which
is connected in `Ḡ`, and an induced path of `Ḡ` inside that set is a `Tⱼ`-antirung between the
two chosen ends.  Since the paper's *"every `Tⱼ`-antirung has one end in `U` and the other in
`V`"* forbids that antirung, no such nonedge exists.

`ReachThroughZ` records "joined to `x` inside `Z ∪ {x}`", `reach_head` and `reach_last` produce
it from a piece of an antirung, and `exists_srung_of_reach` performs the gluing.  Nothing here
uses that `G` is Berge; it is bookkeeping about the antistrip.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringGapReach

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- `w` is joined to `x` inside a set consisting of `x` and vertices of `Z` that is connected
in `Ḡ`. -/
def ReachThroughZ (G : SimpleGraph V) (Z : Set V) (w x : V) : Prop :=
  ∃ A : Set V, ConnectedSet Gᶜ A ∧ w ∈ A ∧ x ∈ A ∧ A ⊆ insert x Z

/-! ### Reading `ReachThroughZ` off a piece of an antirung -/

private theorem getLast_eq {Q : List V} (hne : Q ≠ []) {y : V} (h : Q.getLast? = some y) :
    Q.getLast hne = y :=
  Option.some.inj ((List.getLast?_eq_some_getLast hne).symm.trans h)

private theorem mem_tail_of_ne_head {Q : List V} {x w : V} (hh : Q.head? = some x)
    (hw : w ∈ Q) (hne : w ≠ x) : w ∈ Q.tail := by
  cases Q with
  | nil => simp at hh
  | cons c t =>
    have hc : c = x := Option.some.inj hh
    rcases List.mem_cons.mp hw with rfl | hw'
    · exact absurd hc hne
    · exact hw'

private theorem mem_of_mem_tail' {Q : List V} {w : V} (hw : w ∈ Q.tail) : w ∈ Q :=
  List.mem_of_mem_tail hw

/-- Every vertex of an antirung other than its end in `Y` reaches the end in `X` through `Z`. -/
theorem reach_head {Tx : Set V × Set V × Set V} {Q : List V} (hQ : IsSRung Gᶜ Tx Q)
    {x y : V} (hxy : IsPathFrom Gᶜ Q x y) {w : V} (hw : w ∈ Q) (hwy : w ≠ y) :
    ReachThroughZ G Tx.2.1 w x := by
  have hne : Q ≠ [] := hxy.1.1
  have hnd : Q.Nodup := hxy.1.2.1
  have hlast : Q.getLast hne = y := getLast_eq hne hxy.2.2
  have hxQ : x ∈ Q := PathBasics.head_mem hxy.2.1
  have hint : ∀ v ∈ SPGT.interior Q, v ∈ Tx.2.1 := Thm95OffspringSplit.rung_interior Tx Q hQ
  have hlen2 : 2 ≤ Q.length := by
    match Q, hne with
    | (a :: t), _ =>
      match t with
      | [] =>
        have hay : a = y := Option.some.inj hxy.2.2
        have hwa : w = a := by simpa using hw
        exact absurd (hwa.trans hay) hwy
      | (b :: t') => simp
  have hxy' : x ≠ y :=
    PathBasics.isPathFrom_ends_ne hxy (by simp only [SPGT.pathLength]; omega)
  have hdl : Q.dropLast = Q.take (Q.length - 1) := List.dropLast_eq_take
  have hpath : IsPathList Gᶜ Q.dropLast := by
    rw [hdl]
    exact PathBasics.isPathList_take hxy.1 (by omega)
  refine ⟨{z : V | z ∈ Q.dropLast},
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hpath, ?_, ?_, ?_⟩
  · exact (PathBasics.mem_dropLast_iff hnd hne).mpr ⟨hw, by rw [hlast]; exact hwy⟩
  · exact (PathBasics.mem_dropLast_iff hnd hne).mpr ⟨hxQ, by rw [hlast]; exact hxy'⟩
  · intro z hz
    obtain ⟨hzQ, hzy⟩ := (PathBasics.mem_dropLast_iff hnd hne).mp hz
    rw [hlast] at hzy
    by_cases hzx : z = x
    · exact Or.inl hzx
    · exact Or.inr (hint z ((PathBasics.mem_interior_iff_of_pathFrom hxy).mpr ⟨hzQ, hzx, hzy⟩))

/-- Every vertex of an antirung other than its end in `X` reaches the end in `Y` through `Z`. -/
theorem reach_last {Tx : Set V × Set V × Set V} {Q : List V} (hQ : IsSRung Gᶜ Tx Q)
    {x y : V} (hxy : IsPathFrom Gᶜ Q x y) {w : V} (hw : w ∈ Q) (hwx : w ≠ x) :
    ReachThroughZ G Tx.2.1 w y := by
  have hne : Q ≠ [] := hxy.1.1
  have hnd : Q.Nodup := hxy.1.2.1
  have hyQ : y ∈ Q := PathBasics.getLast_mem hxy.2.2
  have hint : ∀ v ∈ SPGT.interior Q, v ∈ Tx.2.1 := Thm95OffspringSplit.rung_interior Tx Q hQ
  have hlen2 : 2 ≤ Q.length := by
    match Q, hne with
    | (a :: t), _ =>
      match t with
      | [] =>
        have hax : a = x := Option.some.inj hxy.2.1
        have hwa : w = a := by simpa using hw
        exact absurd (hwa.trans hax) hwx
      | (b :: t') => simp
  have hxy' : x ≠ y :=
    PathBasics.isPathFrom_ends_ne hxy (by simp only [SPGT.pathLength]; omega)
  have hpath : IsPathList Gᶜ Q.tail := by
    have h1 : Q.tail = Q.drop 1 := List.drop_one.symm
    rw [h1]
    exact PathBasics.isPathList_drop hxy.1 (by omega)
  refine ⟨{z : V | z ∈ Q.tail},
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hpath, ?_, ?_, ?_⟩
  · exact mem_tail_of_ne_head hxy.2.1 hw hwx
  · exact mem_tail_of_ne_head hxy.2.1 hyQ (Ne.symm hxy')
  · intro z hz
    have hzQ : z ∈ Q := mem_of_mem_tail' hz
    have hzx : z ≠ x := Thm95StripExtension.tail_ne_head hxy hz
    by_cases hzy : z = y
    · exact Or.inl hzy
    · exact Or.inr (hint z ((PathBasics.mem_interior_iff_of_pathFrom hxy).mpr ⟨hzQ, hzx, hzy⟩))

/-! ### Gluing two pieces along a nonedge -/

/-- **The surgery.**  If `u` reaches an end `x ∈ Xⱼ` through `Zⱼ`, `v` reaches an end `y ∈ Yⱼ`
through `Zⱼ`, and `uv` is a nonedge of `G` (possibly `u = v`), then there is a `Tⱼ`-antirung
from `x` to `y`. -/
theorem exists_srung_of_reach {Tx : Set V × Set V × Set V} (hTx : IsAntistrip G Tx)
    {u v x y : V} (hx : x ∈ Tx.1) (hy : y ∈ Tx.2.2)
    (hu : ReachThroughZ G Tx.2.1 u x) (hv : ReachThroughZ G Tx.2.1 v y)
    (huv : ¬ G.Adj u v) :
    ∃ Q : List V, IsSRung Gᶜ Tx Q ∧ IsPathFrom Gᶜ Q x y := by
  obtain ⟨A, hAconn, huA, hxA, hAsub⟩ := hu
  obtain ⟨B, hBconn, hvB, hyB, hBsub⟩ := hv
  have hlink : (A ∩ B).Nonempty ∨ ∃ a ∈ A, ∃ b ∈ B, Gᶜ.Adj a b := by
    by_cases huv' : u = v
    · exact Or.inl ⟨u, huA, huv' ▸ hvB⟩
    · exact Or.inr ⟨u, huA, v, hvB, (SimpleGraph.compl_adj G u v).mpr ⟨huv', huv⟩⟩
  have hconn : ConnectedSet Gᶜ (A ∪ B) :=
    ConnectedSetUnionAttach.connectedSet_union hAconn hBconn hlink
  obtain ⟨P, hP, hPsub⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected (G := Gᶜ) hconn
      (Or.inl hxA) (Or.inr hyB)
  have hmem : ∀ z ∈ P, z = x ∨ z = y ∨ z ∈ Tx.2.1 := by
    intro z hz
    rcases hPsub z hz with h | h
    · rcases hAsub h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr h')
    · rcases hBsub h with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
  refine ⟨P, ?_, hP⟩
  obtain ⟨X, Z, Y⟩ := Tx
  refine ⟨x, y, hP, hx, hy, ?_, ?_, ?_⟩
  · intro z hz hzX
    have hzx : z ≠ x := Thm95StripExtension.tail_ne_head hP hz
    rcases hmem z (mem_of_mem_tail' hz) with h | h | h
    · exact hzx h
    · exact Set.disjoint_left.mp hTx.1 hzX (h ▸ hy)
    · exact Set.disjoint_left.mp hTx.2.1 hzX h
  · intro z hz hzY
    have hzy : z ≠ y := Thm95StripExtension.dropLast_ne_last hP hz
    rcases hmem z (List.mem_of_mem_dropLast hz) with h | h | h
    · exact Set.disjoint_left.mp hTx.1 (h ▸ hx) hzY
    · exact hzy h
    · exact Set.disjoint_left.mp hTx.2.2.1 hzY h
  · intro z hz
    obtain ⟨hzP, hzx, hzy⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hz
    rcases hmem z hzP with h | h | h
    · exact absurd h hzx
    · exact absurd h hzy
    · exact h

end Workspace.ProofLemmas.Thm95OffspringGapReach
