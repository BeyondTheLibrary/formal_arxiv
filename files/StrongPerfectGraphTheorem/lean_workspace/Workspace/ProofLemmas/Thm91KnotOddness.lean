import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.Statements.S02.Thm_2_2

/-!
# Support for 9.1 — the two moves of the printed proof of 9.1

PAPER (9.1, printed p. 48): *"Define `aᵢ, bᵢ, xᵢ, yᵢ (i = 1,2)` as usual.  Certainly `P₁` is odd
since `x₁-a₁-P₁-b₁-y₂-x₁` is a hole, and similarly the other three are odd.  Suppose one of
`P₁, P₂` has length `> 1` and one of `Q₁, Q₂` has length `> 1`.  By exchanging `P₁, P₂` or
`Q₁, Q₂` we may therefore assume that `P₁, Q₁` both have length `> 1`.  Let `Y` be the interior
of `Q₁`.  Then `a₁, b₁, a₂, b₂` are all `Y`-complete, from the last condition in the definition
of a knot, and since `a₂` has no neighbours in the interior of `P₁` it follows from 2.2 that
there is a `Y`-complete vertex (`v` say) in the interior of `P₁`.  But `x₁, y₁` are not
`Y`-complete, and they are adjacent, so `a₁-x₁-y₁-b₁` is an odd path between `Y`-complete
vertices and `v` has no neighbour in its interior, contrary to 2.2."*

This module isolates the two moves as graph-generic lemmas, so that 9.1 can run each of them
on the four instances the paper's *"and similarly"* / *"by exchanging"* refer to.

* `Thm91.odd_of_two_attachments` is the hole `x₁-a₁-P₁-b₁-y₂-x₁`: a path whose two ends carry
  one private neighbour each, the two neighbours being adjacent, closes into a hole, so the
  path has odd length in a Berge graph.  Instantiated at `Gᶜ` it is the antipath/antihole
  mirror, which is how the two antipaths `Q₁, Q₂` of a knot are handled.
* `Thm91.no_long_path_and_antipath` is the whole second paragraph: the contradiction obtained
  from a path `P` of length `≥ 3` and an antipath `Q` of length `≥ 3` sitting in the
  configuration a knot puts them in.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm91

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*}

/-- **The hole `x₁-a₁-P₁-b₁-y₂-x₁`.**

A path `u-p-v` of length `≥ 1` whose end `u` has the private neighbour `s` off the path, whose
end `v` has the private neighbour `t` off the path, with `s` adjacent to `t`, closes into the
hole `t-s-u-p-v-t` of length `pathLength p + 3`.  In a Berge graph that length is even, so
`pathLength p` is odd. -/
theorem odd_of_two_attachments {G : SimpleGraph V} (hG : Berge G)
    {p : List V} {u v s t : V} (hp : IsPathFrom G p u v) (hlen : 1 ≤ pathLength p)
    (hs : s ∉ p) (ht : t ∉ p) (hst : G.Adj s t)
    (hsp : ∀ z ∈ p, (G.Adj s z ↔ z = u)) (htp : ∀ z ∈ p, (G.Adj t z ↔ z = v)) :
    Odd (pathLength p) := by
  have hu : u ∈ p := (PathBasics.isPathFrom_ends_mem hp).1
  have hv : v ∈ p := (PathBasics.isPathFrom_ends_mem hp).2
  have huv : u ≠ v := PathBasics.isPathFrom_ends_ne hp hlen
  have hsu : G.Adj s u := (hsp u hu).mpr rfl
  have htv : G.Adj t v := (htp v hv).mpr rfl
  have hsv : ¬ G.Adj s v := fun h => huv ((hsp v hv).mp h).symm
  have htu : ¬ G.Adj t u := fun h => huv ((htp u hu).mp h)
  have hsint : ∀ z ∈ SPGT.interior p, ¬ G.Adj s z := by
    intro z hz hadj
    obtain ⟨hzp, hzu, hzv⟩ := (PathBasics.mem_interior_iff_of_pathFrom hp).mp hz
    exact hzu ((hsp z hzp).mp hadj)
  have htint : ∀ z ∈ SPGT.interior p, ¬ G.Adj t z := by
    intro z hz hadj
    obtain ⟨hzp, hzu, hzv⟩ := (PathBasics.mem_interior_iff_of_pathFrom hp).mp hz
    exact hzv ((htp z hzp).mp hadj)
  have hhole := PrismBasics.isHoleList_of_path_add_two_vertices hp hlen hsu htv hst hs ht
    hsv htu hsint htint
  have heven := hG.1 _ hhole
  rw [PrismBasics.holeLength_cons_cons s t (PathBasics.path_ne_nil hp.1)] at heven
  obtain ⟨k, hk⟩ := heven
  exact ⟨k - 2, by omega⟩

variable [Fintype V] [DecidableEq V]

/-- **The second paragraph of the printed proof of 9.1.**

`P` is a path `a-P-b` of odd length `≥ 3`; `Q` is an antipath `x-Q-y` of length `≥ 3`, disjoint
from `P`; `Y` is the interior of `Q`.  The ends `a, b` of `P` are `Y`-complete, as is a further
vertex `c` with no neighbour in `P*` (in 9.1 these are `a₁, b₁` and `c = a₂`), and no interior
vertex of `P` has a neighbour in `{x, y}`, while `a` is adjacent to `x` only and `b` to `y`
only among `{x, y}`.  This configuration is contradictory in a Berge graph. -/
theorem no_long_path_and_antipath {G : SimpleGraph V} (hG : Berge G)
    {P Q : List V} {a b x y c : V}
    (hP : IsPathFrom G P a b) (hPodd : Odd (pathLength P)) (hP3 : 3 ≤ pathLength P)
    (hQ : IsPathFrom Gᶜ Q x y) (hQ3 : 3 ≤ pathLength Q)
    (hPQ : ∀ w ∈ P, w ∉ Q)
    (ha : VertexComplete G a {z : V | z ∈ SPGT.interior Q})
    (hb : VertexComplete G b {z : V | z ∈ SPGT.interior Q})
    (hc : VertexComplete G c {z : V | z ∈ SPGT.interior Q})
    (hcP : ∀ w ∈ SPGT.interior P, ¬ G.Adj c w)
    (hax : G.Adj a x) (hby : G.Adj b y)
    (hay : ¬ G.Adj a y) (hxb : ¬ G.Adj x b)
    (hPx : ∀ w ∈ SPGT.interior P, ¬ G.Adj w x)
    (hPy : ∀ w ∈ SPGT.interior P, ¬ G.Adj w y) :
    False := by
  -- ### bookkeeping for `Q`
  have hQlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQ.1
  have hQ4 : 4 ≤ Q.length := by omega
  have hxQ : x ∈ Q := (PathBasics.isPathFrom_ends_mem hQ).1
  have hyQ : y ∈ Q := (PathBasics.isPathFrom_ends_mem hQ).2
  have hxnY : x ∉ SPGT.interior Q := fun h =>
    ((PathBasics.mem_interior_iff_of_pathFrom hQ).mp h).2.1 rfl
  have hynY : y ∉ SPGT.interior Q := fun h =>
    ((PathBasics.mem_interior_iff_of_pathFrom hQ).mp h).2.2 rfl
  have hQ0 : Q[0]'(by omega) = x := PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hQl : Q[Q.length - 1]'(by omega) = y :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
  -- PAPER: *"`x₁, y₁` … are adjacent"* — the ends of an antipath of length `≥ 3`.
  have hxney : x ≠ y := PathBasics.isPathFrom_ends_ne hQ (by omega)
  have hxy : G.Adj x y := by
    by_contra h
    have hne : ¬ Gᶜ.Adj (Q[0]'(by omega)) (Q[Q.length - 1]'(by omega)) :=
      PathBasics.path_ends_not_adj hQ.1 (by omega)
    rw [hQ0, hQl] at hne
    exact hne ((SimpleGraph.compl_adj G x y).mpr ⟨hxney, h⟩)
  -- PAPER: *"`x₁, y₁` are not `Y`-complete"*.
  have h1int : (Q[1]'(by omega)) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQ.1 (by omega) le_rfl (by omega)
  have hl2int : (Q[Q.length - 2]'(by omega)) ∈ SPGT.interior Q :=
    PathBasics.getElem_mem_interior hQ.1 (by omega) (by omega) (by omega)
  have hxnc : ¬ VertexComplete G x {z : V | z ∈ SPGT.interior Q} := by
    intro hcx
    have hc1 : Gᶜ.Adj (Q[0]'(by omega)) (Q[1]'(by omega)) :=
      (PathBasics.path_adj_iff hQ.1 (by omega) (by omega)).mpr (Or.inl rfl)
    rw [hQ0] at hc1
    exact ((SimpleGraph.compl_adj G _ _).mp hc1).2 (hcx _ h1int)
  have hync : ¬ VertexComplete G y {z : V | z ∈ SPGT.interior Q} := by
    intro hcy
    have hc1 : Gᶜ.Adj (Q[Q.length - 1]'(by omega)) (Q[Q.length - 2]'(by omega)) :=
      (PathBasics.path_adj_iff hQ.1 (by omega) (by omega)).mpr (Or.inr (by omega))
    rw [hQl] at hc1
    exact ((SimpleGraph.compl_adj G _ _).mp hc1).2 (hcy _ hl2int)
  -- ### bookkeeping for `P`
  have hPlen : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  have hP4 : 4 ≤ P.length := by omega
  have haP : a ∈ P := (PathBasics.isPathFrom_ends_mem hP).1
  have hbP : b ∈ P := (PathBasics.isPathFrom_ends_mem hP).2
  have hP0 : P[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hPl : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hab : a ≠ b := PathBasics.isPathFrom_ends_ne hP (by omega)
  have hnab : ¬ G.Adj a b := by
    have h := PathBasics.path_ends_not_adj hP.1 (show 3 ≤ P.length by omega)
    rwa [hP0, hPl] at h
  have hPY : ∀ w ∈ P, w ∉ ({z : V | z ∈ SPGT.interior Q} : Set V) := fun w hw hwY =>
    hPQ w hw (PathBasics.interior_subset hwY)
  have hYconn : AnticonnectedSet G ({z : V | z ∈ SPGT.interior Q} : Set V) :=
    MinimalConnectedIsPath.connectedSet_interior hQ
  -- PAPER: *"it follows from 2.2 that there is a `Y`-complete vertex (`v` say) in the interior
  -- of `P₁`"*.
  have hstep1 : ∃ w ∈ SPGT.interior P,
      VertexComplete G w ({z : V | z ∈ SPGT.interior Q} : Set V) := by
    by_contra hcon
    push_neg at hcon
    have hnoedge : ¬ ∃ u ∈ P, ∃ w ∈ P,
        EdgeComplete G ({z : V | z ∈ SPGT.interior Q} : Set V) u w := by
      rintro ⟨u, hu, w, hw, hadj, hcu, hcw⟩
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hu
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
      have hcons := (PathBasics.path_adj_iff hP.1 hi hj).mp hadj
      rcases (show (1 ≤ i ∧ i + 2 ≤ P.length) ∨ (1 ≤ j ∧ j + 2 ≤ P.length) by omega) with
        ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hcon _ (PathBasics.getElem_mem_interior hP.1 hi h1 h2) hcu
      · exact hcon _ (PathBasics.getElem_mem_interior hP.1 hj h1 h2) hcw
    obtain ⟨w, hw, hadj⟩ := Workspace.Statements.S02.SPGT.thm_2_2 G hG
      ({z : V | z ∈ SPGT.interior Q} : Set V) hYconn P a b hP hPY hPodd ha hb hnoedge c hc
    exact hcP w hw hadj
  obtain ⟨v, hvint, hvY⟩ := hstep1
  -- PAPER: *"`a₁-x₁-y₁-b₁` is an odd path between `Y`-complete vertices"*.
  have hax' : G.Adj x a := hax.symm
  have hxy' : G.Adj y x := hxy.symm
  have hby' : G.Adj y b := hby.symm
  have hay' : ¬ G.Adj y a := fun h => hay h.symm
  have hxb' : ¬ G.Adj b x := fun h => hxb h.symm
  have hnab' : ¬ G.Adj b a := fun h => hnab h.symm
  have hanx : a ≠ x := fun h => hPQ a haP (h ▸ hxQ)
  have hany : a ≠ y := fun h => hPQ a haP (h ▸ hyQ)
  have hbnx : b ≠ x := fun h => hPQ b hbP (h ▸ hxQ)
  have hbny : b ≠ y := fun h => hPQ b hbP (h ▸ hyQ)
  have hlist : IsPathList G [a, x, y, b] := by
    refine ⟨by simp, ?_, ?_⟩
    · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        or_false, not_or]
      exact ⟨⟨hanx, hany, hab⟩, ⟨hxney, hbnx.symm⟩, hbny.symm, not_false, trivial⟩
    · intro i j hi hj
      simp only [List.length_cons, List.length_nil] at hi hj
      interval_cases i <;> interval_cases j <;>
        simp [hax, hax', hxy, hxy', hby, hby', hay, hay', hxb, hxb', hnab, hnab',
          SimpleGraph.irrefl]
  have hpath : IsPathFrom G [a, x, y, b] a b := ⟨hlist, rfl, rfl⟩
  have hmemY : ∀ w ∈ [a, x, y, b], w ∉ ({z : V | z ∈ SPGT.interior Q} : Set V) := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact hPY _ haP
    · exact hxnY
    · exact hynY
    · exact hPY _ hbP
  have hnoedge2 : ¬ ∃ u ∈ [a, x, y, b], ∃ w ∈ [a, x, y, b],
      EdgeComplete G ({z : V | z ∈ SPGT.interior Q} : Set V) u w := by
    rintro ⟨u, hu, w, hw, hadj, hcu, hcw⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hw
    have hu' : u = a ∨ u = b := by
      rcases hu with rfl | rfl | rfl | rfl
      exacts [Or.inl rfl, absurd hcu hxnc, absurd hcu hync, Or.inr rfl]
    have hw' : w = a ∨ w = b := by
      rcases hw with rfl | rfl | rfl | rfl
      exacts [Or.inl rfl, absurd hcw hxnc, absurd hcw hync, Or.inr rfl]
    rcases hu' with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact G.irrefl hadj
    · exact hnab hadj
    · exact hnab' hadj
    · exact G.irrefl hadj
  have hodd3 : Odd (pathLength [a, x, y, b]) := ⟨1, by simp [pathLength]⟩
  obtain ⟨w, hw, hadj⟩ := Workspace.Statements.S02.SPGT.thm_2_2 G hG
    ({z : V | z ∈ SPGT.interior Q} : Set V) hYconn [a, x, y, b] a b hpath hmemY hodd3
    ha hb hnoedge2 v hvY
  -- PAPER: *"`v` has no neighbour in its interior, contrary to 2.2"*.
  have hwxy : w = x ∨ w = y := by
    have : SPGT.interior [a, x, y, b] = [x, y] := rfl
    rw [this] at hw
    simpa using hw
  rcases hwxy with rfl | rfl
  · exact hPx v hvint hadj
  · exact hPy v hvint hadj

end Workspace.ProofLemmas.Thm91
