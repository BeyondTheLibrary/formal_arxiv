import Workspace.ProofLemmas.RimSurgery
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm212OnlyTwoComplete
import Workspace.Types.Classes

/-!
The last rim replacement in 23.2 (printed p. 141):

PAPER: *"But then the hole formed by the union of `R` and the path `C \ x₀` is the rim of
an odd wheel with hub `Y`, a contradiction."*

We build the paper's hole with `RimSurgery`.  Its two surviving disjoint `Y`-complete edges
make it a wheel, and on it the segment through the deleted vertex's surviving neighbour has
length `1`: the interior of `R` carries no `Y`-complete vertex, and the four `Y`-complete
edges of the old rim leave no other `Y`-complete neighbour.  So the new wheel is odd, and
that contradicts the no-odd-wheel clause of `G ∈ F₈`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232FinalRim

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : List V} {Y : Set V}

/-- An isolated joining path cannot meet the old rim internally: such a vertex would
have the same two rim neighbours as the deleted vertex, giving a four-cycle in the rim.
This supplies the disjointness needed for the paper's “hole formed by the union”. -/
theorem interior_outside (hC : IsHoleList G C) (hlen : 6 ≤ C.length)
    {x p q : V} (hx : x ∈ C) (hnb : IsRimNeighbours G C x p q)
    (hxY : VertexComplete G x Y) {Q : List V} (hQ : IsPathFrom G Q p q)
    (hnc : ∀ v ∈ SPGT.interior Q, ¬ VertexComplete G v Y)
    (hiso : ∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = p ∨ c = q) :
    ∀ v ∈ SPGT.interior Q, v ∉ C := by
  intro v hv hvC
  obtain ⟨a, b, r, k, hrot⟩ := exists_rim_normal_form hC hvC
  have hpre : [a, v, b] <+: C.rotate k := ⟨r, hrot.symm⟩
  obtain ⟨haC, _, hbC, hvnb⟩ := hole_triple hC ⟨k, hpre⟩
  have ha : a = p ∨ a = q := hiso a haC v hv hvnb.2.2.2.1.symm
  have hb : b = p ∨ b = q := hiso b hbC v hv hvnb.2.2.2.2.1.symm
  have hvp : G.Adj v p := by
    rcases ha with rfl | rfl
    · exact hvnb.2.2.2.1
    · rcases hb with rfl | rfl
      · exact hvnb.2.2.2.2.1
      · exact (hvnb.1 rfl).elim
  have hvq : G.Adj v q := by
    rcases hb with rfl | rfl
    · rcases ha with rfl | rfl
      · exact (hvnb.1 rfl).elim
      · exact hvnb.2.2.2.1
    · exact hvnb.2.2.2.2.1
  have hvx : v ≠ x := fun he => hnc v hv (he ▸ hxY)
  exact hole_no_four_cycle hC (by omega) hx hnb.2.1 hvC hnb.2.2.1
    hnb.2.2.2.1.ne hvx.symm hnb.2.2.2.2.1.ne hvp.ne' hnb.1 hvq.ne
    hnb.2.2.2.1 hvp.symm hvq hnb.2.2.2.2.1.symm

/-- The paper's last hole is a wheel with hub `Y`, and the segment through `p` is the
single edge `p`-`u`, so the wheel is **odd** — contrary to `G ∈ F₈`.

The vertex `x` is the one the paper deletes, `p, q` are its two neighbours on the old rim
(so the new hole is `(C \ x) ∪ R*`), and `u` is the other neighbour of `p` on the old rim.
`hpNbr` and `huNbr` say that on the old rim the only `Y`-complete neighbours of `p` and `u`
are each other and the deleted `x`, and the interior of the joining path carries no
`Y`-complete vertex, so `p`-`u` is a whole segment of the new hole.  The fourth
`Y`-complete vertex `hfourth` shows that the new hole has `Y`-complete vertices beyond
`p, u`, which is what an odd wheel forbids. -/
theorem replacement_absurd (hG : InF8 G) (hw : IsWheel G C Y)
    {x p q u : V} (hxC : x ∈ C) (hnb : IsRimNeighbours G C x p q)
    (hxY : VertexComplete G x Y) (hpY : VertexComplete G p Y)
    (hqY : VertexComplete G q Y)
    (huC : u ∈ C) (hux : u ≠ x) (huY : VertexComplete G u Y) (hpu : G.Adj p u)
    (hpNbr : ∀ w ∈ C, G.Adj p w → w = x ∨ w = u)
    (huNbr : ∀ w ∈ C, G.Adj u w → VertexComplete G w Y → w = p ∨ w = x)
    {Q : List V} (hQ : IsPathFrom G Q p q)
    (hQY : ∀ v ∈ SPGT.interior Q, v ∉ Y)
    (hQnc : ∀ v ∈ SPGT.interior Q, ¬ VertexComplete G v Y)
    (hQiso : ∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = p ∨ c = q)
    (hfourth : ∃ c ∈ C, c ≠ x ∧ c ≠ p ∧ c ≠ u ∧ VertexComplete G c Y) : False := by
  have hQC := interior_outside hw.1.1 hw.1.2 hxC hnb hxY hQ hQnc hQiso
  obtain ⟨a, b, r, k, hrot⟩ := exists_rim_normal_form hw.1.1 hxC
  have hpre : [a, x, b] <+: C.rotate k := ⟨r, hrot.symm⟩
  have habnb := (hole_triple hw.1.1 ⟨k, hpre⟩).2.2.2
  have heq := rimNeighbours_pair_eq habnb hnb
  have hor : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := Set.pair_eq_pair_iff.mp heq
  -- PAPER: *"the hole formed by the union of `R` and the path `C \ x₀`"*.
  have hsurgery : ∃ D : List V, IsHoleList G D ∧ 6 ≤ holeLength D ∧
      (∀ v ∈ D, v ∉ Y) ∧
      (∀ v : V, v ∈ D ↔ ((v ∈ C ∧ v ≠ x) ∨ v ∈ SPGT.interior Q)) := by
    rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a b
      obtain ⟨D, hD, hn, hY, hm, _, _⟩ :=
        RimSurgery.exists_rim_surgery_of_wheel hw p x q Q ⟨k, hpre⟩ hpY hxY hqY hQ
          (fun v hv => ⟨hQC v hv, hQY v hv⟩) hQnc
          (fun v hv c hc hcp _ hcq hadj => (hQiso c hc v hv hadj.symm).elim hcp hcq)
      exact ⟨D, hD, hn, hY, hm⟩
    · subst a b
      obtain ⟨D, hD, hn, hY, hm, _, _⟩ :=
        RimSurgery.exists_rim_surgery_of_wheel hw q x p Q.reverse ⟨k, hpre⟩ hqY hxY hpY
          (PathBasics.isPathFrom_reverse hQ)
          (fun v hv => ⟨hQC v (PathBasics.mem_interior_reverse.mp hv),
            hQY v (PathBasics.mem_interior_reverse.mp hv)⟩)
          (fun v hv => hQnc v (PathBasics.mem_interior_reverse.mp hv))
          (fun v hv c hc hcq _ hcp hadj =>
            (hQiso c hc v (PathBasics.mem_interior_reverse.mp hv) hadj.symm).elim hcp hcq)
      refine ⟨D, hD, hn, hY, ?_⟩
      intro v
      simpa only [PathBasics.mem_interior_reverse] using hm v
  obtain ⟨D, hD, hn, hY, hm⟩ := hsurgery
  have hD6 : 6 ≤ D.length := hn
  have hpD : p ∈ D := (hm p).mpr (Or.inl ⟨hnb.2.1, (hnb.2.2.2.1).ne'⟩)
  have huD : u ∈ D := (hm u).mpr (Or.inl ⟨huC, hux⟩)
  -- *"of an odd wheel"*: `p`-`u` is a segment of `D`, of length `1`.  Its two flanking
  -- vertices on `D` are not `Y`-complete: on the side of `p` the flank lies in `R*`, and
  -- on the side of `u` it is a vertex of `C` covered by `huNbr`.
  have hnbr : ∀ w ∈ D, (G.Adj w p ∨ G.Adj w u) → VertexComplete G w Y → w = p ∨ w = u := by
    intro w hwD hadj hwY
    rcases (hm w).mp hwD with ⟨hwC, hwx⟩ | hwQ
    · rcases hadj with h | h
      · rcases hpNbr w hwC h.symm with he | he
        · exact absurd he hwx
        · exact Or.inr he
      · rcases huNbr w hwC h.symm hwY with he | he
        · exact Or.inl he
        · exact absurd he hwx
    · exact absurd hwY (hQnc w hwQ)
  have honly := Thm212OnlyTwoComplete.only_two_complete hG.1.1.1.1.1 hG.1.2.1
    hD hD6 hw.2.1.1 hw.2.1.2.1 hY hpD huD hpu hpY huY hnbr
  -- A fourth `Y`-complete vertex survives on `D`, so `(D, Y)` would have to be odd.
  obtain ⟨c, hcC, hcxne, hcp, hcu, hcY⟩ := hfourth
  rcases honly c ((hm c).mpr (Or.inl ⟨hcC, hcxne⟩)) hcY with he | he
  · exact hcp he
  · exact hcu he

/-- Two distinct neighbours on a hole are its two rim neighbours. -/
theorem rimNeighbours_of_two (hC : IsHoleList G C) {x p q : V}
    (hx : x ∈ C) (hp : p ∈ C) (hq : q ∈ C) (hpq : p ≠ q)
    (hxp : G.Adj x p) (hxq : G.Adj x q) : IsRimNeighbours G C x p q := by
  obtain ⟨a, b, r, k, hrot⟩ := exists_rim_normal_form hC hx
  have hpre : [a, x, b] <+: C.rotate k := ⟨r, hrot.symm⟩
  have hn := (hole_triple hC ⟨k, hpre⟩).2.2.2
  refine ⟨hpq, hp, hq, hxp, hxq, ?_⟩
  have hpab := hn.2.2.2.2.2 p hp hxp
  have hqab := hn.2.2.2.2.2 q hq hxq
  intro w hw hwx
  have hwab := hn.2.2.2.2.2 w hw hwx
  rcases hpab with hpab | hpab <;> rcases hqab with hqab | hqab <;>
    rcases hwab with hwab | hwab <;> grind

/-- When the two complete triples meet at an end, deleting that end leaves the
two other complete edges disjoint.  The hole has at least six vertices, so those
edges cannot meet to form a four-cycle with the deleted end.

`hedgeY` is the layout of the four `Y`-complete edges of the old rim established before the
closing paragraph of 23.2: they are `x`-`p`, `p`-`u`, `v`-`q` and `q`-`x`. -/
theorem common_end_absurd (hG : InF8 G) (hw : IsWheel G C Y)
    {x p q u v : V} (hpC : p ∈ C) (hqC : q ∈ C) (hpq : p ≠ q)
    (hp : IsRimNeighbours G C p x u) (hq : IsRimNeighbours G C q v x)
    (hxY : VertexComplete G x Y) (hpY : VertexComplete G p Y)
    (hqY : VertexComplete G q Y) (huY : VertexComplete G u Y)
    (hvY : VertexComplete G v Y)
    (hedgeY : ∀ a ∈ C, ∀ b ∈ C, EdgeComplete G Y a b →
      ({a, b} : Set V) = {x, p} ∨ ({a, b} : Set V) = {p, u} ∨
        ({a, b} : Set V) = {v, q} ∨ ({a, b} : Set V) = {q, x})
    {Q : List V} (hQ : IsPathFrom G Q p q)
    (hQY : ∀ w ∈ SPGT.interior Q, w ∉ Y)
    (hQnc : ∀ w ∈ SPGT.interior Q, ¬ VertexComplete G w Y)
    (hQiso : ∀ c ∈ C, ∀ w ∈ SPGT.interior Q, G.Adj c w → c = p ∨ c = q) : False := by
  have hC := hw.1.1
  have hpx := hp.2.2.2.1
  have hpu := hp.2.2.2.2.1
  have hqv := hq.2.2.2.1
  have hqx := hq.2.2.2.2.1
  have hpv : p ≠ v := by
    intro he
    exact rimNeighbours_not_adj hC hqC hq (he ▸ hpx)
  have huq : u ≠ q := by
    intro he
    exact rimNeighbours_not_adj hC hpC hp (by rw [he]; exact hqx.symm)
  have huv : u ≠ v := by
    intro he
    have hqu : G.Adj q u := he ▸ hqv
    exact hole_no_four_cycle hC (by have := hw.1.2; change 6 ≤ C.length at this; omega)
      hpC hp.2.2.1 hqC hp.2.1 hpu.ne hpq hpx.ne huq hp.1.symm hqx.ne
      hpu hqu.symm hqx hpx.symm
  have hux : u ≠ x := hp.1.symm
  have hup : u ≠ p := hpu.ne'
  -- The only `Y`-complete neighbour of `u` on the old rim other than the deleted `x` is `p`:
  -- any other one would make a fifth `Y`-complete edge.
  have huNbr : ∀ w ∈ C, G.Adj u w → VertexComplete G w Y → w = p ∨ w = x := by
    intro w hwC hadj hwY
    have hE : EdgeComplete G Y u w := ⟨hadj, huY, hwY⟩
    rcases hedgeY u hp.2.2.1 w hwC hE with h | h | h | h <;>
      rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h1 hux
    · exact absurd h1 hup
    · exact absurd h1 hup
    · exact Or.inl h2
    · exact absurd h1 huv
    · exact absurd h1 huq
    · exact absurd h1 huq
    · exact absurd h1 hux
  have hxnb := rimNeighbours_of_two hC hp.2.1 hpC hqC hpq hpx.symm hqx.symm
  refine replacement_absurd hG hw hp.2.1 hxnb hxY hpY hqY hp.2.2.1 hux huY hpu
    hp.2.2.2.2.2 huNbr hQ hQY hQnc hQiso ⟨v, hq.2.1, hq.1, hpv.symm, huv.symm, hvY⟩

end Workspace.ProofLemmas.Thm232FinalRim
