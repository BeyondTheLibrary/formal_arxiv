import Workspace.ProofLemmas.RimSurgery
import Workspace.ProofLemmas.KiteTailBasics

/-!
The last rim replacement in 23.2 (printed p. 141).  We use the same hole as the paper.
Its two surviving disjoint complete edges make it a wheel, and the edge count in
`RimSurgery` contradicts the opening choice of the rim.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232FinalRim

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
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

/-- The paper's last hole remains a wheel if two disjoint complete edges avoid the
deleted vertex.  It then contradicts “as few `Y`-complete edges as possible”. -/
theorem replacement_absurd (hw : IsWheel G C Y)
    (hmin : ∀ D : List V, IsWheel G D Y → yEdgeCount G Y C ≤ yEdgeCount G Y D)
    {x p q : V} (hxC : x ∈ C) (hnb : IsRimNeighbours G C x p q)
    (hxY : VertexComplete G x Y) (hpY : VertexComplete G p Y)
    (hqY : VertexComplete G q Y)
    {Q : List V} (hQ : IsPathFrom G Q p q)
    (hQY : ∀ v ∈ SPGT.interior Q, v ∉ Y)
    (hQnc : ∀ v ∈ SPGT.interior Q, ¬ VertexComplete G v Y)
    (hQiso : ∀ c ∈ C, ∀ v ∈ SPGT.interior Q, G.Adj c v → c = p ∨ c = q)
    (hedges : ∃ a b c d : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      a ≠ x ∧ b ≠ x ∧ c ≠ x ∧ d ≠ x ∧
      EdgeComplete G Y a b ∧ EdgeComplete G Y c d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d) : False := by
  have hQC := interior_outside hw.1.1 hw.1.2 hxC hnb hxY hQ hQnc hQiso
  obtain ⟨a, b, r, k, hrot⟩ := exists_rim_normal_form hw.1.1 hxC
  have hpre : [a, x, b] <+: C.rotate k := ⟨r, hrot.symm⟩
  have habnb := (hole_triple hw.1.1 ⟨k, hpre⟩).2.2.2
  have heq := rimNeighbours_pair_eq habnb hnb
  have hor : (a = p ∧ b = q) ∨ (a = q ∧ b = p) := Set.pair_eq_pair_iff.mp heq
  have hsurgery : ∃ D : List V, IsHoleList G D ∧ 6 ≤ holeLength D ∧
      (∀ v ∈ D, v ∉ Y) ∧
      (∀ v : V, v ∈ D ↔ ((v ∈ C ∧ v ≠ x) ∨ v ∈ SPGT.interior Q)) ∧
      yEdgeCount G Y C = yEdgeCount G Y D + 2 := by
    rcases hor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a b
      obtain ⟨D, hD, hn, hY, hm, hc, _⟩ :=
        RimSurgery.exists_rim_surgery_of_wheel hw p x q Q ⟨k, hpre⟩ hpY hxY hqY hQ
          (fun v hv => ⟨hQC v hv, hQY v hv⟩) hQnc
          (fun v hv c hc hcp _ hcq hadj => (hQiso c hc v hv hadj.symm).elim hcp hcq)
      exact ⟨D, hD, hn, hY, hm, hc⟩
    · subst a b
      obtain ⟨D, hD, hn, hY, hm, hc, _⟩ :=
        RimSurgery.exists_rim_surgery_of_wheel hw q x p Q.reverse ⟨k, hpre⟩ hqY hxY hpY
          (PathBasics.isPathFrom_reverse hQ)
          (fun v hv => ⟨hQC v (PathBasics.mem_interior_reverse.mp hv),
            hQY v (PathBasics.mem_interior_reverse.mp hv)⟩)
          (fun v hv => hQnc v (PathBasics.mem_interior_reverse.mp hv))
          (fun v hv c hc hcq _ hcp hadj =>
            (hQiso c hc v (PathBasics.mem_interior_reverse.mp hv) hadj.symm).elim hcp hcq)
      refine ⟨D, hD, hn, hY, ?_, hc⟩
      intro v
      simpa only [PathBasics.mem_interior_reverse] using hm v
  obtain ⟨D, hD, hn, hY, hm, hc⟩ := hsurgery
  obtain ⟨a, b, c, d, ha, hb, hcc, hd, hax, hbx, hcx, hdx, hab, hcd,
    hac, had, hbc, hbd⟩ := hedges
  have hwD : IsWheel G D Y :=
    ⟨⟨hD, hn⟩, ⟨hw.2.1.1, hw.2.1.2.1, hY⟩,
      a, b, c, d, (hm a).mpr (Or.inl ⟨ha, hax⟩), (hm b).mpr (Or.inl ⟨hb, hbx⟩),
      (hm c).mpr (Or.inl ⟨hcc, hcx⟩), (hm d).mpr (Or.inl ⟨hd, hdx⟩),
      hab, hcd, hac, had, hbc, hbd⟩
  have := hmin D hwD
  omega

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
edges cannot meet to form a four-cycle with the deleted end. -/
theorem common_end_absurd (hw : IsWheel G C Y)
    (hmin : ∀ D : List V, IsWheel G D Y → yEdgeCount G Y C ≤ yEdgeCount G Y D)
    {x p q u v : V} (hpC : p ∈ C) (hqC : q ∈ C) (hpq : p ≠ q)
    (hp : IsRimNeighbours G C p x u) (hq : IsRimNeighbours G C q v x)
    (hxY : VertexComplete G x Y) (hpY : VertexComplete G p Y)
    (hqY : VertexComplete G q Y) (huY : VertexComplete G u Y)
    (hvY : VertexComplete G v Y)
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
  have hxnb := rimNeighbours_of_two hC hp.2.1 hpC hqC hpq hpx.symm hqx.symm
  apply replacement_absurd hw hmin hp.2.1 hxnb hxY hpY hqY hQ hQY hQnc hQiso
  exact ⟨p, u, v, q, hpC, hp.2.2.1, hq.2.1, hqC, hpx.ne, hp.1.symm,
    hq.1, hqx.ne, ⟨hpu, hpY, huY⟩, ⟨hqv.symm, hvY, hqY⟩, hpv, hpq, huv, huq⟩

end Workspace.ProofLemmas.Thm232FinalRim
