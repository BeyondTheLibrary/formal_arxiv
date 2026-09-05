import Workspace.ProofLemmas.KiteTailBasics

/-! The complete triples when the two pairs of complete rim edges share an end. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingTriples

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} {G : SimpleGraph V} {C : List V}

/-- The four complete edges form the path `u-p-x-q-v`.  A repeated vertex would
give a triangle or a four-cycle inside the hole. -/
theorem five_distinct [Fintype V] [DecidableEq V] (hC : IsHoleList G C) (hlen : 6 ≤ C.length)
    {x p q u v : V} (hpC : p ∈ C) (hqC : q ∈ C) (hpq : p ≠ q)
    (hp : IsRimNeighbours G C p x u) (hq : IsRimNeighbours G C q v x) :
    [u, p, x, q, v].Nodup := by
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
    exact hole_no_four_cycle hC (by omega) hpC hp.2.2.1 hqC hp.2.1
      hpu.ne hpq hpx.ne huq hp.1.symm hqx.ne hpu hqu.symm hqx hpx.symm
  simp [hpu.ne', hp.1.symm, huq, huv, hpx.ne, hpq, hpv, hqx.ne', hq.1.symm, hqv.ne]

/-- Every three-vertex path made from the four listed edges contains `x`.  If
neither end is `x`, its ends must be `p,q`. -/
theorem triple_shape {x p q u v a b c : V} (hnd : [u, p, x, q, v].Nodup)
    (hac : a ≠ c)
    (hab : ({a,b} : Set V) = {x,p} ∨ ({a,b} : Set V) = {p,u} ∨
      ({a,b} : Set V) = {v,q} ∨ ({a,b} : Set V) = {q,x})
    (hbc : ({b,c} : Set V) = {x,p} ∨ ({b,c} : Set V) = {p,u} ∨
      ({b,c} : Set V) = {v,q} ∨ ({b,c} : Set V) = {q,x}) :
    a = x ∨ c = x ∨ (b = x ∧ ((a = p ∧ c = q) ∨ (a = q ∧ c = p))) := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.not_mem_nil,
    List.nodup_nil, not_or, and_true] at hnd
  simp only [Set.pair_eq_pair_iff] at hab hbc
  grind

end Workspace.ProofLemmas.Thm232ClosingTriples
