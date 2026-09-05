import Workspace.ProofLemmas.KiteTailBasics

/-!
# The hypotheses omitted from the special case of 23.2(3)

Start with the six-cycle, add a false twin `6` of vertex `2`, and add a
universal vertex `7`. Take the hub to be `{7}` and set
`(x₀,z,x₁,c₁,c₂,c₃,y) = (0,1,2,2,3,4,6)`.

This file checks the wheel, its optimality, and all the local hypotheses of
`not_adj_c2_gap`. Nevertheless `y` sees `c₂`. The two omitted hypotheses of
the paper both fail: `y` is hub-complete, and all six rim edges are
hub-complete. The graph-class discussion is in `REPORT.md`; this file does
not assert an unchecked `InF8` certificate.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Workspace.ProofLemmas.Thm232Claim3MissingHypotheses

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.KiteTailBasics

def graph : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet
  {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,0), s(1,6), s(3,6),
   s(0,7), s(1,7), s(2,7), s(3,7), s(4,7), s(5,7), s(6,7)}

def rim : List (Fin 8) := [0,1,2,3,4,5]

instance : DecidableRel graph.Adj := by
  intro u v
  change Decidable (s(u,v) ∈
    ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,0), s(1,6), s(3,6),
      s(0,7), s(1,7), s(2,7), s(3,7), s(4,7), s(5,7), s(6,7)} : Set (Sym2 (Fin 8))) ∧ u ≠ v)
  infer_instance

theorem universal : ∀ v : Fin 8, v ≠ 7 → graph.Adj 7 v := by decide

theorem rim_hole : IsHoleList graph rim := by
  refine ⟨by decide, by decide, ?_⟩
  intro i j hi hj
  have hi' : i < 6 := hi
  have hj' : j < 6 := hj
  interval_cases i <;> interval_cases j <;>
    simp only [rim, List.getElem_cons_zero, List.getElem_cons_succ,
      List.length_cons, List.length_nil] <;> decide

theorem rim_complete : ∀ v ∈ rim, VertexComplete graph v {7} := by
  intro v hv u hu
  have he : u = 7 := hu
  subst u
  exact (universal v (by intro he; subst v; exact (by decide : (7 : Fin 8) ∉ rim) hv)).symm

theorem wheel : IsWheel graph rim {7} := by
  refine ⟨⟨rim_hole, by decide⟩, ⟨⟨7, rfl⟩, ?_, ?_⟩,
    0, 1, 3, 4, by decide, by decide, by decide, by decide,
    ⟨by decide, rim_complete 0 (by decide), rim_complete 1 (by decide)⟩,
    ⟨by decide, rim_complete 3 (by decide), rim_complete 4 (by decide)⟩,
    by decide, by decide, by decide, by decide⟩
  · intro a b
    have he : a = b := Subtype.ext (a.2.trans b.2.symm)
    rw [he]
  · intro v hv he
    have hv7 : v = 7 := he
    subst v
    exact (by decide : (7 : Fin 8) ∉ rim) hv

theorem optimal : OptimalWheel graph rim {7} := by
  refine ⟨wheel, ?_⟩
  rintro ⟨C, Y, hW, hsub⟩
  have h7 : (7 : Fin 8) ∈ Y := hsub.1 rfl
  have hY : Y ⊆ ({7} : Set (Fin 8)) := by
    intro v hv
    have hn : ∀ q : ↥Y, ¬ (graphᶜ.induce Y).Adj ⟨7, h7⟩ q := by
      intro q ha
      change graphᶜ.Adj 7 q.val at ha
      rw [SimpleGraph.compl_adj] at ha
      exact ha.2 (universal q.val ha.1.symm)
    obtain ⟨p⟩ := hW.2.1.2.1 ⟨7, h7⟩ ⟨v, hv⟩
    cases p with
    | nil => rfl
    | cons hadj rest => exact (hn _ hadj).elim
  exact hsub.2 hY

/-- All the local geometric assumptions of the frozen special-case helper,
together with the edge its conclusion forbids. -/
theorem local_certificate :
    OptimalWheel graph rim {7} ∧
    2 ≤ (2 : ℕ) ∧ 2 + 2 ≤ rim.length ∧
    [0,1,2] <+: rim.rotate 0 ∧ [2,3,4] <+: rim.rotate (0 + 2) ∧
    (∀ v ∈ ({0,1,2,3,4} : Set (Fin 8)), VertexComplete graph v {7}) ∧
    IsRimNeighbours graph rim 1 0 2 ∧ IsRimNeighbours graph rim 3 2 4 ∧
    graph.Adj 6 1 ∧ (6 : Fin 8) ∉ rim ∧ (6 : Fin 8) ∉ ({7} : Set (Fin 8)) ∧
    (∀ c : Fin 8, c ∈ rim → c ≠ 1 → c ≠ 0 → c ≠ 2 → c ≠ 3 → ¬ graph.Adj 6 c) ∧
    ¬ (graph.Adj 6 0 ∧ graph.Adj 6 2) ∧ graph.Adj 6 3 := by
  refine ⟨optimal, by decide, by decide, by decide, by decide, ?_,
    (hole_triple rim_hole (by exact ⟨0, by decide⟩)).2.2.2,
    (hole_triple rim_hole (by exact ⟨2, by decide⟩)).2.2.2,
    by decide, by decide, by decide, by decide, by decide, by decide⟩
  intro v hv
  exact rim_complete v (by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl <;> decide)

/-- These are exactly the two paper assumptions absent from the helper. -/
theorem omitted_assumptions_fail :
    VertexComplete graph 6 {7} ∧
    EdgeComplete graph {7} 4 5 ∧
    ({4,5} : Set (Fin 8)) ≠ {0,1} ∧ ({4,5} : Set (Fin 8)) ≠ {1,2} ∧
    ({4,5} : Set (Fin 8)) ≠ {2,3} ∧ ({4,5} : Set (Fin 8)) ≠ {3,4} := by
  refine ⟨?_, ⟨by decide, rim_complete 4 (by decide), rim_complete 5 (by decide)⟩,
    ?_, ?_, ?_, ?_⟩
  intro v hv
  have he : v = 7 := hv
  subst v
  decide
  all_goals
    intro he
    have hf : (5 : Fin 8) ∈ ({4,5} : Set (Fin 8)) := by decide
    rw [he] at hf
    norm_num [Fin.ext_iff] at hf

end Workspace.ProofLemmas.Thm232Claim3MissingHypotheses
