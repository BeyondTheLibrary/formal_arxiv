import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics

/-!
# A counterexample to the original claim (2) bridge

The rim is `0-1-2-3-4-5-0`, the hub is `7`, and `x₂ = y = 6`.
The hub sees precisely `0,1,4,5`. The frame and minimal set are both `{2,3,4}`.
Thus `01` and `45` are disjoint hub-complete rim edges, but only `45` survives
on a path from `1` to `5` with interior in the minimal set.

This graph is not Berge: `7-1-2-3-4-7` is an odd hole. The old bridge omitted
the graph-class and hub hypotheses of the printed argument.
-/

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim2Counterexample

open Workspace.Types.Core Workspace.Types.Core.SPGT Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT Workspace.ProofLemmas.Thm192Setup

def graph : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet
  {s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,0),
   s(0,6), s(3,6), s(7,0), s(7,1), s(7,4), s(7,5)}

def frameSet : Set (Fin 8) := {2,3,4}

def sequence (i : ℕ) : Fin 8 := if i = 0 then 1 else if i = 1 then 5 else 6

instance : DecidableRel graph.Adj := by
  intro u v
  unfold graph SimpleGraph.fromEdgeSet
  change Decidable ((s(u,v) ∈
    ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,0),
      s(0,6), s(3,6), s(7,0), s(7,1), s(7,4), s(7,5)} : Set (Sym2 (Fin 8)))) ∧ u ≠ v)
  infer_instance

instance : DecidablePred (· ∈ frameSet) := by
  unfold frameSet
  infer_instance

private theorem adj_decide (u v : Fin 8) :
    graph.Adj u v ↔ s(u,v) ∈
      ({s(0,1), s(1,2), s(2,3), s(3,4), s(4,5), s(5,0),
        s(0,6), s(3,6), s(7,0), s(7,1), s(7,4), s(7,5)} : Finset (Sym2 (Fin 8))) := by
  fin_cases u <;> fin_cases v <;> decide

private theorem frame_connected : ConnectedSet graph frameSet := by
  have hp : IsPathList graph [2,3,4] := by
    refine ⟨by decide, by decide, ?_⟩
    intro i j hi hj
    have hi' : i < 3 := hi
    have hj' : j < 3 := hj
    interval_cases i <;> interval_cases j <;>
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide
  convert InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp using 1
  ext v
  simp [frameSet]

theorem is_frame : IsFrame graph 0 frameSet := by
  refine ⟨⟨2, by decide⟩, frame_connected, by decide, ?_⟩
  intro v hv
  have : v = 2 ∨ v = 3 ∨ v = 4 := hv
  rcases this with rfl | rfl | rfl <;> decide

theorem wheel_system : IsWheelSystem graph 0 frameSet sequence 2 := by
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj k hk heq
    interval_cases j <;> interval_cases k <;> norm_num [sequence, Fin.ext_iff] at *
  · intro j hj
    interval_cases j <;> decide
  · refine ⟨⟨2, by decide, by decide⟩, ⟨4, by decide, by decide⟩, ?_⟩
    intro a ha hc
    have : a = 2 ∨ a = 3 ∨ a = 4 := ha
    rcases this with rfl | rfl | rfl
    · exact (show ¬ graph.Adj 2 5 by decide) (hc 5 (by decide))
    · exact (show ¬ graph.Adj 3 5 by decide) (hc 5 (by decide))
    · exact (show ¬ graph.Adj 4 1 by decide) (hc 1 (by decide))
  · intro i hi hi2
    have : i = 2 := by omega
    subst i
    refine ⟨frameSet, Set.Subset.rfl, frame_connected, ⟨3, by decide, by decide⟩,
      is_frame.2.2.2, ?_⟩
    intro a ha hc
    have : a = 2 ∨ a = 3 ∨ a = 4 := ha
    rcases this with rfl | rfl | rfl
    · exact (show ¬ graph.Adj 2 5 by decide) (hc 5 ⟨1, by omega, rfl⟩)
    · exact (show ¬ graph.Adj 3 5 by decide) (hc 5 ⟨1, by omega, rfl⟩)
    · exact (show ¬ graph.Adj 4 1 by decide) (hc 1 ⟨0, by omega, rfl⟩)
  · intro i hi hi2 hc
    interval_cases i
    · exact (show ¬ graph.Adj 5 1 by decide) (hc 1 ⟨0, by omega, rfl⟩)
    · exact (show ¬ graph.Adj 6 1 by decide) (hc 1 ⟨0, by omega, rfl⟩)
  · intro j hj
    interval_cases j <;> decide

theorem A1_eq : wheelSystemA graph 0 frameSet sequence 1 = frameSet := by
  apply Set.Subset.antisymm
  · intro v hv
    have hn := wheelSystemA_no_z v hv
    have hc := wheelSystemA_no_complete v hv
    fin_cases v <;> try { exact of_decide_eq_true rfl }
    · exact False.elim (hc (by
        rw [wheelSystemX_one]
        intro w hw
        rcases hw with rfl | rfl <;> decide))
    all_goals exact False.elim (hn (by decide))
  · exact A0_subset_A1 is_frame wheel_system

theorem good : GoodA graph 0 frameSet sequence {6,7} 6 frameSet := by
  refine ⟨by rw [A1_eq], frame_connected, ⟨2, by decide, by decide⟩,
    ⟨4, by decide, by decide⟩, ⟨3, by decide, by decide⟩, ?_,
    ⟨3, by decide, by decide⟩⟩
  intro w hw _
  rcases hw with rfl | rfl
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨4, by decide, by decide⟩

theorem minimal : ∀ B : Set (Fin 8), GoodA graph 0 frameSet sequence {6,7} 6 B →
    frameSet.ncard ≤ B.ncard := by
  intro B hB
  have hsub : B ⊆ frameSet := by simpa only [A1_eq] using hB.1
  obtain ⟨a, ha, hadj⟩ := hB.2.2.1
  have h2 : (2 : Fin 8) ∈ B := by
    have : a = 2 ∨ a = 3 ∨ a = 4 := hsub ha
    rcases this with rfl | rfl | rfl
    · exact ha
    all_goals exact False.elim ((show ¬ graph.Adj _ _ by decide) hadj)
  obtain ⟨a, ha, hadj⟩ := hB.2.2.2.1
  have h4 : (4 : Fin 8) ∈ B := by
    have : a = 2 ∨ a = 3 ∨ a = 4 := hsub ha
    rcases this with rfl | rfl | rfl
    · exact False.elim ((show ¬ graph.Adj 5 2 by decide) hadj)
    · exact False.elim ((show ¬ graph.Adj 5 3 by decide) hadj)
    · exact ha
  have h3 : (3 : Fin 8) ∈ B := by
    obtain ⟨p⟩ := hB.2.1 ⟨2,h2⟩ ⟨4,h4⟩
    cases p
    case cons =>
      rename_i b hadj p
      have heAdj : graph.Adj 2 b.val := hadj
      have hb := hsub b.property
      have : b.val = 2 ∨ b.val = 3 ∨ b.val = 4 := hb
      rcases this with he | he | he
      · rw [he] at heAdj
        exact False.elim ((show ¬ graph.Adj 2 2 by decide) heAdj)
      · exact he ▸ b.property
      · rw [he] at heAdj
        exact False.elim ((show ¬ graph.Adj 2 4 by decide) heAdj)
  apply Set.ncard_le_ncard (ht := Set.toFinite B)
  intro v hv
  rcases hv with rfl | rfl | rfl
  · exact h2
  · exact h3
  · exact h4

theorem inductive_conclusion : Concl192 graph 0 frameSet sequence ({6,7} \ {6}) := by
  have he : ({6,7} \ {6} : Set (Fin 8)) = {7} := by ext v; fin_cases v <;> decide
  rw [he]
  refine ⟨?_, [0,1,2,3,4,5], ?_, by decide, by decide, by decide, ?_⟩
  · intro w hw
    rcases hw with rfl
    decide
  · refine ⟨⟨?_, by decide⟩, ⟨⟨7, by decide⟩, ?_, by decide⟩,
      0, 1, 4, 5, by decide, by decide, by decide, by decide,
      ?_, ?_, by decide, by decide, by decide, by decide⟩
    · refine ⟨by decide, by decide, ?_⟩
      intro i j hi hj
      have hi' : i < 6 := hi
      have hj' : j < 6 := hj
      interval_cases i <;> interval_cases j <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;> decide
    · intro a b
      have hab : a = b := Subtype.ext (a.property.trans b.property.symm)
      rw [hab]
    · unfold EdgeComplete VertexComplete
      decide
    · unfold EdgeComplete VertexComplete
      decide
  · rw [A1_eq]
    intro v hv
    change v ∈ [0,1,2,3,4,5] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    change (v = 1 ∨ v = 5 ∨ v = 0) ∨ v = 2 ∨ v = 3 ∨ v = 4
    tauto

theorem no_required_path : ¬ ∃ P : List (Fin 8),
    IsPathFrom graph P (sequence 0) (sequence 1) ∧
    (∀ w ∈ SPGT.interior P, w ∈ frameSet) ∧
    2 ≤ {e : Sym2 (Fin 8) | ∃ u ∈ P, ∃ v ∈ P, e = s(u,v) ∧
      EdgeComplete graph ({6,7} \ {6}) u v}.ncard := by
  rintro ⟨P, hP, hint, hcard⟩
  have hmem : ∀ v ∈ P, v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by
    intro v hv
    by_cases h1 : v = 1
    · exact Or.inl h1
    by_cases h5 : v = 5
    · exact Or.inr (Or.inr (Or.inr (Or.inr h5)))
    have hm := hint v ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hv,h1,h5⟩)
    have : v = 2 ∨ v = 3 ∨ v = 4 := hm
    tauto
  have hs : {e : Sym2 (Fin 8) | ∃ u ∈ P, ∃ v ∈ P, e = s(u,v) ∧
      EdgeComplete graph ({6,7} \ {6}) u v} ⊆ {s(4,5)} := by
    rintro e ⟨u, hu, v, hv, rfl, hadj, huc, hvc⟩
    have hu7 := huc 7 (by decide)
    have hv7 := hvc 7 (by decide)
    have hu' := hmem u hu
    have hv' := hmem v hv
    rcases hu' with rfl | rfl | rfl | rfl | rfl <;>
      rcases hv' with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [adj_decide]
  have := Set.ncard_le_ncard hs
  simp only [Set.ncard_singleton] at this
  omega

/-- The original bridge, specialized to `Fin 8`, is false. All its hypotheses
hold in the graph above, including cardinal minimality of `A`. -/
theorem original_bridge_false : ¬ (∀ (G : SimpleGraph (Fin 8)) (z : Fin 8)
    (A₀ : Set (Fin 8)) (x : ℕ → Fin 8), IsWheelSystem G z A₀ x 2 →
    ∀ (Y : Set (Fin 8)) (y : Fin 8) (A : Set (Fin 8)), GoodA G z A₀ x Y y A →
    (∀ B : Set (Fin 8), GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard) →
    Concl192 G z A₀ x (Y \ {y}) →
    ∃ P : List (Fin 8), IsPathFrom G P (x 0) (x 1) ∧
      (∀ w ∈ SPGT.interior P, w ∈ A) ∧
      2 ≤ {e : Sym2 (Fin 8) | ∃ u ∈ P, ∃ v ∈ P, e = s(u,v) ∧
        EdgeComplete G (Y \ {y}) u v}.ncard) := by
  intro h
  exact no_required_path (h graph 0 frameSet sequence wheel_system {6,7} 6
    frameSet good minimal inductive_conclusion)

end Workspace.ProofLemmas.Thm192Claim2Counterexample
