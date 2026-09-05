import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HyperprismFromPrism

/-!
# A long arm of a prism is a staircase banister

The proof of 13.4 says, without a separate citation, that a long odd prism contains a
staircase.  This file supplies the elementary construction hidden in that sentence.  Choose
one prism path as the banister.  The other two paths are the two rungs of a single step; their
interiors form the middle class of the strip.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.PrismYieldsStaircase

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas

variable {V : Type*} {G : SimpleGraph V}

private def stripA (a : Fin 3 → V) (i j : Fin 3) : Set V := {a i, a j}

private def stripB (b : Fin 3 → V) (i j : Fin 3) : Set V := {b i, b j}

private def stripC (a b : Fin 3 → V) (R : Fin 3 → List V) (i j : Fin 3) : Set V :=
  ({x : V | x ∈ R i} ∪ {x : V | x ∈ R j}) \ (stripA a i j ∪ stripB b i j)

private theorem partition_pair {x y : V} {X Y : Set V}
    (hunion : X ∪ Y = ({x, y} : Set V)) (hdisj : Disjoint X Y)
    (hX : X.Nonempty) (hY : Y.Nonempty) :
    (x ∈ X ∧ y ∈ Y) ∨ (y ∈ X ∧ x ∈ Y) := by
  have hx : x ∈ X ∨ x ∈ Y := by
    have : x ∈ X ∪ Y := by rw [hunion]; simp
    exact this
  have hy : y ∈ X ∨ y ∈ Y := by
    have : y ∈ X ∪ Y := by rw [hunion]; simp
    exact this
  rcases hx with hxX | hxY <;> rcases hy with hyX | hyY
  · obtain ⟨z, hzY⟩ := hY
    have hz : z = x ∨ z = y := by
      have : z ∈ ({x, y} : Set V) := by rw [← hunion]; exact Or.inr hzY
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hz with rfl | rfl
    · exact False.elim (Set.disjoint_left.mp hdisj hxX hzY)
    · exact False.elim (Set.disjoint_left.mp hdisj hyX hzY)
  · exact Or.inl ⟨hxX, hyY⟩
  · exact Or.inr ⟨hyX, hxY⟩
  · obtain ⟨z, hzX⟩ := hX
    have hz : z = x ∨ z = y := by
      have : z ∈ ({x, y} : Set V) := by rw [← hunion]; exact Or.inl hzX
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    rcases hz with rfl | rfl
    · exact False.elim (Set.disjoint_left.mp hdisj hzX hxY)
    · exact False.elim (Set.disjoint_left.mp hdisj hzX hyY)

private theorem rung_first {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    IsRungOfStrip G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a i) (R i) (b i) := by
  have hpath := HyperprismFromPrism.formPrism_path h i
  have hdisj := HyperprismFromPrism.formPrism_disjoint h hij
  refine ⟨hpath, by simp [stripA], by simp [stripB], ?_, ?_, ?_⟩
  · intro w hw hwA
    simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff] at hwA
    rcases hwA with hwi | hwj
    · exact hwi
    · exfalso
      subst w
      exact hdisj (a j) hw
        (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h j)).1
  · intro w hw hwB
    simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hwB
    rcases hwB with hwi | hwj
    · exact hwi
    · exfalso
      subst w
      exact hdisj (b j) hw
        (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h j)).2
  · intro w hwint
    have hwdata := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hwint
    refine ⟨Or.inl hwdata.1, ?_⟩
    rintro (hwA | hwB)
    · simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff] at hwA
      rcases hwA with hwi | hwj
      · exact hwdata.2.1 hwi
      · subst w
        exact hdisj (a j) hwdata.1
          (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h j)).1
    · simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hwB
      rcases hwB with hwi | hwj
      · exact hwdata.2.2 hwi
      · subst w
        exact hdisj (b j) hwdata.1
          (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h j)).2

private theorem rung_second {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    IsRungOfStrip G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a j) (R j) (b j) := by
  simpa [stripA, stripB, stripC, Set.pair_comm, Set.union_comm] using
    (rung_first h hij.symm)

private theorem prism_step {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    IsStep G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a i) (R i) (b i) (a j) (R j) (b j) := by
  exact ⟨rung_first h hij, rung_second h hij,
    HyperprismFromPrism.formPrism_disjoint h hij,
    HyperprismFromPrism.formPrism_cross h hij⟩

private theorem prism_step_reverse {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    IsStep G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a j) (R j) (b j) (a i) (R i) (b i) := by
  refine ⟨rung_second h hij, rung_first h hij,
    HyperprismFromPrism.formPrism_disjoint h hij.symm, ?_⟩
  intro u hu v hv
  rw [SimpleGraph.adj_comm,
    HyperprismFromPrism.formPrism_cross h hij v hv u hu]
  tauto

private theorem mem_one_of_strip_paths {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} {x : V}
    (hx : x ∈ stripA a i j ∪ stripB b i j ∪ stripC a b R i j) :
    x ∈ R i ∨ x ∈ R j := by
  rcases hx with (hxA | hxB) | hxC
  · simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff] at hxA
    rcases hxA with rfl | rfl
    · exact Or.inl (PathBasics.isPathFrom_ends_mem
        (HyperprismFromPrism.formPrism_path h i)).1
    · exact Or.inr (PathBasics.isPathFrom_ends_mem
        (HyperprismFromPrism.formPrism_path h j)).1
  · simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hxB
    rcases hxB with rfl | rfl
    · exact Or.inl (PathBasics.isPathFrom_ends_mem
        (HyperprismFromPrism.formPrism_path h i)).2
    · exact Or.inr (PathBasics.isPathFrom_ends_mem
        (HyperprismFromPrism.formPrism_path h j)).2
  · exact hxC.1

private theorem stepConnected_of_two_prism_paths
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j) :
    StepConnected G (stripA a i j) (stripC a b R i j) (stripB b i j) := by
  have hstep := prism_step h hij
  have hstep' := prism_step_reverse h hij
  have hAB : Disjoint (stripA a i j) (stripB b i j) := by
    refine Set.disjoint_left.mpr ?_
    intro x hxA hxB
    simp only [stripA, stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hxA hxB
    rcases hxA with hxi | hxj <;> rcases hxB with hxi' | hxj' <;> subst x
    · exact h.2.2.1 i i hxi'
    · exact h.2.2.1 i j hxj'
    · exact h.2.2.1 j i hxi'
    · exact h.2.2.1 j j hxj'
  have hAC : Disjoint (stripA a i j) (stripC a b R i j) := by
    refine Set.disjoint_left.mpr ?_
    exact fun _ hxA hxC => hxC.2 (Or.inl hxA)
  have hBC : Disjoint (stripB b i j) (stripC a b R i j) := by
    refine Set.disjoint_left.mpr ?_
    exact fun _ hxB hxC => hxC.2 (Or.inr hxB)
  refine ⟨⟨hAB, hAC, hBC⟩, ⟨⟨a i, by simp [stripA]⟩, ⟨b i, by simp [stripB]⟩⟩,
    ?_, ?_, ?_⟩
  · intro v hv
    rcases mem_one_of_strip_paths h hv with hvi | hvj
    · exact ⟨a i, R i, b i, rung_first h hij, hvi⟩
    · exact ⟨a j, R j, b j, rung_second h hij, hvj⟩
  · intro v hv
    refine ⟨a i, R i, b i, a j, R j, b j, hstep, ?_⟩
    exact mem_one_of_strip_paths h hv
  · intro X Y hXY hdisj hX hY
    rcases hXY with hA | hB
    · rcases partition_pair hA hdisj hX hY with hp | hp
      · exact ⟨a i, R i, b i, a j, R j, b j, hstep,
          Or.inl hp.1, Or.inl hp.2⟩
      · exact ⟨a j, R j, b j, a i, R i, b i, hstep',
          Or.inl hp.1, Or.inl hp.2⟩
    · rcases partition_pair hB hdisj hX hY with hp | hp
      · exact ⟨a i, R i, b i, a j, R j, b j, hstep,
          Or.inr hp.1, Or.inr hp.2⟩
      · exact ⟨a j, R j, b j, a i, R i, b i, hstep',
          Or.inr hp.1, Or.inr hp.2⟩

private theorem left_adj_iff {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j)
    {y : V} (hy : y ∈ R j) : G.Adj (a i) y ↔ y = a j := by
  have hai : a i ∈ R i :=
    (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h i)).1
  simpa [h.2.2.1 i i] using
    (HyperprismFromPrism.formPrism_cross h hij (a i) hai y hy)

private theorem right_adj_iff {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2)) {i j : Fin 3} (hij : i ≠ j)
    {y : V} (hy : y ∈ R j) : G.Adj (b i) y ↔ y = b j := by
  have hbi : b i ∈ R i :=
    (PathBasics.isPathFrom_ends_mem (HyperprismFromPrism.formPrism_path h i)).2
  simpa [h.2.2.1 i i, (h.2.2.1 i i).symm] using
    (HyperprismFromPrism.formPrism_cross h hij (b i) hbi y hy)

private theorem isBanister_of_third_prism_path
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    {k i j : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) :
    IsBanister G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a k) (R k) (b k) := by
  have hpath := HyperprismFromPrism.formPrism_path h k
  have hmemA : a k ∈ R k := (PathBasics.isPathFrom_ends_mem hpath).1
  have hmemB : b k ∈ R k := (PathBasics.isPathFrom_ends_mem hpath).2
  have hout : ∀ v ∈ R k,
      v ∉ stripA a i j ∪ stripB b i j ∪ stripC a b R i j := by
    intro v hv hvS
    rcases mem_one_of_strip_paths h hvS with hvi | hvj
    · exact HyperprismFromPrism.formPrism_disjoint h hki v hv hvi
    · exact HyperprismFromPrism.formPrism_disjoint h hkj v hv hvj
  have hA_not_BC : ∀ y,
      y ∈ stripB b i j ∪ stripC a b R i j → y ∉ stripA a i j := by
    intro y hy hyA
    rcases hy with hyB | hyC
    · simp only [stripA, stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hyA hyB
      rcases hyA with hai | haj <;> rcases hyB with hbi | hbj
      · exact h.2.2.1 i i (hai.symm.trans hbi)
      · exact h.2.2.1 i j (hai.symm.trans hbj)
      · exact h.2.2.1 j i (haj.symm.trans hbi)
      · exact h.2.2.1 j j (haj.symm.trans hbj)
    · exact hyC.2 (Or.inl hyA)
  have hB_not_AC : ∀ y,
      y ∈ stripA a i j ∪ stripC a b R i j → y ∉ stripB b i j := by
    intro y hy hyB
    rcases hy with hyA | hyC
    · exact hA_not_BC y (Or.inl hyB) hyA
    · exact hyC.2 (Or.inr hyB)
  refine ⟨hpath, hout, ?_, ?_, ?_⟩
  · refine ⟨hout (a k) hmemA, ?_, ?_⟩
    · intro y hyA
      simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff] at hyA
      rcases hyA with rfl | rfl
      · exact h.1 k i hki
      · exact h.1 k j hkj
    · intro y hyBC hadj
      have hyS : y ∈ stripA a i j ∪ stripB b i j ∪ stripC a b R i j := by
        rcases hyBC with hyB | hyC
        · exact Or.inl (Or.inr hyB)
        · exact Or.inr hyC
      rcases mem_one_of_strip_paths h hyS with hyi | hyj
      · exact hA_not_BC y hyBC (by
          simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inl ((left_adj_iff h hki hyi).mp hadj))
      · exact hA_not_BC y hyBC (by
          simp only [stripA, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inr ((left_adj_iff h hkj hyj).mp hadj))
  · refine ⟨hout (b k) hmemB, ?_, ?_⟩
    · intro y hyB
      simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff] at hyB
      rcases hyB with rfl | rfl
      · exact h.2.1 k i hki
      · exact h.2.1 k j hkj
    · intro y hyAC hadj
      have hyS : y ∈ stripA a i j ∪ stripB b i j ∪ stripC a b R i j := by
        rcases hyAC with hyA | hyC
        · exact Or.inl (Or.inl hyA)
        · exact Or.inr hyC
      rcases mem_one_of_strip_paths h hyS with hyi | hyj
      · exact hB_not_AC y hyAC (by
          simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inl ((right_adj_iff h hki hyi).mp hadj))
      · exact hB_not_AC y hyAC (by
          simp only [stripB, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact Or.inr ((right_adj_iff h hkj hyj).mp hadj))
  · intro u hu v hvS hadj
    have hudata := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hu
    rcases mem_one_of_strip_paths h hvS with hvi | hvj
    · rcases (HyperprismFromPrism.formPrism_cross h hki u hudata.1 v hvi).mp hadj with
        hc | hc
      · exact hudata.2.1 hc.1
      · exact hudata.2.2 hc.1
    · rcases (HyperprismFromPrism.formPrism_cross h hkj u hudata.1 v hvj).mp hadj with
        hc | hc
      · exact hudata.2.1 hc.1
      · exact hudata.2.2 hc.1

/-- Choosing one arm of a prism as a banister and the other two as a step gives a staircase,
provided the chosen arm has length at least three. -/
theorem isStaircase_of_formPrism
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    {k i j : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (hlen : 3 ≤ pathLength (R k)) :
    IsStaircase G (stripA a i j) (stripC a b R i j) (stripB b i j)
      (a k) (R k) (b k) := by
  exact ⟨stepConnected_of_two_prism_paths h hij,
    isBanister_of_third_prism_path h hki hkj, hlen⟩

/-- Existential interface to `isStaircase_of_formPrism`, hiding the concrete three strip
classes when a caller only needs the staircase promised in the paper. -/
theorem exists_isStaircase_of_formPrism
    {a b : Fin 3 → V} {R : Fin 3 → List V}
    (h : FormPrism G a b (R 0) (R 1) (R 2))
    {k i j : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (hij : i ≠ j)
    (hlen : 3 ≤ pathLength (R k)) :
    ∃ A C B : Set V, IsStaircase G A C B (a k) (R k) (b k) :=
  ⟨stripA a i j, stripC a b R i j, stripB b i j,
    isStaircase_of_formPrism h hki hkj hij hlen⟩

end Workspace.ProofLemmas.PrismYieldsStaircase
