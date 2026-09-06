import Workspace.ProofLemmas.Thm131ComplementStars
import Workspace.ProofLemmas.Thm131Trajectory
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Enlarging the staircase in the proof of 13.1

Two of the printed claims of 13.1 end by exhibiting a staircase which properly
contains the given one, contradicting its (strong) maximality.  This module
builds the two enlargements.

* PAPER (claim (2), printed p. 80): *"Since `n` is odd it follows that `n > 2`
  and so `w₁, w₂` are both `A ∪ B`-complete.  But then
  `S' = (A ∪ {w₂}, C, B ∪ {w₁})` is a step-connected strip, and `(S', a-R-b)`
  is a staircase, contrary to the maximality of `(S, R₀)`."*
  PAPER (claim (6), printed p. 81): *"… there are nonadjacent vertices
  `x, y ∈ W \ {wₙ}` such that `x-a-R-b-y` is a path.  But then
  `((A ∪ {x}, ∅, B ∪ {y}), a-R-b)` is a staircase, contrary to the maximality
  of `(S, R₀)`."*
  Both are `staircase_adjoin_complete_pair` below (stated with a general middle
  class `C`, as in claim (2); claim (6) instantiates `C = ∅` by claim (5)).

* PAPER (claim (7), printed p. 81): *"Hence `x, y` are both anticomplete to
  `A ∪ B`, and so `((B ∪ {x}, ∅, A ∪ {y}), a-w₁-⋯-wₙ)` is a staircase in `G`,
  contradicting that `(S, R₀)` is strongly maximal."*  This is
  `stepConnected_compl_adjoin_interior_pair` together with
  `staircase_compl_adjoin_pair`; the latter also serves the sub-case
  *"`R'` has length 1"* of the same claim and the closing paragraph.
-/

namespace Workspace.ProofLemmas.Thm131Enlarge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131ComplementStars
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm132Infrastructure

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

/-- Mirror of `Thm131Trajectory.exists_right_nonneighbor`: every vertex of the
right class of a step-connected strip has a nonneighbour in the left class. -/
theorem exists_left_nonneighbor
    {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {b : V} (hb : b ∈ B) :
    ∃ a ∈ A, ¬ G.Adj a b := by
  obtain ⟨⟨hdAB, -, -⟩, -, -, hinstep, -⟩ := hS
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ :=
    hinstep b (Or.inl (Or.inr hb))
  obtain ⟨hr₁, hr₂, -, hcross⟩ := hstep
  have hne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := by
    intro x hx y hy hxy
    exact Set.disjoint_left.mp hdAB hx (hxy ▸ hy)
  rcases hmem with hmem | hmem
  · refine ⟨a₂, hr₂.2.1, ?_⟩
    intro hadj
    rcases (hcross b hmem a₂
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1).mp hadj.symm with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne a₁ hr₁.2.1 b hb h1.symm
    · exact hne a₂ hr₂.2.1 b₂ hr₂.2.2.1 h2
  · refine ⟨a₁, hr₁.2.1, ?_⟩
    intro hadj
    rcases (hcross a₁
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).1 b hmem).mp hadj with
      ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hne a₂ hr₂.2.1 b hb h2.symm
    · exact hne a₁ hr₁.2.1 b₁ hr₁.2.2.1 h1

/-! ### The `G`-side enlargement (claims (2) and (6)) -/

section Adjoin

variable {G : SimpleGraph V} {A C B : Set V} {u v : V}

/-- The two-vertex rung `u`-`b` of the enlarged strip. -/
private theorem rungUB (hS : StepConnected G A C B)
    (hu : u ∉ A ∪ B ∪ C)
    (huAB : VertexComplete G u (A ∪ B)) (huv : u ≠ v)
    {b : V} (hb : b ∈ B) :
    IsRungOfStrip G (A ∪ {u}) C (B ∪ {v}) u [u, b] b := by
  have hub : G.Adj u b := huAB b (Or.inr hb)
  refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hub, rfl, by simp⟩,
    Or.inr rfl, Or.inl hb, ?_, ?_, by simp [Workspace.Types.Core.SPGT.interior]⟩
  · intro z hz hzL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rfl
    · exfalso
      rcases hzL with hzA | hzu
      · exact Set.disjoint_left.mp hS.1.1 hzA hb
      · exact hub.ne' (Set.mem_singleton_iff.mp hzu)
  · intro z hz hzR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exfalso
      rcases hzR with hzB | hzv
      · exact hu (Or.inl (Or.inr hzB))
      · exact huv (Set.mem_singleton_iff.mp hzv)
    · rfl

/-- The two-vertex rung `a`-`v` of the enlarged strip. -/
private theorem rungAV (hS : StepConnected G A C B)
    (hv : v ∉ A ∪ B ∪ C)
    (hvAB : VertexComplete G v (A ∪ B)) (huv : u ≠ v)
    {a : V} (ha : a ∈ A) :
    IsRungOfStrip G (A ∪ {u}) C (B ∪ {v}) a [a, v] v := by
  have hav : G.Adj a v := (hvAB a (Or.inl ha)).symm
  refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hav, rfl, by simp⟩,
    Or.inl ha, Or.inr rfl, ?_, ?_, by simp [Workspace.Types.Core.SPGT.interior]⟩
  · intro z hz hzL
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · rfl
    · exfalso
      rcases hzL with hzA | hzu
      · exact hv (Or.inl (Or.inl hzA))
      · exact huv (Set.mem_singleton_iff.mp hzu).symm
  · intro z hz hzR
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exfalso
      rcases hzR with hzB | hzv
      · exact Set.disjoint_left.mp hS.1.1 ha hzB
      · exact hav.ne (Set.mem_singleton_iff.mp hzv)
    · rfl

/-- The steps of the enlarged strip: one new rung on each side, joined across a
nonedge of the old strip. -/
private theorem mkStep (hS : StepConnected G A C B)
    (hu : u ∉ A ∪ B ∪ C) (hv : v ∉ A ∪ B ∪ C)
    (huAB : VertexComplete G u (A ∪ B)) (hvAB : VertexComplete G v (A ∪ B))
    (huvne : u ≠ v) (huvadj : ¬ G.Adj u v)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (hab : ¬ G.Adj a b) :
    IsStep G (A ∪ {u}) C (B ∪ {v}) u [u, b] b a [a, v] v := by
  have hub : G.Adj u b := huAB b (Or.inr hb)
  have hav : G.Adj a v := (hvAB a (Or.inl ha)).symm
  have hua : G.Adj u a := huAB a (Or.inl ha)
  have hbv : G.Adj b v := (hvAB b (Or.inr hb)).symm
  have hune : u ≠ a := fun he => hu (Or.inl (Or.inl (he ▸ ha)))
  have hbne : b ≠ v := hbv.ne
  have hba : ¬ G.Adj b a := fun h => hab h.symm
  refine ⟨rungUB hS hu huAB huvne hb, rungAV hS hv hvAB huvne ha, ?_, ?_⟩
  · intro z hz₁ hz₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
    rcases hz₁ with h1 | h1 <;> subst h1 <;> rcases hz₂ with h | h
    · exact hune h
    · exact huvne h
    · exact Set.disjoint_left.mp hS.1.1 ha (h ▸ hb)
    · exact hbne h
  · intro z hz₁ y hz₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
    rcases hz₁ with h1 | h1 <;> rcases hz₂ with h2 | h2 <;> rw [h1, h2]
    · exact iff_of_true hua (Or.inl ⟨rfl, rfl⟩)
    · refine iff_of_false huvadj ?_
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hv (Or.inl (Or.inl (h ▸ ha)))
      · exact hub.ne h
    · refine iff_of_false hba ?_
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact hub.ne' h
      · exact hav.ne h
    · exact iff_of_true hbv (Or.inr ⟨rfl, rfl⟩)

/-- A rung of the old strip is a rung of the enlarged one. -/
private theorem rungOld (hu : u ∉ A ∪ B ∪ C) (hv : v ∉ A ∪ B ∪ C)
    {a b : V} {P : List V} (hP : IsRungOfStrip G A C B a P b) :
    IsRungOfStrip G (A ∪ {u}) C (B ∪ {v}) a P b := by
  refine ⟨hP.1, Or.inl hP.2.1, Or.inl hP.2.2.1, ?_, ?_, hP.2.2.2.2.2⟩
  · intro z hz hzL
    rcases hzL with hzA | hzu
    · exact hP.2.2.2.1 z hz hzA
    · exact absurd (rung_mem_strip hP z hz) ((Set.mem_singleton_iff.mp hzu) ▸ hu)
  · intro z hz hzR
    rcases hzR with hzB | hzv
    · exact hP.2.2.2.2.1 z hz hzB
    · exact absurd (rung_mem_strip hP z hz) ((Set.mem_singleton_iff.mp hzv) ▸ hv)

/-- A step of the old strip is a step of the enlarged one. -/
private theorem stepOld (hu : u ∉ A ∪ B ∪ C) (hv : v ∉ A ∪ B ∪ C)
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hs : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G (A ∪ {u}) C (B ∪ {v}) a₁ R₁ b₁ a₂ R₂ b₂ :=
  ⟨rungOld hu hv hs.1, rungOld hu hv hs.2.1, hs.2.2.1, hs.2.2.2⟩

/-- PAPER (claim (2), printed p. 80): *"`w₁, w₂` are both `A ∪ B`-complete.  But
then `S' = (A ∪ {w₂}, C, B ∪ {w₁})` is a step-connected strip"*; and the same
construction for claim (6)'s `(A ∪ {x}, ∅, B ∪ {y})`. -/
theorem stepConnected_adjoin_complete_pair (hS : StepConnected G A C B)
    (hu : u ∉ A ∪ B ∪ C) (hv : v ∉ A ∪ B ∪ C)
    (huAB : VertexComplete G u (A ∪ B)) (hvAB : VertexComplete G v (A ∪ B))
    (huvne : u ≠ v) (huvadj : ¬ G.Adj u v) :
    StepConnected G (A ∪ {u}) C (B ∪ {v}) := by
  classical
  obtain ⟨a₀, ha₀A⟩ := hS.2.1.1
  obtain ⟨b₀, hb₀B, ha₀b₀⟩ := exists_right_nonneighbor hS ha₀A
  have hdefStep := mkStep hS hu hv huAB hvAB huvne huvadj ha₀A hb₀B ha₀b₀
  refine ⟨⟨?_, ?_, ?_⟩, ⟨⟨u, Or.inr rfl⟩, ⟨v, Or.inr rfl⟩⟩, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.mpr ?_
    rintro z (hzA | hzu) (hzB | hzv)
    · exact Set.disjoint_left.mp hS.1.1 hzA hzB
    · exact hv (Or.inl (Or.inl ((Set.mem_singleton_iff.mp hzv) ▸ hzA)))
    · exact hu (Or.inl (Or.inr ((Set.mem_singleton_iff.mp hzu) ▸ hzB)))
    · exact huvne ((Set.mem_singleton_iff.mp hzu).symm.trans (Set.mem_singleton_iff.mp hzv))
  · refine Set.disjoint_left.mpr ?_
    rintro z (hzA | hzu) hzC
    · exact Set.disjoint_left.mp hS.1.2.1 hzA hzC
    · exact hu (Or.inr ((Set.mem_singleton_iff.mp hzu) ▸ hzC))
  · refine Set.disjoint_left.mpr ?_
    rintro z (hzB | hzv) hzC
    · exact Set.disjoint_left.mp hS.1.2.2 hzB hzC
    · exact hv (Or.inr ((Set.mem_singleton_iff.mp hzv) ▸ hzC))
  · rintro z (((hzA | hzu) | (hzB | hzv)) | hzC)
    · obtain ⟨a, P, b, hP, hzP⟩ := hS.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨a, P, b, rungOld hu hv hP, hzP⟩
    · exact ⟨u, [u, b₀], b₀, rungUB hS hu huAB huvne hb₀B,
        (Set.mem_singleton_iff.mp hzu) ▸ (by simp)⟩
    · obtain ⟨a, P, b, hP, hzP⟩ := hS.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨a, P, b, rungOld hu hv hP, hzP⟩
    · exact ⟨a₀, [a₀, v], v, rungAV hS hv hvAB huvne ha₀A,
        (Set.mem_singleton_iff.mp hzv) ▸ (by simp)⟩
    · obtain ⟨a, P, b, hP, hzP⟩ := hS.2.2.1 z (Or.inr hzC)
      exact ⟨a, P, b, rungOld hu hv hP, hzP⟩
  · rintro z (((hzA | hzu) | (hzB | hzv)) | hzC)
    · obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hzm⟩ := hS.2.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, stepOld hu hv hs, hzm⟩
    · exact ⟨u, [u, b₀], b₀, a₀, [a₀, v], v, hdefStep,
        Or.inl ((Set.mem_singleton_iff.mp hzu) ▸ (by simp))⟩
    · obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hzm⟩ := hS.2.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, stepOld hu hv hs, hzm⟩
    · exact ⟨u, [u, b₀], b₀, a₀, [a₀, v], v, hdefStep,
        Or.inr ((Set.mem_singleton_iff.mp hzv) ▸ (by simp))⟩
    · obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hzm⟩ := hS.2.2.2.1 z (Or.inr hzC)
      exact ⟨a₁, R₁, b₁, a₂, R₂, b₂, stepOld hu hv hs, hzm⟩
  · intro X Y hXY hXYdis hX hY
    rcases hXY with hXY | hXY
    · have huXY : u ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases huXY with huX | huY
      · obtain ⟨z, hzY⟩ := hY
        have hzA : z ∈ A := by
          rcases (show z ∈ A ∪ {u} by rw [← hXY]; exact Or.inr hzY) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzY)
              (Set.disjoint_left.mp hXYdis huX)
        obtain ⟨c, hcB, hzc⟩ := exists_right_nonneighbor hS hzA
        exact ⟨u, [u, c], c, z, [z, v], v,
          mkStep hS hu hv huAB hvAB huvne huvadj hzA hcB hzc, Or.inl huX, Or.inl hzY⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzA : z ∈ A := by
          rcases (show z ∈ A ∪ {u} by rw [← hXY]; exact Or.inl hzX) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzX)
              (Set.disjoint_right.mp hXYdis huY)
        obtain ⟨c, hcB, hzc⟩ := exists_right_nonneighbor hS hzA
        exact ⟨z, [z, v], v, u, [u, c], c,
          step_symm (mkStep hS hu hv huAB hvAB huvne huvadj hzA hcB hzc),
          Or.inl hzX, Or.inl huY⟩
    · have hvXY : v ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases hvXY with hvX | hvY
      · obtain ⟨z, hzY⟩ := hY
        have hzB : z ∈ B := by
          rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inr hzY) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzY)
              (Set.disjoint_left.mp hXYdis hvX)
        obtain ⟨c, hcA, hzc⟩ := exists_left_nonneighbor hS hzB
        exact ⟨c, [c, v], v, u, [u, z], z,
          step_symm (mkStep hS hu hv huAB hvAB huvne huvadj hcA hzB hzc),
          Or.inr hvX, Or.inr hzY⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzB : z ∈ B := by
          rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inl hzX) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzX)
              (Set.disjoint_right.mp hXYdis hvY)
        obtain ⟨c, hcA, hzc⟩ := exists_left_nonneighbor hS hzB
        exact ⟨u, [u, z], z, c, [c, v], v,
          mkStep hS hu hv huAB hvAB huvne huvadj hcA hzB hzc,
          Or.inr hzX, Or.inr hvY⟩

/-- PAPER (claim (2), printed p. 80): *"… and `(S', a-R-b)` is a staircase"*;
PAPER (claim (6), printed p. 81): *"But then `((A ∪ {x}, ∅, B ∪ {y}), a-R-b)` is
a staircase"*.  The hypotheses `hua`, `hvb`, `huother`, `hvother` are the printed
*"the only edges between `w₁, w₂` and `R` are `w₁b` and `w₂a`"*, resp.
*"`x-a-R-b-y` is a path"*. -/
theorem staircase_adjoin_complete_pair (hS : StepConnected G A C B)
    (hu : u ∉ A ∪ B ∪ C) (hv : v ∉ A ∪ B ∪ C)
    (huAB : VertexComplete G u (A ∪ B)) (hvAB : VertexComplete G v (A ∪ B))
    (huvne : u ≠ v) (huvadj : ¬ G.Adj u v)
    {a b : V} {R : List V} (hR : IsBanister G A C B a R b)
    (hua : G.Adj u a) (hvb : G.Adj v b)
    (huother : ∀ z ∈ R, z ≠ a → ¬ G.Adj u z)
    (hvother : ∀ z ∈ R, z ≠ b → ¬ G.Adj v z)
    (h3 : 3 ≤ pathLength R) :
    IsStaircase G (A ∪ {u}) C (B ∪ {v}) a R b := by
  classical
  obtain ⟨a₀, ha₀A⟩ := hS.2.1.1
  obtain ⟨b₀, hb₀B⟩ := hS.2.1.2
  have haR : a ∈ R := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR.1).1
  have hbR : b ∈ R := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR.1).2
  have hab : a ≠ b := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hR.1 (by omega)
  -- `u` and `v` are `A ∪ B`-complete, so neither lies on the banister.
  have hnotR : ∀ z : V, VertexComplete G z (A ∪ B) → z ∉ R := by
    intro z hz hzR
    by_cases hza : z = a
    · exact hR.2.2.1.2.2 b₀ (Or.inl hb₀B) (hza ▸ hz b₀ (Or.inr hb₀B))
    by_cases hzb : z = b
    · exact hR.2.2.2.1.2.2 a₀ (Or.inl ha₀A) (hzb ▸ hz a₀ (Or.inl ha₀A))
    · exact hR.2.2.2.2 z
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
          ⟨hzR, hza, hzb⟩) a₀ (Or.inl (Or.inl ha₀A)) (hz a₀ (Or.inl ha₀A))
  have huR : u ∉ R := hnotR u huAB
  have hvR : v ∉ R := hnotR v hvAB
  have hout : ∀ z ∈ R, z ∉ (A ∪ {u}) ∪ (B ∪ {v}) ∪ C := by
    intro z hz hzn
    rcases hzn with ((hzA | hzu) | (hzB | hzv)) | hzC
    · exact hR.2.1 z hz (Or.inl (Or.inl hzA))
    · exact huR ((Set.mem_singleton_iff.mp hzu) ▸ hz)
    · exact hR.2.1 z hz (Or.inl (Or.inr hzB))
    · exact hvR ((Set.mem_singleton_iff.mp hzv) ▸ hz)
    · exact hR.2.1 z hz (Or.inr hzC)
  refine ⟨stepConnected_adjoin_complete_pair hS hu hv huAB hvAB huvne huvadj,
    ⟨hR.1, hout, ?_, ?_, ?_⟩, h3⟩
  · refine ⟨hout a haR, ?_, ?_⟩
    · rintro z (hzA | hzu)
      · exact hR.2.2.1.2.1 z hzA
      · exact (Set.mem_singleton_iff.mp hzu) ▸ hua.symm
    · rintro z ((hzB | hzv) | hzC) hadj
      · exact hR.2.2.1.2.2 z (Or.inl hzB) hadj
      · exact hvother a haR hab ((Set.mem_singleton_iff.mp hzv) ▸ hadj).symm
      · exact hR.2.2.1.2.2 z (Or.inr hzC) hadj
  · refine ⟨hout b hbR, ?_, ?_⟩
    · rintro z (hzB | hzv)
      · exact hR.2.2.2.1.2.1 z hzB
      · exact (Set.mem_singleton_iff.mp hzv) ▸ hvb.symm
    · rintro z ((hzA | hzu) | hzC) hadj
      · exact hR.2.2.2.1.2.2 z (Or.inl hzA) hadj
      · exact huother b hbR hab.symm ((Set.mem_singleton_iff.mp hzu) ▸ hadj).symm
      · exact hR.2.2.2.1.2.2 z (Or.inr hzC) hadj
  · intro z hz y hy hadj
    have hzd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).1 hz
    rcases hy with ((hyA | hyu) | (hyB | hyv)) | hyC
    · exact hR.2.2.2.2 z hz y (Or.inl (Or.inl hyA)) hadj
    · exact huother z hzd.1 hzd.2.1 ((Set.mem_singleton_iff.mp hyu) ▸ hadj).symm
    · exact hR.2.2.2.2 z hz y (Or.inl (Or.inr hyB)) hadj
    · exact hvother z hzd.1 hzd.2.2 ((Set.mem_singleton_iff.mp hyv) ▸ hadj).symm
    · exact hR.2.2.2.2 z hz y (Or.inr hyC) hadj

/-- PAPER (claims (2) and (6)): *"… contrary to the maximality of `(S, R₀)`."* -/
theorem adjoin_complete_pair_absurd {a₀ b₀ : V} {R₀ : List V}
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (hu : u ∉ A ∪ B ∪ C) {a b : V} {R : List V}
    (hstair : IsStaircase G (A ∪ {u}) C (B ∪ {v}) a R b) : False := by
  refine hK.2 ⟨A ∪ {u}, C, B ∪ {v}, a, R, b, hstair, fun z hz => Or.inl hz,
    fun z hz => Or.inl hz, fun z hz => hz, ?_, ?_⟩
  · rintro z ((hzA | hzB) | hzC)
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr (Or.inl hzB))
    · exact Or.inr hzC
  · intro hback
    exact hu (hback (Or.inl (Or.inl (Or.inr rfl))))

end Adjoin

/-! ### The complement-side enlargement (claim (7) and the closing paragraph) -/

section ComplAdjoin

variable {G : SimpleGraph V} {A B : Set V} {p q : V}

/-- With an empty middle class every rung is an edge, so every vertex of the
left class has a neighbour in the right class. -/
private theorem exists_edge_right (hS : StepConnected G A (∅ : Set V) B)
    {a : V} (ha : a ∈ A) : ∃ b ∈ B, G.Adj a b := by
  obtain ⟨a', P, b', hP, haP⟩ := hS.2.2.1 a (Or.inl (Or.inl ha))
  have haa' : a = a' := hP.2.2.2.1 a haP ha
  subst a
  refine ⟨b', hP.2.2.1, ?_⟩
  have hint : SPGT.interior P = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    exact Set.notMem_empty z (hP.2.2.2.2.2 z hz)
  have hlen : P.length - 2 = 0 := by
    have := Workspace.ProofLemmas.PathBasics.interior_length P
    rw [hint] at this
    simpa using this.symm
  have hne : a' ≠ b' := fun he =>
    Set.disjoint_left.mp hS.1.1 hP.2.1 (he ▸ hP.2.2.1)
  have h2 : pathLength P = 1 := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1.1
    have h1 : pathLength P ≠ 0 := fun h0 =>
      hne (by
        have := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.1.2.1 hpos
        have h2 := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.1.2.2 hpos
        rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at h0
        rw [← this, ← h2]
        exact getElem_congr rfl (by omega) _)
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at h1 ⊢
    omega
  exact Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hP.1 h2

private theorem exists_edge_left (hS : StepConnected G A (∅ : Set V) B)
    {b : V} (hb : b ∈ B) : ∃ a ∈ A, G.Adj a b := by
  obtain ⟨a', P, b', hP, hbP⟩ := hS.2.2.1 b (Or.inl (Or.inr hb))
  have hbb' : b = b' := hP.2.2.2.2.1 b hbP hb
  subst b
  refine ⟨a', hP.2.1, ?_⟩
  have hint : SPGT.interior P = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    exact Set.notMem_empty z (hP.2.2.2.2.2 z hz)
  have hlen : P.length - 2 = 0 := by
    have := Workspace.ProofLemmas.PathBasics.interior_length P
    rw [hint] at this
    simpa using this.symm
  have hne : a' ≠ b' := fun he =>
    Set.disjoint_left.mp hS.1.1 hP.2.1 (he ▸ hP.2.2.1)
  have h2 : pathLength P = 1 := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1.1
    have h1 : pathLength P ≠ 0 := fun h0 =>
      hne (by
        have := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.1.2.1 hpos
        have h2 := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.1.2.2 hpos
        rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at h0
        rw [← this, ← h2]
        exact getElem_congr rfl (by omega) _)
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at h1 ⊢
    omega
  exact Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hP.1 h2

/-- The two new rungs and the step joining them, in the complement. -/
private theorem mkStepC (hS : StepConnected G A (∅ : Set V) B)
    (hp : p ∉ A ∪ B ∪ (∅ : Set V)) (hq : q ∉ A ∪ B ∪ (∅ : Set V))
    (hpAB : VertexAnticomplete G p (A ∪ B))
    (hqAB : VertexAnticomplete G q (A ∪ B)) (hpq : G.Adj p q)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) (hab : G.Adj a b) :
    IsStep Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) p [p, a] a b [b, q] q := by
  have hpA : p ∉ A := fun h => hp (Or.inl (Or.inl h))
  have hpB : p ∉ B := fun h => hp (Or.inl (Or.inr h))
  have hqA : q ∉ A := fun h => hq (Or.inl (Or.inl h))
  have hqB : q ∉ B := fun h => hq (Or.inl (Or.inr h))
  have hpqne : p ≠ q := hpq.ne
  have hpa : Gᶜ.Adj p a :=
    (G.compl_adj p a).2 ⟨fun he => hpA (he ▸ ha), hpAB a (Or.inl ha)⟩
  have hpb : Gᶜ.Adj p b :=
    (G.compl_adj p b).2 ⟨fun he => hpB (he ▸ hb), hpAB b (Or.inr hb)⟩
  have haq : Gᶜ.Adj a q :=
    (G.compl_adj a q).2 ⟨fun he => hqA (he ▸ ha), fun h => hqAB a (Or.inl ha) h.symm⟩
  have hbq : Gᶜ.Adj b q :=
    (G.compl_adj b q).2 ⟨fun he => hqB (he ▸ hb), fun h => hqAB b (Or.inr hb) h.symm⟩
  have hane : a ≠ b := hab.ne
  have hrung₁ : IsRungOfStrip Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) p [p, a] a := by
    refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hpa, rfl, by simp⟩,
      Or.inr rfl, Or.inl ha, ?_, ?_, by simp [Workspace.Types.Core.SPGT.interior]⟩
    · intro z hz hzL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h
      · exact h
      · exfalso
        rw [h] at hzL
        rcases hzL with hzB | hzp
        · exact Set.disjoint_left.mp hS.1.1 ha hzB
        · exact hpA ((Set.mem_singleton_iff.mp hzp) ▸ ha)
    · intro z hz hzR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h
      · exfalso
        rw [h] at hzR
        rcases hzR with hzA | hzq
        · exact hpA hzA
        · exact hpqne (Set.mem_singleton_iff.mp hzq)
      · exact h
  have hrung₂ : IsRungOfStrip Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) b [b, q] q := by
    refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hbq, rfl, by simp⟩,
      Or.inl hb, Or.inr rfl, ?_, ?_, by simp [Workspace.Types.Core.SPGT.interior]⟩
    · intro z hz hzL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h
      · exact h
      · exfalso
        rw [h] at hzL
        rcases hzL with hzB | hzp
        · exact hqB hzB
        · exact hpqne (Set.mem_singleton_iff.mp hzp).symm
    · intro z hz hzR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with h | h
      · exfalso
        rw [h] at hzR
        rcases hzR with hzA | hzq
        · exact Set.disjoint_left.mp hS.1.1 hzA hb
        · exact hqB ((Set.mem_singleton_iff.mp hzq) ▸ hb)
      · exact h
  refine ⟨hrung₁, hrung₂, ?_, ?_⟩
  · intro z hz₁ hz₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
    rcases hz₁ with h1 | h1 <;> rcases hz₂ with h2 | h2 <;> rw [h1] at h2
    · exact hpB (h2 ▸ hb)
    · exact hpqne h2
    · exact hane h2
    · exact hqA (h2 ▸ ha)
  · intro z hz₁ y hz₂
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
    rcases hz₁ with h1 | h1 <;> rcases hz₂ with h2 | h2 <;> rw [h1, h2]
    · exact iff_of_true hpb (Or.inl ⟨rfl, rfl⟩)
    · refine iff_of_false (fun h => h.2 hpq) ?_
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hqB (h ▸ hb)
      · exact hpA (h ▸ ha)
    · refine iff_of_false (fun h => h.2 hab) ?_
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact hpA (h ▸ ha)
      · exact hqB (h ▸ hb)
    · exact iff_of_true haq (Or.inr ⟨rfl, rfl⟩)

/-- PAPER (claim (7), printed p. 81): *"Hence `x, y` are both anticomplete to
`A ∪ B`, and so `((B ∪ {x}, ∅, A ∪ {y}), a-w₁-⋯-wₙ)` is a staircase"* — the
step-connected strip half. -/
theorem stepConnected_compl_adjoin_interior_pair (hS : StepConnected G A (∅ : Set V) B)
    (hp : p ∉ A ∪ B ∪ (∅ : Set V)) (hq : q ∉ A ∪ B ∪ (∅ : Set V))
    (hpAB : VertexAnticomplete G p (A ∪ B))
    (hqAB : VertexAnticomplete G q (A ∪ B)) (hpq : G.Adj p q) :
    StepConnected Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) := by
  classical
  have hpA : p ∉ A := fun h => hp (Or.inl (Or.inl h))
  have hpB : p ∉ B := fun h => hp (Or.inl (Or.inr h))
  have hqA : q ∉ A := fun h => hq (Or.inl (Or.inl h))
  have hqB : q ∉ B := fun h => hq (Or.inl (Or.inr h))
  have hpqne : p ≠ q := hpq.ne
  obtain ⟨a₀, ha₀A⟩ := hS.2.1.1
  obtain ⟨b₀, hb₀B, ha₀b₀⟩ := exists_edge_right hS ha₀A
  have hdef := mkStepC hS hp hq hpAB hqAB hpq ha₀A hb₀B ha₀b₀
  refine ⟨⟨?_, Set.disjoint_empty _, Set.disjoint_empty _⟩,
    ⟨⟨p, Or.inr rfl⟩, ⟨q, Or.inr rfl⟩⟩, ?_, ?_, ?_⟩
  · refine Set.disjoint_left.mpr ?_
    rintro z (hzB | hzp) (hzA | hzq)
    · exact Set.disjoint_left.mp hS.1.1 hzA hzB
    · exact hqB ((Set.mem_singleton_iff.mp hzq) ▸ hzB)
    · exact hpA ((Set.mem_singleton_iff.mp hzp) ▸ hzA)
    · exact hpqne ((Set.mem_singleton_iff.mp hzp).symm.trans (Set.mem_singleton_iff.mp hzq))
  · rintro z (((hzB | hzp) | (hzA | hzq)) | hz0)
    · obtain ⟨c, hcA, hc⟩ := exists_edge_left hS hzB
      exact ⟨z, [z, q], q, (mkStepC hS hp hq hpAB hqAB hpq hcA hzB hc).2.1, by simp⟩
    · exact ⟨p, [p, a₀], a₀, hdef.1,
        (Set.mem_singleton_iff.mp hzp) ▸ (by simp)⟩
    · obtain ⟨c, hcB, hc⟩ := exists_edge_right hS hzA
      exact ⟨p, [p, z], z, (mkStepC hS hp hq hpAB hqAB hpq hzA hcB hc).1, by simp⟩
    · exact ⟨b₀, [b₀, q], q, hdef.2.1, (Set.mem_singleton_iff.mp hzq) ▸ (by simp)⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · rintro z (((hzB | hzp) | (hzA | hzq)) | hz0)
    · obtain ⟨c, hcA, hc⟩ := exists_edge_left hS hzB
      exact ⟨p, [p, c], c, z, [z, q], q, mkStepC hS hp hq hpAB hqAB hpq hcA hzB hc,
        Or.inr (by simp)⟩
    · exact ⟨p, [p, a₀], a₀, b₀, [b₀, q], q, hdef,
        Or.inl ((Set.mem_singleton_iff.mp hzp) ▸ (by simp))⟩
    · obtain ⟨c, hcB, hc⟩ := exists_edge_right hS hzA
      exact ⟨p, [p, z], z, c, [c, q], q, mkStepC hS hp hq hpAB hqAB hpq hzA hcB hc,
        Or.inl (by simp)⟩
    · exact ⟨p, [p, a₀], a₀, b₀, [b₀, q], q, hdef,
        Or.inr ((Set.mem_singleton_iff.mp hzq) ▸ (by simp))⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · intro X Y hXY hXYdis hX hY
    rcases hXY with hXY | hXY
    · have hpXY : p ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases hpXY with hpX | hpY
      · obtain ⟨z, hzY⟩ := hY
        have hzB : z ∈ B := by
          rcases (show z ∈ B ∪ {p} by rw [← hXY]; exact Or.inr hzY) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzY)
              (Set.disjoint_left.mp hXYdis hpX)
        obtain ⟨c, hcA, hc⟩ := exists_edge_left hS hzB
        exact ⟨p, [p, c], c, z, [z, q], q, mkStepC hS hp hq hpAB hqAB hpq hcA hzB hc,
          Or.inl hpX, Or.inl hzY⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzB : z ∈ B := by
          rcases (show z ∈ B ∪ {p} by rw [← hXY]; exact Or.inl hzX) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzX)
              (Set.disjoint_right.mp hXYdis hpY)
        obtain ⟨c, hcA, hc⟩ := exists_edge_left hS hzB
        exact ⟨z, [z, q], q, p, [p, c], c,
          step_symm (mkStepC hS hp hq hpAB hqAB hpq hcA hzB hc), Or.inl hzX, Or.inl hpY⟩
    · have hqXY : q ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases hqXY with hqX | hqY
      · obtain ⟨z, hzY⟩ := hY
        have hzA : z ∈ A := by
          rcases (show z ∈ A ∪ {q} by rw [← hXY]; exact Or.inr hzY) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzY)
              (Set.disjoint_left.mp hXYdis hqX)
        obtain ⟨c, hcB, hc⟩ := exists_edge_right hS hzA
        exact ⟨c, [c, q], q, p, [p, z], z,
          step_symm (mkStepC hS hp hq hpAB hqAB hpq hzA hcB hc), Or.inr hqX, Or.inr hzY⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzA : z ∈ A := by
          rcases (show z ∈ A ∪ {q} by rw [← hXY]; exact Or.inl hzX) with h | h
          · exact h
          · exact absurd ((Set.mem_singleton_iff.mp h) ▸ hzX)
              (Set.disjoint_right.mp hXYdis hqY)
        obtain ⟨c, hcB, hc⟩ := exists_edge_right hS hzA
        exact ⟨p, [p, z], z, c, [c, q], q, mkStepC hS hp hq hpAB hqAB hpq hzA hcB hc,
          Or.inr hzX, Or.inr hqY⟩

/-- PAPER (claim (7) and the closing paragraph of 13.1): the complementary
staircase `((B ∪ {p}, ∅, A ∪ {q}), a-w₁-⋯-wₙ)` whose banister is the trajectory
antipath.  `hpT` and `hqT` say that, along the antipath, the new left-class
vertex `p` sees only `a` and the new right-class vertex `q` sees only `wₙ`. -/
theorem staircase_compl_adjoin_pair {a last : V} {w : List V}
    (hS : StepConnected G A (∅ : Set V) B)
    (hSnew : StepConnected Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}))
    (ha : IsLeftStar G A (∅ : Set V) B a)
    (hlast : IsRightStar G A (∅ : Set V) B last)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hT3 : 3 ≤ pathLength (a :: w))
    (hpT : ∀ z ∈ a :: w, (Gᶜ.Adj p z ↔ z = a))
    (hqT : ∀ z ∈ a :: w, (Gᶜ.Adj q z ↔ z = last))
    (hpnotT : p ∉ a :: w) (hqnotT : q ∉ a :: w) :
    IsStaircase Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) a (a :: w) last := by
  classical
  set T : List V := a :: w with hTdef
  have hT : IsPathFrom Gᶜ T a last := hanti
  have haT : a ∈ T := List.mem_cons_self ..
  have hlastT : last ∈ T := Workspace.ProofLemmas.PathBasics.getLast_mem hT.2.2
  have halast : a ≠ last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hT (by omega)
  have hToutOld : ∀ z ∈ T, z ∉ A ∪ B := by
    intro z hz hzAB
    rcases List.mem_cons.mp hz with hza | hzw
    · exact ha.1 (hza ▸ (by
        rcases hzAB with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)))
    · exact bComplete_not_mem_strip hS (hwB z hzw) (by
        rcases hzAB with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h))
  have hToutNew : ∀ z ∈ T, z ∉ (B ∪ {p}) ∪ (A ∪ {q}) ∪ (∅ : Set V) := by
    intro z hz hzn
    rcases hzn with ((hzB | hzp) | (hzA | hzq)) | hz0
    · exact hToutOld z hz (Or.inr hzB)
    · exact hpnotT ((Set.mem_singleton_iff.mp hzp) ▸ hz)
    · exact hToutOld z hz (Or.inl hzA)
    · exact hqnotT ((Set.mem_singleton_iff.mp hzq) ▸ hz)
    · exact Set.notMem_empty z hz0
  refine ⟨hSnew, ⟨hT, hToutNew, ?_, ?_, ?_⟩, hT3⟩
  · refine ⟨hToutNew a haT, ?_, ?_⟩
    · rintro z (hzB | hzp)
      · exact (G.compl_adj a z).2
          ⟨fun he => ha.1 (he ▸ Or.inl (Or.inr hzB)), ha.2.2 z (Or.inl hzB)⟩
      · exact (Set.mem_singleton_iff.mp hzp) ▸ ((hpT a haT).2 rfl).symm
    · rintro z ((hzA | hzq) | hz0) hadj
      · exact ((G.compl_adj a z).1 hadj).2 (ha.2.1 z hzA)
      · exact halast ((hqT a haT).1
          ((Set.mem_singleton_iff.mp hzq) ▸ hadj).symm)
      · exact Set.notMem_empty z hz0
  · refine ⟨hToutNew last hlastT, ?_, ?_⟩
    · rintro z (hzA | hzq)
      · exact (G.compl_adj last z).2
          ⟨fun he => hlast.1 (he ▸ Or.inl (Or.inl hzA)), hlast.2.2 z (Or.inl hzA)⟩
      · exact (Set.mem_singleton_iff.mp hzq) ▸ ((hqT last hlastT).2 rfl).symm
    · rintro z ((hzB | hzp) | hz0) hadj
      · exact ((G.compl_adj last z).1 hadj).2 (hlast.2.1 z hzB)
      · exact halast ((hpT last hlastT).1
          ((Set.mem_singleton_iff.mp hzp) ▸ hadj).symm).symm
      · exact Set.notMem_empty z hz0
  · intro z hz y hy hadj
    have hzd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hT).1 hz
    have hzw : z ∈ w := (List.mem_cons.mp hzd.1).resolve_left hzd.2.1
    rcases hy with ((hyB | hyp) | (hyA | hyq)) | hy0
    · exact ((G.compl_adj z y).1 hadj).2 (hwB z hzw y hyB)
    · exact hzd.2.1 ((hpT z hzd.1).1 ((Set.mem_singleton_iff.mp hyp) ▸ hadj).symm)
    · exact ((G.compl_adj z y).1 hadj).2 (hbeforeA z hzw hzd.2.2 y hyA)
    · exact hzd.2.2 ((hqT z hzd.1).1 ((Set.mem_singleton_iff.mp hyq) ▸ hadj).symm)
    · exact Set.notMem_empty y hy0

/-- PAPER (claim (7) and the closing paragraph): *"… a staircase in `G`,
contradicting that `(S, R₀)` is strongly maximal."* -/
theorem compl_adjoin_pair_absurd {C : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀) (hC : C = ∅)
    (hpOut : p ∉ A ∪ B ∪ C) {a last : V} {T : List V}
    (hstair : IsStaircase Gᶜ (B ∪ {p}) (∅ : Set V) (A ∪ {q}) a T last) : False := by
  have hno : ¬ ∃ (A' C' B' : Set V) (a' : V) (P : List V) (b' : V),
      IsStaircase Gᶜ A' C' B' a' P b' ∧ (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C') :=
    hK.2.resolve_left (by rw [hC]; simp)
  refine hno ⟨B ∪ {p}, ∅, A ∪ {q}, a, T, last, hstair, ?_, ?_⟩
  · rintro z ((hzA | hzB) | hzC)
    · exact Or.inl (Or.inr (Or.inl hzA))
    · exact Or.inl (Or.inl (Or.inl hzB))
    · exact absurd (hC ▸ hzC) (Set.notMem_empty z)
  · intro hback
    exact hpOut (hback (Or.inl (Or.inl (Or.inr rfl))))

end ComplAdjoin

end Workspace.ProofLemmas.Thm131Enlarge
