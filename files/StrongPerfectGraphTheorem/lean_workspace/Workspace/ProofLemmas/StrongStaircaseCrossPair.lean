import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

/-!
# Adjoining a crossed pair to a step-connected strip

This is the elementary strip construction used in claim (3) of the proof of 13.4.  If two
new, nonadjacent vertices are both complete to the two ends of a step-connected strip, one can
put one in `A` and the other in `B`.  A fixed old step supplies the new two-edge step
`x-b₁, a₂-y`; all old rungs and steps remain valid.
-/

namespace Workspace.ProofLemmas.StrongStaircaseCrossPair

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT

private theorem step_symm {V : Type*} {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hzR₂ hzR₁
    exact h.2.2.1 z hzR₁ hzR₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

private theorem rung_mem_strip {V : Type*} {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {p : List V} (h : IsRungOfStrip G A C B a p b) :
    ∀ z ∈ p, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ h.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ h.2.2.1))
  exact Or.inr (h.2.2.2.2.2 z
    ((PathBasics.mem_interior_iff_of_pathFrom h.1).mpr ⟨hz, hza, hzb⟩))

/-- Add a nonadjacent crossed pair to the two end classes of a step-connected strip. -/
theorem stepConnected_adjoin_cross_pair
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V)
    (x y : V)
    (hS : StepConnected G A C B)
    (hxVS : x ∉ A ∪ B ∪ C) (hyVS : y ∉ A ∪ B ∪ C)
    (hxyne : x ≠ y) (hxy : ¬ G.Adj x y)
    (hxcomp : VertexComplete G x (A ∪ B))
    (hycomp : VertexComplete G y (A ∪ B)) :
    StepConnected G (A ∪ {x}) C (B ∪ {y}) := by
  classical
  have hxA : x ∉ A := fun h => hxVS (Or.inl (Or.inl h))
  have hxB : x ∉ B := fun h => hxVS (Or.inl (Or.inr h))
  have hxC : x ∉ C := fun h => hxVS (Or.inr h)
  have hyA : y ∉ A := fun h => hyVS (Or.inl (Or.inl h))
  have hyB : y ∉ B := fun h => hyVS (Or.inl (Or.inr h))
  have hyC : y ∉ C := fun h => hyVS (Or.inr h)
  have hxy' : ¬ G.Adj y x := fun h => hxy h.symm

  -- Fix one old step.  Its opposite ends make the two new two-vertex rungs into a step.
  obtain ⟨a, haA⟩ := hS.2.1.1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, -⟩ :=
    hS.2.2.2.1 a (Or.inl (Or.inl haA))
  obtain ⟨hr1, hr2, hdis, hedge⟩ := hstep
  have ha₁A : a₁ ∈ A := hr1.2.1
  have hb₁B : b₁ ∈ B := hr1.2.2.1
  have ha₂A : a₂ ∈ A := hr2.2.1
  have hb₂B : b₂ ∈ B := hr2.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ := PathBasics.head_mem hr1.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ := PathBasics.getLast_mem hr1.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := PathBasics.head_mem hr2.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := PathBasics.getLast_mem hr2.1.2.2
  have ha₂b₁ : ¬ G.Adj a₂ b₁ := by
    intro hadj
    rcases (hedge b₁ hb₁R₁ a₂ ha₂R₂).mp hadj.symm with h | h
    · exact (Set.disjoint_left.mp hS.1.1 (h.1 ▸ ha₁A)) hb₁B
    · exact (Set.disjoint_left.mp hS.1.1 ha₂A) (h.2 ▸ hb₂B)

  -- Old rungs and steps survive the enlargement.
  have rung_up : ∀ {a b : V} {p : List V}, IsRungOfStrip G A C B a p b →
      IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) a p b := by
    intro a' b' p hp
    refine ⟨hp.1, Or.inl hp.2.1, Or.inl hp.2.2.1, ?_, ?_, hp.2.2.2.2.2⟩
    · intro w hw hwA
      rcases hwA with hwA | hwx
      · exact hp.2.2.2.1 w hw hwA
      · have hwVS := rung_mem_strip hp w hw
        exact absurd hwVS (hwx ▸ hxVS)
    · intro w hw hwB
      rcases hwB with hwB | hwy
      · exact hp.2.2.2.2.1 w hw hwB
      · have hwVS := rung_mem_strip hp w hw
        exact absurd hwVS (hwy ▸ hyVS)
  have step_up : ∀ {c₁ d₁ c₂ d₂ : V} {P₁ P₂ : List V},
      IsStep G A C B c₁ P₁ d₁ c₂ P₂ d₂ →
      IsStep G (A ∪ {x}) C (B ∪ {y}) c₁ P₁ d₁ c₂ P₂ d₂ := by
    intro c₁ d₁ c₂ d₂ P₁ P₂ hs
    exact ⟨rung_up hs.1, rung_up hs.2.1, hs.2.2.1, hs.2.2.2⟩

  have hxb₁ : G.Adj x b₁ := hxcomp b₁ (Or.inr hb₁B)
  have ha₂y : G.Adj a₂ y := (hycomp a₂ (Or.inl ha₂A)).symm
  have hxa₂ : G.Adj x a₂ := hxcomp a₂ (Or.inl ha₂A)
  have hb₁y : G.Adj b₁ y := (hycomp b₁ (Or.inr hb₁B)).symm
  have hx_b₁ : x ≠ b₁ := fun h => hxB (h ▸ hb₁B)
  have ha₂_y : a₂ ≠ y := fun h => hyA (h ▸ ha₂A)
  have hb₁_a₂ : b₁ ≠ a₂ := fun h =>
    Set.disjoint_left.mp hS.1.1 (h ▸ ha₂A) hb₁B

  have hrx : IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) x [x, b₁] b₁ := by
    refine ⟨⟨PathBasics.isPathList_pair hxb₁, rfl, by simp⟩,
      Or.inr rfl, Or.inl hb₁B, ?_, ?_, ?_⟩
    · intro w hw hwA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · rcases hwA with h | h
        · exact absurd h (Set.disjoint_right.mp hS.1.1 hb₁B)
        · exact h
    · intro w hw hwB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hwB with h | h
        · exact absurd h hxB
        · exact absurd h hxyne
      · rfl
    · simp [Workspace.Types.Core.SPGT.interior]
  have hry : IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) a₂ [a₂, y] y := by
    refine ⟨⟨PathBasics.isPathList_pair ha₂y, rfl, by simp⟩,
      Or.inl ha₂A, Or.inr rfl, ?_, ?_, ?_⟩
    · intro w hw hwA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · rcases hwA with h | h
        · exact absurd h hyA
        · exact absurd h hxyne.symm
    · intro w hw hwB
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hwB with h | h
        · exact absurd h (Set.disjoint_left.mp hS.1.1 ha₂A)
        · exact h
      · rfl
    · simp [Workspace.Types.Core.SPGT.interior]

  have hnewstep : IsStep G (A ∪ {x}) C (B ∪ {y}) x [x, b₁] b₁ a₂ [a₂, y] y := by
    refine ⟨hrx, hry, ?_, ?_⟩
    · intro z hz1 hz2
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz1 hz2
      rcases hz1 with rfl | rfl <;> rcases hz2 with rfl | rfl
      · exact hxA ha₂A
      · exact hxyne rfl
      · exact hb₁_a₂ rfl
      · exact hyB hb₁B
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; exact hxa₂
      · constructor
        · exact fun h => absurd h hxy
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact absurd h ha₂_y.symm
          · exact absurd h hx_b₁
      · constructor
        · exact fun h => absurd h.symm ha₂b₁
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact absurd h hx_b₁.symm
          · exact absurd h ha₂_y
      · constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; exact hb₁y

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr fun z hzA hzB => by
        rcases hzA with hzA | hzx <;> rcases hzB with hzB | hzy
        · exact Set.disjoint_left.mp hS.1.1 hzA hzB
        · exact hyA (hzy ▸ hzA)
        · exact hxB (hzx ▸ hzB)
        · exact hxyne (hzx.symm.trans hzy)
    · exact Set.disjoint_left.mpr fun z hzA hzC => by
        rcases hzA with hzA | hzx
        · exact Set.disjoint_left.mp hS.1.2.1 hzA hzC
        · exact hxC (hzx ▸ hzC)
    · exact Set.disjoint_left.mpr fun z hzB hzC => by
        rcases hzB with hzB | hzy
        · exact Set.disjoint_left.mp hS.1.2.2 hzB hzC
        · exact hyC (hzy ▸ hzC)
  · exact ⟨⟨x, Or.inr rfl⟩, ⟨y, Or.inr rfl⟩⟩
  · intro w hw
    rcases hw with ((hwA | hwx) | (hwB | hwy)) | hwC
    · obtain ⟨a', p, b', hp, hwp⟩ := hS.2.2.1 w (Or.inl (Or.inl hwA))
      exact ⟨a', p, b', rung_up hp, hwp⟩
    · subst w; exact ⟨x, [x, b₁], b₁, hrx, by simp⟩
    · obtain ⟨a', p, b', hp, hwp⟩ := hS.2.2.1 w (Or.inl (Or.inr hwB))
      exact ⟨a', p, b', rung_up hp, hwp⟩
    · subst w; exact ⟨a₂, [a₂, y], y, hry, by simp⟩
    · obtain ⟨a', p, b', hp, hwp⟩ := hS.2.2.1 w (Or.inr hwC)
      exact ⟨a', p, b', rung_up hp, hwp⟩
  · intro w hw
    rcases hw with ((hwA | hwx) | (hwB | hwy)) | hwC
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 w (Or.inl (Or.inl hwA))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst w; exact ⟨x, [x, b₁], b₁, a₂, [a₂, y], y, hnewstep, Or.inl (by simp)⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 w (Or.inl (Or.inr hwB))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst w; exact ⟨x, [x, b₁], b₁, a₂, [a₂, y], y, hnewstep, Or.inr (by simp)⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ := hS.2.2.2.1 w (Or.inr hwC)
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
  · intro X Y hXY hdXY hXne hYne
    rcases hXY with hXY | hXY
    · -- A partition of `A ∪ {x}`.
      by_cases hxX : x ∈ X
      · by_cases hXd : (X \ {x}).Nonempty
        · have hold : (X \ {x}) ∪ Y = A := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzx⟩ | hzY)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzx
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z
                  exact absurd hzY (Set.disjoint_left.mp hdXY hxX)
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl ⟨h, fun hz => hxA (hz ▸ hzA)⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm1, hm2⟩ :=
            hS.2.2.2.2 (X \ {x}) Y (Or.inl hold)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm1.imp (fun h => h.1) (fun h => h.1), hm2⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have ha₂Y : a₂ ∈ Y := by
            rcases (show a₂ ∈ X ∪ Y by rw [hXY]; exact Or.inl ha₂A) with h | h
            · exact absurd ⟨h, fun he => hxA (he ▸ ha₂A)⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd a₂)
            · exact h
          exact ⟨x, [x, b₁], b₁, a₂, [a₂, y], y, hnewstep,
            Or.inl hxX, Or.inl ha₂Y⟩
      · have hxY : x ∈ Y := (show x ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hxX
        by_cases hYd : (Y \ {x}).Nonempty
        · have hOld : X ∪ (Y \ {x}) = A := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzx⟩)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z
                  exact absurd hzX (Set.disjoint_right.mp hdXY hxY)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzx
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hz => hxA (hz ▸ hzA)⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm1, hm2⟩ :=
            hS.2.2.2.2 X (Y \ {x}) (Or.inl hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm1,
            hm2.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have ha₂X : a₂ ∈ X := by
            rcases (show a₂ ∈ X ∪ Y by rw [hXY]; exact Or.inl ha₂A) with h | h
            · exact h
            · exact absurd ⟨h, fun he => hxA (he ▸ ha₂A)⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd a₂)
          exact ⟨a₂, [a₂, y], y, x, [x, b₁], b₁, step_symm hnewstep,
            Or.inl ha₂X, Or.inl hxY⟩
    · -- B partition: the same argument, with the new vertex `y` and old end `b₁`.
      by_cases hyX : y ∈ X
      · by_cases hXd : (X \ {y}).Nonempty
        · have hOld : (X \ {y}) ∪ Y = B := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzy⟩ | hzY)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzy
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z
                  exact absurd hzY (Set.disjoint_left.mp hdXY hyX)
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl ⟨h, fun hz => hyB (hz ▸ hzB)⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm1, hm2⟩ :=
            hS.2.2.2.2 (X \ {y}) Y (Or.inr hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm1.imp (fun h => h.1) (fun h => h.1), hm2⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have hb₁Y : b₁ ∈ Y := by
            rcases (show b₁ ∈ X ∪ Y by rw [hXY]; exact Or.inl hb₁B) with h | h
            · exact absurd ⟨h, fun he => hyB (he ▸ hb₁B)⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd b₁)
            · exact h
          exact ⟨a₂, [a₂, y], y, x, [x, b₁], b₁, step_symm hnewstep,
            Or.inr hyX, Or.inr hb₁Y⟩
      · have hyY : y ∈ Y := (show y ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hyX
        by_cases hYd : (Y \ {y}).Nonempty
        · have hOld : X ∪ (Y \ {y}) = B := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzy⟩)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z
                  exact absurd hzX (Set.disjoint_right.mp hdXY hyY)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzy
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hz => hyB (hz ▸ hzB)⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm1, hm2⟩ :=
            hS.2.2.2.2 X (Y \ {y}) (Or.inr hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm1,
            hm2.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have hb₁X : b₁ ∈ X := by
            rcases (show b₁ ∈ X ∪ Y by rw [hXY]; exact Or.inl hb₁B) with h | h
            · exact h
            · exact absurd ⟨h, fun he => hyB (he ▸ hb₁B)⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd b₁)
          exact ⟨x, [x, b₁], b₁, a₂, [a₂, y], y, hnewstep,
            Or.inr hb₁X, Or.inr hyY⟩

/-- The corresponding staircase enlargement, retaining the old banister. -/
theorem staircase_adjoin_cross_pair
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (x y : V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hxK : x ∉ staircaseVertices A C B R₀)
    (hyK : y ∉ staircaseVertices A C B R₀)
    (hxyne : x ≠ y) (hxy : ¬ G.Adj x y)
    (hxcomp : VertexComplete G x (A ∪ B))
    (hycomp : VertexComplete G y (A ∪ B))
    (hxa₀ : G.Adj x a₀) (hxb₀ : ¬ G.Adj x b₀)
    (hya₀ : ¬ G.Adj y a₀) (hyb₀ : G.Adj y b₀)
    (hxint : ∀ z ∈ interior R₀, ¬ G.Adj x z)
    (hyint : ∀ z ∈ interior R₀, ¬ G.Adj y z) :
    IsStaircase G (A ∪ {x}) C (B ∪ {y}) a₀ R₀ b₀ := by
  classical
  have hxVS : x ∉ A ∪ B ∪ C := fun h => hxK (Or.inr h)
  have hyVS : y ∉ A ∪ B ∪ C := fun h => hyK (Or.inr h)
  have hxR : x ∉ R₀ := fun h => hxK (Or.inl h)
  have hyR : y ∉ R₀ := fun h => hyK (Or.inl h)
  have hSnew := stepConnected_adjoin_cross_pair G A C B x y hK.1 hxVS hyVS hxyne hxy
    hxcomp hycomp
  have hban := hK.2.1
  have hbannew : IsBanister G (A ∪ {x}) C (B ∪ {y}) a₀ R₀ b₀ := by
    refine ⟨hban.1, ?_, ?_, ?_, ?_⟩
    · intro z hz hznew
      rcases hznew with ((hA | hzx) | (hB | hzy)) | hC
      · exact hban.2.1 z hz (Or.inl (Or.inl hA))
      · exact hxR (hzx ▸ hz)
      · exact hban.2.1 z hz (Or.inl (Or.inr hB))
      · exact hyR (hzy ▸ hz)
      · exact hban.2.1 z hz (Or.inr hC)
    · refine ⟨?_, ?_, ?_⟩
      · intro hz
        rcases hz with ((hA | hzx) | (hB | hzy)) | hC
        · exact hban.2.2.1.1 (Or.inl (Or.inl hA))
        · exact hxR (hzx ▸ PathBasics.head_mem hban.1.2.1)
        · exact hban.2.2.1.1 (Or.inl (Or.inr hB))
        · exact hyR (hzy ▸ PathBasics.head_mem hban.1.2.1)
        · exact hban.2.2.1.1 (Or.inr hC)
      · intro z hz
        rcases hz with hA | hzx
        · exact hban.2.2.1.2.1 z hA
        · subst z
          exact hxa₀.symm
      · intro z hz hadj
        rcases hz with (hB | hzy) | hC
        · exact hban.2.2.1.2.2 z (Or.inl hB) hadj
        · subst z
          exact hya₀ hadj.symm
        · exact hban.2.2.1.2.2 z (Or.inr hC) hadj
    · refine ⟨?_, ?_, ?_⟩
      · intro hz
        rcases hz with ((hA | hzx) | (hB | hzy)) | hC
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl hA))
        · exact hxR (hzx ▸ PathBasics.getLast_mem hban.1.2.2)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inr hB))
        · exact hyR (hzy ▸ PathBasics.getLast_mem hban.1.2.2)
        · exact hban.2.2.2.1.1 (Or.inr hC)
      · intro z hz
        rcases hz with hB | hzy
        · exact hban.2.2.2.1.2.1 z hB
        · subst z
          exact hyb₀.symm
      · intro z hz hadj
        rcases hz with (hA | hzx) | hC
        · exact hban.2.2.2.1.2.2 z (Or.inl hA) hadj
        · subst z
          exact hxb₀ hadj.symm
        · exact hban.2.2.2.1.2.2 z (Or.inr hC) hadj
    · intro z hz w hw hadj
      rcases hw with ((hA | hwx) | (hB | hwy)) | hC
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inl hA)) hadj
      · subst w
        exact hxint z hz hadj.symm
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inr hB)) hadj
      · subst w
        exact hyint z hz hadj.symm
      · exact hban.2.2.2.2 z hz w (Or.inr hC) hadj
  exact ⟨hSnew, hbannew, hK.2.2⟩

end Workspace.ProofLemmas.StrongStaircaseCrossPair
