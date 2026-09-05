import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The crossed-pair strip enlargement used in case (3) of Theorem 12.5

The two new end-class vertices need only be complete to the opposite old end class.
A selected nonedge `a b`, together with the edges `x a` and `y b`, supplies the new
step `[x,b]`, `[a,y]`.
-/

namespace Workspace.ProofLemmas.Thm125Case3Adjoin

open Workspace.Types.Core.SPGT
open Workspace.Types.Staircases.SPGT

private theorem step_symm {V : Type*} {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [SimpleGraph.adj_comm, h.2.2.2 v hv u hu]
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
    ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).2
      ⟨hz, hza, hzb⟩))

/-- Adjoin `x` to `A` and `y` to `B`.  The crossed paths `[x,b]` and `[a,y]`
are a new step, so the enlarged strip remains step-connected. -/
theorem stepConnected_adjoin_diagonal_pair
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (x y a b : V)
    (hS : StepConnected G A C B)
    (hxVS : x ∉ A ∪ B ∪ C) (hyVS : y ∉ A ∪ B ∪ C)
    (hxyne : x ≠ y) (hxy : ¬ G.Adj x y)
    (hxB : VertexComplete G x B) (hyA : VertexComplete G y A)
    (haA : a ∈ A) (hbB : b ∈ B)
    (hxa : G.Adj x a) (hyb : G.Adj y b) (hab : ¬ G.Adj a b) :
    StepConnected G (A ∪ {x}) C (B ∪ {y}) := by
  classical
  have hxA : x ∉ A := fun h => hxVS (Or.inl (Or.inl h))
  have hxBmem : x ∉ B := fun h => hxVS (Or.inl (Or.inr h))
  have hxC : x ∉ C := fun h => hxVS (Or.inr h)
  have hyA_mem : y ∉ A := fun h => hyVS (Or.inl (Or.inl h))
  have hyB : y ∉ B := fun h => hyVS (Or.inl (Or.inr h))
  have hyC : y ∉ C := fun h => hyVS (Or.inr h)

  have rung_up : ∀ {a' b' : V} {p : List V}, IsRungOfStrip G A C B a' p b' →
      IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) a' p b' := by
    intro a' b' p hp
    refine ⟨hp.1, Or.inl hp.2.1, Or.inl hp.2.2.1, ?_, ?_, hp.2.2.2.2.2⟩
    · intro w hw hwA
      rcases hwA with hwA | hwx
      · exact hp.2.2.2.1 w hw hwA
      · exact absurd (rung_mem_strip hp w hw) (hwx ▸ hxVS)
    · intro w hw hwB
      rcases hwB with hwB | hwy
      · exact hp.2.2.2.2.1 w hw hwB
      · exact absurd (rung_mem_strip hp w hw) (hwy ▸ hyVS)
  have step_up : ∀ {c₁ d₁ c₂ d₂ : V} {P₁ P₂ : List V},
      IsStep G A C B c₁ P₁ d₁ c₂ P₂ d₂ →
      IsStep G (A ∪ {x}) C (B ∪ {y}) c₁ P₁ d₁ c₂ P₂ d₂ := by
    intro c₁ d₁ c₂ d₂ P₁ P₂ hs
    exact ⟨rung_up hs.1, rung_up hs.2.1, hs.2.2.1, hs.2.2.2⟩

  have hxb : G.Adj x b := hxB b hbB
  have hay : G.Adj a y := (hyA a haA).symm
  have hx_b : x ≠ b := fun h => hxBmem (h ▸ hbB)
  have ha_y : a ≠ y := fun h => hyA_mem (h ▸ haA)
  have hb_a : b ≠ a := fun h =>
    Set.disjoint_left.mp hS.1.1 (h.symm ▸ haA) hbB

  have hrx : IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) x [x, b] b := by
    refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hxb, rfl, by simp⟩,
      Or.inr rfl, Or.inl hbB, ?_, ?_, ?_⟩
    · intro w hw hwA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · rcases hwA with h | h
        · exact absurd h (Set.disjoint_right.mp hS.1.1 hbB)
        · exact h
    · intro w hw hwB'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hwB' with h | h
        · exact absurd h hxBmem
        · exact absurd h hxyne
      · rfl
    · simp [Workspace.Types.Core.SPGT.interior]
  have hry : IsRungOfStrip G (A ∪ {x}) C (B ∪ {y}) a [a, y] y := by
    refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hay, rfl, by simp⟩,
      Or.inl haA, Or.inr rfl, ?_, ?_, ?_⟩
    · intro w hw hwA'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rfl
      · rcases hwA' with h | h
        · exact absurd h hyA_mem
        · exact absurd h hxyne.symm
    · intro w hw hwB'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · rcases hwB' with h | h
        · exact absurd h (Set.disjoint_left.mp hS.1.1 haA)
        · exact h
      · rfl
    · simp [Workspace.Types.Core.SPGT.interior]

  have hnewstep : IsStep G (A ∪ {x}) C (B ∪ {y}) x [x, b] b a [a, y] y := by
    refine ⟨hrx, hry, ?_, ?_⟩
    · intro z hz₁ hz₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
      rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl
      · exact hxA haA
      · exact hxyne rfl
      · exact hb_a rfl
      · exact hyB hbB
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · constructor
        · intro _; exact Or.inl ⟨rfl, rfl⟩
        · intro _; exact hxa
      · constructor
        · exact fun h => (hxy h).elim
        · rintro (⟨_, h⟩ | ⟨h, _⟩)
          · exact absurd h ha_y.symm
          · exact absurd h hx_b
      · constructor
        · exact fun h => (hab h.symm).elim
        · rintro (⟨h, _⟩ | ⟨_, h⟩)
          · exact absurd h hx_b.symm
          · exact absurd h ha_y
      · constructor
        · intro _; exact Or.inr ⟨rfl, rfl⟩
        · intro _; exact hyb.symm

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact Set.disjoint_left.mpr fun z hzA hzB => by
        rcases hzA with hzA | hzx <;> rcases hzB with hzB | hzy
        · exact Set.disjoint_left.mp hS.1.1 hzA hzB
        · exact hyA_mem (hzy ▸ hzA)
        · exact hxBmem (hzx ▸ hzB)
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
    · subst w; exact ⟨x, [x, b], b, hrx, by simp⟩
    · obtain ⟨a', p, b', hp, hwp⟩ := hS.2.2.1 w (Or.inl (Or.inr hwB))
      exact ⟨a', p, b', rung_up hp, hwp⟩
    · subst w; exact ⟨a, [a, y], y, hry, by simp⟩
    · obtain ⟨a', p, b', hp, hwp⟩ := hS.2.2.1 w (Or.inr hwC)
      exact ⟨a', p, b', rung_up hp, hwp⟩
  · intro w hw
    rcases hw with ((hwA | hwx) | (hwB | hwy)) | hwC
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 w (Or.inl (Or.inl hwA))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst w; exact ⟨x, [x, b], b, a, [a, y], y, hnewstep, Or.inl (by simp)⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 w (Or.inl (Or.inr hwB))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst w; exact ⟨x, [x, b], b, a, [a, y], y, hnewstep, Or.inr (by simp)⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 w (Or.inr hwC)
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
  · intro X Y hXY hdXY hXne hYne
    rcases hXY with hXY | hXY
    · by_cases hxX : x ∈ X
      · by_cases hXd : (X \ {x}).Nonempty
        · have hOld : (X \ {x}) ∪ Y = A := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzx⟩ | hzY)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzx
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z; exact absurd hzY (Set.disjoint_left.mp hdXY hxX)
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl ⟨h, fun hz => hxA (hz ▸ hzA)⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {x}) Y (Or.inl hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have haY : a ∈ Y := by
            rcases (show a ∈ X ∪ Y by rw [hXY]; exact Or.inl haA) with h | h
            · exact absurd ⟨h, fun he => hxA (he ▸ haA)⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd a)
            · exact h
          exact ⟨x, [x, b], b, a, [a, y], y, hnewstep, Or.inl hxX, Or.inl haY⟩
      · have hxY : x ∈ Y :=
          (show x ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hxX
        by_cases hYd : (Y \ {x}).Nonempty
        · have hOld : X ∪ (Y \ {x}) = A := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzx⟩)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z; exact absurd hzX (Set.disjoint_right.mp hdXY hxY)
              · rcases (show z ∈ A ∪ {x} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzx
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hz => hxA (hz ▸ hzA)⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {x}) (Or.inl hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have haX : a ∈ X := by
            rcases (show a ∈ X ∪ Y by rw [hXY]; exact Or.inl haA) with h | h
            · exact h
            · exact absurd ⟨h, fun he => hxA (he ▸ haA)⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd a)
          exact ⟨a, [a, y], y, x, [x, b], b, step_symm hnewstep,
            Or.inl haX, Or.inl hxY⟩
    · by_cases hyX : y ∈ X
      · by_cases hXd : (X \ {y}).Nonempty
        · have hOld : (X \ {y}) ∪ Y = B := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzy⟩ | hzY)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzy
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z; exact absurd hzY (Set.disjoint_left.mp hdXY hyX)
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl ⟨h, fun hz => hyB (hz ▸ hzB)⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {y}) Y (Or.inr hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have hbY : b ∈ Y := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hbB) with h | h
            · exact absurd ⟨h, fun he => hyB (he ▸ hbB)⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd b)
            · exact h
          exact ⟨a, [a, y], y, x, [x, b], b, step_symm hnewstep,
            Or.inr hyX, Or.inr hbY⟩
      · have hyY : y ∈ Y :=
          (show y ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hyX
        by_cases hYd : (Y \ {y}).Nonempty
        · have hOld : X ∪ (Y \ {y}) = B := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzy⟩)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z; exact absurd hzX (Set.disjoint_right.mp hdXY hyY)
              · rcases (show z ∈ B ∪ {y} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzy
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hz => hyB (hz ▸ hzB)⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {y}) (Or.inr hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have hbX : b ∈ X := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hbB) with h | h
            · exact h
            · exact absurd ⟨h, fun he => hyB (he ▸ hbB)⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd b)
          exact ⟨x, [x, b], b, a, [a, y], y, hnewstep,
            Or.inr hbX, Or.inr hyY⟩

/-- Retain the old banister while adjoining the crossed diagonal pair to the strip. -/
theorem staircase_adjoin_diagonal_pair
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (x y a b : V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hxK : x ∉ staircaseVertices A C B R₀)
    (hyK : y ∉ staircaseVertices A C B R₀)
    (hxyne : x ≠ y) (hxy : ¬ G.Adj x y)
    (hxB : VertexComplete G x B) (hyA : VertexComplete G y A)
    (haA : a ∈ A) (hbB : b ∈ B)
    (hxa : G.Adj x a) (hyb : G.Adj y b) (hab : ¬ G.Adj a b)
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
  have hSnew := stepConnected_adjoin_diagonal_pair G A C B x y a b hK.1
    hxVS hyVS hxyne hxy hxB hyA haA hbB hxa hyb hab
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
        · exact hxR (hzx ▸ Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1)
        · exact hban.2.2.1.1 (Or.inl (Or.inr hB))
        · exact hyR (hzy ▸ Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1)
        · exact hban.2.2.1.1 (Or.inr hC)
      · intro z hz
        rcases hz with hA | hzx
        · exact hban.2.2.1.2.1 z hA
        · subst z; exact hxa₀.symm
      · intro z hz hadj
        rcases hz with (hB | hzy) | hC
        · exact hban.2.2.1.2.2 z (Or.inl hB) hadj
        · subst z; exact hya₀ hadj.symm
        · exact hban.2.2.1.2.2 z (Or.inr hC) hadj
    · refine ⟨?_, ?_, ?_⟩
      · intro hz
        rcases hz with ((hA | hzx) | (hB | hzy)) | hC
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl hA))
        · exact hxR (hzx ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inr hB))
        · exact hyR (hzy ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)
        · exact hban.2.2.2.1.1 (Or.inr hC)
      · intro z hz
        rcases hz with hB | hzy
        · exact hban.2.2.2.1.2.1 z hB
        · subst z; exact hyb₀.symm
      · intro z hz hadj
        rcases hz with (hA | hzx) | hC
        · exact hban.2.2.2.1.2.2 z (Or.inl hA) hadj
        · subst z; exact hxb₀ hadj.symm
        · exact hban.2.2.2.1.2.2 z (Or.inr hC) hadj
    · intro z hz w hw hadj
      rcases hw with ((hA | hwx) | (hB | hwy)) | hC
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inl hA)) hadj
      · subst w; exact hxint z hz hadj.symm
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inr hB)) hadj
      · subst w; exact hyint z hz hadj.symm
      · exact hban.2.2.2.2 z hz w (Or.inr hC) hadj
  exact ⟨hSnew, hbannew, hK.2.2⟩

end Workspace.ProofLemmas.Thm125Case3Adjoin
