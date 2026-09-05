import Workspace.ProofLemmas.NonlocalStaircaseSelectedStep

set_option autoImplicit false

/-! # The strip enlargement in the last paragraph of 12.2

The new rung shares its last end with the old strip. Its first end and some
of its internal vertices are new. One step containing this rung connects the
new first end to the old first ends.
-/

namespace Workspace.ProofLemmas.NonlocalStaircaseAdjoinLeft

open Workspace.Types.Core.SPGT Workspace.Types.Staircases.SPGT
open NonlocalStaircaseSelectedStep

variable {V : Type*} {G : SimpleGraph V} {A C B : Set V}

/-- Old rungs remain rungs when an outside vertex is added to `A` and `C`
is enlarged. -/
theorem rung_up {p a b : V} {D : Set V} {R : List V}
    (hp : p ∉ A ∪ B ∪ C) (hR : IsRungOfStrip G A C B a R b) :
    IsRungOfStrip G (A ∪ {p}) (C ∪ D) B a R b := by
  refine ⟨hR.1, Or.inl hR.2.1, hR.2.2.1, ?_, hR.2.2.2.2.1,
    fun z hz => Or.inl (hR.2.2.2.2.2 z hz)⟩
  rintro z hz (hzA | hzp)
  · exact hR.2.2.2.1 z hz hzA
  · subst z
    exact (hp (rung_mem_strip hR p hz)).elim

/-- PAPER (12.2): "we can add `p₁` to `A` and `V(P \ p₁)` to `C`."
The step-connectedness part only needs one new step covering the added
vertices. All the old steps are preserved. -/
theorem stepConnected_adjoin_left
    (hS : StepConnected G A C B) (p : V) (D : Set V)
    (hp : p ∉ A ∪ B ∪ C) (hD : ∀ z ∈ D, z ∉ A ∪ B ∪ C) (hpD : p ∉ D)
    (b a' b' : V) (T R : List V)
    (ha' : a' ∈ A)
    (hnew : IsStep G (A ∪ {p}) (C ∪ D) B p T b a' R b')
    (hcover : ∀ z ∈ D, z ∈ T) :
    StepConnected G (A ∪ {p}) (C ∪ D) B := by
  classical
  have step_up : ∀ {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V},
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ →
      IsStep G (A ∪ {p}) (C ∪ D) B a₁ R₁ b₁ a₂ R₂ b₂ := by
    intro a₁ b₁ a₂ b₂ R₁ R₂ hs
    exact ⟨rung_up hp hs.1, rung_up hp hs.2.1, hs.2.2.1, hs.2.2.2⟩
  have hmem : ∀ z ∈ (A ∪ {p}) ∪ B ∪ (C ∪ D),
      z ∈ A ∪ B ∪ C ∨ z ∈ T := by
    rintro z (((hzA | rfl) | hzB) | (hzC | hzD))
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inr (PathBasics.head_mem hnew.1.1.2.1)
    · exact Or.inl (Or.inl (Or.inr hzB))
    · exact Or.inl (Or.inr hzC)
    · exact Or.inr (hcover z hzD)
  refine ⟨?_, ⟨⟨p, Or.inr rfl⟩, hS.2.1.2⟩, ?_, ?_, ?_⟩
  · refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_,
      Set.disjoint_left.mpr ?_⟩
    · rintro z (hzA | rfl) hzB
      · exact Set.disjoint_left.mp hS.1.1 hzA hzB
      · exact hp (Or.inl (Or.inr hzB))
    · rintro z (hzA | rfl) (hzC | hzD)
      · exact Set.disjoint_left.mp hS.1.2.1 hzA hzC
      · exact hD z hzD (Or.inl (Or.inl hzA))
      · exact hp (Or.inr hzC)
      · exact hpD hzD
    · rintro z hzB (hzC | hzD)
      · exact Set.disjoint_left.mp hS.1.2.2 hzB hzC
      · exact hD z hzD (Or.inl (Or.inr hzB))
  · intro z hz
    rcases hmem z hz with hzOld | hzT
    · obtain ⟨a, Q, b, hQ, hzQ⟩ := hS.2.2.1 z hzOld
      exact ⟨a, Q, b, rung_up hp hQ, hzQ⟩
    · exact ⟨p, T, b, hnew.1, hzT⟩
  · intro z hz
    rcases hmem z hz with hzOld | hzT
    · obtain ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, hs, hm⟩ := hS.2.2.2.1 z hzOld
      exact ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, step_up hs, hm⟩
    · exact ⟨p, T, b, a', R, b', hnew, Or.inl hzT⟩
  · intro X Y hXY hd hX hY
    rcases hXY with hXY | hXY
    · have hpart : (X ∩ A) ∪ (Y ∩ A) = A := by
        rw [← Set.union_inter_distrib_right, hXY]
        exact Set.inter_eq_right.mpr Set.subset_union_left
      by_cases hXA : (X ∩ A).Nonempty
      · by_cases hYA : (Y ∩ A).Nonempty
        · obtain ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, hs, hx, hy⟩ :=
            hS.2.2.2.2 (X ∩ A) (Y ∩ A) (Or.inl hpart)
              (hd.mono Set.inter_subset_left Set.inter_subset_left) hXA hYA
          exact ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, step_up hs,
            hx.imp And.left And.left, hy.imp And.left And.left⟩
        · have hpY : p ∈ Y := by
            obtain ⟨y, hy⟩ := hY
            have hym : y ∈ A ∪ {p} := hXY ▸ Or.inr hy
            rcases hym with hyA | rfl
            · exact (hYA ⟨y, hy, hyA⟩).elim
            · exact hy
          have haX : a' ∈ X := by
            rcases (show a' ∈ X ∪ Y by rw [hXY]; exact Or.inl ha') with h | h
            · exact h
            · exact (hYA ⟨a', h, ha'⟩).elim
          exact ⟨a', R, b', p, T, b, step_symm hnew, Or.inl haX, Or.inl hpY⟩
      · have hpX : p ∈ X := by
          obtain ⟨x, hx⟩ := hX
          have hxm : x ∈ A ∪ {p} := hXY ▸ Or.inl hx
          rcases hxm with hxA | rfl
          · exact (hXA ⟨x, hx, hxA⟩).elim
          · exact hx
        have haY : a' ∈ Y := by
          rcases (show a' ∈ X ∪ Y by rw [hXY]; exact Or.inl ha') with h | h
          · exact (hXA ⟨a', h, ha'⟩).elim
          · exact h
        exact ⟨p, T, b, a', R, b', hnew, Or.inl hpX, Or.inl haY⟩
    · obtain ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, hs, hx, hy⟩ :=
        hS.2.2.2.2 X Y (Or.inr hXY) hd hX hY
      exact ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, step_up hs, hx, hy⟩

/-- PAPER (12.2): "we can add `p₁` to `A` and `V(P \ p₁)` to `C`,
contrary to the maximality of the staircase."
Once the enlarged strip is step-connected, the single edge from `p₁` to
`a₀` preserves the old banister and gives the strict enlargement. -/
theorem contradicts_maximality
    {a₀ b₀ p : V} {R₀ q : List V}
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    (hpq : p ∈ q) (hqout : ∀ x ∈ q, x ∉ staircaseVertices A C B R₀)
    (hS : StepConnected G (A ∪ {p}) (C ∪ {x | x ∈ q ∧ x ≠ p}) B)
    (hcross : ∀ x ∈ q, ∀ z ∈ R₀, (G.Adj x z ↔ x = p ∧ z = a₀)) : False := by
  let D : Set V := {x | x ∈ q ∧ x ≠ p}
  have hban := hMax.1.2.1
  have haR := PathBasics.head_mem hban.1.2.1
  have hbR := PathBasics.getLast_mem hban.1.2.2
  have hab : a₀ ≠ b₀ := PathBasics.isPathFrom_ends_ne hban.1 (by
    exact le_trans (by decide : 1 ≤ 3) hMax.1.2.2)
  have hout : ∀ z ∈ R₀, z ∉ (A ∪ {p}) ∪ B ∪ (C ∪ D) := by
    rintro z hz (((hzA | hzp) | hzB) | (hzC | hzD))
    · exact hban.2.1 z hz (Or.inl (Or.inl hzA))
    · subst z
      exact hqout p hpq (Or.inl hz)
    · exact hban.2.1 z hz (Or.inl (Or.inr hzB))
    · exact hban.2.1 z hz (Or.inr hzC)
    · exact hqout z hzD.1 (Or.inl hz)
  have hnew : IsBanister G (A ∪ {p}) (C ∪ D) B a₀ R₀ b₀ := by
    refine ⟨hban.1, hout, ⟨hout a₀ haR, ?_, ?_⟩,
      ⟨hout b₀ hbR, hban.2.2.2.1.2.1, ?_⟩, ?_⟩
    · rintro z (hzA | hzp)
      · exact hban.2.2.1.2.1 z hzA
      · subst z
        exact ((hcross p hpq a₀ haR).2 ⟨rfl, rfl⟩).symm
    · rintro z (hzB | (hzC | hzD)) hadj
      · exact hban.2.2.1.2.2 z (Or.inl hzB) hadj
      · exact hban.2.2.1.2.2 z (Or.inr hzC) hadj
      · exact hzD.2 ((hcross z hzD.1 a₀ haR).1 hadj.symm).1
    · rintro z ((hzA | hzp) | (hzC | hzD)) hadj
      · exact hban.2.2.2.1.2.2 z (Or.inl hzA) hadj
      · subst z
        exact hab ((hcross p hpq b₀ hbR).1 hadj.symm).2.symm
      · exact hban.2.2.2.1.2.2 z (Or.inr hzC) hadj
      · exact hzD.2 ((hcross z hzD.1 b₀ hbR).1 hadj.symm).1
    · intro z hz w hw hadj
      have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hban.1).1 hz
      rcases hw with ((hwA | hwp) | hwB) | (hwC | hwD)
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inl hwA)) hadj
      · subst w
        exact hzdata.2.1 ((hcross p hpq z hzdata.1).1 hadj.symm).2
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inr hwB)) hadj
      · exact hban.2.2.2.2 z hz w (Or.inr hwC) hadj
      · exact hwD.2 ((hcross w hwD.1 z hzdata.1).1 hadj.symm).1
  apply hMax.2
  refine ⟨A ∪ {p}, C ∪ D, B, a₀, R₀, b₀, ⟨hS, hnew, hMax.1.2.2⟩,
    Set.subset_union_left, Set.Subset.rfl, Set.subset_union_left, ?_⟩
  constructor
  · rintro z ((hzA | hzB) | hzC)
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr hzB)
    · exact Or.inr (Or.inl hzC)
  · intro hsub
    exact hqout p hpq (Or.inr (hsub (Or.inl (Or.inl (Or.inr rfl)))))

end Workspace.ProofLemmas.NonlocalStaircaseAdjoinLeft
