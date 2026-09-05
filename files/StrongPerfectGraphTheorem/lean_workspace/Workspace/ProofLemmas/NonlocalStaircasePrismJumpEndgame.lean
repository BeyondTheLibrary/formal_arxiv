import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.NonlocalStaircaseRungSuffix

set_option autoImplicit false

/-!
# The two staircase enlargements at the end of 12.2

Theorem 10.1 leaves two path configurations.  In both configurations the
paper enlarges the strip of the staircase.  These lemmas state those two
steps without hiding any of the path or relabelling data returned by 10.1.
-/

namespace Workspace.ProofLemmas.NonlocalStaircasePrismJumpEndgame

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*}

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  · exact Or.inr (hR.2.2.2.2.2 z
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
        ⟨hz, hza, hzb⟩))

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, fun z hz₂ hz₁ => h.2.2.1 z hz₁ hz₂, ?_⟩
  intro u hu v hv
  rw [G.adj_comm, h.2.2.2 v hv u hu]
  tauto

/-- Adjoining an outside path as one new rung preserves step-connectedness
when that path and one old rung form a step. -/
private theorem stepConnected_adjoin_crossed_path
    [DecidableEq V] (G : SimpleGraph V) (A C B : Set V)
    (hS : StepConnected G A C B)
    (r v : V) (Q : List V) (hQ : IsPathFrom G Q r v)
    (hrv : r ≠ v) (hQout : ∀ z ∈ Q, z ∉ A ∪ B ∪ C)
    (a b : V) (R : List V) (hR : IsRungOfStrip G A C B a R b)
    (hcross : ∀ q ∈ Q, ∀ y ∈ R,
      (G.Adj q y ↔ (q = r ∧ y = a) ∨ (q = v ∧ y = b))) :
    StepConnected G (A ∪ {r}) (C ∪ {z : V | z ∈ interior Q}) (B ∪ {v}) := by
  classical
  let D : Set V := {z : V | z ∈ interior Q}
  have hrQ := Workspace.ProofLemmas.PathBasics.head_mem hQ.2.1
  have hvQ := Workspace.ProofLemmas.PathBasics.getLast_mem hQ.2.2
  have hrD : r ∉ D := fun hr =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).1 hr |>.2.1 rfl
  have hvD : v ∉ D := fun hv =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).1 hv |>.2.2 rfl
  have hDmem : ∀ z ∈ D, z ∈ Q := fun z hz =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).1 hz |>.1
  have rung_up : ∀ {c d : V} {P : List V}, IsRungOfStrip G A C B c P d →
      IsRungOfStrip G (A ∪ {r}) (C ∪ D) (B ∪ {v}) c P d := by
    intro c d P hP
    refine ⟨hP.1, Or.inl hP.2.1, Or.inl hP.2.2.1, ?_, ?_, ?_⟩
    · intro z hz hzA
      rcases hzA with hzA | hzr
      · exact hP.2.2.2.1 z hz hzA
      · exact absurd (rung_mem_strip hP z hz) (hzr ▸ hQout r hrQ)
    · intro z hz hzB
      rcases hzB with hzB | hzv
      · exact hP.2.2.2.2.1 z hz hzB
      · exact absurd (rung_mem_strip hP z hz) (hzv ▸ hQout v hvQ)
    · intro z hz
      exact Or.inl (hP.2.2.2.2.2 z hz)
  have step_up : ∀ {c₁ d₁ c₂ d₂ : V} {P₁ P₂ : List V},
      IsStep G A C B c₁ P₁ d₁ c₂ P₂ d₂ →
      IsStep G (A ∪ {r}) (C ∪ D) (B ∪ {v}) c₁ P₁ d₁ c₂ P₂ d₂ := by
    intro c₁ d₁ c₂ d₂ P₁ P₂ hs
    exact ⟨rung_up hs.1, rung_up hs.2.1, hs.2.2.1, hs.2.2.2⟩
  have hnewrung : IsRungOfStrip G (A ∪ {r}) (C ∪ D) (B ∪ {v}) r Q v := by
    refine ⟨hQ, Or.inr rfl, Or.inr rfl, ?_, ?_, ?_⟩
    · intro z hz hzA
      rcases hzA with hzA | hzr
      · exact absurd (Or.inl (Or.inl hzA)) (hQout z hz)
      · exact hzr
    · intro z hz hzB
      rcases hzB with hzB | hzv
      · exact absurd (Or.inl (Or.inr hzB)) (hQout z hz)
      · exact hzv
    · intro z hz
      exact Or.inr hz
  have hnewstep : IsStep G (A ∪ {r}) (C ∪ D) (B ∪ {v}) r Q v a R b := by
    refine ⟨hnewrung, rung_up hR, ?_, hcross⟩
    intro z hzQ hzR
    exact hQout z hzQ (rung_mem_strip hR z hzR)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_,
      Set.disjoint_left.mpr ?_⟩
    · intro z hzA hzB
      rcases hzA with hzA | hzr <;> rcases hzB with hzB | hzv
      · exact Set.disjoint_left.mp hS.1.1 hzA hzB
      · exact hQout v hvQ (hzv ▸ Or.inl (Or.inl hzA))
      · exact hQout r hrQ (hzr ▸ Or.inl (Or.inr hzB))
      · exact hrv (hzr.symm.trans hzv)
    · intro z hzA hzC
      rcases hzA with hzA | hzr <;> rcases hzC with hzC | hzD
      · exact Set.disjoint_left.mp hS.1.2.1 hzA hzC
      · exact hQout z (hDmem z hzD) (Or.inl (Or.inl hzA))
      · exact hQout r hrQ (hzr ▸ Or.inr hzC)
      · exact hrD (hzr ▸ hzD)
    · intro z hzB hzC
      rcases hzB with hzB | hzv <;> rcases hzC with hzC | hzD
      · exact Set.disjoint_left.mp hS.1.2.2 hzB hzC
      · exact hQout z (hDmem z hzD) (Or.inl (Or.inr hzB))
      · exact hQout v hvQ (hzv ▸ Or.inr hzC)
      · exact hvD (hzv ▸ hzD)
  · exact ⟨⟨r, Or.inr rfl⟩, ⟨v, Or.inr rfl⟩⟩
  · intro z hz
    rcases hz with ((hzA | hzr) | (hzB | hzv)) | (hzC | hzD)
    · obtain ⟨c, P, d, hP, hzP⟩ := hS.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨c, P, d, rung_up hP, hzP⟩
    · subst z; exact ⟨r, Q, v, hnewrung, hrQ⟩
    · obtain ⟨c, P, d, hP, hzP⟩ := hS.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨c, P, d, rung_up hP, hzP⟩
    · subst z; exact ⟨r, Q, v, hnewrung, hvQ⟩
    · obtain ⟨c, P, d, hP, hzP⟩ := hS.2.2.1 z (Or.inr hzC)
      exact ⟨c, P, d, rung_up hP, hzP⟩
    · exact ⟨r, Q, v, hnewrung, hDmem z hzD⟩
  · intro z hz
    rcases hz with ((hzA | hzr) | (hzB | hzv)) | (hzC | hzD)
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst z; exact ⟨r, Q, v, a, R, b, hnewstep, Or.inl hrQ⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · subst z; exact ⟨r, Q, v, a, R, b, hnewstep, Or.inl hvQ⟩
    · obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm⟩ :=
        hS.2.2.2.1 z (Or.inr hzC)
      exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm⟩
    · exact ⟨r, Q, v, a, R, b, hnewstep, Or.inl (hDmem z hzD)⟩
  · intro X Y hXY hdXY hXne hYne
    rcases hXY with hXY | hXY
    · by_cases hrX : r ∈ X
      · by_cases hXd : (X \ {r}).Nonempty
        · have hOld : (X \ {r}) ∪ Y = A := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzr⟩ | hzY)
              · rcases (show z ∈ A ∪ {r} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzr
              · rcases (show z ∈ A ∪ {r} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z; exact absurd hzY (Set.disjoint_left.mp hdXY hrX)
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl ⟨h, fun hzr => hQout r hrQ (hzr ▸ Or.inl (Or.inl hzA))⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {r}) Y (Or.inl hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have haY : a ∈ Y := by
            rcases (show a ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.1) with h | h
            · exact absurd ⟨h, fun har => hQout r hrQ (har ▸ Or.inl (Or.inl hR.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd a)
            · exact h
          exact ⟨r, Q, v, a, R, b, hnewstep, Or.inl hrX, Or.inl haY⟩
      · have hrY : r ∈ Y :=
          (show r ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hrX
        by_cases hYd : (Y \ {r}).Nonempty
        · have hOld : X ∪ (Y \ {r}) = A := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzr⟩)
              · rcases (show z ∈ A ∪ {r} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z; exact absurd hzX (Set.disjoint_right.mp hdXY hrY)
              · rcases (show z ∈ A ∪ {r} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzr
            · intro z hzA
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzA) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hzr => hQout r hrQ (hzr ▸ Or.inl (Or.inl hzA))⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {r}) (Or.inl hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have haX : a ∈ X := by
            rcases (show a ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.1) with h | h
            · exact h
            · exact absurd ⟨h, fun har => hQout r hrQ (har ▸ Or.inl (Or.inl hR.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd a)
          exact ⟨a, R, b, r, Q, v, step_symm hnewstep, Or.inl haX, Or.inl hrY⟩
    · by_cases hvX : v ∈ X
      · by_cases hXd : (X \ {v}).Nonempty
        · have hOld : (X \ {v}) ∪ Y = B := by
            apply Set.Subset.antisymm
            · rintro z (⟨hzX, hzv⟩ | hzY)
              · rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · exact absurd h hzv
              · rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · subst z; exact absurd hzY (Set.disjoint_left.mp hdXY hvX)
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl ⟨h, fun hzv => hQout v hvQ (hzv ▸ Or.inl (Or.inr hzB))⟩
              · exact Or.inr h
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {v}) Y (Or.inr hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have hbY : b ∈ Y := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.2.1) with h | h
            · exact absurd ⟨h, fun hbv => hQout v hvQ (hbv ▸ Or.inl (Or.inr hR.2.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd b)
            · exact h
          exact ⟨r, Q, v, a, R, b, hnewstep, Or.inr hvX, Or.inr hbY⟩
      · have hvY : v ∈ Y :=
          (show v ∈ X ∪ Y by rw [hXY]; exact Or.inr rfl).resolve_left hvX
        by_cases hYd : (Y \ {v}).Nonempty
        · have hOld : X ∪ (Y \ {v}) = B := by
            apply Set.Subset.antisymm
            · rintro z (hzX | ⟨hzY, hzv⟩)
              · rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inl hzX) with h | h
                · exact h
                · subst z; exact absurd hzX (Set.disjoint_right.mp hdXY hvY)
              · rcases (show z ∈ B ∪ {v} by rw [← hXY]; exact Or.inr hzY) with h | h
                · exact h
                · exact absurd h hzv
            · intro z hzB
              rcases (show z ∈ X ∪ Y by rw [hXY]; exact Or.inl hzB) with h | h
              · exact Or.inl h
              · exact Or.inr ⟨h, fun hzv => hQout v hvQ (hzv ▸ Or.inl (Or.inr hzB))⟩
          obtain ⟨c₁, P₁, d₁, c₂, P₂, d₂, hs, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {v}) (Or.inr hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, P₁, d₁, c₂, P₂, d₂, step_up hs, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have hbX : b ∈ X := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.2.1) with h | h
            · exact h
            · exact absurd ⟨h, fun hbv => hQout v hvQ (hbv ▸ Or.inl (Or.inr hR.2.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd b)
          exact ⟨a, R, b, r, Q, v, step_symm hnewstep, Or.inr hbX, Or.inr hvY⟩

/-- PAPER (12.2, printed p. 72): *"Then we can add `f₁` to `A`, `fᵢ`
to `B` and `{f₂,…,fᵢ₋₁}` to `C`, contrary to the maximality of the
staircase."*

This is the remaining strip-enlargement construction after the relabelling
in 10.1.3 has been removed. -/
theorem two_end_path_enlarges_staircase
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (q : List V) (s t : V) (hq : IsPathFrom G q s t)
    (hlen : 2 ≤ q.length) (hqF : ∀ x ∈ q, x ∈ F)
    (hsa₁ : G.Adj s a₁) (hsa₀ : G.Adj s a₀)
    (htb₁ : G.Adj t b₁) (htb₀ : G.Adj t b₀)
    (hcross : ∀ x ∈ q, ∀ k ∈
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
      G.Adj x k →
        (x = s ∧ (k = a₁ ∨ k = a₀)) ∨
        (x = t ∧ (k = b₁ ∨ k = b₀))) : False := by
  classical
  have hK := hMax.1
  have hban := hK.2.1
  have hsQ := Workspace.ProofLemmas.PathBasics.head_mem hq.2.1
  have htQ := Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2
  have hst : s ≠ t := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hq (by
    change 1 ≤ q.length - 1
    omega)
  have hQoutside : ∀ x ∈ q, x ∉ staircaseVertices A C B R₀ :=
    fun x hx => hFoutside (hqF x hx)
  have hQstrip : ∀ x ∈ q, x ∉ A ∪ B ∪ C :=
    fun x hx h => hQoutside x hx (Or.inr h)
  have ha₀R₀ := Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1
  have hb₀R₀ := Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2
  have ha₁R₁ := Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1
  have hb₁R₁ := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
  have ha₀R₁ : a₀ ∉ R₁ := fun h =>
    hban.2.1 a₀ ha₀R₀ (rung_mem_strip hstep.1 a₀ h)
  have hb₀R₁ : b₀ ∉ R₁ := fun h =>
    hban.2.1 b₀ hb₀R₀ (rung_mem_strip hstep.1 b₀ h)
  have ha₁R₀ : a₁ ∉ R₀ := fun h =>
    hban.2.1 a₁ h (Or.inl (Or.inl hstep.1.2.1))
  have hb₁R₀ : b₁ ∉ R₀ := fun h =>
    hban.2.1 b₁ h (Or.inl (Or.inr hstep.1.2.2.1))
  have hcrossR₁ : ∀ x ∈ q, ∀ k ∈ R₁,
      (G.Adj x k ↔ (x = s ∧ k = a₁) ∨ (x = t ∧ k = b₁)) := by
    intro x hx k hk
    constructor
    · intro hxk
      rcases hcross x hx k (Or.inl (Or.inl hk)) hxk with hc | hc
      · rcases hc.2 with hka₁ | hka₀
        · exact Or.inl ⟨hc.1, hka₁⟩
        · exact (ha₀R₁ (hka₀ ▸ hk)).elim
      · rcases hc.2 with hkb₁ | hkb₀
        · exact Or.inr ⟨hc.1, hkb₁⟩
        · exact (hb₀R₁ (hkb₀ ▸ hk)).elim
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hsa₁
      · exact htb₁
  have hcrossR₀ : ∀ x ∈ q, ∀ k ∈ R₀,
      (G.Adj x k ↔ (x = s ∧ k = a₀) ∨ (x = t ∧ k = b₀)) := by
    intro x hx k hk
    constructor
    · intro hxk
      rcases hcross x hx k (Or.inr hk) hxk with hc | hc
      · rcases hc.2 with hka₁ | hka₀
        · exact (ha₁R₀ (hka₁ ▸ hk)).elim
        · exact Or.inl ⟨hc.1, hka₀⟩
      · rcases hc.2 with hkb₁ | hkb₀
        · exact (hb₁R₀ (hkb₁ ▸ hk)).elim
        · exact Or.inr ⟨hc.1, hkb₀⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact hsa₀
      · exact htb₀
  have hSnew : StepConnected G (A ∪ {s})
      (C ∪ {z : V | z ∈ interior q}) (B ∪ {t}) :=
    stepConnected_adjoin_crossed_path G A C B hK.1 s t q hq hst hQstrip
      a₁ b₁ R₁ hstep.1 hcrossR₁
  let D : Set V := {z : V | z ∈ interior q}
  have hDmem : ∀ z ∈ D, z ∈ q := fun z hz =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.1
  have hDneS : ∀ z ∈ D, z ≠ s := fun z hz =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.1
  have hDneT : ∀ z ∈ D, z ≠ t := fun z hz =>
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).1 hz |>.2.2
  have hQRother : ∀ x ∈ q, x ≠ s → x ≠ t → ∀ z ∈ R₀, ¬ G.Adj x z := by
    intro x hx hxs hxt z hz hxz
    rcases (hcrossR₀ x hx z hz).1 hxz with hc | hc
    · exact hxs hc.1
    · exact hxt hc.1
  have ha₀b₀ : a₀ ≠ b₀ := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hban.1 (by
    exact le_trans (by decide : 1 ≤ 3) hK.2.2)
  have hta₀ : ¬ G.Adj a₀ t := by
    intro hat
    rcases (hcrossR₀ t htQ a₀ ha₀R₀).1 hat.symm with hc | hc
    · exact hst hc.1.symm
    · exact ha₀b₀ hc.2
  have hsb₀ : ¬ G.Adj b₀ s := by
    intro hbs
    rcases (hcrossR₀ s hsQ b₀ hb₀R₀).1 hbs.symm with hc | hc
    · exact ha₀b₀ hc.2.symm
    · exact hst hc.1
  have hsInt : ∀ z ∈ interior R₀, ¬ G.Adj z s := by
    intro z hz hzs
    have hzdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 hz
    rcases (hcrossR₀ s hsQ z hzdata.1).1 hzs.symm with hc | hc
    · exact hzdata.2.1 hc.2
    · exact hzdata.2.2 hc.2
  have htInt : ∀ z ∈ interior R₀, ¬ G.Adj z t := by
    intro z hz hzt
    have hzdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 hz
    rcases (hcrossR₀ t htQ z hzdata.1).1 hzt.symm with hc | hc
    · exact hst hc.1.symm
    · exact hzdata.2.2 hc.2
  have hbannew : IsBanister G (A ∪ {s}) (C ∪ D) (B ∪ {t}) a₀ R₀ b₀ := by
    refine ⟨hban.1, ?_, ?_, ?_, ?_⟩
    · intro z hz hznew
      rcases hznew with ((hzA | hzs) | (hzB | hzt)) | (hzC | hzD)
      · exact hban.2.1 z hz (Or.inl (Or.inl hzA))
      · exact hQoutside s hsQ (hzs ▸ Or.inl hz)
      · exact hban.2.1 z hz (Or.inl (Or.inr hzB))
      · exact hQoutside t htQ (hzt ▸ Or.inl hz)
      · exact hban.2.1 z hz (Or.inr hzC)
      · exact hQoutside z (hDmem z hzD) (Or.inl hz)
    · refine ⟨?_, ?_, ?_⟩
      · intro ha
        rcases ha with ((haA | has) | (haB | hat)) | (haC | haD)
        · exact hban.2.2.1.1 (Or.inl (Or.inl haA))
        · exact hQoutside s hsQ (has ▸ Or.inl ha₀R₀)
        · exact hban.2.2.1.1 (Or.inl (Or.inr haB))
        · exact hQoutside t htQ (hat ▸ Or.inl ha₀R₀)
        · exact hban.2.2.1.1 (Or.inr haC)
        · exact hQoutside a₀ (hDmem a₀ haD) (Or.inl ha₀R₀)
      · intro z hz
        rcases hz with hzA | hzs
        · exact hban.2.2.1.2.1 z hzA
        · subst z; exact hsa₀.symm
      · intro z hz hadj
        rcases hz with (hzB | hzt) | (hzC | hzD)
        · exact hban.2.2.1.2.2 z (Or.inl hzB) hadj
        · subst z; exact hta₀ hadj
        · exact hban.2.2.1.2.2 z (Or.inr hzC) hadj
        · exact hQRother z (hDmem z hzD) (hDneS z hzD) (hDneT z hzD)
            a₀ ha₀R₀ hadj.symm
    · refine ⟨?_, ?_, ?_⟩
      · intro hb
        rcases hb with ((hbA | hbs) | (hbB | hbt)) | (hbC | hbD)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl hbA))
        · exact hQoutside s hsQ (hbs ▸ Or.inl hb₀R₀)
        · exact hban.2.2.2.1.1 (Or.inl (Or.inr hbB))
        · exact hQoutside t htQ (hbt ▸ Or.inl hb₀R₀)
        · exact hban.2.2.2.1.1 (Or.inr hbC)
        · exact hQoutside b₀ (hDmem b₀ hbD) (Or.inl hb₀R₀)
      · intro z hz
        rcases hz with hzB | hzt
        · exact hban.2.2.2.1.2.1 z hzB
        · subst z; exact htb₀.symm
      · intro z hz hadj
        rcases hz with (hzA | hzs) | (hzC | hzD)
        · exact hban.2.2.2.1.2.2 z (Or.inl hzA) hadj
        · subst z; exact hsb₀ hadj
        · exact hban.2.2.2.1.2.2 z (Or.inr hzC) hadj
        · exact hQRother z (hDmem z hzD) (hDneS z hzD) (hDneT z hzD)
            b₀ hb₀R₀ hadj.symm
    · intro z hz w hw hzw
      rcases hw with ((hwA | hws) | (hwB | hwt)) | (hwC | hwD)
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inl hwA)) hzw
      · subst w; exact hsInt z hz hzw
      · exact hban.2.2.2.2 z hz w (Or.inl (Or.inr hwB)) hzw
      · subst w; exact htInt z hz hzw
      · exact hban.2.2.2.2 z hz w (Or.inr hwC) hzw
      · exact hQRother w (hDmem w hwD) (hDneS w hwD) (hDneT w hwD)
          z ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 hz).1
          hzw.symm
  have hnew : IsStaircase G (A ∪ {s}) (C ∪ D) (B ∪ {t}) a₀ R₀ b₀ :=
    ⟨by simpa [D] using hSnew, hbannew, hK.2.2⟩
  apply hMax.2
  refine ⟨A ∪ {s}, C ∪ D, B ∪ {t}, a₀, R₀, b₀, hnew,
    Set.subset_union_left, Set.subset_union_left, Set.subset_union_left, ?_⟩
  have hsub : A ∪ B ∪ C ⊆ (A ∪ {s}) ∪ (B ∪ {t}) ∪ (C ∪ D) := by
    intro z hz
    rcases hz with (hzA | hzB) | hzC
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr (Or.inl hzB))
    · exact Or.inr (Or.inl hzC)
  apply (Set.ssubset_iff_of_subset hsub).2
  exact ⟨s, Or.inl (Or.inl (Or.inr rfl)), fun hsold => hQstrip s hsQ hsold⟩

/-- PAPER (12.2, printed p. 72): *"Suppose that 10.1.3 holds. Since `f₁` is
not adjacent to `a₂`, it follows that `f₁` is adjacent to `a₀,a₁`, and
there exists `i` with `2 ≤ i ≤ k` such that `fᵢ` is adjacent to `b₀,b₁`, and
there are no other edges between `{f₁,…,fᵢ}` and `V(K⁰)`. Then we can add
`f₁` to `A`, `fᵢ` to `B` and `{f₂,…,fᵢ₋₁}` to `C`, contrary to the
maximality of the staircase."* -/
theorem third_case_contradicts_maximality
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hnoa₂ : ∀ x ∈ F, ¬ G.Adj x a₂)
    (q : List V) (p₁ p₂ : V)
    (hq : IsPathFrom G q p₁ p₂) (hqF : ∀ x ∈ q, x ∈ F)
    (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (σ : Equiv.Perm (Fin 3))
    (hR' : R' = fun i => ![R₁, R₂, R₀] (σ i))
    (hab : ((a' = fun i => ![a₁, a₂, a₀] (σ i)) ∧
        (b' = fun i => ![b₁, b₂, b₀] (σ i))) ∨
      ((a' = fun i => ![b₁, b₂, b₀] (σ i)) ∧
        (b' = fun i => ![a₁, a₂, a₀] (σ i))))
    (hcase : 2 ≤ q.length ∧ G.Adj p₁ (a' 0) ∧ G.Adj p₁ (a' 1) ∧
      G.Adj p₂ (b' 0) ∧ G.Adj p₂ (b' 1) ∧
      (∀ x ∈ q, ∀ k ∈
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
        G.Adj x k →
          (x = p₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨
          (x = p₂ ∧ (k = b' 0 ∨ k = b' 1)))) : False := by
  classical
  obtain ⟨hlen, hp₁a0, hp₁a1, hp₂b0, hp₂b1, hcross⟩ := hcase
  have hp₁F : p₁ ∈ F := hqF p₁
    (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)
  have hp₂F : p₂ ∈ F := hqF p₂
    (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2)
  have pair_of_avoids_one (h0 : σ 0 ≠ 1) (h1 : σ 1 ≠ 1) :
      (σ 0 = 0 ∧ σ 1 = 2) ∨ (σ 0 = 2 ∧ σ 1 = 0) := by
    have hfin : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
    have hz0 : σ 0 = 0 ∨ σ 0 = 2 := by
      rcases hfin (σ 0) with h | h | h
      · exact Or.inl h
      · exact (h0 h).elim
      · exact Or.inr h
    have hz1 : σ 1 = 0 ∨ σ 1 = 2 := by
      rcases hfin (σ 1) with h | h | h
      · exact Or.inl h
      · exact (h1 h).elim
      · exact Or.inr h
    rcases hz0 with h00 | h02 <;> rcases hz1 with h10 | h12
    · exact (by have := σ.injective (h00.trans h10.symm); omega)
    · exact Or.inl ⟨h00, h12⟩
    · exact Or.inr ⟨h02, h10⟩
    · exact (by have := σ.injective (h02.trans h12.symm); omega)
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hσ0 : σ 0 ≠ 1 := by
      intro he
      apply hnoa₂ p₁ hp₁F
      simpa [ha, he] using hp₁a0
    have hσ1 : σ 1 ≠ 1 := by
      intro he
      apply hnoa₂ p₁ hp₁F
      simpa [ha, he] using hp₁a1
    rcases pair_of_avoids_one hσ0 hσ1 with ⟨h00, h12⟩ | ⟨h02, h10⟩
    · apply two_end_path_enlarges_staircase G A C B a₀ b₀ R₀ hMax F hFoutside
        a₁ b₁ a₂ b₂ R₁ R₂ hstep q p₁ p₂ hq hlen hqF
      · simpa [ha, h00] using hp₁a0
      · simpa [ha, h12] using hp₁a1
      · simpa [hb, h00] using hp₂b0
      · simpa [hb, h12] using hp₂b1
      · intro x hx k hk hxk
        simpa [ha, hb, h00, h12] using hcross x hx k hk hxk
    · apply two_end_path_enlarges_staircase G A C B a₀ b₀ R₀ hMax F hFoutside
        a₁ b₁ a₂ b₂ R₁ R₂ hstep q p₁ p₂ hq hlen hqF
      · simpa [ha, h10] using hp₁a1
      · simpa [ha, h02] using hp₁a0
      · simpa [hb, h10] using hp₂b1
      · simpa [hb, h02] using hp₂b0
      · intro x hx k hk hxk
        simpa [ha, hb, h02, h10, or_comm] using hcross x hx k hk hxk
  · have hσ0 : σ 0 ≠ 1 := by
      intro he
      apply hnoa₂ p₂ hp₂F
      simpa [hb, he] using hp₂b0
    have hσ1 : σ 1 ≠ 1 := by
      intro he
      apply hnoa₂ p₂ hp₂F
      simpa [hb, he] using hp₂b1
    rcases pair_of_avoids_one hσ0 hσ1 with ⟨h00, h12⟩ | ⟨h02, h10⟩
    · apply two_end_path_enlarges_staircase G A C B a₀ b₀ R₀ hMax F hFoutside
        a₁ b₁ a₂ b₂ R₁ R₂ hstep q.reverse p₂ p₁
          (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq) (by simpa)
          (fun x hx => hqF x (List.mem_reverse.mp hx))
      · simpa [hb, h00] using hp₂b0
      · simpa [hb, h12] using hp₂b1
      · simpa [ha, h00] using hp₁a0
      · simpa [ha, h12] using hp₁a1
      · intro x hx k hk hxk
        rcases hcross x (List.mem_reverse.mp hx) k hk hxk with hc | hc
        · exact Or.inr ⟨hc.1, by simpa [ha, h00, h12] using hc.2⟩
        · exact Or.inl ⟨hc.1, by simpa [hb, h00, h12] using hc.2⟩
    · apply two_end_path_enlarges_staircase G A C B a₀ b₀ R₀ hMax F hFoutside
        a₁ b₁ a₂ b₂ R₁ R₂ hstep q.reverse p₂ p₁
          (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq) (by simpa)
          (fun x hx => hqF x (List.mem_reverse.mp hx))
      · simpa [hb, h10] using hp₂b1
      · simpa [hb, h02] using hp₂b0
      · simpa [ha, h10] using hp₁a1
      · simpa [ha, h02] using hp₁a0
      · intro x hx k hk hxk
        rcases hcross x (List.mem_reverse.mp hx) k hk hxk with hc | hc
        · exact Or.inr ⟨hc.1, by simpa [ha, h02, h10, or_comm] using hc.2⟩
        · exact Or.inl ⟨hc.1, by simpa [hb, h02, h10, or_comm] using hc.2⟩

/-- PAPER (12.2, printed p. 72): *"If `j > 0` then in the first case we can
add `p₁` to `A` and `V(P \ p₁)` to `C`, contrary to the maximality of the
staircase; and in the second case we do the same with `A` and `B` exchanged."*

Here index `2` is the paper's rung `R₀`, so `σ 2 ≠ 2` is its condition
`j > 0`. -/
theorem positive_missing_rung_contradicts_maximality
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (q : List V) (p₁ p₂ : V)
    (hq : IsPathFrom G q p₁ p₂) (hqF : ∀ x ∈ q, x ∈ F)
    (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (σ : Equiv.Perm (Fin 3))
    (hR' : R' = fun i => ![R₁, R₂, R₀] (σ i))
    (hab : ((a' = fun i => ![a₁, a₂, a₀] (σ i)) ∧
        (b' = fun i => ![b₁, b₂, b₀] (σ i))) ∨
      ((a' = fun i => ![b₁, b₂, b₀] (σ i)) ∧
        (b' = fun i => ![a₁, a₂, a₀] (σ i))))
    (hcase : G.Adj p₁ (a' 0) ∧ G.Adj p₁ (a' 1) ∧
      (∃ y ∈ R' 2, y ≠ a' 2 ∧ G.Adj p₂ y) ∧
      (∀ x ∈ q, ∀ k ∈
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
        k ≠ a' 2 → G.Adj x k →
          (x = p₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨
          (x = p₂ ∧ k ∈ R' 2)))
    (hj : σ 2 ≠ 2) : False := by
  classical
  have hqout : ∀ x ∈ q, x ∉ staircaseVertices A C B R₀ :=
    fun x hx => hFoutside (hqF x hx)
  have hperm :
      (σ 0 = 0 ∧ σ 1 = 2 ∧ σ 2 = 1) ∨
      (σ 0 = 2 ∧ σ 1 = 0 ∧ σ 2 = 1) ∨
      (σ 0 = 1 ∧ σ 1 = 2 ∧ σ 2 = 0) ∨
      (σ 0 = 2 ∧ σ 1 = 1 ∧ σ 2 = 0) := by
    have hfinite : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → k ≠ 2 →
        (i = 0 ∧ j = 2 ∧ k = 1) ∨ (i = 2 ∧ j = 0 ∧ k = 1) ∨
        (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 1 ∧ k = 0) := by decide
    exact hfinite (σ 0) (σ 1) (σ 2)
      (fun he => (by decide : (0 : Fin 3) ≠ 1) (σ.injective he))
      (fun he => (by decide : (0 : Fin 3) ≠ 2) (σ.injective he))
      (fun he => (by decide : (1 : Fin 3) ≠ 2) (σ.injective he)) hj
  rcases hab with ⟨ha, _⟩ | ⟨ha, _⟩
  · rcases hperm with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
        ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.left_case hMax
        (Workspace.ProofLemmas.NonlocalStaircaseSelectedStep.step_symm hstep) hq hqout
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.left_case hMax
        (Workspace.ProofLemmas.NonlocalStaircaseSelectedStep.step_symm hstep) hq hqout
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.left_case hMax
        hstep hq hqout
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.left_case hMax
        hstep hq hqout
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
  · rcases hperm with ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩ |
        ⟨h0, h1, h2⟩ | ⟨h0, h1, h2⟩
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.right_case hMax
        (Workspace.ProofLemmas.NonlocalStaircaseSelectedStep.step_symm hstep) hq hqout
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.right_case hMax
        (Workspace.ProofLemmas.NonlocalStaircaseSelectedStep.step_symm hstep) hq hqout
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.right_case hMax
        hstep hq hqout
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)
    · exact Workspace.ProofLemmas.NonlocalStaircaseRungSuffix.right_case hMax
        hstep hq hqout
        (by simpa [ha, h0] using hcase.1)
        (by simpa [ha, h1] using hcase.2.1)
        (by simpa [ha, hR', h2] using hcase.2.2.1)
        (by simpa [ha, hR', h0, h1, h2, Set.union_comm, or_comm] using hcase.2.2.2)

/-- PAPER (12.2, printed p. 72): *"From the minimality of `F`, `F = V(P)`.
If `j > 0` then in the first case we can add `p₁` to `A` and `V(P \ p₁)`
to `C`, contrary to the maximality of the staircase; and in the second case
we do the same with `A` and `B` exchanged. So `j = 0`. The first case is
impossible since no vertex in `F` is adjacent to `a₂`; and the second case
is impossible since `f₁ ∈ F = V(P)` and `f₁` has a neighbour in
`R₁ \ b₁`."* -/
theorem fourth_case_contradiction
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (hMinimal : ∀ D : Set V, D ⊂ F → ConnectedSet G D →
      LocalForStaircase A C B a₀ R₀ b₀
        (Workspace.Types.Appearances.SPGT.attachments G D
          (staircaseVertices A C B R₀)))
    (f₁ : V) (hf₁F : f₁ ∈ F)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hy : ∃ y ∈ R₁, y ≠ b₁ ∧ G.Adj f₁ y)
    (hnoa₂ : ∀ x ∈ F, ¬ G.Adj x a₂)
    (q : List V) (p₁ p₂ : V)
    (hq : IsPathFrom G q p₁ p₂) (hqF : ∀ x ∈ q, x ∈ F)
    (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (σ : Equiv.Perm (Fin 3))
    (hR' : R' = fun i => ![R₁, R₂, R₀] (σ i))
    (hab : ((a' = fun i => ![a₁, a₂, a₀] (σ i)) ∧
        (b' = fun i => ![b₁, b₂, b₀] (σ i))) ∨
      ((a' = fun i => ![b₁, b₂, b₀] (σ i)) ∧
        (b' = fun i => ![a₁, a₂, a₀] (σ i))))
    (hcase : G.Adj p₁ (a' 0) ∧ G.Adj p₁ (a' 1) ∧
      (∃ y ∈ R' 2, y ≠ a' 2 ∧ G.Adj p₂ y) ∧
      (∀ x ∈ q, ∀ k ∈
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
        k ≠ a' 2 → G.Adj x k →
          (x = p₁ ∧ (k = a' 0 ∨ k = a' 1)) ∨
          (x = p₂ ∧ k ∈ R' 2))) : False := by
  classical
  by_cases hj : σ 2 = 2
  · obtain ⟨hp₁a0, hp₁a1, ⟨y, hyR', hya', hp₂y⟩, honly⟩ := hcase
    have hpair : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
      have hfin : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
      have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
        rcases hfin (σ 0) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (by have := σ.injective (h.trans hj.symm); omega)
      have h1 : σ 1 = 0 ∨ σ 1 = 1 := by
        rcases hfin (σ 1) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (by have := σ.injective (h.trans hj.symm); omega)
      rcases h0 with h00 | h01 <;> rcases h1 with h10 | h11
      · exact (by have := σ.injective (h00.trans h10.symm); omega)
      · exact Or.inl ⟨h00, h11⟩
      · exact Or.inr ⟨h01, h10⟩
      · exact (by have := σ.injective (h01.trans h11.symm); omega)
    rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hpair with ⟨h00, h11⟩ | ⟨h01, h10⟩
      · exact hnoa₂ p₁ (hqF p₁ (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1))
          (by simpa [ha, h11] using hp₁a1)
      · exact hnoa₂ p₁ (hqF p₁ (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1))
          (by simpa [ha, h01] using hp₁a0)
    · have hyR₀ : y ∈ R₀ := by simpa [hR', hj] using hyR'
      have hyb₀ : y ≠ b₀ := by simpa [ha, hj] using hya'
      let D : Set V := {x : V | x ∈ q}
      have hDsub : D ⊆ F := by
        intro x hx
        exact hqF x hx
      have hDconn : ConnectedSet G D :=
        Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hq.1
      have hDeq : D = F := by
        by_contra hne
        have hproper : D ⊂ F := Set.ssubset_iff_subset_ne.2 ⟨hDsub, hne⟩
        have hloc := hMinimal D hproper hDconn
        have hp₁D : p₁ ∈ D := Workspace.ProofLemmas.PathBasics.head_mem hq.2.1
        have hp₂D : p₂ ∈ D := Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2
        have hb₁att : b₁ ∈ Workspace.Types.Appearances.SPGT.attachments G D
            (staircaseVertices A C B R₀) := by
          refine ⟨Or.inr (Or.inl (Or.inr hstep.1.2.2.1)), p₁, hp₁D, ?_⟩
          rcases hpair with ⟨h00, h11⟩ | ⟨h01, h10⟩
          · simpa [ha, h00] using hp₁a0.symm
          · simpa [ha, h10] using hp₁a1.symm
        have hyatt : y ∈ Workspace.Types.Appearances.SPGT.attachments G D
            (staircaseVertices A C B R₀) := ⟨Or.inl hyR₀, p₂, hp₂D, hp₂y.symm⟩
        rcases hloc with hloc | hloc | hloc | hloc
        · exact hMax.1.2.1.2.1 y hyR₀ (hloc hyatt)
        · exact hMax.1.2.1.2.1 b₁ (hloc hb₁att)
            (Or.inl (Or.inr hstep.1.2.2.1))
        · rcases hloc hb₁att with hb₁A | hb₁a₀
          · exact Set.disjoint_left.mp hMax.1.1.1.1 hb₁A hstep.1.2.2.1
          · exact hMax.1.2.1.2.1 a₀
              (Workspace.ProofLemmas.PathBasics.head_mem hMax.1.2.1.1.2.1)
              (hb₁a₀.symm ▸ Or.inl (Or.inr hstep.1.2.2.1))
        · rcases hloc hyatt with hyB | hyb
          · exact hMax.1.2.1.2.1 y hyR₀ (Or.inl (Or.inr hyB))
          · exact hyb₀ (Set.mem_singleton_iff.mp hyb)
      have hf₁q : f₁ ∈ q := by
        have : f₁ ∈ D := by rw [hDeq]; exact hf₁F
        exact this
      obtain ⟨z, hzR₁, hzb₁, hf₁z⟩ := hy
      have hzb₀ : z ≠ b₀ := by
        intro hzb
        exact hMax.1.2.1.2.1 b₀
          (Workspace.ProofLemmas.PathBasics.getLast_mem hMax.1.2.1.1.2.2)
          (hzb.symm ▸ rung_mem_strip hstep.1 z hzR₁)
      have hzK : z ∈ {w : V | w ∈ R₁} ∪ {w : V | w ∈ R₂} ∪
          {w : V | w ∈ R₀} := Or.inl (Or.inl hzR₁)
      have hza' : z ≠ a' 2 := by simpa [ha, hj] using hzb₀
      have hc := honly f₁ hf₁q z hzK hza' hf₁z
      rcases hpair with ⟨h00, h11⟩ | ⟨h01, h10⟩
      · have hc' : (f₁ = p₁ ∧ (z = b₁ ∨ z = b₂)) ∨
            (f₁ = p₂ ∧ z ∈ R₀) := by
          simpa [ha, hR', h00, h11, hj] using hc
        rcases hc' with hc' | hc'
        · rcases hc'.2 with h | h
          · exact hzb₁ h
          · exact hstep.2.2.1 z hzR₁
              (h ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2)
        · exact hMax.1.2.1.2.1 z hc'.2 (rung_mem_strip hstep.1 z hzR₁)
      · have hc' : (f₁ = p₁ ∧ (z = b₂ ∨ z = b₁)) ∨
            (f₁ = p₂ ∧ z ∈ R₀) := by
          simpa [ha, hR', h01, h10, hj] using hc
        rcases hc' with hc' | hc'
        · rcases hc'.2 with h | h
          · exact hstep.2.2.1 z hzR₁
              (h ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2)
          · exact hzb₁ h
        · exact hMax.1.2.1.2.1 z hc'.2 (rung_mem_strip hstep.1 z hzR₁)
  · exact positive_missing_rung_contradicts_maximality G A C B a₀ b₀ R₀ hMax
      F hFoutside a₁ b₁ a₂ b₂ R₁ R₂ hstep q p₁ p₂ hq hqF
      a' b' R' σ hR' hab hcase hj

end Workspace.ProofLemmas.NonlocalStaircasePrismJumpEndgame
