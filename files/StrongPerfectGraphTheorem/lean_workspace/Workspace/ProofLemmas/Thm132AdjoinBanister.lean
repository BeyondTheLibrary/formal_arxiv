import Workspace.ProofLemmas.Thm132BanisterAttachment

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Adjoining a separated banister to a step-connected strip

This is the set-theoretic construction behind claim (1) of 13.2: a banister
`r-Q-v` becomes one additional rung by adjoining `r` to `A`, `v` to `B`, and
the interior of `Q` to `C`.
-/

namespace Workspace.ProofLemmas.Thm132AdjoinBanister

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  · exact Or.inr (hR.2.2.2.2.2 z
      ((PathBasics.mem_interior_iff_of_pathFrom hR.1).2 ⟨hz, hza, hzb⟩))

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, ?_, ?_⟩
  · intro z hz₂ hz₁
    exact h.2.2.1 z hz₁ hz₂
  · intro u hu v hv
    rw [G.adj_comm, h.2.2.2 v hv u hu]
    tauto

/-- Adding all vertices of one outside banister as one new rung preserves
step-connectedness. -/
theorem stepConnected_adjoin_banister
    {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B)
    {r v : V} {Q : List V} (hQ : IsBanister G A C B r Q v) :
    StepConnected G (A ∪ {r}) (C ∪ {z : V | z ∈ interior Q}) (B ∪ {v}) := by
  classical
  let D : Set V := {z : V | z ∈ interior Q}
  have hrQ : r ∈ Q := PathBasics.head_mem hQ.1.2.1
  have hvQ : v ∈ Q := PathBasics.getLast_mem hQ.1.2.2
  have hrne : r ≠ v := by
    obtain ⟨a, ha⟩ := hS.2.1.1
    intro hrv
    exact hQ.2.2.2.1.2.2 a (Or.inl ha) (hrv ▸ hQ.2.2.1.2.1 a ha)
  have hrD : r ∉ D := fun hr =>
    (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hr |>.2.1 rfl
  have hvD : v ∉ D := fun hv =>
    (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hv |>.2.2 rfl
  have hDmem : ∀ z ∈ D, z ∈ Q := fun z hz =>
    (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hz |>.1
  have hQout : ∀ z ∈ Q, z ∉ A ∪ B ∪ C := hQ.2.1

  -- Old rungs and old steps remain valid after the enlargement.
  have rung_up : ∀ {a b : V} {R : List V}, IsRungOfStrip G A C B a R b →
      IsRungOfStrip G (A ∪ {r}) (C ∪ D) (B ∪ {v}) a R b := by
    intro a b R hR
    refine ⟨hR.1, Or.inl hR.2.1, Or.inl hR.2.2.1, ?_, ?_, ?_⟩
    · intro z hz hzA
      rcases hzA with hzA | hzr
      · exact hR.2.2.2.1 z hz hzA
      · subst z
        exact absurd (rung_mem_strip hR r hz) (hQout r hrQ)
    · intro z hz hzB
      rcases hzB with hzB | hzv
      · exact hR.2.2.2.2.1 z hz hzB
      · subst z
        exact absurd (rung_mem_strip hR v hz) (hQout v hvQ)
    · intro z hz
      exact Or.inl (hR.2.2.2.2.2 z hz)
  have step_up : ∀ {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V},
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ →
      IsStep G (A ∪ {r}) (C ∪ D) (B ∪ {v}) a₁ R₁ b₁ a₂ R₂ b₂ := by
    intro a₁ b₁ a₂ b₂ R₁ R₂ h
    exact ⟨rung_up h.1, rung_up h.2.1, h.2.2.1, h.2.2.2⟩

  have hnewrung : IsRungOfStrip G (A ∪ {r}) (C ∪ D) (B ∪ {v}) r Q v := by
    refine ⟨hQ.1, Or.inr rfl, Or.inr rfl, ?_, ?_, ?_⟩
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

  -- Fix one old rung; together with `Q` it is a step of the enlarged strip.
  obtain ⟨a₁, ha₁⟩ := hS.2.1.1
  obtain ⟨a, R, b, hR, haR⟩ := hS.2.2.1 a₁ (Or.inl (Or.inl ha₁))
  have haa₁ : a = a₁ := (hR.2.2.2.1 a₁ haR ha₁).symm
  subst a
  have hnewstep :
      IsStep G (A ∪ {r}) (C ∪ D) (B ∪ {v}) r Q v a₁ R b := by
    refine ⟨hnewrung, rung_up hR, ?_, ?_⟩
    · intro z hzQ hzR
      exact hQout z hzQ (rung_mem_strip hR z hzR)
    · intro q hq y hy
      have hyS := rung_mem_strip hR y hy
      constructor
      · intro hqy
        by_cases hqr : q = r
        · subst q
          rcases hyS with (hyA | hyB) | hyC
          · exact Or.inl ⟨rfl, hR.2.2.2.1 y hy hyA⟩
          · exact absurd hqy (hQ.2.2.1.2.2 y (Or.inl hyB))
          · exact absurd hqy (hQ.2.2.1.2.2 y (Or.inr hyC))
        · by_cases hqv : q = v
          · subst q
            rcases hyS with (hyA | hyB) | hyC
            · exact absurd hqy (hQ.2.2.2.1.2.2 y (Or.inl hyA))
            · exact Or.inr ⟨rfl, hR.2.2.2.2.1 y hy hyB⟩
            · exact absurd hqy (hQ.2.2.2.1.2.2 y (Or.inr hyC))
          · exact absurd hqy (hQ.2.2.2.2 q
              ((PathBasics.mem_interior_iff_of_pathFrom hQ.1).2 ⟨hq, hqr, hqv⟩)
              y hyS)
      · rintro (⟨hqr, hya⟩ | ⟨hqv, hyb⟩)
        · subst q
          subst y
          exact hQ.2.2.1.2.1 a₁ ha₁
        · subst q
          subst y
          exact hQ.2.2.2.1.2.1 b hR.2.2.1

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- pairwise disjointness of the enlarged classes
    refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
    · intro z hzA hzB
      rcases hzA with hzA | hzr <;> rcases hzB with hzB | hzv
      · exact Set.disjoint_left.mp hS.1.1 hzA hzB
      · exact hQout v hvQ (hzv ▸ Or.inl (Or.inl hzA))
      · exact hQout r hrQ (hzr ▸ Or.inl (Or.inr hzB))
      · exact hrne (hzr.symm.trans hzv)
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
    · obtain ⟨c, T, d, hT, hzT⟩ := hS.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨c, T, d, rung_up hT, hzT⟩
    · subst z; exact ⟨r, Q, v, hnewrung, hrQ⟩
    · obtain ⟨c, T, d, hT, hzT⟩ := hS.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨c, T, d, rung_up hT, hzT⟩
    · subst z; exact ⟨r, Q, v, hnewrung, hvQ⟩
    · obtain ⟨c, T, d, hT, hzT⟩ := hS.2.2.1 z (Or.inr hzC)
      exact ⟨c, T, d, rung_up hT, hzT⟩
    · exact ⟨r, Q, v, hnewrung, hDmem z hzD⟩
  · intro z hz
    rcases hz with ((hzA | hzr) | (hzB | hzv)) | (hzC | hzD)
    · obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm⟩ :=
        hS.2.2.2.1 z (Or.inl (Or.inl hzA))
      exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT, hm⟩
    · subst z; exact ⟨r, Q, v, a₁, R, b, hnewstep, Or.inl hrQ⟩
    · obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm⟩ :=
        hS.2.2.2.1 z (Or.inl (Or.inr hzB))
      exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT, hm⟩
    · subst z; exact ⟨r, Q, v, a₁, R, b, hnewstep, Or.inl hvQ⟩
    · obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm⟩ :=
        hS.2.2.2.1 z (Or.inr hzC)
      exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT, hm⟩
    · exact ⟨r, Q, v, a₁, R, b, hnewstep, Or.inl (hDmem z hzD)⟩
  · intro X Y hXY hdXY hXne hYne
    rcases hXY with hXY | hXY
    · -- partition of `A ∪ {r}`
      by_cases hrX : r ∈ X
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
          obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {r}) Y (Or.inl hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have ha₁Y : a₁ ∈ Y := by
            rcases (show a₁ ∈ X ∪ Y by rw [hXY]; exact Or.inl ha₁) with h | h
            · exact absurd ⟨h, fun har => hQout r hrQ (har ▸ Or.inl (Or.inl ha₁))⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd a₁)
            · exact h
          exact ⟨r, Q, v, a₁, R, b, hnewstep, Or.inl hrX, Or.inl ha₁Y⟩
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
          obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {r}) (Or.inl hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have ha₁X : a₁ ∈ X := by
            rcases (show a₁ ∈ X ∪ Y by rw [hXY]; exact Or.inl ha₁) with h | h
            · exact h
            · exact absurd ⟨h, fun har => hQout r hrQ (har ▸ Or.inl (Or.inl ha₁))⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd a₁)
          exact ⟨a₁, R, b, r, Q, v, step_symm hnewstep, Or.inl ha₁X, Or.inl hrY⟩
    · -- partition of `B ∪ {v}` (the exact mirror)
      by_cases hvX : v ∈ X
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
          obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm₁, hm₂⟩ :=
            hS.2.2.2.2 (X \ {v}) Y (Or.inr hOld)
              (Set.disjoint_of_subset_left Set.diff_subset hdXY) hXd hYne
          exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT,
            hm₁.imp (fun h => h.1) (fun h => h.1), hm₂⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hXd
          have hbY : b ∈ Y := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.2.1) with h | h
            · exact absurd ⟨h, fun hbv => hQout v hvQ (hbv ▸ Or.inl (Or.inr hR.2.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hXd b)
            · exact h
          exact ⟨r, Q, v, a₁, R, b, hnewstep, Or.inr hvX, Or.inr hbY⟩
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
          obtain ⟨c₁, T₁, d₁, c₂, T₂, d₂, hT, hm₁, hm₂⟩ :=
            hS.2.2.2.2 X (Y \ {v}) (Or.inr hOld)
              (Set.disjoint_of_subset_right Set.diff_subset hdXY) hXne hYd
          exact ⟨c₁, T₁, d₁, c₂, T₂, d₂, step_up hT, hm₁,
            hm₂.imp (fun h => h.1) (fun h => h.1)⟩
        · rw [Set.not_nonempty_iff_eq_empty] at hYd
          have hbX : b ∈ X := by
            rcases (show b ∈ X ∪ Y by rw [hXY]; exact Or.inl hR.2.2.1) with h | h
            · exact h
            · exact absurd ⟨h, fun hbv => hQout v hvQ (hbv ▸ Or.inl (Or.inr hR.2.2.1))⟩
                (Set.eq_empty_iff_forall_notMem.mp hYd b)
          exact ⟨a₁, R, b, r, Q, v, step_symm hnewstep, Or.inr hbX, Or.inr hvY⟩

/-- If the old banister and the new rung have precisely the endpoint
attachments supplied by the parity lemma, the construction is a strict
staircase enlargement and contradicts maximality. -/
theorem attached_banister_contradicts_maximality
    {G : SimpleGraph V} {A C B : Set V}
    {a b r v : V} {P Q : List V}
    (hK : MaximalStaircase G A C B a P b)
    (hQ : IsBanister G A C B r Q v)
    (hdisj : ∀ z ∈ P, z ∉ Q)
    (hvonly : ∀ z ∈ P, (G.Adj z v ↔ z = b))
    (haonly : ∀ z ∈ Q, (G.Adj a z ↔ z = r))
    (hnolink : ¬ ((({z : V | z ∈ P.tail} ∩ {z : V | z ∈ Q.dropLast}).Nonempty) ∨
      ∃ p ∈ P.tail, ∃ q ∈ Q.dropLast, G.Adj p q)) : False := by
  classical
  let D : Set V := {z : V | z ∈ interior Q}
  have hS := hK.1.1
  have hP := hK.1.2.1
  obtain ⟨a₁, ha₁⟩ := hS.2.1.1
  have hab : a ≠ b := by
    intro hab
    exact hP.2.2.2.1.2.2 a₁ (Or.inl ha₁) (hab ▸ hP.2.2.1.2.1 a₁ ha₁)
  have hrv : r ≠ v := by
    intro hrv
    exact hQ.2.2.2.1.2.2 a₁ (Or.inl ha₁) (hrv ▸ hQ.2.2.1.2.1 a₁ ha₁)
  have haP : a ∈ P := PathBasics.head_mem hP.1.2.1
  have hbP : b ∈ P := PathBasics.getLast_mem hP.1.2.2
  have hrQ : r ∈ Q := PathBasics.head_mem hQ.1.2.1
  have hvQ : v ∈ Q := PathBasics.getLast_mem hQ.1.2.2
  have hbTail : b ∈ P.tail :=
    (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2 ⟨hbP, hab.symm⟩
  have hrDrop : r ∈ Q.dropLast :=
    (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2 ⟨hrQ, hrv⟩
  have hDmem : ∀ z ∈ D, z ∈ Q := fun z hz =>
    (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hz |>.1
  have hDdrop : ∀ z ∈ D, z ∈ Q.dropLast := by
    intro z hz
    have hd := (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hz
    exact (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQ.1).2 ⟨hd.1, hd.2.2⟩
  have hcross :=
    Workspace.ProofLemmas.Thm132BanisterSeparation.halves_anticomplete_of_not_linked hnolink
  have hSnew : StepConnected G (A ∪ {r}) (C ∪ D) (B ∪ {v}) := by
    simpa [D] using stepConnected_adjoin_banister hS hQ
  have hPnew : IsBanister G (A ∪ {r}) (C ∪ D) (B ∪ {v}) a P b := by
    refine ⟨hP.1, ?_, ?_, ?_, ?_⟩
    · intro z hz hznew
      rcases hznew with ((hzA | hzr) | (hzB | hzv)) | (hzC | hzD)
      · exact hP.2.1 z hz (Or.inl (Or.inl hzA))
      · exact hdisj z hz (hzr ▸ hrQ)
      · exact hP.2.1 z hz (Or.inl (Or.inr hzB))
      · exact hdisj z hz (hzv ▸ hvQ)
      · exact hP.2.1 z hz (Or.inr hzC)
      · exact hdisj z hz (hDmem z hzD)
    · refine ⟨?_, ?_, ?_⟩
      · intro ha
        rcases ha with ((haA | har) | (haB | hav)) | (haC | haD)
        · exact hP.2.2.1.1 (Or.inl (Or.inl haA))
        · exact hdisj a haP (har ▸ hrQ)
        · exact hP.2.2.1.1 (Or.inl (Or.inr haB))
        · exact hdisj a haP (hav ▸ hvQ)
        · exact hP.2.2.1.1 (Or.inr haC)
        · exact hdisj a haP (hDmem a haD)
      · intro z hz
        rcases hz with hzA | hzr
        · exact hP.2.2.1.2.1 z hzA
        · subst z
          exact (haonly r hrQ).2 rfl
      · intro z hz
        rcases hz with (hzB | hzv) | (hzC | hzD)
        · exact hP.2.2.1.2.2 z (Or.inl hzB)
        · subst z
          intro hav
          have hvne : v ≠ r := hrv.symm
          exact hvne ((haonly v hvQ).1 hav)
        · exact hP.2.2.1.2.2 z (Or.inr hzC)
        · intro haz
          have hz_ne_r := (PathBasics.mem_interior_iff_of_pathFrom hQ.1).1 hzD |>.2.1
          exact hz_ne_r ((haonly z (hDmem z hzD)).1 haz)
    · refine ⟨?_, ?_, ?_⟩
      · intro hb
        rcases hb with ((hbA | hbr) | (hbB | hbv)) | (hbC | hbD)
        · exact hP.2.2.2.1.1 (Or.inl (Or.inl hbA))
        · exact hdisj b hbP (hbr ▸ hrQ)
        · exact hP.2.2.2.1.1 (Or.inl (Or.inr hbB))
        · exact hdisj b hbP (hbv ▸ hvQ)
        · exact hP.2.2.2.1.1 (Or.inr hbC)
        · exact hdisj b hbP (hDmem b hbD)
      · intro z hz
        rcases hz with hzB | hzv
        · exact hP.2.2.2.1.2.1 z hzB
        · subst z
          exact (hvonly b hbP).2 rfl
      · intro z hz
        rcases hz with (hzA | hzr) | (hzC | hzD)
        · exact hP.2.2.2.1.2.2 z (Or.inl hzA)
        · subst z
          exact hcross b hbTail r hrDrop
        · exact hP.2.2.2.1.2.2 z (Or.inr hzC)
        · exact hcross b hbTail z (hDdrop z hzD)
    · intro z hz y hy
      have hzd := (PathBasics.mem_interior_iff_of_pathFrom hP.1).1 hz
      have hzTail :=
        (HyperprismRungStructure.mem_tail_iff_of_pathFrom hP.1).2 ⟨hzd.1, hzd.2.1⟩
      rcases hy with ((hyA | hyr) | (hyB | hyv)) | (hyC | hyD)
      · exact hP.2.2.2.2 z hz y (Or.inl (Or.inl hyA))
      · subst y
        exact hcross z hzTail r hrDrop
      · exact hP.2.2.2.2 z hz y (Or.inl (Or.inr hyB))
      · subst y
        intro hzv
        exact hzd.2.2 ((hvonly z hzd.1).1 hzv)
      · exact hP.2.2.2.2 z hz y (Or.inr hyC)
      · exact hcross z hzTail y (hDdrop y hyD)
  have hstairsNew : IsStaircase G (A ∪ {r}) (C ∪ D) (B ∪ {v}) a P b :=
    ⟨hSnew, hPnew, hK.1.2.2⟩
  apply hK.2
  refine ⟨A ∪ {r}, C ∪ D, B ∪ {v}, a, P, b, hstairsNew,
    Set.subset_union_left, Set.subset_union_left, Set.subset_union_left, ?_⟩
  constructor
  · intro z hz
    rcases hz with (hzA | hzB) | hzC
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr (Or.inl hzB))
    · exact Or.inr (Or.inl hzC)
  · intro hsub
    have hrnew : r ∈ (A ∪ {r}) ∪ (B ∪ {v}) ∪ (C ∪ D) :=
      Or.inl (Or.inl (Or.inr rfl))
    exact hQ.2.2.1.1 (hsub hrnew)

end Workspace.ProofLemmas.Thm132AdjoinBanister
