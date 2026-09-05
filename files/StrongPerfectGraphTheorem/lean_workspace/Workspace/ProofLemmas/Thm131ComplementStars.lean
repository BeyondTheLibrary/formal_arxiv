import Workspace.ProofLemmas.Thm132ComplementStaircase

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The complementary strip used in the last case of 13.1

When the middle class is empty, a nonadjacent left-star/right-star pair is an
edge in the complement.  That edge is a hub rung: every old step supplies a
cross nonedge, hence a second complementary rung forming a step with the hub.
-/

namespace Workspace.ProofLemmas.Thm131ComplementStars

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

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

/-- A rung of a strip with empty middle class consists only of its ends. -/
private theorem mem_rung_of_empty
    {G : SimpleGraph V} {A B : Set V} {a b z : V} {P : List V}
    (hP : IsRungOfStrip G A (∅ : Set V) B a P b) (hz : z ∈ P) :
    z = a ∨ z = b := by
  by_cases hza : z = a
  · exact Or.inl hza
  by_cases hzb : z = b
  · exact Or.inr hzb
  have hzint := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP.1).2
    ⟨hz, hza, hzb⟩
  exact absurd (hP.2.2.2.2.2 z hzint) (Set.notMem_empty z)

/-- If `r` and `b` are opposite stars and miss one another, adjoining them to
the two swapped end classes gives a step-connected strip in the complement. -/
theorem stepConnected_compl_adjoin_stars
    (G : SimpleGraph V) (A B : Set V) (r b : V)
    (hS : StepConnected G A (∅ : Set V) B)
    (hr : IsLeftStar G A (∅ : Set V) B r)
    (hb : IsRightStar G A (∅ : Set V) B b)
    (hrb : ¬ G.Adj r b) :
    StepConnected Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b}) := by
  classical
  have hAB : Disjoint A B := hS.1.1
  have hrA : r ∉ A := fun h => hr.1 (Or.inl (Or.inl h))
  have hrB : r ∉ B := fun h => hr.1 (Or.inl (Or.inr h))
  have hbA : b ∉ A := fun h => hb.1 (Or.inl (Or.inl h))
  have hbB : b ∉ B := fun h => hb.1 (Or.inl (Or.inr h))
  have hr_ne_b : r ≠ b := by
    obtain ⟨a, ha⟩ := hS.2.1.1
    intro he
    have hra := hr.2.1 a ha
    rw [he] at hra
    exact hb.2.2 a (Or.inl ha) hra
  have hrbc : Gᶜ.Adj r b := (G.compl_adj r b).2 ⟨hr_ne_b, hrb⟩
  have hhub : IsRungOfStrip Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b})
      r [r, b] b := by
    refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hrbc, rfl, by simp⟩,
      Or.inr rfl, Or.inr rfl, ?_, ?_, by
        simp [Workspace.Types.Core.SPGT.interior]⟩
    · intro z hz hzL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [Set.mem_union, Set.mem_singleton_iff] at hzL
      rcases hz with hzr | hzb
      · exact hzr
      · exfalso
        subst z
        rcases hzL with hbB' | hbr
        · exact absurd hbB' hbB
        · exact hr_ne_b.symm hbr
    · intro z hz hzR
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      simp only [Set.mem_union, Set.mem_singleton_iff] at hzR
      rcases hz with hzr | hzb
      · exfalso
        subst z
        rcases hzR with hrA' | hrb'
        · exact absurd hrA' hrA
        · exact hr_ne_b hrb'
      · exact hzb

  have mkSpoke : ∀ (a : V), a ∈ A → ∀ (c : V), c ∈ B → ¬ G.Adj a c →
      IsStep Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b})
        r [r, b] b c [c, a] a := by
    intro a ha c hc hac
    have hca : c ≠ a := fun he => Set.disjoint_left.mp hAB (he.symm ▸ ha) hc
    have hcaC : Gᶜ.Adj c a := (G.compl_adj c a).2
      ⟨hca, fun h => hac h.symm⟩
    have hspoke : IsRungOfStrip Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b})
        c [c, a] a := by
      refine ⟨⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hcaC, rfl, by simp⟩,
        Or.inl hc, Or.inl ha, ?_, ?_, by
          simp [Workspace.Types.Core.SPGT.interior]⟩
      · intro z hz hzL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        simp only [Set.mem_union, Set.mem_singleton_iff] at hzL
        rcases hz with hzc | hza
        · exact hzc
        · exfalso
          subst z
          rcases hzL with haB | har
          · exact absurd haB (Set.disjoint_left.mp hAB ha)
          · exact hrA (har.symm ▸ ha)
      · intro z hz hzR
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        simp only [Set.mem_union, Set.mem_singleton_iff] at hzR
        rcases hz with hzc | hza
        · exfalso
          subst z
          rcases hzR with hcA | hcb
          · exact absurd hcA (Set.disjoint_right.mp hAB hc)
          · exact hbB (hcb ▸ hc)
        · exact hza
    have hrc : Gᶜ.Adj r c := (G.compl_adj r c).2
      ⟨fun he => hrB (he ▸ hc), hr.2.2 c (Or.inl hc)⟩
    have hba : Gᶜ.Adj b a := (G.compl_adj b a).2
      ⟨fun he => hbA (he.symm ▸ ha), fun h => hb.2.2 a (Or.inl ha) h⟩
    refine ⟨hhub, hspoke, ?_, ?_⟩
    · intro z hz₁ hz₂
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz₁ hz₂
      rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl
      · exact hrB hc
      · exact hrA ha
      · exact hbB hc
      · exact hbA ha
    · intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with hur | hub
      · rcases hv with hvc | hva
        · subst u; subst v
          exact iff_of_true hrc (Or.inl ⟨rfl, rfl⟩)
        · subst u; subst v
          exact iff_of_false
            (fun h => h.2 (hr.2.1 a ha))
            (by rintro (⟨-, h⟩ | ⟨h, -⟩); exact hca h.symm; exact hr_ne_b h)
      · rcases hv with hvc | hva
        · subst u; subst v
          exact iff_of_false
            (fun h => h.2 (hb.2.1 c hc))
            (by rintro (⟨h, -⟩ | ⟨-, h⟩); exact hr_ne_b h.symm; exact hca h)
        · subst u; subst v
          exact iff_of_true hba (Or.inr ⟨rfl, rfl⟩)

  have spokeFor : ∀ z ∈ A ∪ B,
      ∃ (c d : V), IsStep Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b})
        r [r, b] b c [c, d] d ∧ (z = c ∨ z = d) := by
    intro z hz
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hs, hzR⟩ :=
      hS.2.2.2.1 z (by rcases hz with h | h; exact Or.inl (Or.inl h); exact Or.inl (Or.inr h))
    have ha₁A := hs.1.2.1
    have hb₁B := hs.1.2.2.1
    have ha₂A := hs.2.1.2.1
    have hb₂B := hs.2.1.2.2.1
    have ha₁R := Workspace.ProofLemmas.PathBasics.head_mem hs.1.1.2.1
    have hb₁R := Workspace.ProofLemmas.PathBasics.getLast_mem hs.1.1.2.2
    have ha₂R := Workspace.ProofLemmas.PathBasics.head_mem hs.2.1.1.2.1
    have hb₂R := Workspace.ProofLemmas.PathBasics.getLast_mem hs.2.1.1.2.2
    have hn12 : ¬ G.Adj a₁ b₂ := by
      intro hadj
      rcases (hs.2.2.2 a₁ ha₁R b₂ hb₂R).1 hadj with h | h
      · exact Set.disjoint_left.mp hAB ha₂A (h.2 ▸ hb₂B)
      · exact Set.disjoint_left.mp hAB ha₁A (h.1.symm ▸ hb₁B)
    have hn21 : ¬ G.Adj a₂ b₁ := by
      intro hadj
      rcases (hs.2.2.2 b₁ hb₁R a₂ ha₂R).1 hadj.symm with h | h
      · exact Set.disjoint_left.mp hAB ha₁A (h.1 ▸ hb₁B)
      · exact Set.disjoint_left.mp hAB ha₂A (h.2.symm ▸ hb₂B)
    rcases hzR with hzR | hzR
    · rcases mem_rung_of_empty hs.1 hzR with hza | hzb
      · exact ⟨b₂, a₁, mkSpoke a₁ ha₁A b₂ hb₂B hn12, Or.inr hza⟩
      · exact ⟨b₁, a₂, mkSpoke a₂ ha₂A b₁ hb₁B hn21, Or.inl hzb⟩
    · rcases mem_rung_of_empty hs.2.1 hzR with hza | hzb
      · exact ⟨b₁, a₂, mkSpoke a₂ ha₂A b₁ hb₁B hn21, Or.inr hza⟩
      · exact ⟨b₂, a₁, mkSpoke a₁ ha₁A b₂ hb₂B hn12, Or.inl hzb⟩

  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, Set.disjoint_empty _, Set.disjoint_empty _⟩
    exact Set.disjoint_left.mpr fun z hzL hzR => by
      rcases hzL with hzB | hzr <;> rcases hzR with hzA | hzb
      · exact Set.disjoint_left.mp hAB hzA hzB
      · exact hbB (hzb ▸ hzB)
      · exact hrA (hzr ▸ hzA)
      · exact hr_ne_b (hzr.symm.trans hzb)
  · exact ⟨⟨r, Or.inr rfl⟩, ⟨b, Or.inr rfl⟩⟩
  · intro z hz
    rcases hz with ((hzB | hzr) | (hzA | hzb)) | hz0
    · obtain ⟨c, d, hs, hzc⟩ := spokeFor z (Or.inr hzB)
      exact ⟨c, [c, d], d, hs.2.1, by simpa [hzc]⟩
    · subst z; exact ⟨r, [r, b], b, hhub, by simp⟩
    · obtain ⟨c, d, hs, hzc⟩ := spokeFor z (Or.inl hzA)
      exact ⟨c, [c, d], d, hs.2.1, by simpa [hzc]⟩
    · subst z; exact ⟨r, [r, b], b, hhub, by simp⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · intro z hz
    rcases hz with ((hzB | hzr) | (hzA | hzb)) | hz0
    · obtain ⟨c, d, hs, hzc⟩ := spokeFor z (Or.inr hzB)
      exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inr (by simpa [hzc])⟩
    · subst z; obtain ⟨a, ha⟩ := hS.2.1.1
      obtain ⟨c, d, hs, -⟩ := spokeFor a (Or.inl ha)
      exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inl (by simp)⟩
    · obtain ⟨c, d, hs, hzc⟩ := spokeFor z (Or.inl hzA)
      exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inr (by simpa [hzc])⟩
    · subst z; obtain ⟨a, ha⟩ := hS.2.1.1
      obtain ⟨c, d, hs, -⟩ := spokeFor a (Or.inl ha)
      exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inl (by simp)⟩
    · exact absurd hz0 (Set.notMem_empty z)
  · intro X Y hXY hXYdis hX hY
    rcases hXY with hXY | hXY
    · have hrXY : r ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases hrXY with hrX | hrY
      · obtain ⟨z, hzY⟩ := hY
        have hzOld : z ∈ B := by
          rcases (show z ∈ B ∪ {r} by rw [← hXY]; exact Or.inr hzY) with hzB | hzr
          · exact hzB
          · subst z; exact absurd hzY (Set.disjoint_left.mp hXYdis hrX)
        obtain ⟨c, d, hs, hzend⟩ := spokeFor z (Or.inr hzOld)
        exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inl hrX,
          hzend.elim (fun h => Or.inl (h.symm ▸ hzY)) (fun h => Or.inr (h.symm ▸ hzY))⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzOld : z ∈ B := by
          rcases (show z ∈ B ∪ {r} by rw [← hXY]; exact Or.inl hzX) with hzB | hzr
          · exact hzB
          · subst z; exact absurd hzX (Set.disjoint_right.mp hXYdis hrY)
        obtain ⟨c, d, hs, hzend⟩ := spokeFor z (Or.inr hzOld)
        exact ⟨c, [c, d], d, r, [r, b], b, step_symm hs,
          hzend.elim (fun h => Or.inl (h.symm ▸ hzX)) (fun h => Or.inr (h.symm ▸ hzX)),
          Or.inl hrY⟩
    · have hbXY : b ∈ X ∪ Y := by rw [hXY]; exact Or.inr rfl
      rcases hbXY with hbX | hbY
      · obtain ⟨z, hzY⟩ := hY
        have hzOld : z ∈ A := by
          rcases (show z ∈ A ∪ {b} by rw [← hXY]; exact Or.inr hzY) with hzA | hzb
          · exact hzA
          · subst z; exact absurd hzY (Set.disjoint_left.mp hXYdis hbX)
        obtain ⟨c, d, hs, hzend⟩ := spokeFor z (Or.inl hzOld)
        exact ⟨r, [r, b], b, c, [c, d], d, hs, Or.inr hbX,
          hzend.elim (fun h => Or.inl (h.symm ▸ hzY)) (fun h => Or.inr (h.symm ▸ hzY))⟩
      · obtain ⟨z, hzX⟩ := hX
        have hzOld : z ∈ A := by
          rcases (show z ∈ A ∪ {b} by rw [← hXY]; exact Or.inl hzX) with hzA | hzb
          · exact hzA
          · subst z; exact absurd hzX (Set.disjoint_right.mp hXYdis hbY)
        obtain ⟨c, d, hs, hzend⟩ := spokeFor z (Or.inl hzOld)
        exact ⟨c, [c, d], d, r, [r, b], b, step_symm hs,
          hzend.elim (fun h => Or.inl (h.symm ▸ hzX)) (fun h => Or.inr (h.symm ▸ hzX)),
          Or.inr hbY⟩

end Workspace.ProofLemmas.Thm131ComplementStars
