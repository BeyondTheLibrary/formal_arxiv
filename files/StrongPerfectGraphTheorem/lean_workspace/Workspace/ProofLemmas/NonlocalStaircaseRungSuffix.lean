import Workspace.ProofLemmas.NonlocalStaircaseAdjoinLeft
import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry

set_option autoImplicit false

/-! # Joining the outside path to the missed rung in 12.2

Choose the last neighbour of the outside path's last end on the missed rung.
The suffix starting there avoids the missed rung's first end. Joining the
outside path to this suffix gives a new rung containing every added vertex.
-/

namespace Workspace.ProofLemmas.NonlocalStaircaseRungSuffix

open Workspace.Types.Core.SPGT Workspace.Types.Staircases.SPGT
open NonlocalStaircaseSelectedStep

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (12.2): "If `j > 0` then in the first case we can add `p₁` to
`A` and `V(P \ p₁)` to `C`, contrary to the maximality of the staircase."
Here the missed rung is `R₁`. The other rung is `R₂`. The path followed by
the last attached suffix of `R₁` forms a new step with `R₂`. -/
theorem left_case
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    {q : List V} {p₁ p₂ : V} (hq : IsPathFrom G q p₁ p₂)
    (hqout : ∀ x ∈ q, x ∉ staircaseVertices A C B R₀)
    (hpa₀ : G.Adj p₁ a₀) (hpa₂ : G.Adj p₁ a₂)
    (hattach : ∃ y ∈ R₁, y ≠ a₁ ∧ G.Adj p₂ y)
    (honly : ∀ x ∈ q, ∀ z ∈
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
      z ≠ a₁ → G.Adj x z →
        (x = p₁ ∧ (z = a₀ ∨ z = a₂)) ∨ (x = p₂ ∧ z ∈ R₁)) : False := by
  classical
  have hban := hMax.1.2.1
  have hpq := PathBasics.head_mem hq.2.1
  have hpout : p₁ ∉ A ∪ B ∪ C := fun hp => hqout p₁ hpq (Or.inr hp)
  have hqstrip : ∀ x ∈ q, x ∉ A ∪ B ∪ C := fun x hx h => hqout x hx (Or.inr h)
  have ha₀R := PathBasics.head_mem hban.1.2.1
  have ha₁R := PathBasics.head_mem hstep.1.1.2.1
  have ha₂R := PathBasics.head_mem hstep.2.1.1.2.1
  have hb₁R := PathBasics.getLast_mem hstep.1.1.2.2
  have hb₂R := PathBasics.getLast_mem hstep.2.1.1.2.2
  have ha₀not₁ : a₀ ∉ R₁ := fun hm =>
    hban.2.1 a₀ ha₀R (rung_mem_strip hstep.1 a₀ hm)
  have ha₀not₂ : a₀ ∉ R₂ := fun hm =>
    hban.2.1 a₀ ha₀R (rung_mem_strip hstep.2.1 a₀ hm)
  have ha₂not₁ : a₂ ∉ R₁ := fun hm => hstep.2.2.1 a₂ hm ha₂R
  have ha₁not₂ : a₁ ∉ R₂ := hstep.2.2.1 a₁ ha₁R
  have hcross₀ : ∀ x ∈ q, ∀ z ∈ R₀, (G.Adj x z ↔ x = p₁ ∧ z = a₀) := by
    intro x hx z hz
    have hzne : z ≠ a₁ := by
      intro he
      exact hban.2.1 z hz (he ▸ rung_mem_strip hstep.1 z (he ▸ ha₁R))
    constructor
    · intro hadj
      rcases honly x hx z (Or.inr hz) hzne hadj with ⟨he, hzA⟩ | ⟨_, hz₁⟩
      · rcases hzA with hz₀ | hz₂
        · exact ⟨he, hz₀⟩
        · exact (hban.2.1 z hz (hz₂ ▸ rung_mem_strip hstep.2.1 z (hz₂ ▸ ha₂R))).elim
      · exact (hban.2.1 z hz (rung_mem_strip hstep.1 z hz₁)).elim
    · rintro ⟨hx', hz'⟩
      simpa only [hx', hz'] using hpa₀
  have hcross₂ : ∀ x ∈ q, ∀ z ∈ R₂, (G.Adj x z ↔ x = p₁ ∧ z = a₂) := by
    intro x hx z hz
    constructor
    · intro hadj
      have hzne : z ≠ a₁ := fun he => ha₁not₂ (he ▸ hz)
      rcases honly x hx z (Or.inl (Or.inr hz)) hzne hadj with ⟨he, hzA⟩ | ⟨_, hz₁⟩
      · rcases hzA with hz₀ | hz₂
        · exact (ha₀not₂ (hz₀ ▸ hz)).elim
        · exact ⟨he, hz₂⟩
      · exact (hstep.2.2.1 z hz₁ hz).elim
    · rintro ⟨hx', hz'⟩
      simpa only [hx', hz'] using hpa₂
  obtain ⟨y, hyR, hya, hp₂y⟩ := hattach
  obtain ⟨k, hk, hSuf, hp₂k, hSufSub, hlast, haSuf, hmax⟩ :=
    Thm101ClaimOne.last_attach hstep.1.1 ⟨y, hyR, hp₂y⟩
  have haNotSuf : a₁ ∉ R₁.drop k := by
    intro ha
    have hfirst := PathBasics.getElem_zero_of_head? hstep.1.1.2.1
      (PathBasics.path_length_pos hstep.1.1.1)
    have hkzero : k = 0 := hstep.1.1.1.2.1.getElem_inj_iff.mp
      ((haSuf.mp ha).trans hfirst.symm)
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hyR
    have hjle := hmax j hj (hjy ▸ hp₂y)
    have hjzero : j = 0 := by omega
    have hsame : R₁[j]'hj = R₁[0]'(PathBasics.path_length_pos hstep.1.1.1) := by
      congr 1
    exact hya (hjy.symm.trans (hsame.trans hfirst))
  have hSufNe : ∀ z ∈ R₁.drop k, z ≠ a₁ := fun z hz he => haNotSuf (he ▸ hz)
  have hqSuf : ∀ x ∈ q, ∀ z ∈ R₁.drop k,
      (G.Adj x z ↔ x = p₂ ∧ z = R₁[k]'hk) := by
    intro x hx z hz
    have hzR := hSufSub z hz
    constructor
    · intro hadj
      rcases honly x hx z (Or.inl (Or.inl hzR)) (hSufNe z hz) hadj with
        ⟨_, hzA⟩ | ⟨hxp, _⟩
      · rcases hzA with he | he
        · exact (ha₀not₁ (he ▸ hzR)).elim
        · exact (ha₂not₁ (he ▸ hzR)).elim
      · exact ⟨hxp, hlast z hz (hxp ▸ hadj)⟩
    · rintro ⟨hx', hz'⟩
      simpa only [hx', hz'] using hp₂k
  have hT : IsPathFrom G (q ++ R₁.drop k) p₁ b₁ := PathGlue.glue_path hq hSuf
    (fun x hx hm => hqstrip x hx (rung_mem_strip hstep.1 x (hSufSub x hm))) hqSuf
  let D : Set V := {x | x ∈ q ∧ x ≠ p₁}
  have hnewrung : IsRungOfStrip G (A ∪ {p₁}) (C ∪ D) B p₁ (q ++ R₁.drop k) b₁ := by
    refine ⟨hT, Or.inr rfl, hstep.1.2.2.1, ?_, ?_, ?_⟩
    · intro z hz hzA
      rcases hzA with hzA | he
      · rcases List.mem_append.mp hz with hzq | hzS
        · exact (hqstrip z hzq (Or.inl (Or.inl hzA))).elim
        · exact (hSufNe z hzS (hstep.1.2.2.2.1 z (hSufSub z hzS) hzA)).elim
      · exact he
    · intro z hz hzB
      rcases List.mem_append.mp hz with hzq | hzS
      · exact (hqstrip z hzq (Or.inl (Or.inr hzB))).elim
      · exact hstep.1.2.2.2.2.1 z (hSufSub z hzS) hzB
    · intro z hz
      have hd := (PathBasics.mem_interior_iff_of_pathFrom hT).1 hz
      rcases List.mem_append.mp hd.1 with hzq | hzS
      · exact Or.inr ⟨hzq, hd.2.1⟩
      · exact Or.inl (hstep.1.2.2.2.2.2 z
          ((PathBasics.mem_interior_iff_of_pathFrom hstep.1.1).2
            ⟨hSufSub z hzS, hSufNe z hzS, hd.2.2⟩))
  have hnewstep : IsStep G (A ∪ {p₁}) (C ∪ D) B
      p₁ (q ++ R₁.drop k) b₁ a₂ R₂ b₂ := by
    refine ⟨hnewrung, NonlocalStaircaseAdjoinLeft.rung_up hpout hstep.2.1, ?_, ?_⟩
    · intro z hz hz₂
      rcases List.mem_append.mp hz with hzq | hzS
      · exact hqstrip z hzq (rung_mem_strip hstep.2.1 z hz₂)
      · exact hstep.2.2.1 z (hSufSub z hzS) hz₂
    · intro x hx z hz
      constructor
      · intro hadj
        rcases List.mem_append.mp hx with hxq | hxS
        · exact Or.inl ((hcross₂ x hxq z hz).1 hadj)
        · rcases (hstep.2.2.2 x (hSufSub x hxS) z hz).1 hadj with h | h
          · exact (hSufNe x hxS h.1).elim
          · exact Or.inr h
      · rintro (⟨hx', hz'⟩ | ⟨hx', hz'⟩)
        · simpa only [hx', hz'] using hpa₂
        · have hbb := (hstep.2.2.2 b₁ hb₁R b₂ hb₂R).2 (Or.inr ⟨rfl, rfl⟩)
          simpa only [hx', hz'] using hbb
  have hSnew := NonlocalStaircaseAdjoinLeft.stepConnected_adjoin_left hMax.1.1 p₁ D
    hpout (fun z hz => hqstrip z hz.1) (fun h => h.2 rfl)
    b₁ a₂ b₂ (q ++ R₁.drop k) R₂ hstep.2.1.2.1 hnewstep
    (fun z hz => List.mem_append_left _ hz.1)
  exact NonlocalStaircaseAdjoinLeft.contradicts_maximality hMax hpq hqout hSnew hcross₀

/-- PAPER (12.2): "in the second case we do the same with `A` and `B`
exchanged." Reverse both rungs and the banister, and use `left_case`. -/
theorem right_case
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    (hMax : MaximalStaircase G A C B a₀ R₀ b₀)
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    {q : List V} {p₁ p₂ : V} (hq : IsPathFrom G q p₁ p₂)
    (hqout : ∀ x ∈ q, x ∉ staircaseVertices A C B R₀)
    (hpb₀ : G.Adj p₁ b₀) (hpb₂ : G.Adj p₁ b₂)
    (hattach : ∃ y ∈ R₁, y ≠ b₁ ∧ G.Adj p₂ y)
    (honly : ∀ x ∈ q, ∀ z ∈
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}),
      z ≠ b₁ → G.Adj x z →
        (x = p₁ ∧ (z = b₀ ∨ z = b₂)) ∨ (x = p₂ ∧ z ∈ R₁)) : False := by
  have rung_rev : ∀ {a b : V} {R : List V}, IsRungOfStrip G A C B a R b →
      IsRungOfStrip G B C A b R.reverse a := by
    intro a b R h
    exact ⟨PathBasics.isPathFrom_reverse h.1, h.2.2.1, h.2.1,
      fun z hz => h.2.2.2.2.1 z (List.mem_reverse.mp hz),
      fun z hz => h.2.2.2.1 z (List.mem_reverse.mp hz),
      fun z hz => h.2.2.2.2.2 z (PathBasics.mem_interior_reverse.mp hz)⟩
  have hrev : IsStep G B C A b₁ R₁.reverse a₁ b₂ R₂.reverse a₂ := by
    refine ⟨rung_rev hstep.1, rung_rev hstep.2.1, ?_, ?_⟩
    · simpa only [List.mem_reverse] using hstep.2.2.1
    · intro x hx z hz
      exact (hstep.2.2.2 x (List.mem_reverse.mp hx) z (List.mem_reverse.mp hz)).trans or_comm
  have hsets : staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ := by
    ext z
    simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
    tauto
  apply left_case (StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hMax) hrev hq
    (by simpa only [hsets] using hqout) hpb₀ hpb₂
  · simpa only [List.mem_reverse] using hattach
  · simpa only [List.mem_reverse] using honly

end Workspace.ProofLemmas.NonlocalStaircaseRungSuffix
