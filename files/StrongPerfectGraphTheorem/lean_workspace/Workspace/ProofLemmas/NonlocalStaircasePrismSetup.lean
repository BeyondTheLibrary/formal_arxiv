import Mathlib
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.NonlocalStaircaseSelectedStep
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The prism used in the last paragraph of 12.2

The chosen step and the staircase banister form a prism.  This file records
the two facts used before applying 10.1: the original minimal set has nonlocal
attachments to that prism, and a vertex major for this prism is already major
for the staircase.
-/

namespace Workspace.ProofLemmas.NonlocalStaircasePrismSetup

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*}

private theorem adj_one_other_of_saturated
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x y z : V}
    (hsat : 2 ≤ (({x, y, z} : Set V) ∩ G.neighborSet v).ncard) :
    G.Adj v x ∨ G.Adj v y := by
  classical
  have hcard : 1 < (({x, y, z} : Set V) ∩ G.neighborSet v).ncard := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (Set.one_lt_ncard (Set.toFinite (({x, y, z} : Set V) ∩ G.neighborSet v))).mp hcard
  have hpT : p = x ∨ p = y ∨ p = z := by simpa using hp.1
  have hqT : q = x ∨ q = y ∨ q = z := by simpa using hq.1
  have hpA : G.Adj v p := hp.2
  have hqA : G.Adj v q := hq.2
  by_contra h
  push Not at h
  have hpz : p = z := by
    rcases hpT with rfl | rfl | rfl
    · exact (h.1 hpA).elim
    · exact (h.2 hpA).elim
    · rfl
  have hqz : q = z := by
    rcases hqT with rfl | rfl | rfl
    · exact (h.1 hqA).elim
    · exact (h.2 hqA).elim
    · rfl
  exact hpq (hpz.trans hqz.symm)

private theorem adj_other_two_of_saturated
    [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {v x y z : V}
    (hsat : 2 ≤ (({x, y, z} : Set V) ∩ G.neighborSet v).ncard)
    (hvz : ¬ G.Adj v z) :
    G.Adj v x ∧ G.Adj v y := by
  classical
  have hcard : 1 < (({x, y, z} : Set V) ∩ G.neighborSet v).ncard := by omega
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (Set.one_lt_ncard (Set.toFinite (({x, y, z} : Set V) ∩ G.neighborSet v))).mp hcard
  have hpT : p = x ∨ p = y ∨ p = z := by simpa using hp.1
  have hqT : q = x ∨ q = y ∨ q = z := by simpa using hq.1
  have hpA : G.Adj v p := hp.2
  have hqA : G.Adj v q := hq.2
  constructor
  · by_contra hvx
    have hpy : p = y := by
      rcases hpT with rfl | rfl | rfl
      · exact (hvx hpA).elim
      · rfl
      · exact (hvz hpA).elim
    have hqy : q = y := by
      rcases hqT with rfl | rfl | rfl
      · exact (hvx hqA).elim
      · rfl
      · exact (hvz hqA).elim
    exact hpq (hpy.trans hqy.symm)
  · by_contra hvy
    have hpx : p = x := by
      rcases hpT with rfl | rfl | rfl
      · rfl
      · exact (hvy hpA).elim
      · exact (hvz hpA).elim
    have hqx : q = x := by
      rcases hqT with rfl | rfl | rfl
      · rfl
      · exact (hvy hqA).elim
      · exact (hvz hqA).elim
    exact hpq (hpx.trans hqx.symm)

/-- The two witnesses selected in the proof of 12.2 make the attachments to
the banister-and-step prism nonlocal. -/
theorem prism_nonlocal
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (F : Set V) (f₁ fk : V)
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hy : ∃ y ∈ R₁, y ≠ b₁ ∧ G.Adj f₁ y)
    (hf₁F : f₁ ∈ F)
    (hr : ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj fk r)
    (hfkF : fk ∈ F) :
    let Kp : Set V :=
      {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}
    F ⊆ Kpᶜ ∧
      ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀]
        R₁ R₂ R₀ (attachments G F Kp) := by
  classical
  dsimp only
  have hS := hK.1
  have hban := hK.2.1
  have hR₁S := NonlocalStaircaseSelectedStep.rung_mem_strip hstep.1
  have hR₂S := NonlocalStaircaseSelectedStep.rung_mem_strip hstep.2.1
  have hFprism : F ⊆
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀})ᶜ := by
    intro x hxF hxK
    rcases hxK with (hxR₁ | hxR₂) | hxR₀
    · exact hFoutside hxF (Or.inr (hR₁S x hxR₁))
    · exact hFoutside hxF (Or.inr (hR₂S x hxR₂))
    · exact hFoutside hxF (Or.inl hxR₀)
  refine ⟨hFprism, ?_⟩
  obtain ⟨y, hyR₁, hyb₁, hf₁y⟩ := hy
  obtain ⟨r, hrR₀, hra₀, hfkr⟩ := hr
  have hyatt : y ∈ attachments G F
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) :=
    ⟨Or.inl (Or.inl hyR₁), f₁, hf₁F, hf₁y.symm⟩
  have hratt : r ∈ attachments G F
      ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) :=
    ⟨Or.inr hrR₀, fk, hfkF, hfkr.symm⟩
  rintro (hloc | hloc | hloc | hloc | hloc)
  · exact hban.2.1 r hrR₀ (hR₁S r (hloc hratt))
  · exact hstep.2.2.1 y hyR₁ (hloc hyatt)
  · exact hban.2.1 y (hloc hyatt) (hR₁S y hyR₁)
  · have hh : r = a₁ ∨ r = a₂ ∨ r = a₀ := by simpa using hloc hratt
    rcases hh with hra₁ | hra₂ | hra₀'
    · exact hban.2.1 r hrR₀ (hra₁.symm ▸ Or.inl (Or.inl hstep.1.2.1))
    · exact hban.2.1 r hrR₀ (hra₂.symm ▸ Or.inl (Or.inl hstep.2.1.2.1))
    · exact hra₀ hra₀'
  · have hh : y = b₁ ∨ y = b₂ ∨ y = b₀ := by simpa using hloc hyatt
    rcases hh with hyb₁' | hyb₂ | hyb₀
    · exact hyb₁ hyb₁'
    · exact hstep.2.2.1 y hyR₁
        (hyb₂.symm ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2)
    · exact hban.2.1 y
        (hyb₀.symm ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)
        (hR₁S y hyR₁)

/-- PAPER (12.2, printed p. 72): *"Suppose that some vertex `v` in `F` is
major with respect to `K⁰`. Then we claim `v` is major with respect to `K`.
For it has a neighbour in `A` and in `B`, and if it has none in `R₀` then it
is adjacent to all of `a₁,a₂,b₁,b₂`, in which case
`v-a₁-a₀-R₀-b₀-b₂-v` is an odd hole."* -/
theorem major_for_prism_is_major_for_staircase
    [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hBerge : Berge G)
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hmaj : MajorForPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] v) :
    MajorForStaircase G A C B a₀ R₀ b₀ v := by
  classical
  have hban := hK.2.1
  have ha₁A := hstep.1.2.1
  have ha₂A := hstep.2.1.2.1
  have hb₁B := hstep.1.2.2.1
  have hb₂B := hstep.2.1.2.2.1
  have ha₀R := Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1
  have hb₀R := Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2
  have hsatA : 2 ≤ (({a₁, a₂, a₀} : Set V) ∩ G.neighborSet v).ncard := by
    simpa only [MajorForPrism, SaturatesPrism, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] using hmaj.1
  have hsatB : 2 ≤ (({b₁, b₂, b₀} : Set V) ∩ G.neighborSet v).ncard := by
    simpa only [MajorForPrism, SaturatesPrism, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] using hmaj.2
  by_cases hR : ∃ z ∈ R₀, G.Adj v z
  · rcases adj_one_other_of_saturated hsatA with hva₁ | hva₂
    · rcases adj_one_other_of_saturated hsatB with hvb₁ | hvb₂
      · exact ⟨hv, ⟨a₁, ha₁A, hva₁⟩, ⟨b₁, hb₁B, hvb₁⟩, hR⟩
      · exact ⟨hv, ⟨a₁, ha₁A, hva₁⟩, ⟨b₂, hb₂B, hvb₂⟩, hR⟩
    · rcases adj_one_other_of_saturated hsatB with hvb₁ | hvb₂
      · exact ⟨hv, ⟨a₂, ha₂A, hva₂⟩, ⟨b₁, hb₁B, hvb₁⟩, hR⟩
      · exact ⟨hv, ⟨a₂, ha₂A, hva₂⟩, ⟨b₂, hb₂B, hvb₂⟩, hR⟩
  · push Not at hR
    have ⟨hva₁, hva₂⟩ := adj_other_two_of_saturated hsatA (hR a₀ ha₀R)
    have ⟨hvb₁, hvb₂⟩ := adj_other_two_of_saturated hsatB (hR b₀ hb₀R)
    have hAB := hK.1.1.1
    have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
      intro hadj
      have ha₁R := Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1
      have hb₂R := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2
      rcases (hstep.2.2.2 a₁ ha₁R b₂ hb₂R).mp hadj with h | h
      · exact Set.disjoint_left.mp hAB ha₂A (h.2 ▸ hb₂B)
      · exact Set.disjoint_left.mp hAB ha₁A (h.1.symm ▸ hb₁B)
    have ha₁b₂ne : a₁ ≠ b₂ := fun e => Set.disjoint_left.mp hAB ha₁A (e ▸ hb₂B)
    have ha₁R₀ : a₁ ∉ R₀ := fun h => hban.2.1 a₁ h (Or.inl (Or.inl ha₁A))
    have hb₂R₀ : b₂ ∉ R₀ := fun h => hban.2.1 b₂ h (Or.inl (Or.inr hb₂B))
    have ha₁a₀ : G.Adj a₁ a₀ := (hban.2.2.1.2.1 a₁ ha₁A).symm
    have hb₂b₀ : G.Adj b₂ b₀ := (hban.2.2.2.1.2.1 b₂ hb₂B).symm
    have ha₁other : ∀ z ∈ R₀, z ≠ a₀ → ¬ G.Adj a₁ z := by
      intro z hz hza hadj
      by_cases hzb : z = b₀
      · subst z
        exact hban.2.2.2.1.2.2 a₁ (Or.inl ha₁A) hadj.symm
      · exact hban.2.2.2.2 z
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
            ⟨hz, hza, hzb⟩) a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
    have hb₂other : ∀ z ∈ R₀, z ≠ b₀ → ¬ G.Adj b₂ z := by
      intro z hz hzb hadj
      by_cases hza : z = a₀
      · subst z
        exact hban.2.2.1.2.2 b₂ (Or.inl hb₂B) hadj.symm
      · exact hban.2.2.2.2 z
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).2
            ⟨hz, hza, hzb⟩) b₂ (Or.inl (Or.inr hb₂B)) hadj.symm
    let P : List V := a₁ :: (R₀ ++ [b₂])
    have hP : IsPathFrom G P a₁ b₂ := by
      simpa [P] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hban.1
        ha₁a₀ hb₂b₀ ha₁b₂ ha₁b₂ne ha₁R₀ hb₂R₀ ha₁other hb₂other
    have hvP : v ∉ P := by
      intro hvp
      have hm : v = a₁ ∨ v ∈ R₀ ∨ v = b₂ := by
        simpa [P] using hvp
      rcases hm with rfl | hvR | rfl
      · exact hv (Or.inr (Or.inl (Or.inl ha₁A)))
      · exact hv (Or.inl hvR)
      · exact hv (Or.inr (Or.inl (Or.inr hb₂B)))
    have hPint : interior P = R₀ := by
      simp [P, Workspace.Types.Core.SPGT.interior]
    have hhole : IsHoleList G (v :: P) :=
      Workspace.ProofLemmas.PrismBasics.isHoleList_of_path_add_vertex hP
        (by
          rw [Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton]
          rw [Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hban.1.1]
          omega)
        hva₁ hvb₂ hvP (by
          intro z hz
          rw [hPint] at hz
          exact hR z hz)
    have heven := hBerge.1 (v :: P) hhole
    have hoddR₀ :=
      (Workspace.ProofLemmas.StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism
        G A C B a₀ b₀ a₁ b₁ a₂ b₂ R₀ R₁ R₂ hK hstep hBerge
          hNoEvenPrism).2.1
    have hoddHole : Odd (holeLength (v :: P)) := by
      rw [Workspace.ProofLemmas.PrismBasics.holeLength_cons v
        (Workspace.ProofLemmas.PathBasics.path_ne_nil hP.1)]
      rw [show pathLength P = R₀.length + 1 by
        simpa [P] using
          (Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton a₁ b₂ R₀)]
      rw [Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hban.1.1]
      simpa [Nat.add_assoc] using hoddR₀.add_even (by decide : Even 4)
    exact (Nat.not_even_iff_odd.mpr hoddHole heven).elim

end Workspace.ProofLemmas.NonlocalStaircasePrismSetup
