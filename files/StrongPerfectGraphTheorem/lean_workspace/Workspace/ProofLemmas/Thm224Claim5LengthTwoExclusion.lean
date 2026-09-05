import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.AntiholeCompletion

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm224Claim5LengthTwoExclusion

open Workspace.Types.Core.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

theorem thm224Claim5LengthTwoExclusion
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u Rp : List V} {Y A₀ : Set V} {z y r : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hqY : ¬ VertexComplete G (x (t + 1)) Y)
    (hRp : IsPathFrom G Rp (x (t + 1)) r)
    (hRsub : ∀ v ∈ Rp, v ≠ x (t + 1) → v ∈ wheelSystemA G z A₀ x t)
    (hr : VertexComplete G r Y)
    (hRnc : ∀ v ∈ Rp, v ≠ r → ¬ VertexComplete G v Y) :
    pathLength Rp ≠ 2 := by
  classical
  intro hlen
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨-, -, -, -, -, hzA, hAnoX, -, -, hXanti, -, -, hqX, hqYy,
    hqXnc, hzXq, hzYy, hXY, hyX, hAY, hpath, -, -, -⟩ := hcons
  have hBerge : Berge G := hG.1.1.1.1.1
  have hRpLen : Rp.length = 3 := by
    rw [pathLength] at hlen
    omega
  obtain ⟨q, a, s, hRpeq⟩ := List.length_eq_three.mp hRpLen
  subst Rp
  have hq : q = x (t + 1) := by simpa using hRp.2.1
  have hs : s = r := by simpa using hRp.2.2
  subst q
  subst s
  have hqa : G.Adj (x (t + 1)) a := by
    simpa using (PathBasics.path_adj_succ hRp.1 (i := 0) (by simp))
  have har : G.Adj a r := by
    simpa using (PathBasics.path_adj_succ hRp.1 (i := 1) (by simp))
  have hqr : ¬ G.Adj (x (t + 1)) r := by
    simpa using (PathBasics.path_not_adj_of_gap hRp.1 (i := 0) (j := 2)
      (by simp) (by simp) (by omega) (by omega))
  have hqrne : x (t + 1) ≠ r := by
    simpa using (PathBasics.path_ne_of_ne_index hRp.1 (i := 0) (j := 2)
      (by simp) (by simp) (by omega))
  have haA : a ∈ wheelSystemA G z A₀ x t :=
    hRsub a (by simp) hqa.ne.symm
  have hrA : r ∈ wheelSystemA G z A₀ x t :=
    hRsub r (by simp) hqrne.symm
  have hzy : G.Adj z y := by
    simpa using (PathBasics.path_adj_succ hpath (i := 0) (by simp))
  have hza : z ≠ a := by
    intro h
    have hno : ¬ G.Adj y z := by simpa [h] using (hcon a (Or.inl haA))
    exact hno hzy.symm
  have hzrne : z ≠ r := by
    intro h
    have hno : ¬ G.Adj y z := by simpa [h] using (hcon r (Or.inl hrA))
    exact hno hzy.symm
  have hzr : ¬ G.Adj z r := hzA r hrA
  have haz : ¬ G.Adj a z := fun h => hzA a haA h.symm
  have hzq : G.Adj z (x (t + 1)) := hzXq _ (Or.inr rfl)
  have hqz : G.Adj (x (t + 1)) z := hzq.symm
  have hqnotY : x (t + 1) ∉ Y := fun h => hqYy (Or.inl h)
  have hanotY : a ∉ Y := fun h => (Set.disjoint_left.mp hAY haA h)
  have hznY : z ∉ Y := fun h => G.irrefl (hzYy z (Or.inl h))
  have hrnY : r ∉ Y := fun h => G.irrefl (hr r h)
  have hYanti : AnticonnectedSet G Y :=
    KiteTailBasics.wheel_hub_anticonnected (KiteTailBasics.tail_isWheel hT)
  have haNotY : ¬ VertexComplete G a Y := hRnc a (by simp) har.ne
  have hqMissY : ∃ w ∈ Y, ¬ G.Adj (x (t + 1)) w := by
    by_contra h
    apply hqY
    intro w hw
    by_contra hqw
    exact h ⟨w, hw, hqw⟩
  have haMissY : ∃ w ∈ Y, ¬ G.Adj a w := by
    by_contra h
    apply haNotY
    intro w hw
    by_contra haw
    exact h ⟨w, hw, haw⟩
  obtain ⟨LY, hLY, hLYint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hYanti hqnotY hanotY hqMissY haMissY
  have hZR : IsPathFrom Gᶜ [z, r] z r :=
    ⟨PathBasics.isPathList_pair ((G.compl_adj z r).mpr ⟨hzrne, hzr⟩), by simp, by simp⟩
  have hznotLY : z ∉ LY := by
    intro hzLY
    exact hznY (hLYint z ((PathBasics.mem_interior_iff_of_pathFrom hLY).mpr
      ⟨hzLY, hzq.ne, hza⟩))
  have hrnotLY : r ∉ LY := by
    intro hrLY
    exact hrnY (hLYint r ((PathBasics.mem_interior_iff_of_pathFrom hLY).mpr
      ⟨hrLY, hqrne.symm, har.ne.symm⟩))
  have hdisj : ∀ w ∈ LY, w ∉ [z, r] := by
    intro w hw hwr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hwr
    rcases hwr with h | h
    · subst w
      exact hznotLY hw
    · subst w
      exact hrnotLY hw
  have hcross : ∀ w ∈ LY, ∀ v ∈ [z, r],
      (Gᶜ.Adj w v ↔
        (w = a ∧ v = z) ∨ (w = x (t + 1) ∧ v = r)) := by
    intro w hw v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with hv | hv
    · subst v
      constructor
      · intro hwz
        by_cases hwa : w = a
        · exact Or.inl ⟨hwa, rfl⟩
        by_cases hwq : w = x (t + 1)
        · subst w
          exact (((G.compl_adj _ _).mp hwz).2 hqz).elim
        · have hwY : w ∈ Y := hLYint w
            ((PathBasics.mem_interior_iff_of_pathFrom hLY).mpr ⟨hw, hwq, hwa⟩)
          exact (((G.compl_adj _ _).mp hwz).2 (hzYy w (Or.inl hwY)).symm).elim
      · rintro (⟨hwa, -⟩ | ⟨-, hzr⟩)
        · subst w
          exact (G.compl_adj a z).mpr ⟨hza.symm, haz⟩
        · exact (hzrne hzr).elim
    · subst v
      constructor
      · intro hwr
        by_cases hwa : w = a
        · subst w
          exact (((G.compl_adj _ _).mp hwr).2 har).elim
        by_cases hwq : w = x (t + 1)
        · exact Or.inr ⟨hwq, rfl⟩
        · have hwY : w ∈ Y := hLYint w
            ((PathBasics.mem_interior_iff_of_pathFrom hLY).mpr ⟨hw, hwq, hwa⟩)
          exact (((G.compl_adj _ _).mp hwr).2 (hr w hwY).symm).elim
      · rintro (⟨-, hrz⟩ | ⟨hwq, -⟩)
        · exact (hzrne hrz.symm).elim
        · subst w
          exact (G.compl_adj (x (t + 1)) r).mpr ⟨hqrne, hqr⟩
  have hLY3 : 3 ≤ LY.length :=
    AntiholeCompletion.three_le_length_of_antipath hLY hqa
  have hhole : IsHoleList Gᶜ (LY ++ [z, r]) :=
    PathGlue.glue_hole hLY hZR hdisj hcross (by simp only [List.length_cons, List.length_nil]; omega)
  have hLYeven : Even (holeLength (LY ++ [z, r])) := hBerge.2 _ hhole
  have hLYodd : Odd (pathLength LY) := by
    have hmod := Nat.even_iff.mp hLYeven
    simp only [holeLength, List.length_append, List.length_cons, List.length_nil] at hmod
    rw [Nat.odd_iff]
    simp only [pathLength]
    omega
  have hanotX : a ∉ wheelSystemX x t := by
    intro haX
    exact (hzA a haA) (hzXq a (Or.inl haX))
  have haNotX : ¬ VertexComplete G a (wheelSystemX x t) := hAnoX a haA
  have hqMissX : ∃ w ∈ wheelSystemX x t, ¬ G.Adj (x (t + 1)) w := by
    by_contra h
    apply hqXnc
    intro w hw
    by_contra hqw
    exact h ⟨w, hw, hqw⟩
  have haMissX : ∃ w ∈ wheelSystemX x t, ¬ G.Adj a w := by
    by_contra h
    apply haNotX
    intro w hw
    by_contra haw
    exact h ⟨w, hw, haw⟩
  obtain ⟨LX, hLX, hLXint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hXanti hqX hanotX hqMissX haMissX
  have hXYdis : Disjoint (wheelSystemX x t) Y := by
    rw [Set.disjoint_left]
    intro w hwX hwY
    exact G.irrefl (hXY w hwX w hwY)
  have hsumEven : Even (pathLength LY + pathLength LX) :=
    AntiholeCompletion.even_add_pathLength_of_two_antipaths hBerge hXYdis hXY hqa
      hqX hanotX hqnotY hanotY hLY hLYint hLX hLXint
  have hLXodd : Odd (pathLength LX) := by
    have hsum := Nat.even_iff.mp hsumEven
    have hly := Nat.odd_iff.mp hLYodd
    rw [Nat.odd_iff]
    omega
  have hyq : ¬ G.Adj y (x (t + 1)) := hcon _ (Or.inr rfl)
  have hya : ¬ G.Adj y a := hcon _ (Or.inl haA)
  have hyqne : y ≠ x (t + 1) := by
    intro h
    apply hqYy
    exact Or.inr h.symm
  have hyane : y ≠ a := by
    intro h
    apply haNotX
    simpa [h] using hyX
  have hLXeven : Even (pathLength LX) :=
    AntiholeCompletion.even_pathLength_of_witness hBerge hqa hyX hyq hya hyqne hyane hLX hLXint
  have heven := Nat.even_iff.mp hLXeven
  have hodd := Nat.odd_iff.mp hLXodd
  omega

end Workspace.ProofLemmas.Thm224Claim5LengthTwoExclusion
