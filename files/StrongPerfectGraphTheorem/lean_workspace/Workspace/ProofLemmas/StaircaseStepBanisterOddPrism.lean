import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S07.Thm_7_2

set_option autoImplicit false

namespace Workspace.ProofLemmas.StaircaseStepBanisterOddPrism

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

private theorem rung_mem_strip_2
    {V : Type*} {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) :
    ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (by rw [hwa]; exact h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (by rw [hwb]; exact h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr
        ⟨hw, hwa, hwb⟩))

private theorem banister_rung_edges_2
    {V : Type*} {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ a b : V}
    {R₀ R : List V} (hban : IsBanister G A C B a₀ R₀ b₀)
    (hr : IsRungOfStrip G A C B a R b) :
    ∀ u ∈ R₀, ∀ w ∈ R,
      (G.Adj u w ↔ (u = a₀ ∧ w = a) ∨ (u = b₀ ∧ w = b)) := by
  obtain ⟨hR₀path, _, hLS, hRS, hR₀int⟩ := hban
  intro u hu w hw
  constructor
  · intro hadj
    have hwS : w ∈ A ∪ B ∪ C := rung_mem_strip_2 hr w hw
    by_cases hua : u = a₀
    · subst u
      refine Or.inl ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact hr.2.2.2.1 w hw hwA
      · exact absurd hadj (hLS.2.2 w (Or.inl hwB))
      · exact absurd hadj (hLS.2.2 w (Or.inr hwC))
    by_cases hub : u = b₀
    · subst u
      refine Or.inr ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact absurd hadj (hRS.2.2 w (Or.inl hwA))
      · exact hr.2.2.2.2.1 w hw hwB
      · exact absurd hadj (hRS.2.2 w (Or.inr hwC))
    · exact absurd hadj (hR₀int u
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
          ⟨hu, hua, hub⟩) w hwS)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hLS.2.1 w hr.2.1
    · exact hRS.2.1 w hr.2.2.1

/-- A staircase banister and either step of its strip present an odd prism
whenever the Berge graph has no even prism. -/
theorem staircaseStepBanisterOddPrism
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V)
    (a₀ b₀ a₁ b₁ a₂ b₂ : V) (R₀ R₁ R₂ : List V)
    (hStaircase : IsStaircase G A C B a₀ R₀ b₀)
    (hStep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hBerge : Berge G)
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃) :
    FormPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ ∧
      Odd (pathLength R₀) ∧ Odd (pathLength R₁) ∧ Odd (pathLength R₂) := by
  obtain ⟨hSC, hban, _⟩ := hStaircase
  obtain ⟨⟨hdAB, _, _⟩, _, _, _, _⟩ := hSC
  have hban' := hban
  obtain ⟨hR₀path, _, hLS, hRS, _⟩ := hban'
  obtain ⟨hr₁, hr₂, _, hcross12⟩ := hStep
  have ha₁A : a₁ ∈ A := hr₁.2.1
  have hb₁B : b₁ ∈ B := hr₁.2.2.1
  have ha₂A : a₂ ∈ A := hr₂.2.1
  have hb₂B : b₂ ∈ B := hr₂.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).1
  have hb₁R₁ : b₁ ∈ R₁ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).2
  have ha₂R₂ : a₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1
  have hb₂R₂ : b₂ ∈ R₂ :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2
  have hAdj_a0a1 : G.Adj a₀ a₁ := hLS.2.1 a₁ ha₁A
  have hAdj_a0a2 : G.Adj a₀ a₂ := hLS.2.1 a₂ ha₂A
  have hAdj_a1a2 : G.Adj a₁ a₂ :=
    (hcross12 a₁ ha₁R₁ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩)
  have hAdj_b0b1 : G.Adj b₀ b₁ := hRS.2.1 b₁ hb₁B
  have hAdj_b0b2 : G.Adj b₀ b₂ := hRS.2.1 b₂ hb₂B
  have hAdj_b1b2 : G.Adj b₁ b₂ :=
    (hcross12 b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
  have hne_a0b0 : a₀ ≠ b₀ := by
    intro hc
    exact hRS.2.2 a₁ (Or.inl ha₁A) (by rw [← hc]; exact hAdj_a0a1)
  have hne_a0b1 : a₀ ≠ b₁ := by
    intro hc
    exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₁B))
  have hne_a0b2 : a₀ ≠ b₂ := by
    intro hc
    exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₂B))
  have hne_a1b0 : a₁ ≠ b₀ := by
    intro hc
    exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₁A))
  have hne_a2b0 : a₂ ≠ b₀ := by
    intro hc
    exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₂A))
  have hne_a1b1 : a₁ ≠ b₁ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a1b2 : a₁ ≠ b₂ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₂B; exact hb₂B)
  have hne_a2b1 : a₂ ≠ b₁ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a2b2 : a₂ ≠ b₂ := by
    intro hc
    exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₂B; exact hb₂B)
  have hcross01 : ∀ u ∈ R₀, ∀ w ∈ R₁,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₁) ∨ (u = b₀ ∧ w = b₁)) :=
    banister_rung_edges_2 hban hr₁
  have hcross02 : ∀ u ∈ R₀, ∀ w ∈ R₂,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₂) ∨ (u = b₀ ∧ w = b₂)) :=
    banister_rung_edges_2 hban hr₂
  have hprism : FormPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ :=
    Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      hAdj_a0a1 hAdj_a0a2 hAdj_a1a2 hAdj_b0b1 hAdj_b0b2 hAdj_b1b2
      hne_a0b0 hne_a0b1 hne_a0b2 hne_a1b0 hne_a1b1 hne_a1b2
      hne_a2b0 hne_a2b1 hne_a2b2 hR₀path hr₁.1 hr₂.1 hcross01 hcross02 hcross12
  have hpar := Workspace.Statements.S07.SPGT.thm_7_2 G hBerge
    ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ hprism
  have hnotEven0 : ¬ Even (pathLength R₀) := by
    intro he0
    have he1 : Even (pathLength R₁) := hpar.1.mp he0
    have he2 : Even (pathLength R₂) := hpar.2.mp he0
    exact hNoEvenPrism ⟨![a₀, a₁, a₂], ![b₀, b₁, b₂], R₀, R₁, R₂,
      hprism, he0, he1, he2⟩
  have hodd0 : Odd (pathLength R₀) := Nat.not_even_iff_odd.mp hnotEven0
  have hodd1 : Odd (pathLength R₁) := Nat.not_even_iff_odd.mp (fun he1 =>
    hnotEven0 (hpar.1.mpr he1))
  have hodd2 : Odd (pathLength R₂) := Nat.not_even_iff_odd.mp (fun he2 =>
    hnotEven0 (hpar.2.mpr he2))
  exact ⟨hprism, hodd0, hodd1, hodd2⟩

end Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
