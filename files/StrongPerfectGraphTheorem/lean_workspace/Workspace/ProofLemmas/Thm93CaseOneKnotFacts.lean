import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.ProofLemmas.KnotLabels
import Workspace.ProofLemmas.PathBasics

/-!
# The six neighbourhoods used in case (1) of 9.3

PAPER (9.3, printed p. 48): *"For assume `Q₁, Q₂` have length 1."*

When both antipaths are single edges the knot is completely explicit, and the eight sets that
case (1) of the proof needs — the neighbours of each of `a₁, b₁, a₂, b₂` in the three other
lists, and the neighbours of each of `x₁, y₁, x₂, y₂` in the three other lists — can be read
off from the definition of a knot.  Those eight computations are collected here so that the
branch dictionary in `Thm93CaseOneClassify` is pure bookkeeping.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93CaseOneKnotFacts

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-- All the data of case (1) of 9.3: a knot with named ends whose two antipaths are edges. -/
structure Setup (G : SimpleGraph V) (P₁ P₂ Q₁ Q₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) : Prop where
  knot : IsKnot G P₁ P₂ Q₁ Q₂
  hP₁ : IsPathFrom G P₁ a₁ b₁
  hP₂ : IsPathFrom G P₂ a₂ b₂
  hQ₁ : IsAntipathFrom G Q₁ x₁ y₁
  hQ₂ : IsAntipathFrom G Q₂ x₂ y₂
  hlen₁ : pathLength Q₁ = 1
  hlen₂ : pathLength Q₂ = 1

namespace Setup

variable {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V} {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V}

/-- `Q₁` is the two-element list `[x₁, y₁]`. -/
theorem q₁_eq (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : Q₁ = [x₁, y₁] :=
  KnotLabels.anti_eq_pair_of_length_one h.hQ₁ h.hlen₁

/-- `Q₂` is the two-element list `[x₂, y₂]`. -/
theorem q₂_eq (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : Q₂ = [x₂, y₂] :=
  KnotLabels.anti_eq_pair_of_length_one h.hQ₂ h.hlen₂

theorem q₁_set (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {v : V | v ∈ Q₁} = ({x₁, y₁} : Set V) := by rw [h.q₁_eq]; ext v; simp

theorem q₂_set (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {v : V | v ∈ Q₂} = ({x₂, y₂} : Set V) := by rw [h.q₂_eq]; ext v; simp

theorem a₁_ne_b₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : a₁ ≠ b₁ := by
  obtain ⟨-, -, -, -, -, -, h1, -⟩ := KnotLabels.knot_labels h.knot h.hP₁ h.hP₂ h.hQ₁ h.hQ₂
  exact PathBasics.isPathFrom_ends_ne h.hP₁ h1

theorem a₂_ne_b₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : a₂ ≠ b₂ := by
  obtain ⟨-, -, -, -, -, -, -, h2, -⟩ := KnotLabels.knot_labels h.knot h.hP₁ h.hP₂ h.hQ₁ h.hQ₂
  exact PathBasics.isPathFrom_ends_ne h.hP₂ h2

theorem x₁_ne_y₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : x₁ ≠ y₁ :=
  PathBasics.isPathFrom_ends_ne (G := Gᶜ) h.hQ₁ (by rw [h.hlen₁])

theorem x₂_ne_y₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : x₂ ≠ y₂ :=
  PathBasics.isPathFrom_ends_ne (G := Gᶜ) h.hQ₂ (by rw [h.hlen₂])

theorem a₁_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : a₁ ∈ P₁ :=
  (PathBasics.isPathFrom_ends_mem h.hP₁).1
theorem b₁_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : b₁ ∈ P₁ :=
  (PathBasics.isPathFrom_ends_mem h.hP₁).2
theorem a₂_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : a₂ ∈ P₂ :=
  (PathBasics.isPathFrom_ends_mem h.hP₂).1
theorem b₂_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : b₂ ∈ P₂ :=
  (PathBasics.isPathFrom_ends_mem h.hP₂).2
theorem x₁_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : x₁ ∈ Q₁ := by
  rw [h.q₁_eq]; simp
theorem y₁_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : y₁ ∈ Q₁ := by
  rw [h.q₁_eq]; simp
theorem x₂_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : x₂ ∈ Q₂ := by
  rw [h.q₂_eq]; simp
theorem y₂_mem (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) : y₂ ∈ Q₂ := by
  rw [h.q₂_eq]; simp


/-- The eight clauses of the definition of a knot, with the given end labels. -/
theorem dict (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    Anticomplete G {v : V | v ∈ P₁} {v : V | v ∈ P₂} ∧
    Complete G {v : V | v ∈ Q₁} {v : V | v ∈ Q₂} ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₁) ∨ (u = b₁ ∧ w = y₁)))) ∧
    (∀ u ∈ P₁, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₁ ∧ w = x₂) ∨ (u = b₁ ∧ w = y₂)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₁, y₁} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = x₁) ∨ (u = b₂ ∧ w = y₁)))) ∧
    (∀ u ∈ P₂, ∀ w ∈ ({x₂, y₂} : Set V),
      (G.Adj u w ↔ ((u = a₂ ∧ w = y₂) ∨ (u = b₂ ∧ w = x₂)))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, anti, comp, e11, e12, e21, e22, -⟩ :=
    KnotLabels.knot_labels h.knot h.hP₁ h.hP₂ h.hQ₁ h.hQ₂
  exact ⟨anti, comp, e11, e12, e21, e22⟩

/-- The lists of the knot are pairwise disjoint. -/
theorem disj (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    (∀ v ∈ P₁, v ∉ P₂) ∧ (∀ v ∈ P₁, v ∉ Q₁) ∧ (∀ v ∈ P₁, v ∉ Q₂) ∧
    (∀ v ∈ P₂, v ∉ Q₁) ∧ (∀ v ∈ P₂, v ∉ Q₂) ∧ (∀ v ∈ Q₁, v ∉ Q₂) := by
  obtain ⟨d1, d2, d3, d4, d5, d6, -⟩ :=
    KnotLabels.knot_labels h.knot h.hP₁ h.hP₂ h.hQ₁ h.hQ₂
  exact ⟨d1, d2, d3, d4, d5, d6⟩

/-- Vertices on the paths are different from vertices on the antipaths. -/
theorem ne_p_q (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) {u w : V}
    (hu : u ∈ P₁ ∨ u ∈ P₂) (hw : w ∈ Q₁ ∨ w ∈ Q₂) : u ≠ w := by
  obtain ⟨-, d2, d3, d4, d5, -⟩ := h.disj
  rintro rfl
  rcases hu with hu | hu <;> rcases hw with hw | hw
  exacts [d2 u hu hw, d3 u hu hw, d4 u hu hw, d5 u hu hw]

/-- A vertex of `P₁` is not a vertex of `P₂`. -/
theorem ne_p₁_p₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) {u w : V}
    (hu : u ∈ P₁) (hw : w ∈ P₂) : u ≠ w := by
  obtain ⟨d1, -⟩ := h.disj
  rintro rfl; exact d1 u hu hw

/-- A vertex of `Q₁` is not a vertex of `Q₂`. -/
theorem ne_q₁_q₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) {u w : V}
    (hu : u ∈ Q₁) (hw : w ∈ Q₂) : u ≠ w := by
  obtain ⟨-, -, -, -, -, d6⟩ := h.disj
  rintro rfl; exact d6 u hu hw

/-! ### The four path-end neighbourhoods -/

/-- The neighbours of `a₁` in the rest of the knot are `x₁` and `x₂`. -/
theorem nbrs_a₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj a₁ w}
      = ({x₁, x₂} : Set V) := by
  obtain ⟨anti, -, e11, e12, -, -⟩ := h.dict
  have hab := h.a₁_ne_b₁
  have hxy₁ := h.x₁_ne_y₁
  have hxy₂ := h.x₂_ne_y₂
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set, h.q₂_set] at hw
    show w = x₁ ∨ w = x₂
    rcases hw with (hw | hw) | hw
    · exact absurd hadj (anti a₁ h.a₁_mem w hw)
    · rcases hw with rfl | rfl
      · exact Or.inl rfl
      · rcases (e11 a₁ h.a₁_mem w (by simp)).mp hadj with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact absurd hc.symm hxy₁
        · exact absurd hc hab
    · rcases hw with rfl | rfl
      · exact Or.inr rfl
      · rcases (e12 a₁ h.a₁_mem w (by simp)).mp hadj with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact absurd hc.symm hxy₂
        · exact absurd hc hab
  · intro hw
    rcases hw with rfl | rfl
    · refine ⟨?_, (e11 a₁ h.a₁_mem w (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      exact Or.inl (Or.inr (by rw [h.q₁_set]; exact Or.inl rfl))
    · refine ⟨?_, (e12 a₁ h.a₁_mem w (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      exact Or.inr (by rw [h.q₂_set]; exact Or.inl rfl)

/-- The neighbours of `b₁` in the rest of the knot are `y₁` and `y₂`. -/
theorem nbrs_b₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj b₁ w}
      = ({y₁, y₂} : Set V) := by
  obtain ⟨anti, -, e11, e12, -, -⟩ := h.dict
  have hab := h.a₁_ne_b₁
  have hxy₁ := h.x₁_ne_y₁
  have hxy₂ := h.x₂_ne_y₂
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set, h.q₂_set] at hw
    show w = y₁ ∨ w = y₂
    rcases hw with (hw | hw) | hw
    · exact absurd hadj (anti b₁ h.b₁_mem w hw)
    · rcases hw with rfl | rfl
      · rcases (e11 b₁ h.b₁_mem w (by simp)).mp hadj with ⟨hc, -⟩ | ⟨-, hc⟩
        · exact absurd hc.symm hab
        · exact absurd hc hxy₁
      · exact Or.inl rfl
    · rcases hw with rfl | rfl
      · rcases (e12 b₁ h.b₁_mem w (by simp)).mp hadj with ⟨hc, -⟩ | ⟨-, hc⟩
        · exact absurd hc.symm hab
        · exact absurd hc hxy₂
      · exact Or.inr rfl
  · intro hw
    rcases hw with rfl | rfl
    · refine ⟨?_, (e11 b₁ h.b₁_mem w (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      exact Or.inl (Or.inr (by rw [h.q₁_set]; exact Or.inr rfl))
    · refine ⟨?_, (e12 b₁ h.b₁_mem w (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      exact Or.inr (by rw [h.q₂_set]; exact Or.inr rfl)

/-- The neighbours of `a₂` in the rest of the knot are `x₁` and `y₂`. -/
theorem nbrs_a₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj a₂ w}
      = ({x₁, y₂} : Set V) := by
  obtain ⟨anti, -, -, -, e21, e22⟩ := h.dict
  have hab := h.a₂_ne_b₂
  have hxy₁ := h.x₁_ne_y₁
  have hxy₂ := h.x₂_ne_y₂
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set, h.q₂_set] at hw
    show w = x₁ ∨ w = y₂
    rcases hw with (hw | hw) | hw
    · exact absurd hadj.symm (anti w hw a₂ h.a₂_mem)
    · rcases hw with rfl | rfl
      · exact Or.inl rfl
      · rcases (e21 a₂ h.a₂_mem w (by simp)).mp hadj with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact absurd hc.symm hxy₁
        · exact absurd hc hab
    · rcases hw with rfl | rfl
      · rcases (e22 a₂ h.a₂_mem w (by simp)).mp hadj with ⟨-, hc⟩ | ⟨hc, -⟩
        · exact absurd hc hxy₂
        · exact absurd hc hab
      · exact Or.inr rfl
  · intro hw
    rcases hw with rfl | rfl
    · refine ⟨?_, (e21 a₂ h.a₂_mem w (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      exact Or.inl (Or.inr (by rw [h.q₁_set]; exact Or.inl rfl))
    · refine ⟨?_, (e22 a₂ h.a₂_mem w (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      exact Or.inr (by rw [h.q₂_set]; exact Or.inr rfl)

/-- The neighbours of `b₂` in the rest of the knot are `y₁` and `x₂`. -/
theorem nbrs_b₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj b₂ w}
      = ({y₁, x₂} : Set V) := by
  obtain ⟨anti, -, -, -, e21, e22⟩ := h.dict
  have hab := h.a₂_ne_b₂
  have hxy₁ := h.x₁_ne_y₁
  have hxy₂ := h.x₂_ne_y₂
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set, h.q₂_set] at hw
    show w = y₁ ∨ w = x₂
    rcases hw with (hw | hw) | hw
    · exact absurd hadj.symm (anti w hw b₂ h.b₂_mem)
    · rcases hw with rfl | rfl
      · rcases (e21 b₂ h.b₂_mem w (by simp)).mp hadj with ⟨hc, -⟩ | ⟨-, hc⟩
        · exact absurd hc.symm hab
        · exact absurd hc hxy₁
      · exact Or.inl rfl
    · rcases hw with rfl | rfl
      · exact Or.inr rfl
      · rcases (e22 b₂ h.b₂_mem w (by simp)).mp hadj with ⟨hc, -⟩ | ⟨-, hc⟩
        · exact absurd hc.symm hab
        · exact absurd hc.symm hxy₂
  · intro hw
    rcases hw with rfl | rfl
    · refine ⟨?_, (e21 b₂ h.b₂_mem w (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      exact Or.inl (Or.inr (by rw [h.q₁_set]; exact Or.inr rfl))
    · refine ⟨?_, (e22 b₂ h.b₂_mem w (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)⟩
      exact Or.inr (by rw [h.q₂_set]; exact Or.inl rfl)

/-! ### The four antipath-end neighbourhoods -/

/-- The neighbours of `x₁` in `V(P₁) ∪ V(P₂) ∪ V(Q₂)`. -/
theorem nbrs_x₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj x₁ w}
      = ({a₁, a₂, x₂, y₂} : Set V) := by
  obtain ⟨-, comp, e11, -, e21, -⟩ := h.dict
  have hxy₁ := h.x₁_ne_y₁
  have hcx : ∀ u ∈ ({x₂, y₂} : Set V), G.Adj x₁ u := by
    intro u hu
    exact comp x₁ h.x₁_mem u (by rw [h.q₂_set]; exact hu)
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₂_set] at hw
    show w = a₁ ∨ w = a₂ ∨ w = x₂ ∨ w = y₂
    rcases hw with (hw | hw) | hw
    · rcases (e11 w hw x₁ (by simp)).mp hadj.symm with ⟨hc, -⟩ | ⟨-, hc⟩
      · exact Or.inl hc
      · exact absurd hc hxy₁
    · rcases (e21 w hw x₁ (by simp)).mp hadj.symm with ⟨hc, -⟩ | ⟨-, hc⟩
      · exact Or.inr (Or.inl hc)
      · exact absurd hc hxy₁
    · rcases hw with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨Or.inl (Or.inl h.a₁_mem),
        ((e11 w h.a₁_mem x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inl (Or.inr h.a₂_mem),
        ((e21 w h.a₂_mem x₁ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inr (by rw [h.q₂_set]; exact Or.inl rfl), hcx w (Or.inl rfl)⟩
    · exact ⟨Or.inr (by rw [h.q₂_set]; exact Or.inr rfl), hcx w (Or.inr rfl)⟩

/-- The neighbours of `y₁` in `V(P₁) ∪ V(P₂) ∪ V(Q₂)`. -/
theorem nbrs_y₁ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂}) : Set V) | G.Adj y₁ w}
      = ({b₁, b₂, x₂, y₂} : Set V) := by
  obtain ⟨-, comp, e11, -, e21, -⟩ := h.dict
  have hxy₁ := h.x₁_ne_y₁
  have hcy : ∀ u ∈ ({x₂, y₂} : Set V), G.Adj y₁ u := by
    intro u hu
    exact comp y₁ h.y₁_mem u (by rw [h.q₂_set]; exact hu)
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₂_set] at hw
    show w = b₁ ∨ w = b₂ ∨ w = x₂ ∨ w = y₂
    rcases hw with (hw | hw) | hw
    · rcases (e11 w hw y₁ (by simp)).mp hadj.symm with ⟨-, hc⟩ | ⟨hc, -⟩
      · exact absurd hc.symm hxy₁
      · exact Or.inl hc
    · rcases (e21 w hw y₁ (by simp)).mp hadj.symm with ⟨-, hc⟩ | ⟨hc, -⟩
      · exact absurd hc.symm hxy₁
      · exact Or.inr (Or.inl hc)
    · rcases hw with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨Or.inl (Or.inl h.b₁_mem),
        ((e11 w h.b₁_mem y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inl (Or.inr h.b₂_mem),
        ((e21 w h.b₂_mem y₁ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inr (by rw [h.q₂_set]; exact Or.inl rfl), hcy w (Or.inl rfl)⟩
    · exact ⟨Or.inr (by rw [h.q₂_set]; exact Or.inr rfl), hcy w (Or.inr rfl)⟩

/-- The neighbours of `x₂` in `V(P₁) ∪ V(P₂) ∪ V(Q₁)`. -/
theorem nbrs_x₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁}) : Set V) | G.Adj x₂ w}
      = ({a₁, b₂, x₁, y₁} : Set V) := by
  obtain ⟨-, comp, -, e12, -, e22⟩ := h.dict
  have hxy₂ := h.x₂_ne_y₂
  have hcx : ∀ u ∈ ({x₁, y₁} : Set V), G.Adj x₂ u := by
    intro u hu
    exact (comp u (by rw [h.q₁_set]; exact hu) x₂ h.x₂_mem).symm
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set] at hw
    show w = a₁ ∨ w = b₂ ∨ w = x₁ ∨ w = y₁
    rcases hw with (hw | hw) | hw
    · rcases (e12 w hw x₂ (by simp)).mp hadj.symm with ⟨hc, -⟩ | ⟨-, hc⟩
      · exact Or.inl hc
      · exact absurd hc hxy₂
    · rcases (e22 w hw x₂ (by simp)).mp hadj.symm with ⟨-, hc⟩ | ⟨hc, -⟩
      · exact absurd hc hxy₂
      · exact Or.inr (Or.inl hc)
    · rcases hw with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨Or.inl (Or.inl h.a₁_mem),
        ((e12 w h.a₁_mem x₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inl (Or.inr h.b₂_mem),
        ((e22 w h.b₂_mem x₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inr (by rw [h.q₁_set]; exact Or.inl rfl), hcx w (Or.inl rfl)⟩
    · exact ⟨Or.inr (by rw [h.q₁_set]; exact Or.inr rfl), hcx w (Or.inr rfl)⟩

/-- The neighbours of `y₂` in `V(P₁) ∪ V(P₂) ∪ V(Q₁)`. -/
theorem nbrs_y₂ (h : Setup G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂) :
    {w ∈ (({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁}) : Set V) | G.Adj y₂ w}
      = ({b₁, a₂, x₁, y₁} : Set V) := by
  obtain ⟨-, comp, -, e12, -, e22⟩ := h.dict
  have hxy₂ := h.x₂_ne_y₂
  have hcy : ∀ u ∈ ({x₁, y₁} : Set V), G.Adj y₂ u := by
    intro u hu
    exact (comp u (by rw [h.q₁_set]; exact hu) y₂ h.y₂_mem).symm
  ext w
  constructor
  · rintro ⟨hw, hadj⟩
    rw [h.q₁_set] at hw
    show w = b₁ ∨ w = a₂ ∨ w = x₁ ∨ w = y₁
    rcases hw with (hw | hw) | hw
    · rcases (e12 w hw y₂ (by simp)).mp hadj.symm with ⟨-, hc⟩ | ⟨hc, -⟩
      · exact absurd hc.symm hxy₂
      · exact Or.inl hc
    · rcases (e22 w hw y₂ (by simp)).mp hadj.symm with ⟨hc, -⟩ | ⟨-, hc⟩
      · exact Or.inr (Or.inl hc)
      · exact absurd hc.symm hxy₂
    · rcases hw with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
  · intro hw
    rcases hw with rfl | rfl | rfl | rfl
    · exact ⟨Or.inl (Or.inl h.b₁_mem),
        ((e12 w h.b₁_mem y₂ (by simp)).mpr (Or.inr ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inl (Or.inr h.a₂_mem),
        ((e22 w h.a₂_mem y₂ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)).symm⟩
    · exact ⟨Or.inr (by rw [h.q₁_set]; exact Or.inl rfl), hcy w (Or.inl rfl)⟩
    · exact ⟨Or.inr (by rw [h.q₁_set]; exact Or.inr rfl), hcy w (Or.inr rfl)⟩

end Setup

end Workspace.ProofLemmas.Thm93CaseOneKnotFacts
