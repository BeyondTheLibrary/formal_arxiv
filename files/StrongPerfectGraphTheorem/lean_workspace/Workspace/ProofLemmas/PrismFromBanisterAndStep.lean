import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics

/-!
# The prism formed by a banister together with a step

Sections 11 and 12 apply the prism results of §§7 and 10 to a staircase without ever spelling
out which prism they mean.  The prism is always the same one: the two rungs `a₁`-`R₁`-`b₁`,
`a₂`-`R₂`-`b₂` of a step, together with the banister `a₀`-`R₀`-`b₀` as a third rung.

Why the three paths form a prism, in the paper's own terms:

* the two triangles are `{a₁, a₂, a₀}` and `{b₁, b₂, b₀}`.  `a₁a₂` and `b₁b₂` are edges by the
  definition of a step; `a₀` is a *left-star*, hence complete to `A ∋ a₁, a₂`, and `b₀` is a
  *right-star*, hence complete to `B ∋ b₁, b₂`;
* the only edges between `V(R₁)` and `V(R₂)` are `a₁a₂` and `b₁b₂` — this is the second bullet
  of the definition of a step;
* the only edges between `V(Rᵢ)` (`i = 1, 2`) and `V(R₀)` are `aᵢa₀` and `bᵢb₀`.  Every vertex
  of `Rᵢ` lies in `V(S) = A ∪ B ∪ C`; the interior of the banister is anticomplete to `V(S)`;
  the left-star `a₀` is anticomplete to `B ∪ C`, so its only neighbour on `Rᵢ` is `aᵢ`; and the
  right-star `b₀` is anticomplete to `A ∪ C`, so its only neighbour on `Rᵢ` is `bᵢ`.

Nothing here is a numbered result of the paper — it is the construction the authors leave
implicit whenever they write *"by 10.4"* or *"by 10.3"* inside §§11–12.

The vertex indices follow `PrismBasics.formPrism_of_data`: the triangle vertices are supplied
as `![a₁, a₂, a₀]` and `![b₁, b₂, b₀]`, so the banister is the *third* rung `R₃` of the prism —
which is exactly the rôle 10.4 gives it (*"none [of the attachments] are in `V(R₃)`"*).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.PrismFromBanisterAndStep

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- **The prism formed by a banister and a step.**

If `a₀`-`R₀`-`b₀` is a banister for the strip `S = (A, C, B)` and `a₁`-`R₁`-`b₁`,
`a₂`-`R₂`-`b₂` is a step of `S`, then `R₁, R₂, R₀` form a prism with triangles
`{a₁, a₂, a₀}` and `{b₁, b₂, b₀}`. -/
theorem formPrism_of_banister_and_step {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hban : IsBanister G A C B a₀ R₀ b₀)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ := by
  obtain ⟨hR₀, -, hls, hrs, hac⟩ := hban
  obtain ⟨ha₀S, ha₀A, ha₀BC⟩ := hls
  obtain ⟨hb₀S, hb₀B, hb₀AC⟩ := hrs
  obtain ⟨hr1, hr2, -, hedge⟩ := hstep
  -- every vertex of a rung lies in `V(S) = A ∪ B ∪ C`
  have memS : ∀ {a b : V} {R : List V}, IsRungOfStrip G A C B a R b →
      ∀ u ∈ R, u ∈ A ∪ B ∪ C := by
    intro a b R hrung u hu
    by_cases h1 : u = a
    · exact Or.inl (Or.inl (h1 ▸ hrung.2.1))
    · by_cases h2 : u = b
      · exact Or.inl (Or.inr (h2 ▸ hrung.2.2.1))
      · exact Or.inr (hrung.2.2.2.2.2 u
          ((PathBasics.mem_interior_iff_of_pathFrom hrung.1).mpr ⟨hu, h1, h2⟩))
  -- the only edges between a rung and the banister are `a a₀` and `b b₀`
  have ecross : ∀ {a b : V} {R : List V}, IsRungOfStrip G A C B a R b →
      ∀ u ∈ R, ∀ w ∈ R₀, (G.Adj u w ↔ (u = a ∧ w = a₀) ∨ (u = b ∧ w = b₀)) := by
    intro a b R hrung u hu w hw
    have huS : u ∈ A ∪ B ∪ C := memS hrung u hu
    constructor
    · intro hadj
      by_cases hwa : w = a₀
      · subst hwa
        refine Or.inl ⟨?_, rfl⟩
        have huA : u ∈ A := by
          rcases huS with (h | h) | h
          · exact h
          · exact absurd hadj.symm (ha₀BC u (Or.inl h))
          · exact absurd hadj.symm (ha₀BC u (Or.inr h))
        exact hrung.2.2.2.1 u hu huA
      · by_cases hwb : w = b₀
        · subst hwb
          refine Or.inr ⟨?_, rfl⟩
          have huB : u ∈ B := by
            rcases huS with (h | h) | h
            · exact absurd hadj.symm (hb₀AC u (Or.inl h))
            · exact h
            · exact absurd hadj.symm (hb₀AC u (Or.inr h))
          exact hrung.2.2.2.2.1 u hu huB
        · exfalso
          exact hac w ((PathBasics.mem_interior_iff_of_pathFrom hR₀).mpr ⟨hw, hwa, hwb⟩)
            u huS hadj.symm
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · subst h1; subst h2; exact (ha₀A _ hrung.2.1).symm
      · subst h1; subst h2; exact (hb₀B _ hrung.2.2.1).symm
  have ha₁R₁ : a₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hr1.1).1
  have hb₁R₁ : b₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hr1.1).2
  have ha₂R₂ : a₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hr2.1).1
  have hb₂R₂ : b₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hr2.1).2
  -- the two triangles
  have ha01 : G.Adj a₁ a₂ := (hedge a₁ ha₁R₁ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩)
  have hb01 : G.Adj b₁ b₂ := (hedge b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
  have ha02 : G.Adj a₁ a₀ := (ha₀A a₁ hr1.2.1).symm
  have ha12 : G.Adj a₂ a₀ := (ha₀A a₂ hr2.2.1).symm
  have hb02 : G.Adj b₁ b₀ := (hb₀B b₁ hr1.2.2.1).symm
  have hb12 : G.Adj b₂ b₀ := (hb₀B b₂ hr2.2.2.1).symm
  -- the nine disequalities between the two triangles
  have hAB : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := by
    rintro x hx y hy rfl
    exact ha₀BC x (Or.inl hy) (ha₀A x hx)
  have h00 : a₁ ≠ b₁ := hAB a₁ hr1.2.1 b₁ hr1.2.2.1
  have h01 : a₁ ≠ b₂ := hAB a₁ hr1.2.1 b₂ hr2.2.2.1
  have h10 : a₂ ≠ b₁ := hAB a₂ hr2.2.1 b₁ hr1.2.2.1
  have h11 : a₂ ≠ b₂ := hAB a₂ hr2.2.1 b₂ hr2.2.2.1
  have h02 : a₁ ≠ b₀ := by rintro rfl; exact hb₀S (Or.inl (Or.inl hr1.2.1))
  have h12 : a₂ ≠ b₀ := by rintro rfl; exact hb₀S (Or.inl (Or.inl hr2.2.1))
  have h20 : a₀ ≠ b₁ := by rintro rfl; exact ha₀S (Or.inl (Or.inr hr1.2.2.1))
  have h21 : a₀ ≠ b₂ := by rintro rfl; exact ha₀S (Or.inl (Or.inr hr2.2.2.1))
  have h22 : a₀ ≠ b₀ := by
    rintro rfl
    exact hb₀AC a₁ (Or.inl hr1.2.1) (ha₀A a₁ hr1.2.1)
  exact PrismBasics.formPrism_of_data ha01 ha02 ha12 hb01 hb02 hb12
    h00 h01 h02 h10 h11 h12 h20 h21 h22 hr1.1 hr2.1 hR₀ hedge
    (ecross hr1) (ecross hr2)

end Workspace.ProofLemmas.PrismFromBanisterAndStep
