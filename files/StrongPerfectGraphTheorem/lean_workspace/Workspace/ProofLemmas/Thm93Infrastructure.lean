import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Knots

/-!
# Shared proposition names for the proof of 9.3

The conclusion of 9.3 and the output of 5.8 are both long disjunctions.  This module only
gives those propositions short names.  The definitions unfold to the frozen statements.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm93Infrastructure

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*}

/-- The four alternatives in the frozen statement of 9.3. -/
abbrev Conclusion (G : SimpleGraph V)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) (K F : Set V) : Prop :=
    (∃ f ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet f ∩ K)) ∨
    (∃ (a : V) (P P' : List V),
      ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
        (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₁})
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∃ w ∈ ({v : V | v ∈ P} \ {a} : Set V), G.Adj r₂ w) ∧
        Anticomplete G ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P} \ {a})) ∨
    (∃ (a b : V) (P P' : List V),
      ((a, b, P, P') = (a₁, b₁, P₁, P₂) ∨ (a, b, P, P') = (b₁, a₁, P₁, P₂) ∨
        (a, b, P, P') = (a₂, b₂, P₂, P₁) ∨ (a, b, P, P') = (b₂, a₂, P₂, P₁)) ∧
      ∃ (R : List V) (r₁ r₂ : V),
        IsPathFrom G R r₁ r₂ ∧ (∀ v ∈ R, v ∈ F) ∧ Odd (pathLength R) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₁ w ↔ G.Adj a w)) ∧
        (∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (G.Adj r₂ w ↔ G.Adj b w)) ∧
        Anticomplete G {v : V | v ∈ SPGT.interior R}
          ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∀ u ∈ R, ∀ w ∈ P, G.Adj u w → ((u = r₁ ∧ w = a) ∨ (u = r₂ ∧ w = b)))) ∨
    (∃ (x y : V) (Q' : List V),
      ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
        (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)) ∧
      ∃ f ∈ F,
        (∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
          (G.Adj f w ↔ G.Adj x w)) ∧
        (∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w))

/-- The conclusion of 5.8, named so the two uses in 9.3 share one interface. -/
abbrev FiveEightOutcome {n : ℕ} (G : SimpleGraph V) (H : SimpleGraph (Fin n))
    (K : Set V) (phi : H.lineGraph ≃g G.induce K) (N : Fin n → Set V) (F : Set V) : Prop :=
    ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧ (∀ x ∈ P, x ∈ F) ∧
      ((∃ c₁ c₂ : Fin n,
          (¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
          (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
          (∀ x ∈ P, ∀ y ∈ K, G.Adj x y → (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
       (∃ (d₁ d₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V),
          d₁ ∈ branchVertices H ∧ d₂ ∈ branchVertices H ∧
          IsBranch H q ∧ IsTrackFrom H q d₁ d₂ ∧
          IsPathList G R ∧
          {x : V | x ∈ R} =
            {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
              e ∈ trackEdges q ∧ x = (↑(phi ⟨e, he⟩) : V)} ∧
          N d₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N d₂ ∩ {x : V | x ∈ R} = {r₂} ∧
          (((∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧
            (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
           ((∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂}) ∨
              (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
            (Even (pathLength P) ↔ Even (pathLength R))) ∨
           (p₁ = p₂ ∧ (∀ x ∈ (N d₁ ∪ N d₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
            (∀ y ∈ K, G.Adj p₁ y → y ∈ N d₁ ∪ N d₂ ∪ {z : V | z ∈ R}) ∧
            Even (pathLength R)) ∨
           (r₁ = r₂ ∧ (∀ x ∈ N d₁ \ {r₁}, G.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, G.Adj p₂ x) ∧
            (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
              (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂})) ∧
            Even (pathLength P)))))

/-- The part of `AppearanceFromKnot` used by 9.3 after `n`, `H`, and `phi` are chosen. -/
abbrev KnotAppearanceDictionary {n : ℕ} (G : SimpleGraph V) (H : SimpleGraph (Fin n))
    (K : Set V) (phi : H.lineGraph ≃g G.induce K)
    (P₁ P₂ : List V)
    (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V) : Prop :=
    (∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)}) ∧
    [c₁, c₂, c₃, c₄].Nodup ∧
    H.Adj c₁ c₂ ∧ H.Adj c₂ c₃ ∧ H.Adj c₃ c₄ ∧ H.Adj c₄ c₁ ∧
    branchVertices H = ({c₁, c₂, c₃, c₄} : Set (Fin n)) ∧
    (∃ he : s(c₁, c₂) ∈ H.edgeSet, (↑(phi ⟨s(c₁, c₂), he⟩) : V) = x₁) ∧
    (∃ he : s(c₂, c₃) ∈ H.edgeSet, (↑(phi ⟨s(c₂, c₃), he⟩) : V) = y₂) ∧
    (∃ he : s(c₃, c₄) ∈ H.edgeSet, (↑(phi ⟨s(c₃, c₄), he⟩) : V) = y₁) ∧
    (∃ he : s(c₄, c₁) ∈ H.edgeSet, (↑(phi ⟨s(c₄, c₁), he⟩) : V) = x₂) ∧
    N c₁ = ({x₁, x₂, a₁} : Set V) ∧ N c₂ = ({x₁, y₂, a₂} : Set V) ∧
    N c₃ = ({y₁, y₂, b₁} : Set V) ∧ N c₄ = ({y₁, x₂, b₂} : Set V) ∧
    (∃ q : List (Fin n), IsBranch H q ∧ IsTrackFrom H q c₁ c₃ ∧
      {v : V | v ∈ P₁} =
        {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
          e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)}) ∧
    (∃ q : List (Fin n), IsBranch H q ∧ IsTrackFrom H q c₂ c₄ ∧
      {v : V | v ∈ P₂} =
        {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
          e ∈ trackEdges q ∧ v = (↑(phi ⟨e, he⟩) : V)})

/-- The complete appearance package used in both lanes of 9.3. -/
abbrev KnotAppearanceData (G : SimpleGraph V)
    (P₁ P₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V) (K : Set V) : Prop :=
    ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g G.induce K),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧ DegenerateK4Appearance H ∧
      ∃ (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V),
        KnotAppearanceDictionary G H K phi P₁ P₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ c₁ c₂ c₃ c₄ N

end Workspace.ProofLemmas.Thm93Infrastructure
