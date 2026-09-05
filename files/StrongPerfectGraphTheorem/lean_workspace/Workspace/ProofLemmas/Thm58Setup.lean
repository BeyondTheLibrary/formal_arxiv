import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances

/-!
# Shared notation for the proof of 5.8

The conclusion of 5.8 is a long disjunction.  This file gives that disjunction a name so the
reduction to a minimal connected set and the remaining case analysis can be checked separately.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm58Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- The alternatives in the conclusion of 5.8, for a fixed path and its ends. -/
def Outcome {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (P : List V) (p₁ p₂ : V) : Prop :=
  (∃ c₁ c₂ : Fin n,
      (¬ ∃ q : List (Fin n), IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q) ∧
      (∀ x ∈ N c₁, G.Adj p₁ x) ∧ (∀ x ∈ N c₂, G.Adj p₂ x) ∧
      (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
        (x = p₁ ∧ y ∈ N c₁) ∨ (x = p₂ ∧ y ∈ N c₂))) ∨
  (∃ (b₁ b₂ : Fin n) (q : List (Fin n)) (R : List V) (r₁ r₂ : V),
      b₁ ∈ branchVertices H ∧ b₂ ∈ branchVertices H ∧
      IsBranch H q ∧ IsTrackFrom H q b₁ b₂ ∧
      IsPathList G R ∧
      {x : V | x ∈ R} =
        {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
          e ∈ trackEdges q ∧ x = (↑(φ ⟨e, he⟩) : V)} ∧
      N b₁ ∩ {x : V | x ∈ R} = {r₁} ∧ N b₂ ∩ {x : V | x ∈ R} = {r₂} ∧
      (((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∃ x ∈ {y : V | y ∈ R} \ {r₁}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨
          (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
       ((∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
          (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂}) ∨
          (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
        (Even (pathLength P) ↔ Even (pathLength R))) ∨
       (p₁ = p₂ ∧
        (∀ x ∈ (N b₁ ∪ N b₂) \ {r₁, r₂}, G.Adj p₁ x) ∧
        (∀ y ∈ K, G.Adj p₁ y → y ∈ N b₁ ∪ N b₂ ∪ {z : V | z ∈ R}) ∧
        Even (pathLength R)) ∨
       (r₁ = r₂ ∧
        (∀ x ∈ N b₁ \ {r₁}, G.Adj p₁ x) ∧
        (∀ x ∈ N b₂ \ {r₂}, G.Adj p₂ x) ∧
        (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
          (x = p₁ ∧ y ∈ N b₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N b₂ \ {r₂})) ∧
        Even (pathLength P))))

/-- The complete conclusion of 5.8. -/
def Conclusion {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V) (F : Set V) : Prop :=
  ∃ (P : List V) (p₁ p₂ : V), IsPathFrom G P p₁ p₂ ∧
    (∀ x ∈ P, x ∈ F) ∧ Outcome G n H K φ N P p₁ p₂

/-- The common hypotheses at the start of claims (2)--(7) in the proof of 5.8. -/
def Ready {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (N : Fin n → Set V)
    (F : Set V) (P : List V) (p₁ p₂ : V) : Prop :=
  Berge G ∧ IsKConnected J 3 ∧ IsBipartiteSubdivision J H ∧
  (∀ c : Fin n, N c =
    {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
      e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)}) ∧
  F ⊆ Kᶜ ∧
  (¬ LocalForLineGraph H
    {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
      (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K}) ∧
  IsPathFrom G P p₁ p₂ ∧ {x : V | x ∈ P} = F ∧ 2 ≤ F.ncard

end Workspace.ProofLemmas.Thm58Setup
