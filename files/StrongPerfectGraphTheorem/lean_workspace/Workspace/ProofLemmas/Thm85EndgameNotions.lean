import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm85RungChoice

/-!
# The proof-local notions in the endgame of 8.5

The paper introduces broad choices, traversals, and optimal choices only inside the proof of
8.5.  This file gives those notions names so that claims (4), (5), and (6) can be stated
separately.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EndgameNotions

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-- A choice of one rung for every unoriented edge.  The second conjunct says that changing
the orientation reverses the list. -/
def RungChoice {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (R : U → U → List V) : Prop :=
  (∀ u v : U, J.Adj u v → IsUVRung G J S N u v (R u v)) ∧
    ∀ u v : U, J.Adj u v → R v u = (R u v).reverse

/-- The paper's broad choice: two vertex-disjoint edges have selected rungs meeting `X`. -/
def BroadChoice {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (X : Set V)
    (R : U → U → List V) : Prop :=
  RungChoice G J S N R ∧
    ∃ i j h k : U, J.Adj i j ∧ J.Adj h k ∧ [i, j, h, k].Nodup ∧
      (∃ x ∈ X, x ∈ R i j) ∧ ∃ x ∈ X, x ∈ R h k

/-- `xy` is the unique edge of `G` between `A` and `B`. -/
def UniqueEdgeBetween {V : Type*} (G : SimpleGraph V) (A B : Set V) (x y : V) : Prop :=
  x ∈ A ∧ y ∈ B ∧ G.Adj x y ∧
    ∀ a ∈ A, ∀ b ∈ B, G.Adj a b → a = x ∧ b = y

/-- The three bullets in claim (4), with the orientation fixed by the path ends `f₁` and
`fn`.  Membership in `N i` identifies the endpoint called `r_iw` in the paper. -/
def IsTraversal {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (N : U → Set V) (F : Set V) (f₁ fn : V) (R : U → U → List V) (i j : U) : Prop :=
  J.Adj i j ∧
    (∀ w : U, w ≠ j → J.Adj i w →
      ∃ r : V, r ∈ R i w ∧ r ∈ N i ∧
        UniqueEdgeBetween G {x : V | x ∈ R i w} F r f₁) ∧
    (∀ w : U, w ≠ i → J.Adj j w →
      ∃ r : V, r ∈ R j w ∧ r ∈ N j ∧
        UniqueEdgeBetween G {x : V | x ∈ R j w} F r fn) ∧
    ∀ u v : U, J.Adj u v → [u, v, i, j].Nodup →
      Anticomplete G {x : V | x ∈ R u v} F

/-- A selected family has one and only one oriented traversal. -/
def HasUniqueTraversal {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (N : U → Set V) (F : Set V) (f₁ fn : V) (R : U → U → List V) : Prop :=
  ∃ i j : U, IsTraversal G J N F f₁ fn R i j ∧
    ∀ i' j' : U, IsTraversal G J N F f₁ fn R i' j' → i' = i ∧ j' = j

/-- Claim (6): two choices have different traversal edges. -/
def HasDifferentTraversals {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (F : Set V) (f₁ fn : V) : Prop :=
  ∃ R R' : U → U → List V, ∃ i j i' j' : U,
    RungChoice G J S N R ∧ RungChoice G J S N R' ∧
      IsTraversal G J N F f₁ fn R i j ∧ IsTraversal G J N F f₁ fn R' i' j' ∧
      s(i, j) ≠ s(i', j')

/-- The paper's optimal choice.  The edges in `K` are expressed without introducing a second
set: they are exactly the edges whose strips meet `X`. -/
def OptimalChoice {V U : Type*} (G : SimpleGraph V) (J : SimpleGraph U)
    (S : U → U → Set V) (N : U → Set V) (X : Set V)
    (R : U → U → List V) : Prop :=
  RungChoice G J S N R ∧
    ∀ u v : U, J.Adj u v → (X ∩ S u v).Nonempty → ∃ x ∈ X, x ∈ R u v

/-- Claim (3) supplies a broad choice by selecting, on every active strip, a rung through an
attachment in that strip. -/
theorem exists_broad_choice {V U : Type*} [Fintype U]
    {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
    (hSN : IsJStripSystem G J S N) (X : Set V)
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧
      [u, v, u', v'].Nodup ∧ (X ∩ S u v).Nonempty ∧ (X ∩ S u' v').Nonempty) :
    ∃ R : U → U → List V, BroadChoice G J S N X R := by
  classical
  obtain ⟨u, v, u', v', huv, hu'v', hdisjoint, huvX, hu'v'X⟩ := hclaim3
  obtain ⟨R, hR, hRsymm, hmeet⟩ :=
    Workspace.ProofLemmas.Thm85RungChoice.exists_rung_family_meeting hSN X
  refine ⟨R, ⟨⟨hR, hRsymm⟩, u, v, u', v', huv, hu'v', hdisjoint, ?_, ?_⟩⟩
  · exact hmeet u v huv huvX
  · exact hmeet u' v' hu'v' hu'v'X

end Workspace.ProofLemmas.Thm85EndgameNotions
