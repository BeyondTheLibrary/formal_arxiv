import Mathlib
import Workspace.Types.Core

set_option autoImplicit false

namespace Workspace.Types.Thm245MaximalAdmissibleSet

open Workspace.Types.Core.SPGT

theorem thm245MaximalAdmissibleSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (X Y : Set V) (p : List V) (p₁ z : V)
    (hX : AnticonnectedSet G X)
    (hXY : Disjoint X Y) (hcomp : Complete G X Y)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hzX : z ∉ X) (hzcomp : VertexComplete G z (X ∪ Y)) :
    ∃ S : Set V,
      AnticonnectedSet G S ∧
      Disjoint S Y ∧ Complete G S Y ∧
      (∀ w ∈ p, w ∉ S ∪ Y) ∧
      (∀ w ∈ p, (VertexComplete G w S ↔ w = p₁)) ∧
      z ∉ S ∧ VertexComplete G z (S ∪ Y) ∧
      ∀ T : Set V, S ⊆ T →
        AnticonnectedSet G T →
        Disjoint T Y → Complete G T Y →
        (∀ w ∈ p, w ∉ T ∪ Y) →
        (∀ w ∈ p, (VertexComplete G w T ↔ w = p₁)) →
        z ∉ T → VertexComplete G z (T ∪ Y) →
        T = S := by
  classical
  let admissible : Set (Set V) :=
    {S |
      AnticonnectedSet G S ∧
      Disjoint S Y ∧ Complete G S Y ∧
      (∀ w ∈ p, w ∉ S ∪ Y) ∧
      (∀ w ∈ p, (VertexComplete G w S ↔ w = p₁)) ∧
      z ∉ S ∧ VertexComplete G z (S ∪ Y)}
  have hXmem : X ∈ admissible := by
    exact ⟨hX, hXY, hcomp, hpXY, hXuniq, hzX, hzcomp⟩
  obtain ⟨S, hXS, hmax⟩ :=
    Set.Finite.exists_le_maximal (Set.toFinite admissible) hXmem
  rcases hmax.1 with ⟨hSanti, hSY, hScomp, hpS, hSuniq, hzS, hzScomp⟩
  refine ⟨S, hSanti, hSY, hScomp, hpS, hSuniq, hzS, hzScomp, ?_⟩
  intro T hST hTanti hTY hTcomp hpT hTuniq hzT hzTcomp
  have hTmem : T ∈ admissible :=
    ⟨hTanti, hTY, hTcomp, hpT, hTuniq, hzT, hzTcomp⟩
  exact Set.Subset.antisymm (hmax.2 hTmem hST) hST

end Workspace.Types.Thm245MaximalAdmissibleSet
