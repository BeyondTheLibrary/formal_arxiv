import Workspace.ProofLemmas.Thm93CaseOneLong

/-! The length-zero path in the short-branch case gives alternative 4 of 9.3. -/
set_option autoImplicit false
namespace Workspace.ProofLemmas.Thm93CaseOneShort
open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm93CaseOneLong

/-- Two triangles meet in the cross-edge vertex `x`. After `x` is removed, their union is
exactly its neighbourhood in the other three lists of the knot. -/
structure ShortSide {V : Type*} (G : SimpleGraph V) (x y : V) (K S N₁ N₂ : Set V) : Prop where
  distinct : x ≠ y
  x_not_mem : x ∉ S
  y_not_mem : y ∉ S
  y_mem_K : y ∈ K
  subset_K : S ⊆ K
  neighbours : (N₁ ∪ N₂) \ {x} = {w ∈ S | G.Adj x w}

/-- **PAPER (9.3, printed p. 49):** *"If `R` has length 0 then statement 4 of the theorem
holds."* The path in `F` has just one endpoint value, so that value sees both triangles. -/
theorem singleton_endgame {V : Type*} {G : SimpleGraph V} {x y p : V}
    {K S N₁ N₂ : Set V} {R T : List V}
    (hs : ShortSide G x y K S N₁ N₂)
    (hset : {v | v ∈ R} = {x}) (hT : IsPathFrom G T p p)
    (halt : BranchAlternatives G K N₁ N₂ R x x T p p) :
    (∀ w ∈ S, G.Adj p w ↔ G.Adj x w) ∧ ¬ G.Adj p y := by
  have hp := (PathBasics.isPathFrom_ends_mem hT).1
  have hyN : y ∉ N₁ ∪ N₂ := by
    intro hy
    have : y ∈ {w ∈ S | G.Adj x w} := hs.neighbours ▸ ⟨hy, hs.distinct.symm⟩
    exact hs.y_not_mem this.1
  have finish
      (hcomplete : ∀ w ∈ (N₁ ∪ N₂) \ {x}, G.Adj p w)
      (hno : ∀ w ∈ K, w ≠ x → G.Adj p w → w ∈ N₁ ∪ N₂) :
      (∀ w ∈ S, G.Adj p w ↔ G.Adj x w) ∧ ¬ G.Adj p y := by
    refine ⟨?_, fun h => hyN (hno y hs.y_mem_K hs.distinct.symm h)⟩
    intro w hw
    have hwx : w ≠ x := fun h => hs.x_not_mem (h ▸ hw)
    constructor
    · intro hadj
      exact (show w ∈ {w ∈ S | G.Adj x w} from hs.neighbours ▸
        ⟨hno w (hs.subset_K hw) hwx hadj, hwx⟩).2
    · intro hadj
      exact hcomplete w (hs.neighbours ▸ (show w ∈ {w ∈ S | G.Adj x w} from ⟨hw, hadj⟩))
  have complete_union (h₁ : ∀ w ∈ N₁ \ {x}, G.Adj p w)
      (h₂ : ∀ w ∈ N₂ \ {x}, G.Adj p w) : ∀ w ∈ (N₁ ∪ N₂) \ {x}, G.Adj p w := by
    rintro w ⟨h | h, hw⟩
    exacts [h₁ w ⟨h, hw⟩, h₂ w ⟨h, hw⟩]
  rcases halt with ⟨_, hhit, _⟩ | ⟨h₁, h₂, hno, _⟩ | ⟨_, hcomp, hno, _⟩ | ⟨_, h₁, h₂, hno, _⟩
  · obtain ⟨w, hw, _⟩ := hhit
    rw [hset] at hw
    exact (hw.2 hw.1).elim
  · apply finish (complete_union h₁ h₂)
    intro w hw hwx hadj
    rcases hno p hp w hw hadj with h | h | h | h
    exacts [Or.inl h.2.1, Or.inr h.2.1, (hwx h.2).elim, (hwx h.2).elim]
  · apply finish (by simpa using hcomp)
    intro w hw hwx hadj
    rcases hno w hw hadj with h | h
    · exact h
    · rw [hset] at h
      exact (hwx h).elim
  · apply finish (complete_union h₁ h₂)
    intro w hw hwx hadj
    rcases hno p hp w hw hwx hadj with h | h
    exacts [Or.inl h.2.1, Or.inr h.2.1]

end Workspace.ProofLemmas.Thm93CaseOneShort
