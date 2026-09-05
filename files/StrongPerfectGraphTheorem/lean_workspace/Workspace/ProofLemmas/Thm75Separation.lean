import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.ComponentsOfSetBasics

/-!
# 7.5, the step "it follows from (2) that there is a partition"

PAPER (proof of 7.5, printed p. 38): *"It follows from (2) that there is a partition of
`V(G) \ (X₀ ∪ X₁ ∪ Y)` into two sets `L` and `M` say, where there is no edge between `L` and
`M`, and `S ⊆ L` and `T ⊆ M`."*

Claim (2) of the printed proof reads: *"If `F ⊆ V(G)` is connected and some vertex of `S` has a
neighbour in `F`, and so does some vertex of `T`, and `F ∩ (X₀ ∪ X₁ ∪ Y) = ∅`, then the theorem
holds."*  Under the standing assumption (in the proof by contradiction) that the theorem does
*not* hold, claim (2) says there is no such `F`; that is the hypothesis `hno` below, with
`Z = X₀ ∪ X₁ ∪ Y`.

The construction is the paper's implicit one: `L` is the union of those components of
`V(G) \ Z` that meet `S`, and `M` is what is left.  `T ⊆ M` is where claim (2) is used: a
component meeting both `S` and `T` would be an `F` as in (2), since a connected set containing
two distinct vertices gives each of them a neighbour inside it.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Separation

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V]

/-- The separation extracted from claim (2) of the proof of 7.5.

`Z` is the paper's `X₀ ∪ X₁ ∪ Y`, and `S`, `T` are the paper's `S` and `T`.  The hypothesis
`hno` is the contrapositive form of claim (2) under the standing assumption that neither
conclusion of 7.5 holds. -/
theorem thm75Separation (G : SimpleGraph V) (Z S T : Set V)
    (hSZ : ∀ x ∈ S, x ∉ Z) (hTZ : ∀ x ∈ T, x ∉ Z) (hST : Disjoint S T)
    (hno : ∀ F : Set V, ConnectedSet G F → (∀ x ∈ F, x ∉ Z) →
      (∃ s ∈ S, ∃ f ∈ F, G.Adj s f) → (∃ t ∈ T, ∃ f ∈ F, G.Adj t f) → False) :
    ∃ L M : Set V, L ∪ M = Zᶜ ∧ Disjoint L M ∧ Anticomplete G L M ∧ S ⊆ L ∧ T ⊆ M := by
  classical
  -- `L` is the union of the components of `Zᶜ` that meet `S`.
  set L : Set V := {x : V | ∃ C : Set V, IsComponent G Zᶜ C ∧ (C ∩ S).Nonempty ∧ x ∈ C} with hL
  refine ⟨L, Zᶜ \ L, ?_, ?_, ?_, ?_, ?_⟩
  · -- `L ∪ (Zᶜ \ L) = Zᶜ`
    have hLsub : L ⊆ Zᶜ := by
      rintro x ⟨C, hC, -, hxC⟩
      exact hC.1 hxC
    rw [Set.union_diff_cancel' (le_refl L) hLsub]
  · exact Set.disjoint_sdiff_right
  · -- no edge between `L` and `Zᶜ \ L`
    rintro x ⟨C, hC, hCS, hxC⟩ y ⟨hyZ, hyL⟩ hadj
    obtain ⟨D, hD, hyD⟩ := ComponentsOfSetBasics.exists_isComponent_mem G Zᶜ hyZ
    by_cases hCD : C = D
    · exact hyL ⟨C, hC, hCS, hCD ▸ hyD⟩
    · exact ComponentsOfSetBasics.anticomplete_of_isComponent G hC hD hCD x hxC y hyD hadj
  · -- `S ⊆ L`
    intro s hs
    obtain ⟨C, hC, hsC⟩ :=
      ComponentsOfSetBasics.exists_isComponent_mem G Zᶜ (Set.mem_compl (hSZ s hs))
    exact ⟨C, hC, ⟨s, hsC, hs⟩, hsC⟩
  · -- `T ⊆ M`: this is where claim (2) is used
    intro t ht
    refine ⟨Set.mem_compl (hTZ t ht), ?_⟩
    rintro ⟨C, hC, ⟨s, hsC, hsS⟩, htC⟩
    -- `s ≠ t` since `S` and `T` are disjoint
    have hst : s ≠ t := by
      rintro rfl
      exact Set.disjoint_left.mp hST hsS ht
    -- a connected set containing two distinct vertices gives each of them a neighbour in it
    have hnbr : ∀ a ∈ C, ∀ b ∈ C, a ≠ b → ∃ f ∈ C, G.Adj a f := by
      intro a haC b hbC hab
      obtain ⟨w⟩ := hC.2.1 ⟨a, haC⟩ ⟨b, hbC⟩
      cases w with
      | nil => exact absurd rfl hab
      | cons hadj _ => exact ⟨_, Subtype.coe_prop _, hadj⟩
    exact hno C hC.2.1 (fun x hx => hC.1 hx)
      ⟨s, hsS, hnbr s hsC t htC hst⟩ ⟨t, ht, hnbr t htC s hsC (Ne.symm hst)⟩

end Workspace.ProofLemmas.Thm75Separation
