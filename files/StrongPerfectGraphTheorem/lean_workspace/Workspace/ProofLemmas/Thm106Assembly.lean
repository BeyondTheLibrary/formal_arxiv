import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.HyperprismTwoAttachments

/-!
# Assembly of 10.6 from its three printed steps (P10)

`thm_10_6_of_steps` proves **10.6** from three `def`-wrapped hypotheses matching the
paragraph breaks of the printed proof (pp. 60–63), so the node closes with one `exact` while
the three blocks are written independently.  Same shape as `Thm53Assembly`.

## The three steps

* `Claim2 G` — *"(2) We may assume that for every connected subset `F` of `V(G) \ V(H)`, its
  set of attachments in `H` is local."*  (printed pp. 60–62; the longest block, comprising the
  `X ∩ C₁ ≠ ∅` case and the `n` even and `n` odd cases.)

  **Its Lean conclusion must be a disjunction**
  `AdmitsBalancedSkewPartition G ∨ (∀ F, …)`, **not** the locality statement alone.  The
  printed *"we may assume"* is not a normalisation: the block **cites 10.5** (*"By 10.5 we may
  assume no vertex in `F` is major with respect to `K`"*, and again *"by 10.5 we may assume
  that `n > 1`"*), and 10.5's conclusion is `AdmitsBalancedSkewPartition G`.  Dropping the
  disjunct would make the step unprovable.  This is easy to get wrong and is the reason the
  step is stated as it is below.

* `SkewFromSide G` — *"Suppose `F` is a component of `V(G) \ V(H)`, and all its attachments
  are in `A`.  … By 4.5, `G` admits a balanced skew partition."*  (printed p. 62.)
  Only the `A`-side is asked for: the paper's *"and the same for `B`"* is free here, because
  `HyperprismTwoAttachments.isHyperprism_swap` turns `(A,B,C)` into `(B,A,C)` and carries the
  maximality along (`hyperVerts` is symmetric in its first two arguments).

* `Endgame G` — *"From (2) it follows that for every component of `V(G) \ V(H)`, all its
  attachments in `H` are a subset of one of `S₁, S₂, S₃`.  Let `X` be the union of `S₁` and
  all components … This proves 10.6."*  (printed p. 63.)

## What the assembly itself does

The opening sentence (an even prism yields a hyperprism, and one may choose `V(H)` maximal)
is `HyperprismFromPrism.exists_maximal_hyperprism_of_evenPrism`; claim (1) is
`HyperprismBasics.rung_even`.  The assembly then splits the five alternatives of
`LocalForHyperprism` into *"inside some `Sᵢ`"* (feed `Endgame`), *"inside `A`"* (feed
`SkewFromSide`) and *"inside `B`"* (feed `SkewFromSide` at the swapped hyperprism).
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm106Assembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The conclusion of `Workspace.Statements.S10.SPGT.thm_10_6`, named. -/
def Thm106Conclusion (G : SimpleGraph V) : Prop :=
  ((∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃ ∧
      {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
    Fintype.card V = 9) ∨
  AdmitsProper2Join G ∨ AdmitsBalancedSkewPartition G

/-- *"There is no nondegenerate appearance of `K₄` in `G`"*, named. -/
def NoK4 (G : SimpleGraph V) : Prop :=
  ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
    IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
      NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H

/-- *"`V(H)` is maximal"* — the choice made in the opening paragraph of the printed proof. -/
def MaximalHyperprism (G : SimpleGraph V) (A B C : Fin 3 → Set V) : Prop :=
  ∀ A' B' C' : Fin 3 → Set V, IsHyperprism G A' B' C' →
    (hyperVerts A' B' C').ncard ≤ (hyperVerts A B C).ncard

/-- **Step (2)** of the printed proof.  See the module docstring for why the conclusion is a
disjunction rather than the locality statement alone. -/
def Claim2 (G : SimpleGraph V) : Prop :=
  Berge G → NoK4 G → ∀ A B C : Fin 3 → Set V, IsHyperprism G A B C →
    MaximalHyperprism G A B C →
      AdmitsBalancedSkewPartition G ∨
      ∀ F : Set V, ConnectedSet G F → F ⊆ (hyperVerts A B C)ᶜ →
        LocalForHyperprism A B C (attachments G F (hyperVerts A B C))

/-- **The `A`-side skew partition** (printed p. 62).  The `B`-side is obtained from this by
`HyperprismTwoAttachments.isHyperprism_swap`. -/
def SkewFromSide (G : SimpleGraph V) : Prop :=
  Berge G → ∀ A B C : Fin 3 → Set V, IsHyperprism G A B C →
    MaximalHyperprism G A B C →
    ∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F → F.Nonempty →
      attachments G F (hyperVerts A B C) ⊆ A 0 ∪ A 1 ∪ A 2 →
      AdmitsBalancedSkewPartition G

/-- **The closing paragraph** (printed p. 63). -/
def Endgame (G : SimpleGraph V) : Prop :=
  Berge G → NoK4 G → ∀ A B C : Fin 3 → Set V, IsHyperprism G A B C →
    MaximalHyperprism G A B C →
    (∀ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F →
      ∃ i : Fin 3, attachments G F (hyperVerts A B C) ⊆ A i ∪ B i ∪ C i) →
    Thm106Conclusion G

/-- `hyperVerts` is symmetric in its first two arguments, so the swapped hyperprism inherits
maximality. -/
theorem hyperVerts_swap (A B C : Fin 3 → Set V) :
    hyperVerts B A C = hyperVerts A B C := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    refine mem_hyperVerts_iff.mpr ⟨i, ?_⟩
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    refine mem_hyperVerts_iff.mpr ⟨i, ?_⟩
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

/-- **10.6 from its three printed steps.** -/
theorem thm_10_6_of_steps (G : SimpleGraph V) (hG : Berge G) (hK4 : NoK4 G)
    (hclaim2 : Claim2 G) (hside : SkewFromSide G) (hend : Endgame G)
    (heven : ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃) :
    Thm106Conclusion G := by
  -- The opening paragraph: a maximal hyperprism.
  obtain ⟨A, B, C, hH, hmax⟩ :=
    HyperprismFromPrism.exists_maximal_hyperprism_of_evenPrism heven
  -- Step (2).
  rcases hclaim2 hG hK4 A B C hH hmax with hbal | hlocal
  · exact Or.inr (Or.inr hbal)
  -- Step (3) and the closing paragraph.
  by_cases hAside : ∃ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F ∧ F.Nonempty ∧
      attachments G F (hyperVerts A B C) ⊆ A 0 ∪ A 1 ∪ A 2
  · obtain ⟨F, hF, hFne, hFA⟩ := hAside
    exact Or.inr (Or.inr (hside hG A B C hH hmax F hF hFne hFA))
  by_cases hBside : ∃ F : Set V, IsComponent G (hyperVerts A B C)ᶜ F ∧ F.Nonempty ∧
      attachments G F (hyperVerts A B C) ⊆ B 0 ∪ B 1 ∪ B 2
  · -- *"and the same for `B`"*: apply the `A`-side step to the swapped hyperprism.
    obtain ⟨F, hF, hFne, hFB⟩ := hBside
    have hswap : IsHyperprism G B A C := HyperprismTwoAttachments.isHyperprism_swap hH
    have hvs : hyperVerts B A C = hyperVerts A B C := hyperVerts_swap A B C
    have hmax' : MaximalHyperprism G B A C := by
      intro A' B' C' h'
      rw [hvs]
      exact hmax A' B' C' h'
    refine Or.inr (Or.inr (hside hG B A C hswap hmax' F ?_ hFne ?_))
    · rw [hvs]; exact hF
    · rw [hvs]; exact hFB
  -- Every component's attachment set is inside a single `Sᵢ`.
  refine hend hG hK4 A B C hH hmax ?_
  intro F hF
  rcases hlocal F hF.2.1 hF.1 with h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · -- attachments inside `A`: excluded above unless `F = ∅`, when the claim is trivial
    rcases Set.eq_empty_or_nonempty F with rfl | hFne
    · refine ⟨0, ?_⟩
      intro v hv
      exact absurd hv.2 (by rintro ⟨f, hf, -⟩; exact hf)
    · exact absurd ⟨F, hF, hFne, h⟩ hAside
  · rcases Set.eq_empty_or_nonempty F with rfl | hFne
    · refine ⟨0, ?_⟩
      intro v hv
      exact absurd hv.2 (by rintro ⟨f, hf, -⟩; exact hf)
    · exact absurd ⟨F, hF, hFne, h⟩ hBside

end Workspace.ProofLemmas.Thm106Assembly
