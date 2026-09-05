import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm121Case1
import Workspace.ProofLemmas.Thm121MinorCriteria
import Workspace.ProofLemmas.Thm121Case3Link
import Workspace.ProofLemmas.Thm121Case3RightDiagonal
import Workspace.ProofLemmas.PathBasics

/-!
# 12.1, case (3) of the printed proof

PAPER (printed p. 69): *"(3) If `v` is adjacent to `a₀` and not to `b₀` then the theorem holds.*

*For we may assume `v` has a neighbour in `V(S)`.  If `v` has a neighbour in `R₀*`, then by 11.2
it is either `B`-complete (when it is right-diagonal and the claim follows from (1)) or a
left-star (when statement 3 holds).  So we may assume it has no neighbour in `R₀*`.  We may
assume it has a neighbour in `B ∪ C`, for otherwise it is minor and statement 1 of the theorem
holds; let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that `v` has a neighbour in `R₁ \ a₁`,
and in addition such that `v` is not adjacent to `b₂` if possible.  By 10.4, `v` has a neighbour
in `R₂`.  If `a₂` is its only neighbour in `R₂`, then the strip `S' = (A ∪ {v}, C, B)` is
step-connected, since `v`-`R`-`b₁`, `a₂`-`R₂`-`b₂` is an `S'`-step where `R` is the path from
`v` to `b₁` with interior in `R₁ \ a₁`; and since `v` is adjacent to `a₀` and has no other
neighbours in `R₀`, this is contrary to the maximality of the staircase.  So `v` has a neighbour
in `R₂ \ a₂`; and hence `v` can be linked onto the triangle `{b₀, b₁, b₂}` via
`v`-`a₀`-`R₀`-`b₀`, and for `i = 1, 2`, the path from `v` to `bᵢ` with interior in `Rᵢ \ aᵢ`.  By
2.4 it follows that `v` is adjacent to both `b₁, b₂`; and hence from our choice of the step
`R₁, R₂`, and since the strip is step-connected, it follows that `v` is right-diagonal, and the
claim follows from (1).  This proves (3)."*

The results cited are 11.2, 10.4, 2.4, the maximality of the staircase, and case (1)
(`Workspace.ProofLemmas.Thm121Case1`).

The mirror-image case — `v` adjacent to `b₀` and not to `a₀` — is what the paper's closing
sentence *"But (2)-(4) cover all the possibilities, **up to symmetry**"* refers to; it is
obtained from this one by the exchange formalized in
`Workspace.ProofLemmas.Thm121Symmetry`.

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm121Case3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

/-- **12.1 (3)**: *"If `v` is adjacent to `a₀` and not to `b₀` then the theorem holds."* -/
theorem thm121Case3 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hlen : 3 ≤ SPGT.pathLength R₀ := hK.1.2.2
  by_cases hVS : ∃ x ∈ A ∪ B ∪ C, G.Adj v x
  · by_cases hR0 : ∃ x ∈ SPGT.interior R₀, G.Adj v x
    · -- PAPER: *"If `v` has a neighbour in `R₀*`, then by 11.2 it is either `B`-complete … or a
      -- left-star …"*
      rcases Workspace.ProofLemmas.Thm121Case3Link.thm121Case3Link G hG hK4 A C B a₀ b₀ R₀ hS hban hlen v hv hVS ha hb hR0 with hBc | hls
      · -- *"… `B`-complete (when it is right-diagonal and the claim follows from (1))"*
        refine Workspace.ProofLemmas.Thm121Case1.thm121Case1 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv (Or.inr ⟨hv, ?_⟩)
        rintro x (hx | hx)
        · exact hBc x hx
        · have hx' : x = a₀ := hx
          rw [hx']; exact ha
      · -- *"… or a left-star (when statement 3 holds)"*
        obtain ⟨x, hxint, hvx⟩ := hR0
        exact Or.inr (Or.inr (Or.inl ⟨hls, x,
          Workspace.ProofLemmas.PathBasics.interior_subset hxint,
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).mp hxint).2.1,
          hvx⟩))
    · by_cases hBC : ∃ x ∈ B ∪ C, G.Adj v x
      · -- PAPER: the main stretch of case (3) — *"it follows that `v` is right-diagonal, and the
        -- claim follows from (1)"*
        exact Workspace.ProofLemmas.Thm121Case1.thm121Case1 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv (Or.inr (Workspace.ProofLemmas.Thm121Case3RightDiagonal.thm121Case3RightDiagonal G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK v hv ha hb (by push_neg at hR0; exact hR0) hBC))
      · -- PAPER: *"We may assume it has a neighbour in `B ∪ C`, for otherwise it is minor and
        -- statement 1 of the theorem holds"*
        exact Or.inl (Workspace.ProofLemmas.Thm121MinorCriteria.thm121AltOneOfNoNeighbourInBC G A C B a₀ b₀ R₀ hS hban v hv (by push_neg at hBC; exact hBC) (by push_neg at hR0; exact hR0) hb)
  · -- PAPER: *"For we may assume `v` has a neighbour in `V(S)`."*
    exact Or.inl (Workspace.ProofLemmas.Thm121MinorCriteria.thm121AltOneOfNoStripNeighbour G A C B a₀ b₀ R₀ hS v hv (by push_neg at hVS; exact hVS))

end Workspace.ProofLemmas.Thm121Case3
