import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.OddWheelNoOddExtSegment
import Workspace.ProofLemmas.OddWheelLines
import Workspace.ProofLemmas.OddWheelBulletThree

/-!
# 16.3, assembled up to the final step

The printed proof of 16.3 (p. 101) runs:

1. *"Suppose `(C,Y)` is an odd wheel with `Y` maximal, and subject to that, such that the number of
   `Y`-complete edges in `C` is minimum."* — `WheelBasics.exists_optimal_odd_wheel`;
2. claim (1), whose two cases are `OddWheelNoOddExtSegment.no_odd_ext_segment` (there is no odd
   `Y ∪ {v}`-segment) and `OddWheelLines.no_bad_vertex_of_no_odd_ext_segment` (the "lines"
   argument) — glued here as `claim_one`;
3. everything from *"Since `(C,Y)` is an odd wheel, `C` has at least two segments"* to the third
   bullet of 16.2 — `OddWheelBulletThree.exists_bullet_three`;
4. the construction of `C'` from `C \ p₂` and the closing edge count — `RebuildStep` below, which
   is exactly `OddWheelRebuild.contradiction_from_bullet_three`, taken here as a hypothesis so
   that steps 1–3 can be verified independently of it.

`thm_16_3_of_rebuild` is therefore 16.3 with step 4 abstracted.  Supplying `RebuildStep G` closes
the theorem.

Nothing here corresponds to a numbered result of the paper beyond 16.3 itself.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAssembly

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-- The final step of the printed proof of 16.3: *"But then `C \ p₂` can be completed to a hole
`C'` say, via `p₁-f₁-⋯-f_k-p₃` … contrary to the optimality of `(C,Y)`."*

The hypotheses are exactly the data that `OddWheelBulletThree.exists_bullet_three` produces,
together with the optimality of `(C,Y)`; they are a superset of the interface of
`OddWheelRebuild.contradiction_from_bullet_three`, so that lemma discharges this by dropping the
arguments it does not use. -/
def RebuildStep (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V), IsWheel G C Y → IsOddWheel G C Y →
    (∀ C' : List V, IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C') →
    ∀ F : Set V, (∀ f ∈ F, f ∉ C) → (∀ f ∈ F, f ∉ Y) → ConnectedSet G F →
      (∀ f ∈ F, ¬ VertexComplete G f Y) →
      ∀ p₁ p₂ p₃ : V,
        (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) →
        VertexComplete G p₁ Y → VertexComplete G p₂ Y → VertexComplete G p₃ Y →
        ∀ P : List V, IsPathFrom G P p₁ p₃ → (∀ x ∈ SPGT.interior P, x ∈ F) →
          (∀ x ∈ SPGT.interior P, ∀ u ∈ C, u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → ¬ G.Adj x u) → False

/-- PAPER (16.3, printed p. 101), claim (1): *"There is no vertex `v ∈ V(G) \ (V(C) ∪ Y)` such
that `v` is not `Y`-complete and has nonadjacent neighbours in `C` of opposite wheel-parity."*
Its two cases are the two modules cited below. -/
theorem claim_one [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : InF6 G)
    {C : List V} {Y : Set V} (hodd : IsOddWheel G C Y)
    (hYmax : ¬ ∃ (C' : List V) (Y' : Set V), IsOddWheel G C' Y' ∧ Y ⊂ Y')
    (hmin : ∀ C' : List V, IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C') :
    ∀ z : V, z ∉ C → z ∉ Y → ¬ VertexComplete G z Y →
      ∀ x y : V, G.Adj z x → G.Adj z y → ¬ G.Adj x y → ¬ OppositeWheelParity G C Y x y := by
  intro z hzC hzY hznc x y hzx hzy hnadj hopp
  have hBerge : Berge G := hG.1.1.1
  have hw : IsWheel G C Y := hodd.1
  exact OddWheelLines.no_bad_vertex_of_no_odd_ext_segment hBerge hG hw hodd hmin
    hzC hzY hznc hzx hzy hnadj hopp
    (OddWheelNoOddExtSegment.no_odd_ext_segment hBerge hw hYmax hzC hzY hznc
      hopp.2.1 hopp.2.2.1 hopp.1 hzx hzy hnadj)

/-- **16.3, with only the final step abstracted.** -/
theorem thm_16_3_of_rebuild [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : InF6 G)
    (hstep : RebuildStep G) :
    (∃ (C : List V) (Y : Set V), IsOddWheel G C Y) → AdmitsBalancedSkewPartition G := by
  intro hex
  by_contra hno
  -- "Suppose `(C,Y)` is an odd wheel with `Y` maximal, and subject to that, such that the number
  -- of `Y`-complete edges in `C` is minimum."
  obtain ⟨C, Y, hodd, hYmax, hmin0⟩ := WheelBasics.exists_optimal_odd_wheel G hex
  have hw : IsWheel G C Y := hodd.1
  have hmin : ∀ C' : List V, IsOddWheel G C' Y →
      OptimalWheelChoice.yEdgeCount G Y C ≤ OptimalWheelChoice.yEdgeCount G Y C' := by
    intro C' h
    rw [OptimalWheelChoice.yEdgeCount_def, OptimalWheelChoice.yEdgeCount_def]
    exact hmin0 C' h
  -- claim (1), then the third bullet of 16.2, then the rebuild
  obtain ⟨F, p₁, p₂, p₃, P, hFC, hFY, hFconn, hFnc, hblock, hY1, hY2, hY3, hP, hPF, hPno⟩ :=
    OddWheelBulletThree.exists_bullet_three hG hno hodd (claim_one G hG hodd hYmax hmin)
  exact hstep C Y hw hodd hmin F hFC hFY hFconn hFnc p₁ p₂ p₃ hblock hY1 hY2 hY3 P hP hPF hPno

end Workspace.ProofLemmas.OddWheelAssembly
