import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.Thm61Claim8
import Workspace.ProofLemmas.Thm61Claim9
import Workspace.ProofLemmas.Thm61Claim10
import Workspace.ProofLemmas.Thm61EvenEndgame

/-!
# 6.1, second case: if the antipath `Q` is even then the theorem holds

PAPER (proof of 6.1, printed p. 31):

> *"In view of (7) we may henceforth assume that `Q` is even."*

and then, printed pp. 31–33, claims (8)–(13) and the closing paragraph, which ends
*"But then the fourth outcome of the theorem holds.  This proves 6.1."*

The steps are:

* *(8) Every edge in `X₁` meets every edge in `X₂`.*
* *(9) For all `W ∈ {X, X ∪ X₁, X ∪ X₂}` and for every even track `P` in `H` of length `≥ 4`
  and with both end-edges and no internal edges in `W`, every edge in `W` is incident with a
  penultimate vertex of `P`.*
* *(10) If `P₁, P₂, P₃` are tracks in `H` with a common end `v`, say, and otherwise
  vertex-disjoint, each with an edge in `X`, then at least two of the three edges of
  `P₁ ∪ P₂ ∪ P₃` incident with `v` belong to `X`.*
* *(11) For `i = 1, 2` there is an edge `fᵢ ∈ X` incident with `bᵢ` that does not meet `e₃`.*
* *(12) If there exist `f₁, f₂` as in (11) with `f₁, f₂ ≠ b₁b₂` then the theorem holds.*
* *(13) `b₄ = b₃`, and `B₃` has length 1, and `H` is a subdivision of `K₄`, and `B₄` is even.*
* the closing paragraph, which finishes with the first or the fourth outcome.

As in the odd case, the auxiliary sets are recovered from the hypotheses and are not parameters:
`X` is the set of `Y`-complete vertices of `L(H)`, and `Xᵢ` is the set of `Y \ {yᵢ}`-complete
vertices of `L(H)` that are not in `X`, where `y₁, y₂` are the ends of `Q`.

## How this file discharges the printed argument

The three general claims (8), (9), (10) are stated once and for all as
`Thm61EvenClaims.Claim8`, `Claim9`, `Claim10` and proved in
`Workspace.ProofLemmas.Thm61Claim8`, `.Thm61Claim9`, `.Thm61Claim10`.  The configuration
argument — the refinement of the choice of `b`, then (11), (12), (13) and the closing paragraph
— is `Workspace.ProofLemmas.Thm61EvenEndgame.thm_6_1_even_endgame`, which consumes exactly
those three claims.  This file is only the assembly: it feeds the three claims to the endgame.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm61EvenCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Conclusion

/-- **6.1, even case.**  *"In view of (7) we may henceforth assume that `Q` is even"* — and the
argument of (8)–(13) and the closing paragraph then proves the theorem. -/
theorem thm_6_1_even_case
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, VertexComplete G (↑(φ ⟨e, he⟩) : V) Y})
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
          VertexComplete G (↑(φ ⟨e, he⟩) : V) Y₁})
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q)) :
    Thm61Concl G m J n H K φ Y := by
  -- *"(8) Every edge in `X₁` meets every edge in `X₂`."*
  have h8 : Thm61EvenClaims.Claim8 G H K φ Y y₁ y₂ := fun h₁ h₂ hh₁ hh₂ =>
    Thm61Claim8.thm_6_1_claim8 G hG H K φ Y hYmajor y₁ y₂ Q hQ hQY hy hQeven h₁ h₂ hh₁ hh₂
  -- *"(9) … every edge in `W` is incident with a penultimate vertex of `P`."*
  have h9 : Thm61EvenClaims.Claim9 G H K φ Y y₁ y₂ :=
    Thm61Claim9.thm_6_1_claim9 G hG m J hJ n H K hsub φ Y hYanti hYmajor hmin
      y₁ y₂ Q hQ hQY hy hQeven h8
  -- *"(10) … at least two of the three edges of `P₁ ∪ P₂ ∪ P₃` incident with `v` belong to
  -- `X`."*
  have h10 : Thm61EvenClaims.Claim10 G H K φ Y :=
    Thm61Claim10.thm_6_1_claim10 G hG m J hJ n H K hsub φ Y hYanti hYmajor
      y₁ y₂ Q hQ hQY hy hQeven h9
  -- (11), (12), (13) and the closing paragraph.
  exact Thm61EvenEndgame.thm_6_1_even_endgame G hG m J hJ n H K hsub φ Y hYanti hYmajor
    hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10

end Workspace.ProofLemmas.Thm61EvenCase
