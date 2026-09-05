import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm84K4CaseReduction

/-!
# 8.4, paragraphs three to five: the `J = K₄` endgame

PAPER (printed pp. 41–42, the proof of 8.4, from *"Let `V(J) = {1,2,3,4}`"* to the end, verbatim):

*"Let `V(J) = {1,2,3,4}`, and `R_ij ≠ R'_ij` only for the edge 1-2.  Let the ends of each `R_ij` be
`r_ij` and `r_ji`, where `{r_ij : j ∈ {1,…,4} \ {i}}` is a triangle `T_i` for each `i`.  Similarly
each `R'_ij` is between `r'_ij` and `r'_ji`, where for each `i`, `{r'_ij : j ∈ {1,…,4} \ {i}}` is a
triangle `T'_i`.  Since `X` saturates `L(H)`, it has at least two members in each of `T₁,…,T₄`; and
since `X` does not saturate `L(H')`, there is some `T'_i` containing at most one member of `X`.
Since `T₃ = T'₃` and `T₄ = T'₄`, we may assume that `|X ∩ T₁| = 2` and `|X ∩ T'₁| = 1`; and so
`r_{1,2} ∈ X`, `r'_{1,2} ∉ X`, and exactly one of `r_{1,3}, r_{1,4} ∈ X`, say `r_{1,3} ∈ X` and
`r_{1,4} ∉ X`.*

*Also, at least two vertices of `T₃` and `T₄` are in `X`, so there are at least two branch-vertices
of `H'` incident in `H'` with more than one edge in `X`.  By 5.7 applied to `H'`, we deduce that
5.7.5 holds, and so there is an edge `ij` of `J` such that `R'_ij` is even and
`(X ∩ V(L(H'))) \ V(R'_ij) = (T'_i ∪ T'_j) \ V(R'_ij)`.  In particular, `T'_i` and `T'_j` both
contain at least two vertices in `X`, and so `i, j ≥ 2`.  Since `r_{1,3} ∈ X` it follows that one of
`i, j = 3`, say `j = 3`, and `r_{1,3} ∈ T₃`; so `R_{1,3}` has length 0.  Now there are two cases,
`i = 2` and `i = 4`.  Suppose first that `i = 2`.  Then
`(X ∩ V(L(H'))) \ V(R_{2,3}) = {r_{1,3}, r_{3,4}, r_{2,4}, r'_{2,1}}`, and since at least two
vertices of `T₄` are in `X` it follows that `R_{2,4}, R_{3,4}` both have length 0, a contradiction
since `R'_ij = R_{2,3}` is even.  So `i = 4`, and hence `R_{3,4}` is even and
`(X ∩ V(L(H'))) \ V(R_{3,4}) = {r_{3,1}, r_{4,1}, r_{3,2}, r_{4,2}}`.*

*Since the path `r_{3,2}-R_{2,3}-r_{2,3}-r_{2,4}-R_{2,4}-r_{4,2}` can be completed to a hole via
`r_{4,2}-r_{4,3}-R_{3,4}-r_{3,4}-r_{3,2}`, it follows that the first path is even, and so exactly
one of `R_{2,3}, R_{2,4}` is odd; and since the same path can be completed to a hole via
`r_{4,2}-r_{4,1}-R_{1,4}-r_{1,4}-r_{1,3}-r_{3,2}` it follows that `R_{1,4}` is odd.  Since one of
`R_{2,3}, R_{2,4}` is odd, they do not both have length 0, and hence at most one of
`r_{2,3}, r_{2,4} ∈ X`.  Since `X` saturates `L(H)`, it follows that exactly one of
`r_{2,3}, r_{2,4} ∈ X` (and hence one of `R_{2,3}, R_{2,4}` has length 0), and also that
`r_{2,1} ∈ X`.  Since no vertex of `R'_{1,2}` is in `X`, this restores the symmetry between `T'₁`
and `T'₂`.*

*Suppose that `R_{2,3}` has length 0.  Then `R_{2,4}` and `R_{1,2}` are odd, and in particular
`r_{2,1} ≠ r_{1,2}`.  If `r_{2,1}` has no neighbour in `R'_{1,2}`, then
`y-r_{2,1}-r_{2,4}-r'_{2,1}-R'_{1,2}-r'_{1,2}-r_{1,4}-R_{1,4}-r_{4,1}-y` is an odd hole, a
contradiction.  So `r_{2,1}` has a neighbour in `R'_{1,2}`; but then `y` can be linked onto the
triangle `T'₁` via `R'_{1,2}` and `R_{1,4}`, contrary to 2.4.  This proves that `R_{2,3}` has length
`≥ 1`.  Hence `R_{2,3}` has odd length and `R_{2,4}` has length 0, and consequently
`R_{1,2}, R_{3,4}` have even length and `R_{1,4}` is odd.  If `R_{3,4}` has positive length then
`L(H)` is overshadowed (because of the vertex `y`), and so the theorem holds.  We may therefore
assume that `R_{3,4}` has length 0.  If `r_{2,1} ≠ r_{1,2}` and `r_{2,1}` has no neighbour in
`R'_{1,2}`, then `y-r_{2,1}-r_{2,4}-r'_{2,1}-R'_{1,2}-r'_{1,2}-r_{1,3}-y` is an odd hole, a
contradiction; while if `r_{2,1} ≠ r_{1,2}` and `r_{2,1}` has a neighbour in `R'_{1,2}`, then then
`y` can be linked onto the triangle `T'₁` via `R'_{1,2}` and `R_{1,4}`, contrary to 2.4.  So
`r_{2,1} = r_{1,2}`.  But then `L(H)` is degenerate.  Since the strip system is nondegenerate, it
follows from 8.3 that there is an overshadowed appearance of `K₄` in `G`.  This proves 8.4."*

The hypotheses below are exactly the state the printed proof is in when this paragraph begins: the
standing hypotheses of 8.4, the two adjacent choices of rungs produced by
`Thm84AdjacentChoices.adjacentChoices` (`R` saturated, `R'` not, agreeing off the single edge `ab`),
and `J = K₄`.  The conclusion is the disjunction of 8.4's last two outcomes.

Everything the paragraphs use is available in the workspace: `thm_2_4` (the two *"contrary to
2.4"* appeals), `thm_8_3` (the closing *"since the strip system is nondegenerate, it follows from
8.3"*), `thm_5_7` (the second application, yielding 5.7.5), `thm_8_1` (rung parity),
`Thm84RungEndDictionary.rungEndDictionary` (the identification of `δ_H(ι i)` with the triangle
`T_i` and of the edge indexed by `j` with the rung end `r_ij`), `TwoPathsHole` and
`PrismBasics.isHoleList_of_path_add_{one,two}_vertices` (the four displayed holes), and
`Thm101LinkOntoTriangle` (the two *"`y` can be linked onto the triangle `T'₁`"* constructions).

**Status: statement only.**  Commissioned by the 8.4 assembly lane; this is the single largest
remaining piece of 8.4 and should itself be broken down along the paper's own paragraph breaks.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm84K4Case

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The `J = K₄` endgame of 8.4** (printed pp. 41–42). -/
theorem k4Case {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (a b : U) (hab : J.Adj a b)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
    (φ : H.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
    (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
    (φ' : H'.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v}))
    (hForms : FormsLineGraph G J S N R H)
    (hsym : ∀ u v : U, J.Adj u v → R v u = (R u v).reverse)
    (hForms' : FormsLineGraph G J S N R' H')
    (hsym' : ∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse)
    (hSat : SaturatesLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X})
    (hUnsat : ¬ SaturatesLineGraph H'
      {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X})
    (hdiff : ∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v) :
    (∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V),
        IsAppearance G J' H'' K'' ∧ NondegenerateAppearance J' H'') ∨
    (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
      ∃ (k : ℕ) (H'' : SimpleGraph (Fin k)) (K'' : Set V)
        (ψ : H''.lineGraph ≃g G.induce K''),
        IsAppearance G J H'' K'' ∧ IsOvershadowedAppearance G H'' K'' ψ) := by
  exact Workspace.ProofLemmas.Thm84K4CaseReduction.reduction
    G hG J hJ S N hSN hnd y hy X hX hK4 a b hab n H R φ n' H' R' φ'
    hForms hsym hForms' hsym' hSat hUnsat hdiff

end Workspace.ProofLemmas.Thm84K4Case
