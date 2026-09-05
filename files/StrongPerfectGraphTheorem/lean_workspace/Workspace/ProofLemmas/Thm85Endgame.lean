import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameClaims
import Workspace.ProofLemmas.Thm85EndgamePathTwoVertices

/-!
# 8.5, claims (4), (5), (6) and the closing paragraph

This module carries the remainder of the printed proof of 8.5 (printed pp. 43–44), from the
definition of a *broad* choice of rungs to the final contradiction.  Claims (4), (5), (6) and
the closing paragraph all speak about the proof-local notions *broad choice*, *traversal* and
*optimal choice*, which the paper introduces inside this proof and which occur in no numbered
statement (see the closing comment of `Workspace.Types.StripSystems`); they are therefore not
formalized separately, and the three claims are consumed together here.

PAPER (printed pp. 43–44), verbatim:

*"Let us say a choice `R_uv` (`uv ∈ E(J)`) of rungs is **broad** if there are two disjoint
edges `ij` and `hk` of `J` such that `X` meets both `R_ij` and `R_hk`.  From (3) there is a
broad choice.  We denote the ends of `R_uv` by `r_uv` and `r_vu`, where `r_uv ∈ N_u` and
`r_vu ∈ N_v`.*

*(4) For every broad choice of rungs `R_uv` (`uv ∈ E(J)`), there is a unique pair `(i,j)` of
adjacent vertices of `J` such that:*

*• for every `w ∈ V(J)` different from `j` and adjacent to `i` in `J`, `r_iw f₁` is the unique
edge of `G` between `V(R_iw)` and `F`,*

*• for every `w ∈ V(J)` different from `i` and adjacent to `j` in `J`, `r_jw f_n` is the unique
edge of `G` between `V(R_jw)` and `F`,*

*• for every edge `uv` of `J` disjoint from `ij`, there are no edges of `G` between `V(R_uv)`
and `F`.*

*For by (1) we can apply 5.8, and since the choice of rungs is broad, the minimality of `F`
implies that one of 5.8.2.b, 5.8.2.c, 5.8.2.d holds.  Hence there is an edge `ij` as in (4).
Suppose there is another, say `i'j'`.  Since `i'j'` meets all edges of `J` that share exactly
one end with `ij`, and `J` is 3-connected, it follows that `J = K₄` and the two edges `ij`,
`i'j'` are disjoint.  Moreover, the unique vertex of `R_{ii'}` in `X` is both `r_{ii'}` and
`r_{i'i}`, so `R_{ii'}` has length 0.  Similarly `R_{ij'}`, `R_{ji'}`, `R_{jj'}` all have length
0, and so `L(H)` is degenerate, contrary to (1).  This proves (4).*

*(5) Every choice of rungs is broad.*

*For from (3), there is a broad choice, and from (4) in any broad choice `R_uv` (`uv ∈ E(J)`)
there are four different edges `a₁b₁, …, a₄b₄` of `J`, such that `a₁b₁` is disjoint from `a₂b₂`,
and `a₃b₃` is disjoint from `a₄b₄`, and `X` meets `R_{a_i b_i}` for `1 ≤ i ≤ 4`.  Consequently,
if we take another choice of rungs, differing from this one on only one edge, then it too is
broad.  It follows that every choice is broad.  This proves (5).*

*For a given choice of rungs, let us call the edge `ij` as in (4) the **traversal** for the
choice.*

*(6) There are two choices of rungs with different traversals.*

*Take a choice of rungs, and let `ij` be its traversal; and suppose that all other choices of
rungs have the same traversal.  Let `A₁ = N_i \ S_ij`, and `A₂ = N_j \ S_ij`.  From (4),(5), and
the uniqueness of `ij` it follows that `X ∩ (V(S,N) \ S_ij) = A₁ ∪ A₂`.  Hence `n ≥ 2`, for if
`n = 1` then we can add `f₁` to `N_i`, `N_j` and `S_ij`, contrary to the maximality of the strip
system.  Choose `x₁ ∈ A₁` and `x₂ ∈ A₂` in disjoint strips.  From (4), `x₁` is adjacent to
exactly one of `f₁, f_n`, say `f₁`.  For any other vertex `x₃ ∈ A₂`, let `R_uv` (`uv ∈ E(J)`) be
a choice of rungs forming `L(H)` say, such that `x₁, x₃ ∈ V(H)`.  From (4) and (5) it follows
that `f_n` is adjacent to `x₃`; and so `f_n` is complete to `A₂`, and similarly `f₁` is complete
to `A₁`.  From the minimality of `F`, there are no other edges between `F` and `A₁ ∪ A₂`; but
then we can add `f₁` to `N_i`, `f_n` to `N_j`, and `F` to `S_ij`, contrary to the maximality of
the strip system.  This proves (6).*

*Let us say a choice `R_uv` (`uv ∈ E(J)`) is **optimal** if `R_uv` has a vertex in `X` for all
edges `uv` in `K`.  For any choice of rungs, there is an optimal choice with the same traversal
(just replace rungs that miss `X` by rungs that meet `X` wherever possible); so (6) implies that
there are two optimal choices of rungs with different traversals.  Now for any optimal choice of
rungs, if `hi` is its traversal, then by (4) and the optimality of the choice, it follows that
`K` consists precisely of the edges of `J` with exactly one end in common with `hi`, together
possibly with `hi` itself.  In particular `hi` meets all edges in `K`.  We may assume that some
other edge `jk` is the traversal for some other optimal choice; and hence (since `J` is
3-connected) it follows that `J = K₄` and `jk` is disjoint from `hi`, and neither edge is in
`K`.  Hence `V(J) = {h,i,j,k}`.  Now since the strip system is not degenerate, there is one of
the four edges `hj, hk, ij, ik` whose strip contains a rung of nonzero length; some `hj`-rung
`R` has length `> 0` say.  From (4) it follows that exactly one vertex of `R` is in `X`, one of
its ends; say the end in `N_h`.  Let `R_uv` (`uv ∈ E(J)`) be any choice of rungs such that
`R_hj = R`.  Since the end of `R` in `N_j` does not belong to `X`, it follows from (4) that for
each of `R_hk, R_ij, R_ik`, its unique vertex in `X` is its end in `N_h ∪ N_i`.  Since the
choice of these rungs was arbitrary, it follows that `X ∩ S_hk = N_hk`, `X ∩ S_ij = N_ij`, and
`X ∩ S_ik = N_ik`.  If also `X ∩ S_hj = N_hj` then `hi` is the traversal for every choice of
rungs, contrary to (6), so `X ∩ S_hj ≠ N_hj`.  It follows that every `ij`-rung has length 0; for
if one, `R'` say, has length `> 0`, then its unique vertex in `X` is its end in `N_i`, and by
exchanging `h` and `i` it follows that `X ∩ S_hj = N_hj`, a contradiction.  Similarly all `hk`-
and `ik`-rungs have length 0, and therefore all `hj`-rungs have even length, since `G` is Berge.
From (1), we may assume that `f₁` is adjacent to `r_hj` and complete to `S_hk`, and `f_n` is
complete to `S_ij ∪ S_ik`, and there are no other edges between `F` and
`S_hk ∪ S_ij ∪ S_ik ∪ {r_hj}`.  Let `R'` be an `hj`-rung such that its vertex in `N_h`
(`r'_hj`, say) is not its unique vertex in `X`.  Consequently, its other end (`r'_jh`) is its
unique vertex in `X`.  By the same argument with `hi` and `jk` exchanged, it follows that one of
`f₁, f_n` is complete to `S_ij ∪ {r'_jh}` and the other to `S_hk ∪ S_ik`; and hence `n = 1`.
But then the path `f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction.  This proves
8.5."*

**Status: this module is a work item — the theorem below is stated but not yet proved.**
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- **Claims (4), (5), (6) and the closing paragraph of the proof of 8.5** (printed pp. 43–44).

Everything the printed proof has established at the point where a *broad* choice of rungs is
introduced is supplied as a hypothesis: `hclaim1` is (1), `hclaim2` is (2), `hclaim3` is (3),
and `hPF` says that the minimal `F` is the vertex set of the path `f₁ … f_n`.  The conclusion is
the contradiction the printed proof reaches. -/
theorem thm85Endgame {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g G.induce K'),
          IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' φ)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmajor : ∀ f ∈ F, ¬ MajorForStripSystem G J S N f)
    (hXnotlocal :
      ¬ LocalForStripSystem J S N (attachments G F (stripSystemVertices J S)))
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hclaim2 : ¬ ∃ v : U, attachments G F (stripSystemVertices J S) ⊆
        ⋃ (u : U) (_ : J.Adj u v), S u v)
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty)
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P}) :
    False := by
  classical
  open Workspace.ProofLemmas.Thm85EndgameNotions in
    have hBroadExists : ∃ R : U → U → List V,
        BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R :=
      Workspace.ProofLemmas.Thm85EndgameNotions.exists_broad_choice hSN
        (attachments G F (stripSystemVertices J S)) hclaim3
    have hfne : f₁ ≠ fn :=
      Workspace.ProofLemmas.Thm85EndgamePathTwoVertices.path_ends_distinct
        G hG J hJ S N hSN hmax hnoenl hK₄ F hFcompl hFne hFconn hFmajor hXnotlocal hFmin
        hclaim1 hclaim3 P f₁ fn hP hPF
    have hclaim4' : ∀ R : U → U → List V,
        BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
        HasUniqueTraversal G J N F f₁ fn R := by
      intro R hBroad
      exact Workspace.ProofLemmas.Thm85EndgameClaims.claim4_unique_traversal
        G hG J hJ S N hSN hnoenl F hFcompl hFne hFconn hFmin hclaim1
          P f₁ fn hP hfne hPF R hBroad
    have hf₁F : f₁ ∈ F := by
      rw [hPF]
      exact List.mem_of_mem_head? hP.2.1
    have hfnF : fn ∈ F := by
      rw [hPF]
      exact List.mem_of_getLast? hP.2.2
    have hclaim5' : ∀ R : U → U → List V, RungChoice G J S N R →
        BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R :=
      Workspace.ProofLemmas.Thm85EndgameClaims.claim5_every_choice_broad
        G J hJ S N hSN F f₁ fn hf₁F hfnF hBroadExists hclaim4'
    have hclaim6' : HasDifferentTraversals G J S N F f₁ fn :=
      Workspace.ProofLemmas.Thm85EndgameClaims.claim6_different_traversals
        G J hJ S N hSN hmax F hFcompl hFne hFconn hFmin hclaim2 hclaim3
          P f₁ fn hP hPF hclaim4' hclaim5'
    exact Workspace.ProofLemmas.Thm85EndgameClaims.closing_optimal_choices_give_odd_hole
      G hG J hJ S N hSN hK₄ F hFcompl hFne hFconn hFmin hclaim1
        P f₁ fn hP hPF hclaim4' hclaim5' hclaim6'

end Workspace.ProofLemmas.Thm85Endgame
