import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85Claim5Proof
import Workspace.ProofLemmas.Thm85EndgameClaim6
import Workspace.ProofLemmas.Thm85EndgameClaim4
import Workspace.ProofLemmas.Thm85EndgameClosing

/-!
# The four remaining paper arguments in the endgame of 8.5

Each declaration below isolates one consecutive part of the printed proof.  The proof-local
notions used by the paper are defined in `Thm85EndgameNotions`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EndgameClaims

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

/-- **Gap for claim (4) of 8.5** (printed p. 43).

PAPER: *"For every broad choice of rungs `R_uv` (`uv ∈ E(J)`), there is a unique pair `(i,j)`
of adjacent vertices of `J` such that: for every `w` different from `j` and adjacent to `i`,
`r_iw f₁` is the unique edge between `V(R_iw)` and `F`; for every `w` different from `i` and
adjacent to `j`, `r_jw f_n` is the unique edge between `V(R_jw)` and `F`; and for every edge
`uv` disjoint from `ij`, there are no edges between `V(R_uv)` and `F`.  For by (1) we can apply
5.8, and since the choice of rungs is broad, the minimality of `F` implies that one of 5.8.2.b,
5.8.2.c, 5.8.2.d holds. ... This proves (4)."* -/
theorem claim4_unique_traversal {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hfne : f₁ ≠ fn)
    (hPF : F = {x : V | x ∈ P}) (R : U → U → List V)
    (hBroad : BroadChoice G J S N
      (attachments G F (stripSystemVertices J S)) R) :
    HasUniqueTraversal G J N F f₁ fn R :=
  Workspace.ProofLemmas.Thm85EndgameClaim4.claim4 G hG J hJ S N hSN hnoenl F hFcompl hFconn
    hFmin hclaim1 P f₁ fn hP hfne hPF R hBroad

/-- **Gap for claim (5) of 8.5** (printed pp. 43–44).

PAPER: *"Every choice of rungs is broad.  For from (3), there is a broad choice, and from (4)
in any broad choice ... there are four different edges ... such that the first two are
disjoint, the last two are disjoint, and `X` meets all four selected rungs.  Consequently, if
we take another choice of rungs, differing from this one on only one edge, then it too is
broad.  It follows that every choice is broad.  This proves (5)."* -/
theorem claim5_every_choice_broad {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hBroadExists : ∃ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R) :
    ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R := by
  exact Workspace.ProofLemmas.Thm85Claim5Proof.every_choice_broad
    G J hJ S N hSN F f₁ fn hf₁ hfn hBroadExists hclaim4

/-- **Gap for claim (6) of 8.5** (printed p. 44).

PAPER: *"There are two choices of rungs with different traversals.  Take a choice of rungs,
and let `ij` be its traversal; and suppose that all other choices of rungs have the same
traversal. ... From the minimality of `F`, there are no other edges between `F` and
`A₁ ∪ A₂`; but then we can add `f₁` to `N_i`, `f_n` to `N_j`, and `F` to `S_ij`, contrary
to the maximality of the strip system.  This proves (6)."* -/
theorem claim6_different_traversals {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim2 : ¬ ∃ v : U, attachments G F (stripSystemVertices J S) ⊆
      ⋃ (u : U) (_ : J.Adj u v), S u v)
    (hclaim3 : ∃ u v u' v' : U, J.Adj u v ∧ J.Adj u' v' ∧ [u, v, u', v'].Nodup ∧
      (attachments G F (stripSystemVertices J S) ∩ S u v).Nonempty ∧
      (attachments G F (stripSystemVertices J S) ∩ S u' v').Nonempty)
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R) :
    HasDifferentTraversals G J S N F f₁ fn :=
  Workspace.ProofLemmas.Thm85EndgameClaim6.claim6 hJ hSN hmax hFcompl hFne hclaim3
    P hP hPF hclaim4 hclaim5

/-- **Gap for the closing paragraph of 8.5** (printed p. 44).

PAPER: *"For any choice of rungs, there is an optimal choice with the same traversal ... so
(6) implies that there are two optimal choices of rungs with different traversals. ... Hence
`J = K₄` and `jk` is disjoint from `hi`. ... Similarly all `hk`- and `ik`-rungs have length
0, and therefore all `hj`-rungs have even length, since `G` is Berge. ... But then the path
`f₁-r_hj-R_hj-r_jh-r_ji-f₁` is an odd hole, a contradiction.  This proves 8.5."* -/
theorem closing_optimal_choices_give_odd_hole {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
          (phi : H.lineGraph ≃g G.induce K'),
        IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' phi)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} →
        FormsLineGraph G J S N R H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (P : List V) (f₁ fn : V) (hP : IsPathFrom G P f₁ fn) (hPF : F = {x : V | x ∈ P})
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      HasUniqueTraversal G J N F f₁ fn R)
    (hclaim5 : ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hclaim6 : HasDifferentTraversals G J S N F f₁ fn) : False :=
  Workspace.ProofLemmas.Thm85EndgameClosing.closing G hG J hJ S N hSN hK₄ F hFcompl hFmin
    hclaim1 P f₁ fn hP hPF hclaim4 hclaim5 hclaim6

end Workspace.ProofLemmas.Thm85EndgameClaims
