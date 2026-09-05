import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm85Claim5Proof
import Workspace.ProofLemmas.Thm85EndgameNotions

/-!
# 8.5, claim (5), without the ordered uniqueness of the traversal

`Thm85Claim5Proof.every_choice_broad` takes claim (4) in the form
`BroadChoice … R → HasUniqueTraversal … R`, but it only ever uses the *existence* half of that
statement.  The `n = 1` step of 8.5 (`Thm85EndgamePathTwoVertices.path_ends_distinct`) has to
run claim (5) before `f₁ ≠ f_n` is known, and for `f₁ = f_n` the ordered uniqueness is false
(`(j,i)` is a traversal whenever `(i,j)` is).  This module therefore repeats the two steps of
claim (5) with the weaker hypothesis.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesBroad

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

/-- Replacing the rung on at most one unoriented edge preserves broadness. -/
theorem broad_of_single_edge_change {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (R R' : U → U → List V) (hR' : RungChoice G J S N R')
    (e : Sym2 U)
    (hsame : ∀ u v : U, J.Adj u v → s(u, v) ≠ e → R' u v = R u v)
    (hBroad : BroadChoice G J S N
      (attachments G F (stripSystemVertices J S)) R)
    (hclaim4 : ∀ Q : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Q →
      ∃ p q : U, IsTraversal G J N F f₁ fn Q p q) :
    BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R' := by
  obtain ⟨i, j, hij⟩ := hclaim4 R hBroad
  obtain ⟨w, w', hiw, hjw', hnd, hiwe, hjw'e, hmeet, hmeet'⟩ :=
    Thm85Claim5Proof.traversal_has_disjoint_meeting_rungs_avoiding
      G J hJ S N hSN F f₁ fn hf₁ hfn R hBroad.1 i j hij e
  refine ⟨hR', i, w, j, w', hiw, hjw', hnd, ?_, ?_⟩
  · obtain ⟨x, hx, hxR⟩ := hmeet
    exact ⟨x, hx, by rwa [hsame i w hiw hiwe]⟩
  · obtain ⟨x, hx, hxR⟩ := hmeet'
    exact ⟨x, hx, by rwa [hsame j w' hjw' hjw'e]⟩

/-- **Claim (5) of 8.5**: *"every choice of rungs is broad"* (printed pp. 43–44), with claim (4)
supplied only as the existence of a traversal. -/
theorem every_choice_broad {V U : Type*} [Fintype U]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (F : Set V) (f₁ fn : V) (hf₁ : f₁ ∈ F) (hfn : fn ∈ F)
    (hBroadExists : ∃ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R)
    (hclaim4 : ∀ R : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R →
      ∃ p q : U, IsTraversal G J N F f₁ fn R p q) :
    ∀ R : U → U → List V, RungChoice G J S N R →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) R := by
  classical
  obtain ⟨R₀, hR₀Broad⟩ := hBroadExists
  intro R₁ hR₁
  let mix : Finset (Sym2 U) → U → U → List V := fun A u v =>
    if s(u, v) ∈ A then R₁ u v else R₀ u v
  have hmixChoice : ∀ A : Finset (Sym2 U), RungChoice G J S N (mix A) := by
    intro A
    constructor
    · intro u v huv
      by_cases hmem : s(u, v) ∈ A
      · simpa [mix, hmem] using hR₁.1 u v huv
      · simpa [mix, hmem] using hR₀Broad.1.1 u v huv
    · intro u v huv
      have hswap : s(v, u) = s(u, v) := Sym2.eq_swap
      by_cases hmem : s(u, v) ∈ A
      · simp only [mix, hmem, if_true]
        rw [hswap, if_pos hmem]
        exact hR₁.2 u v huv
      · simp only [mix, hmem, if_false]
        rw [hswap, if_neg hmem]
        exact hR₀Broad.1.2 u v huv
  have hmixBroad : ∀ A : Finset (Sym2 U),
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) (mix A) := by
    intro A
    induction A using Finset.induction with
    | empty =>
        obtain ⟨-, i, j, h, k, hij, hhk, hnd, hmeet, hmeet'⟩ := hR₀Broad
        refine ⟨hmixChoice ∅, i, j, h, k, hij, hhk, hnd, ?_, ?_⟩
        · simpa [mix] using hmeet
        · simpa [mix] using hmeet'
    | @insert e A he ih =>
        apply broad_of_single_edge_change G J hJ S N hSN F f₁ fn hf₁ hfn
          (mix A) (mix (insert e A)) (hmixChoice (insert e A)) e
        · intro u v huv hne
          simp [mix, hne]
        · exact ih
        · exact hclaim4
  obtain ⟨-, i, j, h, k, hij, hhk, hnd, hmeet, hmeet'⟩ := hmixBroad J.edgeFinset
  refine ⟨hR₁, i, j, h, k, hij, hhk, hnd, ?_, ?_⟩
  · have hedge : s(i, j) ∈ J.edgeFinset := by simpa using hij
    simpa [mix, hedge] using hmeet
  · have hedge : s(h, k) ∈ J.edgeFinset := by simpa using hhk
    simpa [mix, hedge] using hmeet'

end Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesBroad
