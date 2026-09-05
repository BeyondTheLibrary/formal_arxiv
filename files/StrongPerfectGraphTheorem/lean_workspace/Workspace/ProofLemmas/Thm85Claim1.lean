import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.Statements.S08.Thm_8_3
import Workspace.Statements.S08.Thm_8_4

/-!
# 8.5, claim (1)

PAPER (printed p. 42, proof of 8.5):

*"(1) For every choice of rungs, forming `L(H)` say:*

*• for each `y ∈ F`, the set of neighbours of `y` does not saturate `L(H)`, and*

*• if `J = K₄` then `L(H)` is not degenerate.*

*For no `y ∈ F` is major with respect to the strip system, and no `J`-enlargement has a
nondegenerate appearance in `G`, and if `J = K₄` then there is no overshadowed appearance of `J`
in `G`, so the first claim follows from 8.4.  For the second claim, assume `J = K₄`; then by
hypothesis, the strip system is not degenerate, and the claim follows from 8.3.  This proves
(1)."*

The two bullets are transcribed with the encoding 8.4 already uses: the vertices of `L(H)` are
the *edges* of `H`, so "the set of neighbours of `y`" is read across the identification
`φ : H.lineGraph ≃g G.induce K` as the set of edges `e` of `H` with `φ e` adjacent to `y` in
`G`, and "does not saturate `L(H)`" is the negation of `Appearances.SaturatesLineGraph`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm85Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT

/-- **Claim (1) of the proof of 8.5** (printed p. 42).

`F` is the connected set of the statement of 8.5 (no member of it major), and `R` is an
arbitrary choice of rungs, forming `L(H)` on the vertex set `K`. -/
theorem thm85Claim1 {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H')
    (hK₄ : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) →
      NondegenerateStripSystem G J S N ∧
      ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V) (φ : H.lineGraph ≃g G.induce K'),
          IsAppearance G J H K' ∧ IsOvershadowedAppearance G H K' φ)
    (F : Set V) (hF : F ⊆ (stripSystemVertices J S)ᶜ)
    (hFmajor : ∀ f ∈ F, ¬ MajorForStripSystem G J S N f)
    (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    (hK : K = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v})
    (hforms : FormsLineGraph G J S N R H) :
    (∀ y ∈ F, ¬ SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
    (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H) := by
  constructor
  · -- PAPER: *"for each `y ∈ F`, the set of neighbours of `y` does not saturate `L(H)`"*,
    -- which *"follows from 8.4"*.
    intro y hy hsat
    have hy' : y ∉ stripSystemVertices J S := hF hy
    rcases Workspace.Statements.S08.SPGT.thm_8_4 G hG J hJ S N hSN
        (fun h => (hK₄ h).1) y hy' (G.neighborSet y) rfl
        ⟨n, H, R, K, φ, hK, hforms, hsat⟩ with h1 | h2 | h3
    · -- 8.4's first outcome says `y` is major, contrary to hypothesis.
      refine hFmajor y hy ⟨hy', ?_⟩
      intro u
      have hset :
          {v : U | J.Adj u v ∧
              ¬ (stripSystemNuv S N u v ⊆
                    G.neighborSet y ∩ stripSystemVertices J S)}
            = {v : U | J.Adj u v ∧ ¬ (stripSystemNuv S N u v ⊆ G.neighborSet y)} := by
        ext v
        constructor
        · rintro ⟨hadj, hnot⟩
          refine ⟨hadj, fun hsub => hnot ?_⟩
          exact Set.subset_inter hsub (fun x hx =>
            StripSystemBasics.strip_subset_vertices hadj
              (StripSystemBasics.Nuv_subset_strip hx))
        · rintro ⟨hadj, hnot⟩
          exact ⟨hadj, fun hsub => hnot (hsub.trans Set.inter_subset_left)⟩
      rw [hset]
      exact h1 u
    · -- 8.4's second outcome is a `J`-enlargement with a nondegenerate appearance.
      exact hnoenl h2
    · -- 8.4's third outcome is an overshadowed appearance of `K₄`.
      exact (hK₄ h3.1).2 h3.2
  · -- PAPER: *"For the second claim, assume `J = K₄`; then by hypothesis, the strip system is
    -- not degenerate, and the claim follows from 8.3."*
    intro hk4
    exact Workspace.Statements.S08.SPGT.thm_8_3 G hG J hJ S N hSN (hK₄ hk4).1 (hK₄ hk4).2
      n H R hforms

end Workspace.ProofLemmas.Thm85Claim1
