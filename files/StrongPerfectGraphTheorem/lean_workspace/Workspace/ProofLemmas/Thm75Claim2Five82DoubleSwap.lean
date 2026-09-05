import Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
import Workspace.ProofLemmas.Thm75Claim2Five82Dominance
import Workspace.ProofLemmas.PathBasics

/-!
# The two changed cliques in 7.5 claim (2)

PAPER (printed p. 38): *"Consequently all vertices of Y are B'-dominant with respect to
L(H'). We claim also that Y is still maximal."*

Once both old clique remainders are common neighbours of `Y`, dominance follows by deleting
the two new ends. For maximality, apply claim (1) in the new appearance to a proposed larger
set, then transfer its complete clique remainders back to the old appearance.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82DoubleSwap

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas.Thm75Claim2Five82AppearanceData
open Workspace.ProofLemmas.Thm75Claim2Five82Dominance

/-- PAPER: *"r'₁ has no neighbour in T, and in particular every vertex in Nc₁ \\ {r₁} is
in X"*. A vertex of the old clique remainder outside `X` would be in `T`. -/
theorem clique_remainder_subset_of_no_T {V : Type*} (G : SimpleGraph V)
    (N K Rset X X₁ T : Set V) (r p : V) (hNK : N ⊆ K)
    (hr : N ∩ Rset = {r}) (hX₁ : X₁ ⊆ X) (hT : T = (K \ Rset) \ X₁)
    (hp : ∀ x ∈ N \ {r}, G.Adj p x) (hpT : ∀ x ∈ T, ¬ G.Adj p x) :
    N \ {r} ⊆ X := by
  intro x hx
  by_contra hxX
  have hxR : x ∉ Rset := by
    intro hxR
    exact hx.2 (hr ▸ (show x ∈ N ∩ Rset from ⟨hx.1, hxR⟩))
  have hxT : x ∈ T := by
    rw [hT]
    exact ⟨⟨hNK hx.1, hxR⟩, fun h => hxX (hX₁ h)⟩
  exact hpT x hxT (hp x hx)

/-- The dominance and maximality part of the same-branch case, once both old clique
remainders are common neighbours of `Y`. -/
theorem dominance_and_maximality_of_double_swap {V U : Type*}
    [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (N₁ N₂ K Rset T F Y : Set V) (a : BranchAppearance G J)
    (d : SameBranchReplacementData G N₁ N₂ K Rset T F a)
    (hN₁K : N₁ ⊆ K) (hN₂K : N₂ ⊆ K)
    (hFK : ∀ x ∈ F, x ∉ K) (hFX : ∀ x ∈ F, ¬ VertexComplete G x Y)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G N₁ N₂ y) → Y' = Y)
    (h₁ : ∀ x ∈ N₁ \ {d.r₁}, VertexComplete G x Y)
    (h₂ : ∀ x ∈ N₂ \ {d.r₂}, VertexComplete G x Y) :
    (∀ y ∈ Y, IsDominantFor G a.leftClique a.rightClique y) ∧
      (∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
        (∀ y ∈ Y', IsDominantFor G a.leftClique a.rightClique y) → Y' = Y) := by
  have hp₁F := d.hPF d.p₁ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).1
  have hp₂F := d.hPF d.p₂ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem d.hP).2
  have hp₁N : d.p₁ ∈ a.leftClique := by rw [d.hleft]; exact Or.inr rfl
  have hp₂N : d.p₂ ∈ a.rightClique := by rw [d.hright]; exact Or.inr rfl
  have hrem₁ : ∀ x ∈ a.leftClique \ {d.p₁}, VertexComplete G x Y := by
    rintro x ⟨hx, hxp⟩
    rw [d.hleft] at hx
    exact h₁ x (hx.resolve_right hxp)
  have hrem₂ : ∀ x ∈ a.rightClique \ {d.p₂}, VertexComplete G x Y := by
    rintro x ⟨hx, hxp⟩
    rw [d.hright] at hx
    exact h₂ x (hx.resolve_right hxp)
  refine ⟨dominant_of_complete_remainders G a.leftClique a.rightClique Y
    d.p₁ d.p₂ hrem₁ hrem₂, ?_⟩
  intro Y' hYY' hY'anti hY'dom
  have hsmall := a.cliques_diff_complete_subsingleton hG hJ Y' (hYne.mono hYY') hY'anti hY'dom
  have hc₁ := complete_remainder_of_missing_end G a.leftClique Y Y' d.p₁ hYY' hp₁N
    (hFX d.p₁ hp₁F) hsmall.1
  have hc₂ := complete_remainder_of_missing_end G a.rightClique Y Y' d.p₂ hYY' hp₂N
    (hFX d.p₂ hp₂F) hsmall.2
  apply hYmax Y' hYY' hY'anti
  apply dominant_of_complete_remainders G N₁ N₂ Y' d.r₁ d.r₂
  · intro x hx
    apply hc₁ x
    refine ⟨?_, ?_⟩
    · rw [d.hleft]
      exact Or.inl hx
    · intro hxp
      exact hFK d.p₁ hp₁F (hxp ▸ hN₁K hx.1)
  · intro x hx
    apply hc₂ x
    refine ⟨?_, ?_⟩
    · rw [d.hright]
      exact Or.inl hx
    · intro hxp
      exact hFK d.p₂ hp₂F (hxp ▸ hN₂K hx.1)

end Workspace.ProofLemmas.Thm75Claim2Five82DoubleSwap
