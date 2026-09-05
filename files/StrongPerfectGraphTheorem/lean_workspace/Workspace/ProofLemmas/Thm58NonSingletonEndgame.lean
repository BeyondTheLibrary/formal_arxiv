import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm58Setup
import Workspace.ProofLemmas.Thm58LocalCases

/-!
# The remaining non-singleton case analysis in 5.8

This file isolates the part of the printed proof that begins with claim (2) and ends with the
exhaustion of the two local attachment sets.  The reduction before this point is proved in the
main theorem from smaller helpers.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm58NonSingletonEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (proof of 5.8, printed pp. 26--28): *"But (2)--(7) cover all the possibilities for
the local sets `X₁` and `X₂`, and so this proves 5.8."*

Its hypotheses are exactly the state used from claim (2) onward: `F` is the vertex set of the
induced path `P`, `F` has at least two vertices, and the attachment sets of `F \ {p₂}` and
`F \ {p₁}` are local.  The four case lemmas used below are the remaining proof gaps. -/
theorem thm58NonSingletonEndgame
    (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (F : Set V) (hFK : F ⊆ Kᶜ)
    (hnotlocal : ¬ LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G F K})
    (P : List V) (p₁ p₂ : V)
    (hP : IsPathFrom G P p₁ p₂) (hPF : {x : V | x ∈ P} = F)
    (hlocal₁ : LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₂}) K})
    (hlocal₂ : LocalForLineGraph H
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
        (↑(φ ⟨e, he⟩) : V) ∈ attachments G (F \ {p₁}) K})
    (hcard : 2 ≤ F.ncard) :
    Thm58Setup.Outcome G n H K φ N P p₁ p₂ ∨
      Thm58Setup.Outcome G n H K φ N P.reverse p₂ p₁ := by
  have hready : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂ :=
    ⟨hG, hJ, hsub, hN, hFK, hnotlocal, hP, hPF, hcard⟩
  rcases hlocal₁ with ⟨c₁, hc₁, hX₁⟩ | ⟨q₁, hq₁, hX₁⟩
  · rcases hlocal₂ with ⟨c₂, hc₂, hX₂⟩ | ⟨q₂, hq₂, hX₂⟩
    · exact Thm58LocalCases.starStar
        (G := G) (m := m) (J := J) (n := n) (H := H) (K := K) (φ := φ) (N := N) (F := F)
        (P := P) (p₁ := p₁) (p₂ := p₂) hready c₁ c₂ hc₁ hc₂ hX₁ hX₂
    · exact Or.inl <| Thm58LocalCases.starBranch
        (G := G) (m := m) (J := J) (n := n) (H := H) (K := K) (φ := φ) (N := N) (F := F)
        (P := P) (p₁ := p₁) (p₂ := p₂) hready c₁ hc₁ q₂ hq₂ hX₁ hX₂
  · rcases hlocal₂ with ⟨c₂, hc₂, hX₂⟩ | ⟨q₂, hq₂, hX₂⟩
    · exact Thm58LocalCases.branchStar
        (G := G) (m := m) (J := J) (n := n) (H := H) (K := K) (φ := φ) (N := N) (F := F)
        (P := P) (p₁ := p₁) (p₂ := p₂) hready q₁ hq₁ c₂ hc₂ hX₁ hX₂
    · exact Or.inl <| Thm58LocalCases.branchBranch
        (G := G) (m := m) (J := J) (n := n) (H := H) (K := K) (φ := φ) (N := N) (F := F)
        (P := P) (p₁ := p₁) (p₂ := p₂) hready q₁ q₂ hq₁ hq₂ hX₁ hX₂

end Workspace.ProofLemmas.Thm58NonSingletonEndgame
