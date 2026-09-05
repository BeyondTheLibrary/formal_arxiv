/-  Proof attempt for statement 9.4 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  Reproduces the printed proof
    (`paper/proofs/9_4.md`, printed p. 51) step for step, through
    `Workspace.ProofLemmas.Thm94Body`. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.Thm94Body

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S09

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **9.4** (printed p. 51)

PAPER: *"Let `G` be Berge, such that there is no appearance in `G` or in `Ḡ` of any
`K₄`-enlargement, and there is no overshadowed appearance of `K₄` in `G` or in `Ḡ`.  Let `L`
be a maximal striation in `G`.  Let `f ∈ V(G) \ V(L)`, and let `X` be the set of neighbours of
`f` in `V(L)`.  Then either `X` is local with respect to `L`, or `X` resolves `L`."*

Notes on the transcription.

* A *striation* `L` is the pair of families `S : Fin m → Set V × Set V × Set V` (the strips)
  and `T : Fin n → Set V × Set V × Set V` (the antistrips); `V(L)` is
  `Knots.striationVertices S T`, and *maximal* is `Knots.MaximalStriation`, which (unlike
  `MaximalStripSystem` in §8) already includes being a striation.
* *"The set of neighbours of `f` in `V(L)`"* is `G.neighborSet f ∩ V(L)`.
* *"Local with respect to `L`"* and *"resolves `L`"* are `Knots.LocalForStriation` and
  `Knots.ResolvesStriation` — the striation notions, not the knot ones. -/
theorem thm_9_4 (G : SimpleGraph V) (hG : Berge G)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (m n : ℕ) (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hL : MaximalStriation G S T)
    (f : V) (hf : f ∉ striationVertices S T)
    (X : Set V) (hX : X = G.neighborSet f ∩ striationVertices S T) :
    LocalForStriation G S T X ∨ ResolvesStriation G S T X := by
  subst hX
  -- PAPER: *"Let `L` have strips `Sᵢ = (Aᵢ, Cᵢ, Bᵢ)` and antistrips `Tⱼ = (Xⱼ, Zⱼ, Yⱼ)`."*
  have hsetup : Thm94Body.Setup G S T f := ⟨hG, hnoenl, hnoover, hnoovercompl, hL, hf⟩
  -- PAPER: *"From (1), taking complements if necessary, we may assume that for all
  -- `1 ≤ j ≤ n`, and for all `Tⱼ`-antirungs `Qⱼ`, `V(Qⱼ) ⊄ X`."*
  by_cases hanti : ∀ (j : Fin n) (Q : List V), IsSRung Gᶜ (T j) Q →
      ∃ v ∈ Q, v ∉ G.neighborSet f ∩ striationVertices S T
  · -- the assumption holds: claim (2) and the closing paragraph give that `X` is local
    exact Or.inl (Thm94Body.localForStriation_of_antirungs hsetup hanti)
  · -- otherwise some antirung lies inside `X`, and claim (1) forces the other alternative for
    -- every rung; the argument is then rerun in `Ḡ` with the strips and antistrips exchanged,
    -- which is exactly what *"taking complements if necessary"* licenses.
    right
    push_neg at hanti
    obtain ⟨j₀, Q₀, hQ₀, hsub⟩ := hanti
    -- PAPER, claim (1): *"either `X ∩ V(Pᵢ) ≠ ∅`, or `V(Qⱼ) ⊄ X`"* — the second alternative
    -- is now impossible, so every `Sᵢ`-rung meets `X`.
    have hmeet : ∀ (i : Fin m) (P : List V), IsSRung G (S i) P →
        ∃ v ∈ P, v ∈ G.neighborSet f ∩ striationVertices S T := by
      intro i P hP
      rcases Thm94Body.claim1 hsetup i j₀ P Q₀ hP hQ₀ with h | ⟨v, hv, hvn⟩
      · exact h
      · exact absurd (hsub v hv) hvn
    have hsc : Thm94Body.Setup Gᶜ T S f := Thm94Body.setup_compl hsetup
    have hXsub : G.neighborSet f ∩ striationVertices S T ⊆ striationVertices S T :=
      Set.inter_subset_right
    have hkey : LocalForStriation Gᶜ T S (Gᶜ.neighborSet f ∩ striationVertices T S) := by
      refine Thm94Body.localForStriation_of_antirungs hsc ?_
      intro i P hP
      have hP' : IsSRung G (S i) P := by rwa [compl_compl] at hP
      obtain ⟨v, hv, hvX⟩ := hmeet i P hP'
      refine ⟨v, hv, ?_⟩
      rw [StriationCompl.striationVertices_swap S T,
        StriationCompl.compl_neighborSet_inter hf]
      exact fun hc => hc.2 hvX
    rw [StriationCompl.striationVertices_swap S T,
      StriationCompl.compl_neighborSet_inter hf] at hkey
    exact (StriationCompl.resolves_iff_local_compl hL.1 hXsub).mpr hkey


end SPGT

end Workspace.Statements.S09
