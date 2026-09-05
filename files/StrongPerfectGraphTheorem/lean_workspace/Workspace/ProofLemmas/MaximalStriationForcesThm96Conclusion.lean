/-  Proof of the 9.6 leaf `MaximalStriationForcesThm96Conclusion`: the body of the printed
    proof of 9.6 (claims (1), (2), (3) and the closing paragraph), assembled in the paper's
    own order from `Workspace.ProofLemmas.Thm96Body`. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Statements.S09.Thm_9_1
import Workspace.Statements.S09.Thm_9_5
import Workspace.Statements.S04.Thm_4_1
import Workspace.Statements.S04.Thm_4_2
import Workspace.ProofLemmas.Thm96Assembly
import Workspace.ProofLemmas.Thm96Body

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.MaximalStriationForcesThm96Conclusion

open Workspace.Types.Core.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions.SPGT

theorem maximalStriationForcesThm96Conclusion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (hG : Berge G)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧
        (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance Gᶜ H K' φ)
    (hcard : 8 ≤ Nat.card V)
    (m n : ℕ)
    (S : Fin m → Set V × Set V × Set V)
    (T : Fin n → Set V × Set V × Set V)
    (hmax : MaximalStriation G S T)
    (M N : Set V)
    (hpartition : M ∪ N = (striationVertices S T)ᶜ)
    (hdisjoint : Disjoint M N)
    (hMlocal : ∀ v ∈ M,
      LocalForStriation G S T (G.neighborSet v ∩ striationVertices S T))
    (hNresolves : ∀ v ∈ N,
      ResolvesStriation G S T (G.neighborSet v ∩ striationVertices S T)) :
    IsDoubleSplitGraph G ∨
      AdmitsBalancedSkewPartition G ∨
      (AdmitsProper2Join G ∨ AdmitsProper2Join Gᶜ) ∨
      (¬ Appears G (⊤ : SimpleGraph (Fin 4)) ∧
        ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4))) := by
  -- The standing hypotheses at the point where the printed proof reaches claim (1).
  have hsetup : Thm96Body.Setup G S T M N :=
    ⟨hG, hnoenl, hnoover, hnoovercompl, hcard, hmax, hpartition, hdisjoint,
      hMlocal, hNresolves⟩
  show Thm96Assembly.Concl G
  -- PAPER: *"(1) If there exists `f ∈ N` with a nonneighbour in `V(S₁) ∪ ⋯ ∪ V(S_m)` then the
  -- theorem holds."*
  by_cases hc1 : ∃ f ∈ N, ∃ u ∈ (⋃ i : Fin m, stripVertices (S i)), ¬ G.Adj f u
  · exact Thm96Body.claim1 hsetup hc1
  · -- PAPER: *"… and by taking complements, that `M` is anticomplete to
    -- `V(T₁) ∪ ⋯ ∪ V(T_n)`."*  This is claim (1) read in `Ḡ` with the strips and the
    -- antistrips — and hence `M` and `N` — exchanged.
    by_cases hc1' : ∃ f ∈ M, ∃ u ∈ (⋃ j : Fin n, stripVertices (T j)), ¬ Gᶜ.Adj f u
    · exact Thm96Assembly.concl_compl
        (Thm96Body.claim1 (Thm96Body.setup_compl hsetup) hc1')
    · -- PAPER: *"From (1) we may assume that `N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`, and by
      -- taking complements, that `M` is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`."*
      have hbal : Thm96Body.Balanced G S T M N := by
        push_neg at hc1 hc1'
        refine ⟨hc1, fun f hf u hu hadj => ?_⟩
        exact ((SimpleGraph.compl_adj G f u).mp (hc1' f hf u hu)).2 hadj
      rcases Set.eq_empty_or_nonempty M with hM | hM
      · rcases Set.eq_empty_or_nonempty N with hN | hN
        -- PAPER: *"(3) If `M, N` are both empty then the theorem holds."*
        · exact Thm96Body.claim3 hsetup hbal hM hN
        -- PAPER: *"From (2) and (3), and taking complements if necessary, we may assume that
        -- `N` is empty and `M` is nonempty."*  Here it is `M` that is empty, so the closing
        -- paragraph is run in `Ḡ`.
        · exact Thm96Assembly.concl_compl
            (Thm96Body.closing (Thm96Body.setup_compl hsetup)
              (Thm96Body.balanced_compl hsetup hbal) hM hN)
      · rcases Set.eq_empty_or_nonempty N with hN | hN
        -- PAPER: the closing paragraph, *"`N` is empty and `M` is nonempty"*.
        · exact Thm96Body.closing hsetup hbal hN hM
        -- PAPER: *"(2) If `M, N` are both nonempty then the theorem holds."*
        · exact Thm96Body.claim2 hsetup hbal hM hN

end Workspace.ProofLemmas.MaximalStriationForcesThm96Conclusion
