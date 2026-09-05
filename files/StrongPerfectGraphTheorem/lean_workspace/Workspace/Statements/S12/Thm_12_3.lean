import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm123Minimal
import Workspace.ProofLemmas.Thm123Body
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry

/-!
# Section 12 — Attachments in a staircase

The five numbered statements 12.1–12.5 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published/Annals version, printed pages 69–77),
transcribed from `paper/pdf/S12_Attachments_in_a_staircase.md`.

All the defined terms used here are imported and never restated: *step-connected strip*,
*left-star*, *right-star*, *banister*, *1-breaker*, *staircase*, `V(K)`, *maximal*, *local*,
*minor*, *major*, *left-diagonal*, *right-diagonal*, *central*, *strongly maximal* and
*2-breaker* come
from `Workspace.Types.Staircases`; *even prism* from `Workspace.Types.Prisms`; *attachment*,
*appearance* from `Workspace.Types.Appearances`; *Berge*, *connected set*, *antipath*,
*interior*, *complete*/*anticomplete* from `Workspace.Types.Core`; *balanced skew partition*
from `Workspace.Types.Decompositions`.

Encoding conventions (see `paper/spec/CONVENTIONS.md`):

* a staircase `K = (S = (A, C, B), a₀-R₀-b₀)` is carried by the six pieces of data
  `A C B : Set V`, `a₀ : V`, `R₀ : List V`, `b₀ : V`, in the paper's order; `V(S)` is
  `A ∪ B ∪ C` and `V(K)` is `staircaseVertices A C B R₀`;
* a path/antipath is the list of its vertices in order, `V(R)` for such a list `R` is
  `{v | v ∈ R}`, and `R₀ \ a₀` is `{x | x ∈ R₀ ∧ x ≠ a₀}`;
* *"`F` contains a path `u`-`R`-`v`"* is: `R` is a path of `G` from `u` to `v` all of whose
  vertices lie in `F`;
* *"there are no edges between `X` and `Y`"* is `SPGT.Anticomplete G X Y`;
* *"there is no appearance of `K₄` in `G`"* is `¬ Appears G (⊤ : SimpleGraph (Fin 4))`;
  *"no even prism in `G`"* is: no three paths of `G` form an even prism; *"no 1-breaker
  (2-breaker) in `G`"* is the negated existential over the data of a 1-breaker (2-breaker).

Published-vs-draft note: case 1 of **12.1** is the published one, *"`v` is minor; and in that
case, either `v` is a left-star or `v` is not `A`-complete, and either `v` is a right-star or
`v` is not `B`-complete"*; the arXiv v1 draft has only *"`v` is minor"*.
-/

set_option autoImplicit false

namespace Workspace.Statements.S12

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*}

/-- Transport a banister obtained after exchanging the two ends of the staircase back to the
published orientation. -/
private theorem banister_of_swapped {G : SimpleGraph V} {A C B : Set V} {u v : V}
    {R : List V} (h : IsBanister G B C A u R v) :
    IsBanister G A C B v R.reverse u := by
  obtain ⟨hpath, hout, hleft, hright, hanti⟩ := h
  refine ⟨Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hpath, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hwR : w ∈ R := List.mem_reverse.mp hw
    simpa [Set.union_comm A B] using hout w hwR
  · exact
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isRightStar_swap.mp hright
  · exact
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.isLeftStar_swap.mp hleft
  · intro w hw
    have hwR := Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hw
    simpa [Set.union_comm A B] using hanti w hwR

variable [Fintype V] [DecidableEq V]


/-- **12.3** (printed p. 73), introduced by *"The previous result can be strengthened as
follows."*

PAPER: *"Let `G` be a Berge graph, such that there is no appearance of `K₄` in `G`, no even
prism in `G`, and no 1-breaker in `G`.  Let `K = (S = (A, C, B), a₀`-`R₀`-`b₀)` be a maximal
staircase in `G`, and let `F ⊆ V(G) \ V(S)` be connected, containing a left-star and with an
attachment in `B ∪ C`.  (Note that `F` may intersect `V(R₀)`.)  Then `F` contains either a
major vertex or a banister."*

Notes on the transcription.

* Here `F` avoids `V(S) = A ∪ B ∪ C` only — **not** `V(K)`; the parenthetical *"(Note that `F`
  may intersect `V(R₀)`.)"* is a remark pointing this out, and so is deliberately not a
  hypothesis.
* *"with an attachment in `B ∪ C`"*: some vertex of `B ∪ C` has a neighbour in `F`, i.e. the
  set of attachments of `F` in `B ∪ C` is nonempty. -/
theorem thm_12_3 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (hFS : F ⊆ (A ∪ B ∪ C)ᶜ) (hFconn : ConnectedSet G F)
    (hFstar : ∃ u ∈ F, IsLeftStar G A C B u)
    (hFatt : (attachments G F (B ∪ C)).Nonempty) :
    (∃ w ∈ F, MajorForStaircase G A C B a₀ R₀ b₀ w) ∨
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G A C B u R v) := by
  -- PAPER: *"We may assume there is no major vertex in `F`."*  If there is one, the first
  -- alternative of the conclusion already holds.
  by_cases hmaj : ∃ w ∈ F, MajorForStaircase G A C B a₀ R₀ b₀ w
  · exact Or.inl hmaj
  refine Or.inr ?_
  -- PAPER: *"We may assume `F` is minimal …; so `F` is the vertex set of a path `f₁`-…-`f_k`,
  -- where `f₁` is the unique left-star in `F`, and `f_k` is the only vertex in `F` with a
  -- neighbour in `B ∪ C`.  Since `f₁` is a left-star and `f_k` has a neighbour in `B ∪ C` it
  -- follows that `k ≥ 2`."*
  have hCand : Workspace.ProofLemmas.Thm123Minimal.Cand G A C B F :=
    ⟨hFS, hFconn, hFstar, hFatt⟩
  obtain ⟨F', f, f₁, fk, hsub, hmin, hFf, hpath, hlen, horient⟩ :=
    Workspace.ProofLemmas.Thm123Minimal.thm123Minimal G A C B F hCand
  rcases horient with
    ⟨hCand', hstar, hstaruniq, hatt, hattuniq⟩ |
      ⟨hCand', hstar, hstaruniq, hatt, hattuniq⟩
  · -- The selected set has the displayed orientation.
    have hnomaj : ∀ w ∈ F', ¬ MajorForStaircase G A C B a₀ R₀ b₀ w := by
      intro w hw hw'
      exact hmaj ⟨w, hsub hw, hw'⟩
    have hS : Workspace.ProofLemmas.Thm123Body.Setup G A C B a₀ R₀ b₀ F' f f₁ fk :=
      ⟨hCand', hmin, hFf, hpath, hlen, hstar, hstaruniq, hatt, hattuniq, hnomaj⟩
    obtain ⟨u, v, R, hRF', hban⟩ :=
      Workspace.ProofLemmas.Thm123Body.thm123Body G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK
        F' f f₁ fk hS
    exact ⟨u, v, R, fun w hw => hsub (hRF' w hw), hban⟩
  · -- The whole argument is run after exchanging `A` and `B`.
    have hKswap : MaximalStaircase G B C A b₀ R₀.reverse a₀ :=
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.maximalStaircase_swap.mp hK
    have hminswap :
        ∀ F'' ⊆ F',
          (Workspace.ProofLemmas.Thm123Minimal.Cand G B C A F'' ∨
            Workspace.ProofLemmas.Thm123Minimal.Cand G A C B F'') → F'' = F' := by
      intro F'' hF'' hor
      exact hmin F'' hF'' (hor.elim Or.inr Or.inl)
    have hnomaj : ∀ w ∈ F', ¬ MajorForStaircase G B C A b₀ R₀.reverse a₀ w := by
      intro w hw hw'
      exact hmaj ⟨w, hsub hw,
        Workspace.ProofLemmas.StaircaseLeftRightSymmetry.majorForStaircase_swap.mpr hw'⟩
    have hS : Workspace.ProofLemmas.Thm123Body.Setup G B C A b₀ R₀.reverse a₀ F' f f₁ fk :=
      ⟨hCand', hminswap, hFf, hpath, hlen, hstar, hstaruniq, hatt, hattuniq, hnomaj⟩
    obtain ⟨u, v, R, hRF', hban⟩ :=
      Workspace.ProofLemmas.Thm123Body.thm123Body G hG hK4 hprism hbreaker B C A b₀ a₀
        R₀.reverse hKswap F' f f₁ fk hS
    exact ⟨v, u, R.reverse, fun w hw => hsub (hRF' w (List.mem_reverse.mp hw)),
      banister_of_swapped hban⟩


end SPGT

end Workspace.Statements.S12
