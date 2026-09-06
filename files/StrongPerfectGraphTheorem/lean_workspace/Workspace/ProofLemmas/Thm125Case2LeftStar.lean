import Workspace.ProofLemmas.Thm125Case2Prelude
import Workspace.Statements.S11.Thm_11_4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The 11.4 step inside case (2) of Theorem 12.5

PAPER (printed p. 79, case (2) of 12.5): *"Hence `t` is `Q`-complete, and in
particular, all of `q₁,…,q_k` have neighbours in the interior of `R₀`.  By 11.4 it
follows that `Q` contains a left-star, which must be `q₁`."*

The module discharges exactly that sentence: 11.4 is applied to the strip
`S = (A, C, B)`, the connected set `F = R₀*` (the interior of the old banister)
and the anticonnected set `Q = {q₁,…,q_k}`.  The vertex `t` supplied by the
previous step gives the bullet *"every vertex in `Q` has a neighbour in `F`"*;
the remaining bullets come from the ends of the banister and from the
diagonality hypotheses.  Since 11.4 forbids such a configuration when no vertex
of `Q` is a left-star, some vertex of `Q` is one, and every vertex of `Q` other
than `q₁` is right-diagonal, hence has a neighbour in `B`, hence is not a
left-star.  So `q₁` is the left-star.
-/

namespace Workspace.ProofLemmas.Thm125Case2LeftStar

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the asymmetric endpoint case of 12.5, the left endpoint is a left-star.

PAPER: *"By 11.4 it follows that `Q` contains a left-star, which must be `q₁`."* -/
theorem leftStar
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀)
    (t : V) (htint : t ∈ interior R₀)
    (htQ : VertexComplete G t {z : V | z ∈ q}) :
    IsLeftStar G A C B q₁ := by
  classical
  by_contra hnleft
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS : StepConnected G A C B := hstair.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hstair.2.1
  have hR₀len : 4 ≤ R₀.length := by
    have hlen := hstair.2.2
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    omega

  -- `F` is the interior `R₀*` of the old banister: connected, and with no edges
  -- to `V(S)` because `a₀-R₀-b₀` is a banister.
  let F : Set V := {z : V | z ∈ interior R₀}
  let Q : Set V := {z : V | z ∈ q}
  have hFconn : ConnectedSet G F :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathGlue.isPathFrom_interior hban.1.1 (by omega)).1
  have hFant : Anticomplete G F (A ∪ B ∪ C) := by
    simpa [F] using hban.2.2.2.2
  have hFsub : F ⊆ (A ∪ B ∪ C)ᶜ := by
    intro z hz
    exact hban.2.1 z (Workspace.ProofLemmas.PathBasics.interior_subset hz)

  -- The two ends of the banister have neighbours in `F` (its first and last
  -- interior vertices).
  let fL : V := R₀[1]'(by omega)
  let fR : V := R₀[R₀.length - 2]'(by omega)
  have hfLF : fL ∈ F :=
    Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1
      (k := 1) (by omega) (by omega) (by omega)
  have hfRF : fR ∈ F :=
    Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1
      (k := R₀.length - 2) (by omega) (by omega) (by omega)
  have ha₀fL : G.Adj a₀ fL := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hban.1.1 (i := 0) (by omega)
    have h0 : R₀[0]'(by omega) = a₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
    simpa [fL, h0] using h
  have hb₀fR : G.Adj b₀ fR := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hban.1.1
      (i := R₀.length - 2) (by omega)
    have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
    have he : R₀[R₀.length - 2 + 1]'(by omega) = b₀ := by
      calc
        R₀[R₀.length - 2 + 1]'(by omega) = R₀[R₀.length - 1]'(by omega) := by
          congr 1 <;> omega
        _ = b₀ := hl
    exact he ▸ h.symm

  -- `Q` is anticonnected (it is the vertex set of an antipath) and disjoint from
  -- `V(S) ∪ F` (its vertices are diagonal, hence outside the staircase).
  have hQanti : AnticonnectedSet G Q :=
    Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      hq.1
  have hQsub : Q ⊆ ((A ∪ B ∪ C) ∪ F)ᶜ := by
    intro z hz hmem
    have hzout := outside_of_mem hq hqint hq₁.1 hqk.1 hz
    rcases hmem with hzS | hzF
    · exact hzout (Or.inr hzS)
    · exact hzout (Or.inl (Workspace.ProofLemmas.PathBasics.interior_subset hzF))

  -- `a₀` is `Q`-complete: `q₁` is adjacent to it by the hypothesis of case (2),
  -- and every other vertex of the antipath is right-diagonal, hence `a₀`-adjacent.
  have ha₀Q : VertexComplete G a₀ Q := by
    intro z hz
    by_cases hz₁ : z = q₁
    · simpa [hz₁] using hqa₀.symm
    · exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 a₀
        (Or.inr rfl)).symm

  -- `q₁` has a nonneighbour in `B`, for otherwise it would be right-diagonal.
  have hBmiss : ∃ b ∈ B, ¬ G.Adj q₁ b := by
    by_contra hno
    push_neg at hno
    exact hq₁.2 ⟨hq₁.1.1, by
      rintro x (hxB | rfl)
      · exact hno x hxB
      · exact hqa₀⟩

  -- Every vertex of `Q` has a neighbour in `V(S)`: `q₁` is left-diagonal, hence
  -- `A`-complete, and the others are right-diagonal, hence `B`-complete.
  have hQstripNbr : ∀ z ∈ Q, ∃ w ∈ A ∪ B ∪ C, G.Adj z w := by
    intro z hz
    by_cases hz₁ : z = q₁
    · obtain ⟨a, haA⟩ := hS.2.1.1
      exact ⟨a, Or.inl (Or.inl haA), by subst z; exact hq₁.1.2 a (Or.inl haA)⟩
    · obtain ⟨b, hbB⟩ := hS.2.1.2
      exact ⟨b, Or.inl (Or.inr hbB),
        (rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 b (Or.inl hbB)⟩

  -- No vertex of `Q` is a left-star: `q₁` is not one by the assumption we are
  -- refuting, and any other vertex of `Q` is right-diagonal, so it has a
  -- neighbour in `B`, while a left-star is anticomplete to `B ∪ C`.
  have hQnoLeft : ∀ z ∈ Q, ¬ IsLeftStar G A C B z := by
    intro z hz hstar
    by_cases hz₁ : z = q₁
    · exact hnleft (hz₁ ▸ hstar)
    · obtain ⟨b, hbB⟩ := hS.2.1.2
      exact hstar.2.2 b (Or.inl hbB)
        ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 b (Or.inl hbB))

  -- PAPER: *"By 11.4 it follows that `Q` contains a left-star"* — 11.4 says that
  -- the configuration just assembled cannot exist.
  refine Workspace.Statements.S11.SPGT.thm_11_4 G hG hK4 hprism A C B hS F hFsub
    hFconn hFant ⟨Q, hQsub, hQanti, ?_, ?_, ?_, ?_, hQstripNbr, hQnoLeft⟩
  · -- *"some right-star has a neighbour in `F` and a nonneighbour in `Q`"*:
    -- the right end `b₀` of the banister, whose nonneighbour is `qk`.
    exact ⟨b₀, hban.2.2.2.1, ⟨fR, hfRF, hb₀fR⟩,
      qk, Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2,
      fun h => hqkb₀ h.symm⟩
  · -- *"some vertex in `B` has a nonneighbour in `Q`"*: the `B`-nonneighbour of `q₁`.
    obtain ⟨b, hbB, hqb⟩ := hBmiss
    exact ⟨b, hbB, q₁, Workspace.ProofLemmas.PathBasics.head_mem hq.2.1,
      fun h => hqb h.symm⟩
  · -- *"some left-star with a neighbour in `F` is `Q`-complete"*: the left end `a₀`.
    exact ⟨a₀, hban.2.2.1, ⟨fL, hfLF, ha₀fL⟩, ha₀Q⟩
  · -- *"every vertex in `Q` has a neighbour in `F`"* — this is the printed
    -- *"all of `q₁,…,q_k` have neighbours in the interior of `R₀`"*, witnessed by
    -- the `Q`-complete vertex `t` of `R₀*`.
    exact fun z hz => ⟨t, htint, (htQ z hz).symm⟩

end Workspace.ProofLemmas.Thm125Case2LeftStar
