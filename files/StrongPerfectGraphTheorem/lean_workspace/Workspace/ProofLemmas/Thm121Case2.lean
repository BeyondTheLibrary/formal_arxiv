import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.Thm121Case1
import Workspace.ProofLemmas.Thm121MinorCriteria
import Workspace.ProofLemmas.Thm121Symmetry
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.Statements.S11.Thm_11_1
import Workspace.Statements.S11.Thm_11_3

/-!
# 12.1, case (2) of the printed proof

PAPER (printed p. 69): *"(2) If `v` is adjacent to both `a₀, b₀` then the theorem holds.*

*For then it has a neighbour in `R₀*`, since `R₀` is odd and has length `≥ 3` and `v` is
adjacent to both its ends; and we may assume that `v` has a neighbour in `V(S)`, for otherwise
statement 1 of the theorem holds.  If `v` has no neighbour in `B` then it is a left-star by
11.1, and statement 3 of the theorem holds, so we may assume it has neighbours in `B` and
similarly in `A`.  Hence it is major.  Since `(S, V(R₀*), {v})` is not a 1-breaker, `v` does not
have nonneighbours in both `A` and `B`, so it is either left- or right-diagonal and the claim
follows from (1).  This proves (2)."*

The results cited are 11.1, the hypothesis that `G` has no 1-breaker, and case (1)
(`Workspace.ProofLemmas.Thm121Case1`).  *"`R₀` is odd"* is 11.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm121Case2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

section Helpers

variable {V : Type*}

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx (q : List V) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- A one-element set is connected. -/
private theorem connectedSet_singleton (G : SimpleGraph V) (v : V) :
    SPGT.ConnectedSet G ({v} : Set V) := by
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

end Helpers

/-- **12.1 (2)**: *"If `v` is adjacent to both `a₀, b₀` then the theorem holds."* -/
theorem thm121Case2 {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (ha : G.Adj v a₀) (hb : G.Adj v b₀) :
    (MinorForStaircase G A C B a₀ R₀ b₀ v ∧
        (IsLeftStar G A C B v ∨ ¬ SPGT.VertexComplete G v A) ∧
        (IsRightStar G A C B v ∨ ¬ SPGT.VertexComplete G v B)) ∨
      (MajorForStaircase G A C B a₀ R₀ b₀ v ∧
        (LeftDiagonal G A C B a₀ R₀ b₀ v ∨ RightDiagonal G A C B a₀ R₀ b₀ v ∨
          CentralForStaircase G A C B a₀ R₀ b₀ v)) ∨
      ((IsLeftStar G A C B v ∧ ∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∨
        (IsRightStar G A C B v ∧ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x)) := by
  have hS : StepConnected G A C B := hK.1.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.1.2.1
  have hlen : 3 ≤ SPGT.pathLength R₀ := hK.1.2.2
  have hR₀ : SPGT.IsPathFrom G R₀ a₀ b₀ := hban.1
  have hlenR : R₀.length = SPGT.pathLength R₀ + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hR₀.1
  have hlen4 : 4 ≤ R₀.length := by omega
  have hvS : v ∉ A ∪ B ∪ C := fun h => hv (Or.inr h)
  have hvR₀ : v ∉ R₀ := fun h => hv (Or.inl h)
  have ha₀R₀ : a₀ ∈ R₀ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR₀).1
  have hb₀R₀ : b₀ ∈ R₀ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR₀).2
  have ha₀b₀ : a₀ ≠ b₀ :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hR₀ (by omega)
  have hb₀S : b₀ ∉ A ∪ B ∪ C := hban.2.2.2.1.1
  -- PAPER: *"For then it has a neighbour in `R₀*`, since `R₀` is odd and has length `≥ 3` and
  -- `v` is adjacent to both its ends"* — `R₀` odd is 11.3.
  have hodd : Odd (SPGT.pathLength R₀) :=
    (_root_.Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hS a₀ b₀ R₀ hban).2
  have hRstar : ∃ x ∈ SPGT.interior R₀, G.Adj v x := by
    by_contra hc
    push_neg at hc
    have heven : Even (R₀.length + 1) :=
      Workspace.ProofLemmas.PrismBasics.even_of_path_closed_by_vertex hG hR₀ hlen4 hvR₀ ha hb hc
    rw [Nat.even_iff] at heven
    have hodd' : SPGT.pathLength R₀ % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  -- PAPER: *"and we may assume that `v` has a neighbour in `V(S)`, for otherwise statement 1 of
  -- the theorem holds."*
  by_cases hVS : ∃ x ∈ A ∪ B ∪ C, G.Adj v x
  swap
  · exact Or.inl (Workspace.ProofLemmas.Thm121MinorCriteria.thm121AltOneOfNoStripNeighbour
      G A C B a₀ b₀ R₀ hS v hv (by push_neg at hVS; exact hVS))
  -- 11.1 is stated with the weaker "no *nondegenerate* appearance of `K₄`" hypothesis.
  have hK4' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K, happ, -⟩
    exact hK4 ⟨n, H, K, happ⟩
  -- PAPER: *"If `v` has no neighbour in `B` then it is a left-star by 11.1, and statement 3 of
  -- the theorem holds"*
  by_cases hBn : ∃ y ∈ B, G.Adj v y
  swap
  · push_neg at hBn
    have hvAC : ∃ x ∈ A ∪ C, G.Adj v x := by
      obtain ⟨x, hxS, hvx⟩ := hVS
      rcases hxS with hx | hx
      · rcases hx with hx | hx
        · exact ⟨x, Or.inl hx, hvx⟩
        · exact absurd hvx (hBn x hx)
      · exact ⟨x, Or.inr hx, hvx⟩
    have hls : IsLeftStar G A C B v := by
      refine _root_.Workspace.Statements.S11.SPGT.thm_11_1 G hG hK4' A C B hS a₀ b₀ R₀ hban
        v hvS hvAC hBn [v, b₀] ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hb, rfl, rfl⟩
        ?_ ?_
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rintro (hc | hc)
          · exact hvS hc
          · exact hvR₀ (by rw [(hc : w = a₀)]; exact ha₀R₀)
        · rcases List.mem_cons.mp hw with rfl | hw
          · rintro (hc | hc)
            · exact hb₀S hc
            · exact ha₀b₀ (hc : w = a₀).symm
          · exact absurd hw List.not_mem_nil
      · intro w hw
        simp only [Set.mem_setOf_eq, SPGT.interior] at hw
        simp at hw
    exact Or.inr (Or.inr (Or.inl ⟨hls, b₀, hb₀R₀, ha₀b₀.symm, hb⟩))
  -- PAPER: *"so we may assume it has neighbours in `B` and similarly in `A`."*
  by_cases hAn : ∃ y ∈ A, G.Adj v y
  swap
  · push_neg at hAn
    have hKs : MaximalStaircase G B C A b₀ R₀.reverse a₀ :=
      Workspace.ProofLemmas.Thm121Symmetry.thm121SwapStaircase G A C B a₀ b₀ R₀ hK
    have hS' : StepConnected G B C A := hKs.1.1
    have hban' : IsBanister G B C A b₀ R₀.reverse a₀ := hKs.1.2.1
    have hvS' : v ∉ B ∪ A ∪ C := by
      intro h
      refine hvS ?_
      rcases h with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
      · exact Or.inr h
    have ha₀S : a₀ ∉ B ∪ A ∪ C := by
      intro h
      refine hban.2.2.1.1 ?_
      rcases h with h | h
      · rcases h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inl (Or.inl h)
      · exact Or.inr h
    have hvBC : ∃ x ∈ B ∪ C, G.Adj v x := by
      obtain ⟨x, hxS, hvx⟩ := hVS
      rcases hxS with hx | hx
      · rcases hx with hx | hx
        · exact absurd hvx (hAn x hx)
        · exact ⟨x, Or.inl hx, hvx⟩
      · exact ⟨x, Or.inr hx, hvx⟩
    have hls' : IsLeftStar G B C A v := by
      refine _root_.Workspace.Statements.S11.SPGT.thm_11_1 G hG hK4' B C A hS' b₀ a₀ R₀.reverse
        hban' v hvS' hvBC hAn [v, a₀]
        ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair ha, rfl, rfl⟩ ?_ ?_
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · rintro (hc | hc)
          · exact hvS' hc
          · exact hvR₀ (by rw [(hc : w = b₀)]; exact hb₀R₀)
        · rcases List.mem_cons.mp hw with rfl | hw
          · rintro (hc | hc)
            · exact ha₀S hc
            · exact ha₀b₀ (hc : w = b₀)
          · exact absurd hw List.not_mem_nil
      · intro w hw
        simp only [Set.mem_setOf_eq, SPGT.interior] at hw
        simp at hw
    have hrs : IsRightStar G A C B v := ⟨hvS, hls'.2.1, hls'.2.2⟩
    exact Or.inr (Or.inr (Or.inr ⟨hrs, a₀, ha₀R₀, ha₀b₀, ha⟩))
  -- PAPER: *"Hence it is major."*
  have hmajor : MajorForStaircase G A C B a₀ R₀ b₀ v := ⟨hv, hAn, hBn, ⟨a₀, ha₀R₀, ha⟩⟩
  -- PAPER: *"Since `(S, V(R₀*), {v})` is not a 1-breaker, `v` does not have nonneighbours in
  -- both `A` and `B`, so it is either left- or right-diagonal and the claim follows from (1)."*
  by_cases hAc : SPGT.VertexComplete G v A
  · refine Workspace.ProofLemmas.Thm121Case1.thm121Case1 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀
      hK v hv (Or.inl ⟨hv, ?_⟩)
    rintro y (hy | hy)
    · exact hAc y hy
    · rw [(hy : y = b₀)]; exact hb
  by_cases hBc : SPGT.VertexComplete G v B
  · refine Workspace.ProofLemmas.Thm121Case1.thm121Case1 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀
      hK v hv (Or.inr ⟨hv, ?_⟩)
    rintro y (hy | hy)
    · exact hBc y hy
    · rw [(hy : y = a₀)]; exact ha
  -- both nonneighbour sets are nonempty: `(S, V(R₀*), {v})` is a 1-breaker, contradiction
  exfalso
  have hAnn : ∃ a ∈ A, ¬ G.Adj v a := by
    by_contra hc; push_neg at hc; exact hAc hc
  have hBnn : ∃ b ∈ B, ¬ G.Adj v b := by
    by_contra hc; push_neg at hc; exact hBc hc
  refine hbreaker ⟨A, C, B, {w : V | w ∈ SPGT.interior R₀}, {v}, hS, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact fun w hw => hban.2.1 w (Workspace.ProofLemmas.PathBasics.interior_subset hw)
  · exact Workspace.ProofLemmas.MinimalConnectedIsPath.connectedSet_interior hR₀
  · exact hban.2.2.2.2
  · -- the left-star `a₀` has the neighbour `R₀[1]` in `R₀*`
    refine ⟨a₀, hban.2.2.1, R₀[1]'(by omega), ?_, ?_⟩
    · exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hR₀.1 (by omega) le_rfl
        (by omega)
    · have h0 : R₀[0]'(by omega) = a₀ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR₀.2.1 (by omega)
      have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hR₀.1
        (show 0 + 1 < R₀.length by omega)
      rw [h0] at h
      exact h
  · -- the right-star `b₀` has the neighbour `R₀[|R₀| - 2]` in `R₀*`
    refine ⟨b₀, hban.2.2.2.1, R₀[R₀.length - 2]'(by omega), ?_, ?_⟩
    · exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hR₀.1 (by omega) (by omega)
        (by omega)
    · have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR₀.2.2 (by omega)
      have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hR₀.1
        (show (R₀.length - 2) + 1 < R₀.length by omega)
      have he : R₀[(R₀.length - 2) + 1]'(show (R₀.length - 2) + 1 < R₀.length by omega) = b₀ := by
        rw [gidx R₀ (show (R₀.length - 2) + 1 = R₀.length - 1 by omega) (by omega) (by omega)]
        exact hl
      rw [he] at h
      exact h.symm
  · rintro q rfl
    rintro (hc | hc)
    · exact hvS hc
    · exact hvR₀ (Workspace.ProofLemmas.PathBasics.interior_subset hc)
  · exact connectedSet_singleton Gᶜ v
  · obtain ⟨a, haA, hna⟩ := hAnn
    exact ⟨a, haA, v, rfl, fun hc => hna hc.symm⟩
  · obtain ⟨b, hbB, hnb⟩ := hBnn
    exact ⟨b, hbB, v, rfl, fun hc => hnb hc.symm⟩
  · rintro q rfl
    exact ⟨hRstar, hVS⟩
  · refine ⟨a₀, hban.2.2.1, ⟨R₀[1]'(by omega), ?_, ?_⟩, ?_⟩
    · exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hR₀.1 (by omega) le_rfl
        (by omega)
    · have h0 : R₀[0]'(by omega) = a₀ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR₀.2.1 (by omega)
      have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hR₀.1
        (show 0 + 1 < R₀.length by omega)
      rw [h0] at h
      exact h
    · rintro y rfl
      exact ha.symm
  · rintro q rfl hcls
    obtain ⟨y, hyB, hvy⟩ := hBn
    exact hcls.2.2 y (Or.inl hyB) hvy

end Workspace.ProofLemmas.Thm121Case2
