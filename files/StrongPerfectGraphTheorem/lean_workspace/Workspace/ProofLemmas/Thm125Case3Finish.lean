import Workspace.ProofLemmas.Thm125Case3Core
import Workspace.ProofLemmas.Thm125Case3Adjoin
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.Statements.S12.Thm_12_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Finishing case (3) of Theorem 12.5

An endpoint neighbour in the wrong end class gives the crossed-pair enlargement, contrary
to maximality.  With neither such neighbour, the published trichotomy 12.1 makes the two
endpoints stars.  Left--right symmetry handles the opposite wrong endpoint.
-/

namespace Workspace.ProofLemmas.Thm125Case3Finish

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem staircaseVertices_swap (A C B : Set V) (R : List V) :
    staircaseVertices B C A R.reverse = staircaseVertices A C B R := by
  ext z
  simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
  tauto

theorem leftDiagonal_swap
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ v : V} {R₀ : List V} :
    LeftDiagonal G A C B a₀ R₀ b₀ v ↔
      RightDiagonal G B C A b₀ R₀.reverse a₀ v := by
  constructor
  · rintro ⟨hout, hc⟩
    exact ⟨by rwa [staircaseVertices_swap], hc⟩
  · rintro ⟨hout, hc⟩
    exact ⟨by rwa [staircaseVertices_swap] at hout, hc⟩

theorem rightDiagonal_swap
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ v : V} {R₀ : List V} :
    RightDiagonal G A C B a₀ R₀ b₀ v ↔
      LeftDiagonal G B C A b₀ R₀.reverse a₀ v := by
  constructor
  · rintro ⟨hout, hc⟩
    exact ⟨by rwa [staircaseVertices_swap], hc⟩
  · rintro ⟨hout, hc⟩
    exact ⟨by rwa [staircaseVertices_swap] at hout, hc⟩

/-- In the orientation where `qk` has an `A`-neighbour, the crossed pair enlarges the
strongly maximal staircase. -/
private theorem oriented_contra
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (h2breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' : V)
      (Q' : Set V), IsTwoBreaker G A' C' B' a₀' R₀' b₀' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : ¬ G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀)
    (aneigh : V) (haneighA : aneigh ∈ A) (hqkaneigh : G.Adj qk aneigh) : False := by
  obtain ⟨a₁, ha₁A, b₁, hb₁B, hqka₁, hq₁b₁, ha₁b₁, hqshape,
      hq₁int, hqkint⟩ :=
    Workspace.ProofLemmas.Thm125Case3Core.core G hG hprism h2breaker
      A C B a₀ b₀ R₀ hK q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀
      aneigh haneighA hqkaneigh
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hqnon : ¬ G.Adj q₁ qk := by
    have hc : Gᶜ.Adj q₁ qk := by
      have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hq.1 (i := 0) (by
        rw [hqshape]
        simp)
      simpa [hqshape] using h
    exact ((G.compl_adj q₁ qk).1 hc).2
  have hnew := Workspace.ProofLemmas.Thm125Case3Adjoin.staircase_adjoin_diagonal_pair
    G A C B a₀ b₀ R₀ qk q₁ a₁ b₁ hK.1.1
      hqk.1.1 hq₁.1.1 hne.symm (fun h => hqnon h.symm)
      (fun b hb => hqk.1.2 b (Or.inl hb))
      (fun a ha => hq₁.1.2 a (Or.inl ha))
      ha₁A hb₁B hqka₁ hq₁b₁ ha₁b₁
      (hqk.1.2 a₀ (Or.inr rfl)) hqkb₀ hqa₀
      (hq₁.1.2 b₀ (Or.inr rfl)) hqkint hq₁int
  apply hK.1.2
  refine ⟨A ∪ {qk}, C, B ∪ {q₁}, a₀, R₀, b₀, hnew,
    Set.subset_union_left, Set.subset_union_left, Set.Subset.rfl, ?_⟩
  constructor
  · intro z hz
    rcases hz with (hzA | hzB) | hzC
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr (Or.inl hzB))
    · exact Or.inr hzC
  · intro hback
    have hqknew : qk ∈ (A ∪ {qk}) ∪ (B ∪ {q₁}) ∪ C :=
      Or.inl (Or.inl (Or.inr rfl))
    exact hqk.1.1 (Or.inr (hback hqknew))

/-- Case (3) of the printed proof: both displayed endpoint--banister pairs are nonedges. -/
theorem case3
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (h2breaker : ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R₀' : List V) (b₀' : V)
      (Q' : Set V), IsTwoBreaker G A' C' B' a₀' R₀' b₀' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hqa₀ : ¬ G.Adj q₁ a₀) (hqkb₀ : ¬ G.Adj qk b₀) :
    IsLeftStar G A C B q₁ ∧ IsRightStar G A C B qk := by
  classical
  by_cases hkA : ∃ a ∈ A, G.Adj qk a
  · obtain ⟨a, haA, hka⟩ := hkA
    exact (oriented_contra G hG hprism h2breaker A C B a₀ b₀ R₀ hK
      q q₁ qk hq hqint hq₁ hqk hqa₀ hqkb₀ a haA hka).elim
  push_neg at hkA
  by_cases h₁B : ∃ b ∈ B, G.Adj q₁ b
  · obtain ⟨b, hbB, h₁b⟩ := h₁B
    have hKswap :=
      Workspace.ProofLemmas.StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hK
    have hqrev : IsAntipathFrom G q.reverse qk q₁ :=
      Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq
    have hqintSwap : ∀ w ∈ interior q.reverse,
        LeftDiagonal G B C A b₀ R₀.reverse a₀ w ∧
          RightDiagonal G B C A b₀ R₀.reverse a₀ w := by
      intro w hw
      have ho := hqint w (Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hw)
      exact ⟨rightDiagonal_swap.mp ho.2, leftDiagonal_swap.mp ho.1⟩
    have hqkSwap : LeftDiagonal G B C A b₀ R₀.reverse a₀ qk ∧
        ¬ RightDiagonal G B C A b₀ R₀.reverse a₀ qk :=
      ⟨rightDiagonal_swap.mp hqk.1, fun h => hqk.2 (leftDiagonal_swap.mpr h)⟩
    have hq₁Swap : RightDiagonal G B C A b₀ R₀.reverse a₀ q₁ ∧
        ¬ LeftDiagonal G B C A b₀ R₀.reverse a₀ q₁ :=
      ⟨leftDiagonal_swap.mp hq₁.1, fun h => hq₁.2 (rightDiagonal_swap.mpr h)⟩
    exact (oriented_contra G hG hprism h2breaker B C A b₀ a₀ R₀.reverse hKswap
      q.reverse qk q₁ hqrev hqintSwap hqkSwap hq₁Swap hqkb₀ hqa₀
      b hbB h₁b).elim
  push_neg at h₁B
  have hleft : IsLeftStar G A C B q₁ := by
    obtain ⟨j, hj, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 hprism
      hbreaker A C B a₀ b₀ R₀ hK.1 q₁ hq₁.1.1
    fin_cases j
    · rcases hj.2.1 with h | hnA
      · exact h
      · exact (hnA (fun a ha => hq₁.1.2 a (Or.inl ha))).elim
    · obtain ⟨b, hbB, hqb⟩ := hj.1.2.2.1
      exact (h₁B b hbB hqb).elim
    · rcases hj with h | h
      · exact h.1
      · obtain ⟨b, hbB⟩ := hK.1.1.1.2.1.2
        exact (h₁B b hbB (h.1.2.1 b hbB)).elim
  have hright : IsRightStar G A C B qk := by
    obtain ⟨j, hj, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1 G hG hK4 hprism
      hbreaker A C B a₀ b₀ R₀ hK.1 qk hqk.1.1
    fin_cases j
    · rcases hj.2.2 with h | hnB
      · exact h
      · exact (hnB (fun b hb => hqk.1.2 b (Or.inl hb))).elim
    · obtain ⟨a, haA, hqa⟩ := hj.1.2.1
      exact (hkA a haA hqa).elim
    · rcases hj with h | h
      · obtain ⟨a, haA⟩ := hK.1.1.1.2.1.1
        exact (hkA a haA (h.1.2.1 a haA)).elim
      · exact h.1
  exact ⟨hleft, hright⟩

end Workspace.ProofLemmas.Thm125Case3Finish
