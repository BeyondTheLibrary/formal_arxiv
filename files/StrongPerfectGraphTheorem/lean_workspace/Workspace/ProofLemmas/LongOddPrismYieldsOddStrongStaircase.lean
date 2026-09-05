import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismYieldsStaircase
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.Statements.S07.Thm_7_2

set_option autoImplicit false

namespace Workspace.ProofLemmas.LongOddPrismYieldsOddStrongStaircase

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

theorem longOddPrismYieldsOddStrongStaircase
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hprism : ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsLongPrism G s t R₁ R₂ R₃ ∧ IsOddPrism G s t R₁ R₂ R₃)
    (hevenG : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (hevenGc : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism Gᶜ s t R₁ R₂ R₃) :
    ∃ (H : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V),
      (H = G ∨ H = Gᶜ) ∧
      StronglyMaximalStaircase H A C B a₀ R₀ b₀ ∧
      Odd (pathLength R₀) ∧
      3 ≤ pathLength R₀ := by
  classical
  obtain ⟨s, t, R₁, R₂, R₃, hlong, hoddPrism⟩ := hprism
  have hpar := Workspace.Statements.S07.SPGT.thm_7_2
    G hG s t R₁ R₂ R₃ hlong.1
  have hodd₁ : Odd (pathLength R₁) := Nat.not_even_iff_odd.mp (by
    intro he₁
    exact hoddPrism.2 ⟨he₁, hpar.1.mp he₁, hpar.2.mp he₁⟩)
  have hodd₂ : Odd (pathLength R₂) := Nat.not_even_iff_odd.mp (by
    intro he₂
    have he₁ : Even (pathLength R₁) := hpar.1.mpr he₂
    exact hoddPrism.2 ⟨he₁, he₂, hpar.2.mp he₁⟩)
  have hodd₃ : Odd (pathLength R₃) := Nat.not_even_iff_odd.mp (by
    intro he₃
    have he₁ : Even (pathLength R₁) := hpar.2.mpr he₃
    exact hoddPrism.2 ⟨he₁, hpar.1.mp he₁, he₃⟩)
  have hinitial : ∃ (A C B : Set V) (a₀ b₀ : V) (R₀ : List V),
      IsStaircase G A C B a₀ R₀ b₀ := by
    rcases hlong.2 with hlong₁ | hlong₂ | hlong₃
    · have hthree : 3 ≤ pathLength R₁ := by
        obtain ⟨q, hq⟩ := hodd₁
        omega
      obtain ⟨A, C, B, hstairs⟩ :=
        Workspace.ProofLemmas.PrismYieldsStaircase.exists_isStaircase_of_formPrism
          (R := ![R₁, R₂, R₃]) hlong.1
          (k := (0 : Fin 3)) (i := (1 : Fin 3)) (j := (2 : Fin 3))
          (by decide) (by decide) (by decide) (by simpa using hthree)
      exact ⟨A, C, B, s 0, t 0, R₁, by simpa using hstairs⟩
    · have hthree : 3 ≤ pathLength R₂ := by
        obtain ⟨q, hq⟩ := hodd₂
        omega
      obtain ⟨A, C, B, hstairs⟩ :=
        Workspace.ProofLemmas.PrismYieldsStaircase.exists_isStaircase_of_formPrism
          (R := ![R₁, R₂, R₃]) hlong.1
          (k := (1 : Fin 3)) (i := (0 : Fin 3)) (j := (2 : Fin 3))
          (by decide) (by decide) (by decide) (by simpa using hthree)
      exact ⟨A, C, B, s 1, t 1, R₂, by simpa using hstairs⟩
    · have hthree : 3 ≤ pathLength R₃ := by
        obtain ⟨q, hq⟩ := hodd₃
        omega
      obtain ⟨A, C, B, hstairs⟩ :=
        Workspace.ProofLemmas.PrismYieldsStaircase.exists_isStaircase_of_formPrism
          (R := ![R₁, R₂, R₃]) hlong.1
          (k := (2 : Fin 3)) (i := (0 : Fin 3)) (j := (1 : Fin 3))
          (by decide) (by decide) (by decide) (by simpa using hthree)
      exact ⟨A, C, B, s 2, t 2, R₃, by simpa using hstairs⟩

  -- Choose a staircase whose strip vertex set has maximum cardinality among staircases in
  -- `G` and in `Gᶜ`.  This one choice simultaneously gives ordinary maximality in its
  -- ambient graph and the extra complement clause in strong maximality.
  set ℳ : Set ℕ :=
    {n | ∃ (H : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V),
      (H = G ∨ H = Gᶜ) ∧ IsStaircase H A C B a₀ R₀ b₀ ∧
        (A ∪ B ∪ C).ncard = n} with hℳ
  have hℳne : ℳ.Nonempty := by
    obtain ⟨A, C, B, a₀, b₀, R₀, hstairs⟩ := hinitial
    exact ⟨(A ∪ B ∪ C).ncard, G, A, C, B, a₀, b₀, R₀,
      Or.inl rfl, hstairs, rfl⟩
  have hℳbdd : BddAbove ℳ := by
    refine ⟨Fintype.card V, ?_⟩
    rintro n ⟨H, A, C, B, a₀, b₀, R₀, -, -, rfl⟩
    exact Workspace.ProofLemmas.ExtremalChoice.ncard_le_card _
  obtain ⟨H, A, C, B, a₀, b₀, R₀, hHG, hstairs, hcard⟩ : sSup ℳ ∈ ℳ :=
    Nat.sSup_mem hℳne hℳbdd
  have hmaxCard : ∀ (H' : SimpleGraph V) (A' C' B' : Set V)
      (a₀' b₀' : V) (R₀' : List V),
      (H' = G ∨ H' = Gᶜ) → IsStaircase H' A' C' B' a₀' R₀' b₀' →
        (A' ∪ B' ∪ C').ncard ≤ (A ∪ B ∪ C).ncard := by
    intro H' A' C' B' a₀' b₀' R₀' hH' hstairs'
    have hmem : (A' ∪ B' ∪ C').ncard ∈ ℳ :=
      ⟨H', A', C', B', a₀', b₀', R₀', hH', hstairs', rfl⟩
    have hle := le_csSup hℳbdd hmem
    simpa [hcard] using hle
  have hmaximal : MaximalStaircase H A C B a₀ R₀ b₀ := by
    refine ⟨hstairs, ?_⟩
    rintro ⟨A', C', B', a₀', R₀', b₀', hstairs', -, -, -, hstrict⟩
    have hle := hmaxCard H A' C' B' a₀' b₀' R₀' hHG hstairs'
    have hlt : (A ∪ B ∪ C).ncard < (A' ∪ B' ∪ C').ncard :=
      Set.ncard_lt_ncard hstrict (Set.toFinite _)
    omega
  have hstrong : StronglyMaximalStaircase H A C B a₀ R₀ b₀ := by
    refine ⟨hmaximal, ?_⟩
    by_cases hC : C.Nonempty
    · exact Or.inl hC
    · refine Or.inr ?_
      rintro ⟨A', C', B', a₀', R₀', b₀', hstairs', hstrict⟩
      have hcompl : Hᶜ = G ∨ Hᶜ = Gᶜ := by
        rcases hHG with rfl | rfl
        · exact Or.inr rfl
        · exact Or.inl (by simp)
      have hle := hmaxCard Hᶜ A' C' B' a₀' b₀' R₀' hcompl hstairs'
      have hlt : (A ∪ B ∪ C).ncard < (A' ∪ B' ∪ C').ncard :=
        Set.ncard_lt_ncard hstrict (Set.toFinite _)
      omega
  have hHBerge : Berge H := by
    rcases hHG with rfl | rfl
    · exact hG
    · exact Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hNoEvenH : ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
      IsEvenPrism H alpha beta P₁ P₂ P₃ := by
    rcases hHG with rfl | rfl
    · exact hevenG
    · exact hevenGc
  obtain ⟨v, hvA⟩ := hstairs.1.2.1.1
  obtain ⟨a₁, Q₁, b₁, a₂, Q₂, b₂, hstep, -⟩ :=
    hstairs.1.2.2.2.1 v (Or.inl (Or.inl hvA))
  have hbanOdd :=
    Workspace.ProofLemmas.StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism
      H A C B a₀ b₀ a₁ b₁ a₂ b₂ R₀ Q₁ Q₂
      hstairs hstep hHBerge hNoEvenH
  exact ⟨H, A, C, B, a₀, b₀, R₀, hHG, hstrong, hbanOdd.2.1, hstairs.2.2⟩

end Workspace.ProofLemmas.LongOddPrismYieldsOddStrongStaircase
