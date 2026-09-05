import Workspace.ProofLemmas.Thm132AdjoinBanister
import Workspace.ProofLemmas.Thm132Reduction
import Workspace.Statements.S13.Thm_13_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Claim (1) of 13.2

At the first term of a right-sequence missing the staircase's left end, the
reduction lemma says that term is a right-star.  Consequently the trajectory
of the old left-star is the singleton trajectory ending at that term.  The
13.1 dichotomy, optimal-banister separation, parity attachment, and strict
strip enlargement then prove that the staircase banister was not optimal.
-/

namespace Workspace.ProofLemmas.Thm132Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation
open Workspace.ProofLemmas.Thm132BanisterAttachment
open Workspace.ProofLemmas.Thm132AdjoinBanister

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER claim (1): the distinguished banister is not `b₀`-optimal. -/
theorem initial_banister_not_optimal
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    (i : ℕ) (hi : i < x.length)
    (hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a₀)
    (hbad : ¬ G.Adj x[i] a₀)
    (hvstar : IsRightStar G A C B x[i]) :
    ¬ BOptimalBanister G A C B x a₀ R₀ b₀ := by
  classical
  intro hopt
  let v : V := x[i]
  have hS : StepConnected G A C B := hK.1.1.1
  have hP : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have haLeft : IsLeftStar G A C B a₀ := hP.2.2.1
  have hbRight : IsRightStar G A C B b₀ := hP.2.2.2.1
  have hvRight : IsRightStar G A C B v := by simpa [v] using hvstar
  obtain ⟨a₁, ha₁⟩ := hS.2.1.1
  obtain ⟨b₁, hb₁⟩ := hS.2.1.2
  have ha_not_mem_x : a₀ ∉ x := by
    intro hax
    have haB := hx.1.2 a₀ hax
    exact haLeft.2.2 b₁ (Or.inl hb₁) (haB b₁ hb₁)
  have ha_not_complete : ¬ VertexComplete G a₀ {z : V | z ∈ x} := by
    intro hac
    exact hbad (hac v (by simp [v, hi])).symm
  have hav : ¬ G.Adj a₀ v := fun h => hbad (by simpa [v] using h.symm)
  have htrajIndex : trajectoryOfIndex G A x i [v] := by
    refine ⟨⟨by simp, ?_⟩, ?_, ?_⟩
    · simp [v, hi]
    · exact ⟨v, by simp, a₁, ha₁,
        hvRight.2.2 a₁ (Or.inl ha₁)⟩
    · intro j hj
      simp at hj
  have htraj : trajectoryOfVertex G A x a₀ [a₀, v] := by
    refine ⟨⟨haLeft.2.1, ha_not_mem_x, ha_not_complete⟩,
      i, hi, [v], ⟨?_, ?_⟩, htrajIndex, rfl⟩
    · exact hav
    · intro k hk
      exact (hprev k hk).symm
  have h13 := Workspace.Statements.S13.SPGT.thm_13_1
    G hG hK4 heven h1br h2br A C B a₀ b₀ R₀ hK x hx b₀ hbRight
      a₀ R₀ hopt [v] (by simpa using htraj)
  have hunique : ∀ z ∈ R₀,
      (VertexComplete G z {u : V | u ∈ [v]} ↔ z = b₀) := by
    rcases h13.2 with h | h
    · exact h
    · have hlen : 3 ≤ pathLength R₀ := hK.1.1.2.2
      exact absurd h.1 (by omega : pathLength R₀ ≠ 1)
  have hvonly : ∀ z ∈ R₀, (G.Adj z v ↔ z = b₀) := by
    intro z hz
    simpa [VertexComplete] using hunique z hz

  -- Axiom 3 supplies the earlier-born banister ending at the right-star `v`.
  have hvAntiA : VertexAnticomplete G v A := by
    intro z hz
    exact hvRight.2.2 z (Or.inl hz)
  obtain ⟨r, Q, hQ, y, hyTake, hry⟩ := hx.2.2 i hi hvAntiA
  have hryX : y ∈ x := List.mem_of_mem_take hyTake
  have hr_not_complete : ¬ VertexComplete G r {z : V | z ∈ x} := by
    intro hrc
    exact hry (hrc y hryX)
  obtain ⟨j, hj, hbirthR⟩ := exists_birth hQ.2.2.1 hr_not_complete
  have hbirthR' := hbirthR
  obtain ⟨-, -, j', hj', hj'eq, -, hbeforeR⟩ := hbirthR'
  have hj'j : j' = j :=
    (List.Nodup.getElem_inj_iff hx.1.1).mp hj'eq
  subst j'
  have hbirthP : birth G A C B x a₀ v := by
    refine ⟨haLeft, ha_not_complete, i, hi, rfl, hav, ?_⟩
    intro k hk
    exact (hprev k hk).symm
  obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hyTake
  have hki : k < i := by
    have hklen : k < (x.take i).length := hk
    simp only [List.length_take] at hklen
    omega
  have hkx : (x.take i)[k]'hk = x[k]'(by omega) := by
    simp only [List.getElem_take]
  have hjle : j ≤ k := by
    by_contra hjk
    have hkj : k < j := by omega
    have hrk := hbeforeR k hkj
    apply hry
    rw [← hky, hkx]
    exact hrk
  have hji : j < i := lt_of_le_of_lt hjle hki
  have hearlier : Earlier x x[j] v :=
    ⟨j, i, hj, hi, rfl, by simp [v], hji⟩
  have hnolink := optimal_halves_not_linked hS.2.1.1 hopt hQ hbirthR hbirthP hearlier
  have hdisj := banisters_disjoint_of_halves_not_linked hS.2.1.1 hP hQ hnolink
  have haonly := left_end_sees_exactly_left_end hG heven hS hP hQ hav hvonly hnolink hdisj
  exact attached_banister_contradicts_maximality hK.1 hQ hdisj hvonly haonly hnolink

end Workspace.ProofLemmas.Thm132Claim1
