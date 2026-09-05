import Workspace.ProofLemmas.Thm131Singleton
import Workspace.ProofLemmas.Thm132Reduction
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Optimal banisters in 13.1 have length one

The induction hypothesis for a strict prefix supplies claim (4) of the paper.
If the current optimal banister were long, it could itself be used as the
distinguished strongly maximal staircase.  Its birth then produces exactly
the singleton configuration ruled out by that claim.
-/

namespace Workspace.ProofLemmas.Thm131OptimalLength

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131Singleton
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132Reduction

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the induction used for 13.1, every optimal banister for the current
right-sequence is an edge. -/
theorem optimal_banister_length_one
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
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z)
    {a b : V} {R : List V}
    (hopt : BOptimalBanister G A C B x a R b) :
    pathLength R = 1 := by
  classical
  obtain ⟨i, hi, hbirth⟩ := exists_birth hopt.1.2.2.1 hopt.2.1
  obtain ⟨-, -, i', hi', hi'eq, hnon, hbefore⟩ := hbirth
  have hi'i : i' = i :=
    (List.Nodup.getElem_inj_iff hx.1.1).mp hi'eq
  subst i'
  by_contra hne
  have hodd : Odd (pathLength R) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a b R hopt.1).2
  have hge : 3 ≤ pathLength R := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK' : StronglyMaximalStaircase G A C B a R b := by
    exact ⟨⟨⟨hK.1.1.1, hopt.1, hge⟩, hK.1.2⟩, hK.2⟩
  have hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a := by
    intro j hj
    exact (hbefore j hj).symm
  have hbad : ¬ G.Adj x[i] a := fun hadj => hnon hadj.symm
  have hvstar := first_bad_isRightStar hG hK4 heven h1br h2br
    hK' hx i hi hprev hbad
  exact singleton_long_optimal_absurd hG hK4 heven h1br h2br
    hK' hx hopt i hi hbefore hnon hvstar hIH

end Workspace.ProofLemmas.Thm131OptimalLength
