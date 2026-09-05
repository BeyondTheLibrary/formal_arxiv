import Workspace.ProofLemmas.Thm132Claim1
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Optimal banisters in the proof of 13.2 have length one

The paper obtains this from minimality of the counterexample.  There is a
slightly more direct finite-descent argument: if an optimal banister had length
at least three, it could replace the distinguished banister without changing
either maximality condition.  Claim (1), applied at the birth of its left end,
would then say that this same banister is not optimal.  Statement 11.3 supplies
oddness and rules out length two.
-/

namespace Workspace.ProofLemmas.Thm132OptimalLength

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132Reduction
open Workspace.ProofLemmas.Thm132Claim1

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every optimal banister (for the fixed strip and right-sequence occurring in
13.2) is an edge. -/
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
    {a b : V} {R : List V}
    (hopt : BOptimalBanister G A C B x a R b) :
    pathLength R = 1 := by
  classical
  obtain ⟨i, hi, hbirth⟩ := exists_birth hopt.1.2.2.1 hopt.2.1
  have hbirth' := hbirth
  obtain ⟨-, -, i', hi', hi'eq, hnon, hbefore⟩ := hbirth'
  have hi'i : i' = i :=
    (List.Nodup.getElem_inj_iff hx.1.1).mp hi'eq
  subst i'
  have hbad : ¬ G.Adj x[i] a := fun hadj => hnon hadj.symm
  have hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a := by
    intro j hj
    exact (hbefore j hj).symm
  by_contra hne
  have hodd : Odd (pathLength R) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a b R hopt.1).2
  have hge : 3 ≤ pathLength R := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK' : StronglyMaximalStaircase G A C B a R b := by
    refine ⟨⟨⟨hK.1.1.1, hopt.1, hge⟩, hK.1.2⟩, hK.2⟩
  have hvstar := first_bad_isRightStar hG hK4 heven h1br h2br hK' hx i hi hprev hbad
  exact (initial_banister_not_optimal hG hK4 heven h1br h2br hK' hx
    i hi hprev hbad hvstar) hopt

end Workspace.ProofLemmas.Thm132OptimalLength
