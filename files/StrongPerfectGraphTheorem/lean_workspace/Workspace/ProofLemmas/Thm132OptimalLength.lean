import Workspace.ProofLemmas.Thm132Claim1
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Optimal banisters in the proof of 13.2 have length one

PAPER (13.2, printed p. 84): *"From the minimality of `t` (replacing `R₀` by `R`) it follows
that `R` has length 1, and so `rb₀` is an edge."*

The printed proof of 13.2 is a minimal counterexample argument: `t` is as small as possible.
Here that is the induction hypothesis `hIH` — the theorem itself for every strictly shorter
right-sequence and every strongly maximal staircase on the same strip.  If the optimal
banister `r`-`R`-`b₀` had length `> 1`, then (its length being odd by 11.3) it would have
length `≥ 3`, so `((A, C, B), r`-`R`-`b₀)` would itself be a strongly maximal staircase —
only the banister has changed, and the strip is untouched.  The birth `x_j` of `r` is a
nonneighbour of `r`, and `j` is earlier than the term of the right-sequence that the printed
proof is working with, so `x₁, …, x_{j+1}` is a strictly shorter right-sequence.  Applying
the induction hypothesis to it and to the new staircase says that all of its terms — `x_j`
among them — are adjacent to `r`, a contradiction.  So `R` has length `1`.
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

/-- PAPER (§13, printed p. 78): *"Any initial subsequence of a right-sequence is therefore
another right-sequence."* -/
theorem isRightSequence_take {G : SimpleGraph V} {A C B : Set V} {x : List V}
    (hx : IsRightSequence G A C B x) (m : ℕ) :
    IsRightSequence G A C B (x.take m) := by
  classical
  have hsub : ∀ (i : ℕ) (hi : i < (x.take m).length),
      ∃ hi' : i < x.length, (x.take m)[i]'hi = x[i]'hi' ∧ (x.take m).take i = x.take i := by
    intro i hi
    have hlem : (x.take m).length ≤ x.length := by
      simpa using (List.length_take_le m x)
    have him : i < m := by
      have : (x.take m).length ≤ m := by simp
      omega
    refine ⟨by omega, by simp, ?_⟩
    rw [List.take_take]
    congr 1
    omega
  refine ⟨⟨List.Nodup.sublist (List.take_sublist m x) hx.1.1,
    fun v hv => hx.1.2 v (List.mem_of_mem_take hv)⟩, ?_, ?_⟩
  · intro i hi hA
    obtain ⟨hi', hget, htake⟩ := hsub i hi
    rw [hget] at hA ⊢
    obtain ⟨y, hy, hny⟩ := hx.2.1 i hi' hA
    exact ⟨y, by rw [htake]; exact hy, hny⟩
  · intro i hi hA
    obtain ⟨hi', hget, htake⟩ := hsub i hi
    rw [hget] at hA ⊢
    obtain ⟨r, R, hban, y, hy, hny⟩ := hx.2.2 i hi' hA
    exact ⟨r, R, hban, y, by rw [htake]; exact hy, hny⟩

/-- Every optimal banister occurring in the proof of 13.2 is an edge.

PAPER: *"From the minimality of `t` (replacing `R₀` by `R`) it follows that `R` has length 1,
and so `rb₀` is an edge."*  The minimality of `t` is `hIH`; `x[j]` is the birth of the left
end `a` of the optimal banister, and `hjlast` says that it is not the last term of the
right-sequence, which is what *"replacing `R₀` by `R`"* needs in order to shorten the
sequence. -/
theorem optimal_banister_length_one
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    {a b : V} {R : List V}
    (hopt : BOptimalBanister G A C B x a R b)
    (j : ℕ) (hj : j < x.length) (hbirth : birth G A C B x a (x[j]'hj))
    (hjlast : j + 1 < x.length)
    (hIH : ∀ y : List V, y.length < x.length → IsRightSequence G A C B y →
      ∀ (a' b' : V) (R' : List V), StronglyMaximalStaircase G A C B a' R' b' →
      ∀ v ∈ y, G.Adj v a') :
    pathLength R = 1 := by
  classical
  obtain ⟨-, -, i, hi, hieq, hnon, -⟩ := hbirth
  have hij : i = j := (List.Nodup.getElem_inj_iff hx.1.1).mp hieq
  subst i
  by_contra hne
  -- 11.3: the banister is odd, so if it is not an edge it has length at least three.
  have hodd : Odd (pathLength R) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a b R hopt.1).2
  have hge : 3 ≤ pathLength R := by
    obtain ⟨k, hk⟩ := hodd
    omega
  -- *"replacing `R₀` by `R`"*: only the banister changes, so the new pair is again a
  -- strongly maximal staircase on the same strip.
  have hK' : StronglyMaximalStaircase G A C B a R b :=
    ⟨⟨⟨hK.1.1.1, hopt.1, hge⟩, hK.1.2⟩, hK.2⟩
  -- The shorter right-sequence `x₁, …, x_{j+1}`.
  have hylen : (x.take (j + 1)).length < x.length := by
    simp only [List.length_take]
    omega
  have hmem : x[j] ∈ x.take (j + 1) := by
    have hjt : j < (x.take (j + 1)).length := by
      simp only [List.length_take]
      omega
    have : (x.take (j + 1))[j]'hjt = x[j] := by simp
    exact this ▸ List.getElem_mem hjt
  -- *"the minimality of `t`"*: every term of the shorter sequence is adjacent to the new
  -- left end `a`.  But the birth of `a` is a nonneighbour of `a`.
  exact hnon (hIH (x.take (j + 1)) hylen (isRightSequence_take hx (j + 1)) a b R hK'
    x[j] hmem).symm

end Workspace.ProofLemmas.Thm132OptimalLength
