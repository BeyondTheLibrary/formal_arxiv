import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124Claims
import Workspace.ProofLemmas.Thm124Claim4Part1
import Workspace.ProofLemmas.Thm124Claim4Leap
import Workspace.ProofLemmas.Thm124Claim4LeapQComplete
import Workspace.ProofLemmas.Thm132ComplementStaircase

/-!
# 12.4, claim (4)

PAPER (printed p. 75):

*"There is no edge `uv` of `G \ V(S)` such that `u` is a left-star, `v` is a
right-star, and `u, v` are not `Q`-complete."*

The earlier `Thm124Claim4*` modules prove that such an edge forces `C = ∅` and
produce adjacent vertices `a,b` in the interior of the old banister.  The leap
also gives the adjacencies needed to make `v-q_k-...-q_1-u` a banister in the
complement.  Adjoining `a` and `b` to the two sides of the old strip then gives
a larger staircase in the complement, against strong maximality.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm124Claim4Finish

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **12.4(4).** No edge joins a non-`Q`-complete left-star to a
non-`Q`-complete right-star. -/
theorem claim4 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v) :
    VertexComplete G u Q ∨ VertexComplete G v Q := by
  classical
  by_contra hcon
  obtain ⟨hunc, hvnc⟩ := not_or.mp hcon
  have hC : C = ∅ :=
    ProofAttempts.Thm124Claim4.claim4_C_empty h huv hu hv hunc hvnc
  obtain ⟨a, b, a₁, b₁, q, ha₁A, hb₁B, ha₁b₁, hq, hqQ, hqlen,
      haR, hbR, hab, hleap⟩ :=
    ProofAttempts.Thm124Claim4Leap.leap_exists h huv hu hv hunc hvnc
  obtain ⟨hav, hbv, hbu, hau, hqadj, hanu, hanv, hbnu, hbnv, hqne⟩ :=
    ProofAttempts.Thm124Claim4LeapQComplete.leap_adjacency_package
      h hu hv hq hqlen hqQ haR hbR hleap

  -- With `C = ∅`, the old strip read from right to left is a strip
  -- `(B, ∅, A)`.  The general complement construction adjoins `a,b` and
  -- returns the strip `(A ∪ {a}, ∅, B ∪ {b})` in `Gᶜ`.
  have hSswap : StepConnected G B (∅ : Set V) A := by
    simpa [hC] using (Thm124Setup.Setup.swap h).stepConnected
  have haout : a ∉ B ∪ A := by
    intro haBA
    exact h.outsideStrip a (PathBasics.interior_subset haR)
      (by rcases haBA with haB | haA
          · exact Or.inl (Or.inr haB)
          · exact Or.inl (Or.inl haA))
  have hbout : b ∉ B ∪ A := by
    intro hbBA
    exact h.outsideStrip b (PathBasics.interior_subset hbR)
      (by rcases hbBA with hbB | hbA
          · exact Or.inl (Or.inr hbB)
          · exact Or.inl (Or.inl hbA))
  have haanti : VertexAnticomplete G a (B ∪ A) := by
    intro z hz hadj
    exact h.interiorAnti a haR z
      (by rcases hz with hzB | hzA
          · exact Or.inl (Or.inr hzB)
          · exact Or.inl (Or.inl hzA)) hadj
  have hbanti : VertexAnticomplete G b (B ∪ A) := by
    intro z hz hadj
    exact h.interiorAnti b hbR z
      (by rcases hz with hzB | hzA
          · exact Or.inl (Or.inr hzB)
          · exact Or.inl (Or.inl hzA)) hadj
  have hSnew : StepConnected Gᶜ (A ∪ {a}) (∅ : Set V) (B ∪ {b}) :=
    Thm132ComplementStaircase.stepConnected_compl_adjoin_pair
      G B A a b hSswap haout hbout hab haanti hbanti

  -- The reversed `u`-`Q`-`v` antipath is the new complement banister.
  have hqrev : IsPathFrom Gᶜ q.reverse v u := PathBasics.isPathFrom_reverse hq
  have hqStrip : ∀ z ∈ q, z ∉ A ∪ B ∪ C := by
    intro z hz hzS
    by_cases hzu : z = u
    · exact hu.1 (hzu ▸ hzS)
    by_cases hzv : z = v
    · exact hv.1 (hzv ▸ hzS)
    have hzint : z ∈ SPGT.interior q :=
      (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hz, hzu, hzv⟩
    exact h.notMemQ_of_memStrip z hzS (hqQ z hzint)
  have hqout : ∀ z ∈ q.reverse, z ∉ (A ∪ {a}) ∪ (B ∪ {b}) ∪ (∅ : Set V) := by
    intro z hz hznew
    have hzq : z ∈ q := List.mem_reverse.mp hz
    rcases hznew with ((hzA | hza) | (hzB | hzb)) | hz0
    · exact hqStrip z hzq (Or.inl (Or.inl hzA))
    · exact (hqne z hzq).1 hza.symm
    · exact hqStrip z hzq (Or.inl (Or.inr hzB))
    · exact (hqne z hzq).2 hzb.symm
    · exact Set.notMem_empty z hz0

  have hvleft : IsLeftStar Gᶜ (A ∪ {a}) (∅ : Set V) (B ∪ {b}) v := by
    refine ⟨?_, ?_, ?_⟩
    · intro hvnew
      rcases hvnew with ((hvA | hva) | (hvB | hvb)) | hv0
      · exact hv.1 (Or.inl (Or.inl hvA))
      · exact hanv hva.symm
      · exact hv.1 (Or.inl (Or.inr hvB))
      · exact hbnv hvb.symm
      · exact Set.notMem_empty v hv0
    · intro z hz
      rw [SimpleGraph.compl_adj]
      rcases hz with hzA | hza
      · exact ⟨fun he => hv.1 (Or.inl (Or.inl (he ▸ hzA))), hv.2.2 z (Or.inl hzA)⟩
      · subst z
        exact ⟨hanv.symm, fun hadj => hav hadj.symm⟩
    · intro z hz hadj
      rcases hz with (hzB | hzb) | hz0
      · exact ((SimpleGraph.compl_adj G v z).mp hadj).2 (hv.2.1 z hzB)
      · subst z
        exact ((SimpleGraph.compl_adj G v b).mp hadj).2 hbv.symm
      · exact Set.notMem_empty z hz0
  have huright : IsRightStar Gᶜ (A ∪ {a}) (∅ : Set V) (B ∪ {b}) u := by
    refine ⟨?_, ?_, ?_⟩
    · intro hunew
      rcases hunew with ((huA | hua) | (huB | hub)) | hu0
      · exact hu.1 (Or.inl (Or.inl huA))
      · exact hanu hua.symm
      · exact hu.1 (Or.inl (Or.inr huB))
      · exact hbnu hub.symm
      · exact Set.notMem_empty u hu0
    · intro z hz
      rw [SimpleGraph.compl_adj]
      rcases hz with hzB | hzb
      · exact ⟨fun he => hu.1 (Or.inl (Or.inr (he ▸ hzB))), hu.2.2 z (Or.inl hzB)⟩
      · subst z
        exact ⟨hbnu.symm, fun hadj => hbu hadj.symm⟩
    · intro z hz hadj
      rcases hz with (hzA | hza) | hz0
      · exact ((SimpleGraph.compl_adj G u z).mp hadj).2 (hu.2.1 z hzA)
      · subst z
        exact ((SimpleGraph.compl_adj G u a).mp hadj).2 hau.symm
      · exact Set.notMem_empty z hz0

  have hqanti : Anticomplete Gᶜ {z : V | z ∈ SPGT.interior q.reverse}
      ((A ∪ {a}) ∪ (B ∪ {b}) ∪ (∅ : Set V)) := by
    intro z hz w hw hadj
    have hzint : z ∈ SPGT.interior q := PathBasics.mem_interior_reverse.mp hz
    have hzQ : z ∈ Q := hqQ z hzint
    rcases hw with ((hwA | hwa) | (hwB | hwb)) | hw0
    · exact ((SimpleGraph.compl_adj G z w).mp hadj).2
        (Thm124Claims.claim2 h w (Or.inl hwA) z hzQ).symm
    · subst w
      exact ((SimpleGraph.compl_adj G z a).mp hadj).2 (hqadj z hzint).1.symm
    · exact ((SimpleGraph.compl_adj G z w).mp hadj).2
        (Thm124Claims.claim2 h w (Or.inr hwB) z hzQ).symm
    · subst w
      exact ((SimpleGraph.compl_adj G z b).mp hadj).2 (hqadj z hzint).2.symm
    · exact Set.notMem_empty w hw0
  have hbannew : IsBanister Gᶜ (A ∪ {a}) (∅ : Set V) (B ∪ {b}) v q.reverse u :=
    ⟨hqrev, hqout, hvleft, huright, hqanti⟩
  have hnew : IsStaircase Gᶜ (A ∪ {a}) (∅ : Set V) (B ∪ {b}) v q.reverse u :=
    ⟨hSnew, hbannew, by simpa [PathBasics.pathLength_reverse] using hqlen⟩

  apply ProofAttempts.Thm124Claim4.no_compl_staircase h hC
  refine ⟨A ∪ {a}, ∅, B ∪ {b}, v, q.reverse, u, hnew, ?_⟩
  have hsub : A ∪ B ∪ C ⊆ (A ∪ {a}) ∪ (B ∪ {b}) ∪ (∅ : Set V) := by
    intro z hz
    rcases hz with (hzA | hzB) | hzC
    · exact Or.inl (Or.inl (Or.inl hzA))
    · exact Or.inl (Or.inr (Or.inl hzB))
    · exact (hC ▸ hzC).elim
  apply (Set.ssubset_iff_of_subset hsub).2
  refine ⟨a, Or.inl (Or.inl (Or.inr rfl)), ?_⟩
  exact h.outsideStrip a (PathBasics.interior_subset haR)

end Workspace.ProofLemmas.Thm124Claim4Finish
