import Workspace.ProofLemmas.Thm132SecondBanister
import Workspace.ProofLemmas.Thm132BaseSeparation
import Workspace.ProofLemmas.Thm132FinalPath
import Workspace.ProofLemmas.Thm132OptimalLength

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # The separated second banister used in the endgame of 13.2. -/

namespace Workspace.ProofLemmas.Thm132EndgameSetup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choose the second optimal banister, separate it from the old one, and use
the final Roussel--Rubio path to show that its left end misses `r`. -/
theorem exists_second_configuration
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (hx : IsRightSequence G A C B x)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hlast : IsRightStar G A C B d.last)
    (hwone : d.w.length = 1)
    (P : List V) (hP : IsPathFrom G P d.r d.last)
    (hPodd : Odd (pathLength P))
    (hPint : ∀ z, z ∈ interior P ↔ z ∈ interior R₀) :
    ∃ (r' : V) (R' : List V) (j : ℕ) (hj : j < x.length),
      BOptimalBanister G A C B x r' R' d.last ∧
      birth G A C B x r' x[j] ∧ j < d.birthIndex ∧
      pathLength R' = 1 ∧
      (∀ z ∈ R₀, z ∉ R') ∧
      (∀ p ∈ R₀.tail, ∀ q ∈ R'.dropLast, ¬ G.Adj p q) ∧
      ¬ G.Adj d.r r' := by
  classical
  obtain ⟨r', R', j, hj, hopt', hbirth', hjd⟩ :=
    Workspace.ProofLemmas.Thm132SecondBanister.exists_second_optimal hx d hlast hwone
  have hR'one := Workspace.ProofLemmas.Thm132OptimalLength.optimal_banister_length_one
    hG hK4 heven h1br h2br hK hx hopt'
  have hearlier : Earlier x (x[j]'hj) (x[d.birthIndex]'d.birthIndex_lt) :=
    ⟨j, d.birthIndex, hj, d.birthIndex_lt, rfl, rfl, hjd⟩
  have hA : A.Nonempty := hK.1.1.1.2.1.1
  have hnolink := Workspace.ProofLemmas.Thm132BaseSeparation.base_halves_not_linked
    hA d.optimal hK.1.1.2.1 hopt'.1 hbirth' d.birth_r hearlier
  have hdisj : ∀ z ∈ R₀, z ∉ R' :=
    Workspace.ProofLemmas.Thm132BanisterSeparation.banisters_disjoint_of_halves_not_linked
      hA hK.1.1.2.1 hopt'.1 hnolink
  have hanti : ∀ p ∈ R₀.tail, ∀ q ∈ R'.dropLast, ¬ G.Adj p q :=
    Workspace.ProofLemmas.Thm132BanisterSeparation.halves_anticomplete_of_not_linked hnolink
  have hR'len : R'.length = 2 := by
    rw [pathLength] at hR'one
    have hpos := PathBasics.path_length_pos hopt'.1.1.1
    omega
  obtain ⟨u, v, hR'shape⟩ := Workspace.ProofLemmas.PathGlue.length_eq_two hR'len
  have hu : u = r' := by
    rw [hR'shape] at hopt'
    simpa using hopt'.1.1.2.1
  have hv : v = d.last := by
    rw [hR'shape] at hopt'
    simpa using hopt'.1.1.2.2
  subst u
  subst v
  have hR'shape' : R' = [r', d.last] := hR'shape
  have hr'last : G.Adj r' d.last :=
    PathBasics.isPathFrom_ends_adj_of_length_one hopt'.1.1 hR'one
  have hrw : ¬ G.Adj d.r d.last := by
    have hwne : d.w ≠ [] := by rw [List.ne_nil_iff_length_pos, hwone]; omega
    have hlastMem : d.last ∈ d.w := by
      have hc' : d.w.getLast? = some d.last := by
        simpa [List.getLast?_cons_of_ne_nil hwne] using d.trajectory_antipath.2.2
      exact PathBasics.getLast_mem hc'
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hwone
    have hzlast : z = d.last := by
      have hc := d.trajectory_antipath.2.2
      rw [hz] at hc
      simpa [List.getLast?_cons_of_ne_nil (by simp : [z] ≠ [])] using hc
    have htrajOne : pathLength (d.r :: d.w) = 1 := by simp [pathLength, hz]
    have hc := PathBasics.isPathFrom_ends_adj_of_length_one d.trajectory_antipath htrajOne
    rw [SimpleGraph.compl_adj] at hc
    exact hc.2
  have hno : ¬ G.Adj d.r r' := by
    intro hrr'
    have hr'neR : r' ∉ R₀ := by
      intro hm
      exact hdisj r' hm (by simp [hR'shape'])
    have hr'notP : r' ∉ P := by
      intro hm
      by_cases hint : r' ∈ interior P
      · exact hr'neR ((hPint r').mp hint |> PathBasics.interior_subset)
      · have hc := (PathBasics.mem_interior_iff_of_pathFrom hP).not.mp hint
        push_neg at hc
        have hre : r' = d.r ∨ r' = d.last := by
          by_cases hne : r' = d.r
          · exact Or.inl hne
          · exact Or.inr (hc hm hne)
        rcases hre with hre | hre
        · exact G.irrefl (hre ▸ hrr')
        · exact G.irrefl (hre ▸ hr'last)
    have hcross : ∀ z ∈ P, (G.Adj z r' ↔ z = d.r ∨ z = d.last) := by
      intro z hz
      constructor
      · intro hzr'
        by_cases hint : z ∈ interior P
        · have hzR : z ∈ interior R₀ := (hPint z).mp hint
          have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hK.1.1.2.1.1).mp hzR
          have hztail :=
            (HyperprismRungStructure.mem_tail_iff_of_pathFrom hK.1.1.2.1.1).2
              ⟨hzdata.1, hzdata.2.1⟩
          exact absurd hzr' (hanti z hztail r' (by simp [hR'shape']))
        · have hc := (PathBasics.mem_interior_iff_of_pathFrom hP).not.mp hint
          push_neg at hc
          by_cases hzr : z = d.r
          · exact Or.inl hzr
          · exact Or.inr (hc hz hzr)
      · rintro (rfl | rfl)
        · exact hrr'
        · exact hr'last.symm
    have hP3 : 3 ≤ P.length := by
      have hpnotone : pathLength P ≠ 1 := by
        intro hone
        exact hrw (PathBasics.isPathFrom_ends_adj_of_length_one hP hone)
      obtain ⟨k, hk⟩ := hPodd
      rw [PathBasics.pathLength_eq] at hk hpnotone
      have hp := PathBasics.path_length_pos hP.1
      omega
    exact Workspace.ProofLemmas.Thm132Claim5Long.no_odd_path_closer
      hG hP hPodd hP3 hr'notP hcross
  exact ⟨r', R', j, hj, hopt', hbirth', hjd, hR'one, hdisj, hanti, hno⟩

end Workspace.ProofLemmas.Thm132EndgameSetup
