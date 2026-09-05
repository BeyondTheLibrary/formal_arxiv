import Workspace.ProofLemmas.Thm132Infrastructure
import Workspace.ProofLemmas.Thm132Setup
import Workspace.ProofLemmas.Thm132Claim5Long
import Workspace.ProofLemmas.Thm132Claim5Short
import Workspace.ProofLemmas.Thm132ComplementStaircase

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Completion of the short-path half of claim (5) in 13.2

The antipath supplied by 2.1 must contain both ends of the trajectory (or an
odd antihole results).  It therefore traverses the entire trajectory.  After
claim (5)'s `C = ∅` consequence, this trajectory is the banister of a
strictly larger staircase in the complement, contradicting strong maximality.
-/

namespace Workspace.ProofLemmas.Thm132Claim5ShortFinish

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Claim5Long
open Workspace.ProofLemmas.Thm132Claim5Short
open Workspace.ProofLemmas.Thm132ComplementStaircase

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The third outcome of 2.1 for a length-three old banister is impossible
when the trajectory has more than one term. -/
theorem no_short_antipath_of_long_trajectory
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hlast : IsRightStar G A C B d.last)
    (hwlong : 1 < d.w.length)
    (hR3 : pathLength R₀ = 3)
    {c e : V} (hinterior : interior R₀ = [c, e])
    {q : List V} (hq : IsAntipathFrom G q c e)
    (hqodd : Odd (pathLength q))
    (hqinner : ∀ z ∈ interior q, z ∈ d.r :: d.w) : False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hRlen : R₀.length = 4 := by
    rw [PathBasics.pathLength_eq] at hR3
    have := PathBasics.path_length_pos hban₀.1.1
    omega
  have hcint : c ∈ interior R₀ := by rw [hinterior]; simp
  have heint : e ∈ interior R₀ := by rw [hinterior]; simp
  have hcd : G.Adj c e := by
    have hI : IsPathList G (interior R₀) :=
      (Workspace.ProofLemmas.PathGlue.isPathFrom_interior hban₀.1.1 (by omega)).1
    rw [hinterior] at hI
    simpa using PathBasics.path_adj_succ hI (i := 0) (by simp)
  have hce : c ≠ e := hcd.ne
  have hcStrip : c ∉ A ∪ B ∪ C :=
    hban₀.2.1 c (PathBasics.interior_subset hcint)
  have heStrip : e ∉ A ∪ B ∪ C :=
    hban₀.2.1 e (PathBasics.interior_subset heint)
  have hcAB : c ∉ A ∪ B := fun h => hcStrip (Or.inl h)
  have heAB : e ∉ A ∪ B := fun h => heStrip (Or.inl h)
  have hcAnti : VertexAnticomplete G c (A ∪ B) := by
    intro z hz hadj
    exact hban₀.2.2.2.2 c hcint z (Or.inl hz) hadj
  have heAnti : VertexAnticomplete G e (A ∪ B) := by
    intro z hz hadj
    exact hban₀.2.2.2.2 e heint z (Or.inl hz) hadj

  let T : List V := d.r :: d.w
  have hTpath : IsPathFrom Gᶜ T d.r d.last := by
    simpa [T] using d.trajectory_antipath
  have hTlen : 3 ≤ pathLength T := by
    simp only [T, pathLength, List.length_cons]
    obtain ⟨k, hk⟩ := d.w_odd
    omega
  have hT2 : 2 ≤ T.length := by
    rw [PathBasics.pathLength_eq] at hTlen
    omega
  have hrb₀ : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hrout : d.r ∉ staircaseVertices A C B R₀ :=
    Workspace.ProofLemmas.Thm132Claim2.leftStar_adj_rightEnd_outside
      hK.1.1 d.optimal.1.2.2.1 hra.ne' hrb₀
  have hToutK : ∀ z ∈ T, z ∉ staircaseVertices A C B R₀ := by
    intro z hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z; exact hrout
    · exact bComplete_adj_left_not_mem_staircase hK.1.1
        (d.w_B_complete z hzw) (d.a₀_complete_w z hzw).symm
  have hcT : c ∉ T := fun h => hToutK c h (Or.inl (PathBasics.interior_subset hcint))
  have heT : e ∉ T := fun h => hToutK e h (Or.inl (PathBasics.interior_subset heint))
  have hToutAB : ∀ z ∈ T, z ∉ A ∪ B := by
    intro z hz hAB
    exact hToutK z hz (Or.inr (Or.inl hAB))
  have hqOutside : ∀ z ∈ q, z ∉ A ∪ B ∪ C := by
    intro z hz
    by_cases hzc : z = c
    · simpa [hzc] using hcStrip
    by_cases hze : z = e
    · simpa [hze] using heStrip
    have hzint : z ∈ interior q :=
      (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hz, hzc, hze⟩
    have hzT := hqinner z hzint
    exact fun hzS => hToutK z hzT (Or.inr hzS)
  have hq3 : 3 ≤ q.length :=
    Workspace.ProofLemmas.AntiholeCompletion.three_le_length_of_antipath hq hcd
  have hGc : Berge Gᶜ := Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG

  have hrq : d.r ∈ q := by
    by_contra hrnot
    obtain ⟨b, hbB⟩ := hS.2.1.2
    have hbq : b ∉ q := fun hbmem =>
      hqOutside b hbmem (Or.inl (Or.inr hbB))
    have hcross : ∀ z ∈ q, (Gᶜ.Adj z b ↔ z = c ∨ z = e) := by
      intro z hz
      by_cases hzc : z = c
      · subst z
        apply iff_of_true
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => hcStrip (he ▸ Or.inl (Or.inr hbB)),
            hban₀.2.2.2.2 c hcint b (Or.inl (Or.inr hbB))⟩
        · exact Or.inl rfl
      by_cases hze : z = e
      · subst z
        apply iff_of_true
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => heStrip (he ▸ Or.inl (Or.inr hbB)),
            hban₀.2.2.2.2 e heint b (Or.inl (Or.inr hbB))⟩
        · exact Or.inr rfl
      · have hzint : z ∈ interior q :=
          (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hz, hzc, hze⟩
        have hzT := hqinner z hzint
        have hzw : z ∈ d.w := by
          rcases List.mem_cons.mp hzT with hzr | hzw
          · exact absurd (hzr ▸ hz) hrnot
          · exact hzw
        exact iff_of_false
          (fun hcomp => (G.compl_adj z b).mp hcomp |>.2
            (d.w_B_complete z hzw b hbB))
          (by tauto)
    exact no_odd_path_closer hGc hq hqodd hq3 hbq hcross

  have hsq : d.last ∈ q := by
    by_contra hsnot
    obtain ⟨a, haA⟩ := hS.2.1.1
    have haq : a ∉ q := fun hamem =>
      hqOutside a hamem (Or.inl (Or.inl haA))
    have hcross : ∀ z ∈ q, (Gᶜ.Adj z a ↔ z = c ∨ z = e) := by
      intro z hz
      by_cases hzc : z = c
      · subst z
        apply iff_of_true
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => hcStrip (he ▸ Or.inl (Or.inl haA)),
            hban₀.2.2.2.2 c hcint a (Or.inl (Or.inl haA))⟩
        · exact Or.inl rfl
      by_cases hze : z = e
      · subst z
        apply iff_of_true
        · rw [SimpleGraph.compl_adj]
          exact ⟨fun he => heStrip (he ▸ Or.inl (Or.inl haA)),
            hban₀.2.2.2.2 e heint a (Or.inl (Or.inl haA))⟩
        · exact Or.inr rfl
      · have hzint : z ∈ interior q :=
          (PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hz, hzc, hze⟩
        have hzT := hqinner z hzint
        have hza : G.Adj z a := by
          rcases List.mem_cons.mp hzT with hzr | hzw
          · subst z
            exact d.optimal.1.2.2.1.2.1 a haA
          · exact d.before_last_A_complete z hzw
              (fun he => hsnot (he ▸ hz)) a haA
        exact iff_of_false
          (fun hcomp => (G.compl_adj z a).mp hcomp |>.2 hza)
          (by tauto)
    exact no_odd_path_closer hGc hq hqodd hq3 haq hcross

  have hCempty : C = ∅ :=
    C_eq_empty_of_long_trajectory hG heven hK d hbW hra hlast hwlong
  have hS0 : StepConnected G A (∅ : Set V) B := by simpa [hCempty] using hS
  have hleft0 : IsLeftStar G A (∅ : Set V) B d.r := by
    simpa [hCempty] using d.optimal.1.2.2.1
  have hright0 : IsRightStar G A (∅ : Set V) B d.last := by
    simpa [hCempty] using hlast
  have hTint : ∀ z ∈ interior T, VertexComplete G z (A ∪ B) := by
    intro z hz u hu
    have hzdata := (PathBasics.mem_interior_iff_of_pathFrom hTpath).mp hz
    have hzw : z ∈ d.w := by
      rcases List.mem_cons.mp hzdata.1 with hzr | hzw
      · exact absurd hzr hzdata.2.1
      · exact hzw
    rcases hu with huA | huB
    · exact d.before_last_A_complete z hzw hzdata.2.2 u huA
    · exact d.w_B_complete z hzw u huB
  have horient := path_orientation_of_inner_subset hTpath hT2 hq hcT heT
    (by simpa [T] using hqinner) hrq hsq
  have hno : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V),
      IsStaircase Gᶜ A' C' B' a' R' b' ∧
        (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C') :=
    hK.2.resolve_left (by rw [hCempty]; simp)
  rcases horient with hforward | hreverse
  · have hstairs := staircase_compl_of_outer_path G A B c e d.r d.last T q
      hS0 hleft0 hright0 hTpath hTlen hToutAB hTint hcAB heAB hcT heT
      hcd hcAnti heAnti hq hforward
    apply hno
    refine ⟨B ∪ {c}, ∅, A ∪ {e}, d.r, T, d.last, hstairs, ?_⟩
    constructor
    · intro z hz
      rcases hz with (hzA | hzB) | hzC
      · exact Or.inl (Or.inr (Or.inl hzA))
      · exact Or.inl (Or.inl (Or.inl hzB))
      · exact absurd (hCempty ▸ hzC) (Set.notMem_empty z)
    · intro hback
      have hcnew : c ∈ (B ∪ {c}) ∪ (A ∪ {e}) ∪ (∅ : Set V) :=
        Or.inl (Or.inl (Or.inr rfl))
      exact hcStrip (hback hcnew)
  · have hqrev : IsPathFrom Gᶜ q.reverse e c := PathBasics.isPathFrom_reverse hq
    have hrevEq : q.reverse = e :: (T ++ [c]) := by
      rw [hreverse]
      simp
    have hstairs := staircase_compl_of_outer_path G A B e c d.r d.last T q.reverse
      hS0 hleft0 hright0 hTpath hTlen hToutAB hTint heAB hcAB heT hcT
      hcd.symm heAnti hcAnti hqrev hrevEq
    apply hno
    refine ⟨B ∪ {e}, ∅, A ∪ {c}, d.r, T, d.last, hstairs, ?_⟩
    constructor
    · intro z hz
      rcases hz with (hzA | hzB) | hzC
      · exact Or.inl (Or.inr (Or.inl hzA))
      · exact Or.inl (Or.inl (Or.inl hzB))
      · exact absurd (hCempty ▸ hzC) (Set.notMem_empty z)
    · intro hback
      have henew : e ∈ (B ∪ {e}) ∪ (A ∪ {c}) ∪ (∅ : Set V) :=
        Or.inl (Or.inl (Or.inr rfl))
      exact heStrip (hback henew)

end Workspace.ProofLemmas.Thm132Claim5ShortFinish
