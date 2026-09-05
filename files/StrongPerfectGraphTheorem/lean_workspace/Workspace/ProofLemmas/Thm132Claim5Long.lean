import Workspace.ProofLemmas.Thm132Claim4
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Types.RousselRubio

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The long-path half of claim (5) in 13.2

A leap for the old banister supplies an odd path between two nonadjacent
trajectory vertices, with the old banister interior as its interior.  Closing
that path first through a vertex of `B` shows that one leap vertex is `r`.
When the trajectory has more than one term, the other leap vertex is an
earlier term and hence is `A`-complete; closing the same path through a vertex
of `A` then gives an odd hole.
-/

namespace Workspace.ProofLemmas.Thm132Claim5Long

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup
open Workspace.ProofLemmas.Thm132Claim2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The path between the two vertices of a leap, whose interior is the
interior of the path on which the leap sits. -/
theorem leap_path {G : SimpleGraph V} {T : Set V}
    {P : List V} {p₀ pₙ u v : V}
    (hP : IsPathFrom G P p₀ pₙ) (hP5 : 5 ≤ pathLength P)
    (hPT : ∀ z ∈ P, z ∉ T) (huT : u ∈ T) (hvT : v ∈ T)
    (hleap : IsLeapForPath G P u v) :
    IsPathFrom G (u :: (interior P ++ [v])) u v ∧
      pathLength (u :: (interior P ++ [v])) = pathLength P := by
  obtain ⟨-, -, huv, hnuv, huadj, hvadj⟩ := hleap
  have hP6 : 6 ≤ P.length := by
    rw [PathBasics.pathLength_eq] at hP5
    omega
  have hIP : IsPathFrom G (interior P) (P[1]'(by omega))
      (P[P.length - 2]'(by omega)) :=
    Workspace.ProofLemmas.PathGlue.isPathFrom_interior hP.1 (by omega)
  have huFirst : G.Adj u (P[1]'(by omega)) :=
    (huadj 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hvLast : G.Adj v (P[P.length - 2]'(by omega)) :=
    (hvadj (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
  have huNot : u ∉ interior P := fun hm => hPT u (PathBasics.interior_subset hm) huT
  have hvNot : v ∉ interior P := fun hm => hPT v (PathBasics.interior_subset hm) hvT
  have huOther : ∀ z ∈ interior P, z ≠ P[1]'(by omega) → ¬ G.Adj u z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ 1 := by
      intro he
      exact hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (huadj k hk).mp hadj with h | h | h <;> omega
  have hvOther : ∀ z ∈ interior P, z ≠ P[P.length - 2]'(by omega) →
      ¬ G.Adj v z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ P.length - 2 := by
      intro he
      exact hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (hvadj k hk).mp hadj with h | h | h <;> omega
  have hQ : IsPathFrom G (u :: (interior P ++ [v])) u v :=
    PathAttach.isPathFrom_cons_concat hIP huFirst hvLast hnuv huv huNot hvNot huOther hvOther
  refine ⟨hQ, ?_⟩
  rw [PathAttach.pathLength_cons_append_singleton, PathBasics.interior_length,
    PathBasics.pathLength_eq]
  omega

/-- An odd induced path cannot be closed by a vertex whose only neighbours on
the path are its two ends. -/
theorem no_odd_path_closer {G : SimpleGraph V} (hG : Berge G)
    {Q : List V} {u v c : V} (hQ : IsPathFrom G Q u v)
    (hodd : Odd (pathLength Q)) (hQ4 : 3 ≤ Q.length)
    (hcQ : c ∉ Q)
    (hcross : ∀ z ∈ Q, (G.Adj z c ↔ z = u ∨ z = v)) : False := by
  have hc : IsPathFrom G [c] c c :=
    ⟨PathBasics.isPathList_singleton G c, by simp, by simp⟩
  have hh : IsHoleList G (Q ++ [c]) := by
    refine Workspace.ProofLemmas.PathGlue.glue_hole hQ hc ?_ ?_ ?_
    · intro z hz
      simp only [List.mem_singleton]
      exact fun he => hcQ (he ▸ hz)
    · intro z hz y hy
      simp only [List.mem_singleton] at hy
      subst y
      rw [hcross z hz]
      tauto
    · simp only [List.length_append, List.length_singleton]
      omega
  have heven := hG.1 _ hh
  obtain ⟨ko, hko⟩ := hodd
  obtain ⟨ke, hke⟩ := heven
  rw [PathBasics.pathLength_eq] at hko
  simp only [holeLength, List.length_append, List.length_singleton] at hke
  omega

/-- If the trajectory has more than one term, the leap alternative of 2.1 for
the old banister is impossible. -/
theorem no_leap_of_long_trajectory
    {G : SimpleGraph V} (hG : Berge G)
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    {A C B : Set V} {a₀ b₀ : V} {R₀ x : List V} {i : ℕ}
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i)
    (hbW : VertexComplete G b₀ {z : V | z ∈ d.w})
    (hra : G.Adj a₀ d.r)
    (hwlong : 1 < d.w.length)
    (hR5 : 5 ≤ pathLength R₀)
    {u v : V} (huT : u ∈ d.r :: d.w) (hvT : v ∈ d.r :: d.w)
    (hleap : IsLeapForPath G R₀ u v) : False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hban₀ : IsBanister G A C B a₀ R₀ b₀ := hK.1.1.2.1
  have hrb : G.Adj d.r b₀ :=
    PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
  have hrout : d.r ∉ staircaseVertices A C B R₀ :=
    leftStar_adj_rightEnd_outside hK.1.1 d.optimal.1.2.2.1 hra.ne' hrb
  have hTout : ∀ z ∈ d.r :: d.w, z ∉ staircaseVertices A C B R₀ := by
    intro z hz
    rcases List.mem_cons.mp hz with hzr | hzw
    · subst z
      exact hrout
    · exact bComplete_adj_left_not_mem_staircase hK.1.1
        (d.w_B_complete z hzw) (d.a₀_complete_w z hzw).symm
  have hR₀T : ∀ z ∈ R₀, z ∉ {y : V | y ∈ d.r :: d.w} := by
    intro z hzR hzT
    exact hTout z hzT (Or.inl hzR)
  obtain ⟨hQ, hQlen⟩ := leap_path hban₀.1 hR5 hR₀T huT hvT hleap
  let Q : List V := u :: (interior R₀ ++ [v])
  have hQodd : Odd (pathLength Q) := by
    rw [hQlen]
    exact (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven
      A C B hS a₀ b₀ R₀ hban₀).2
  have hQmem : ∀ z ∈ Q, z = u ∨ z ∈ interior R₀ ∨ z = v := by
    intro z hz
    simpa [Q] using hz
  have hQoutside : ∀ z ∈ Q, z ∉ A ∪ B ∪ C := by
    intro z hz
    rcases hQmem z hz with hzu | hzint | hzv
    · subst z
      exact fun huS => hTout u huT (Or.inr huS)
    · exact hban₀.2.1 z (PathBasics.interior_subset hzint)
    · subst z
      exact fun hvS => hTout v hvT (Or.inr hvS)
  obtain ⟨b, hbB⟩ := hS.2.1.2
  have hnotBothB : ¬ (G.Adj u b ∧ G.Adj v b) := by
    rintro ⟨hub, hvb⟩
    have hbQ : b ∉ Q := fun hbmem => hQoutside b hbmem (Or.inl (Or.inr hbB))
    have hcross : ∀ z ∈ Q, (G.Adj z b ↔ z = u ∨ z = v) := by
      intro z hz
      rcases hQmem z hz with hzu | hzint | hzv
      · subst z
        exact iff_of_true hub (Or.inl rfl)
      · exact iff_of_false
          (hban₀.2.2.2.2 z hzint b (Or.inl (Or.inr hbB)))
          (by
            intro h
            rcases h with h | h
            · subst z
              exact hTout u huT (Or.inl (PathBasics.interior_subset hzint))
            · subst z
              exact hTout v hvT (Or.inl (PathBasics.interior_subset hzint)))
      · subst z
        exact iff_of_true hvb (Or.inr rfl)
    have hQ3 : 3 ≤ Q.length := by
      simp only [Q, List.length_cons, List.length_append, List.length_singleton,
        PathBasics.interior_length]
      rw [PathBasics.pathLength_eq] at hR5
      omega
    exact no_odd_path_closer hG hQ hQodd hQ3 hbQ hcross

  have hEndR : u = d.r ∨ v = d.r := by
    by_cases hub : G.Adj u b
    · right
      rcases List.mem_cons.mp hvT with hvr | hvw
      · exact hvr
      · exfalso
        exact hnotBothB ⟨hub, d.w_B_complete v hvw b hbB⟩
    · left
      rcases List.mem_cons.mp huT with hur | huw
      · exact hur
      · exfalso
        exact hub (d.w_B_complete u huw b hbB)
  have huv_ne : u ≠ v := hleap.2.2.1
  have huv_non : ¬ G.Adj u v := hleap.2.2.2.1
  have hrlast_non : ¬ Gᶜ.Adj d.r d.last := by
    have hlen : 3 ≤ (d.r :: d.w).length := by simp; omega
    have hn := PathBasics.path_ends_not_adj d.trajectory_antipath.1 hlen
    have h0 : (d.r :: d.w)[0]'(by omega) = d.r := by simp
    have hl : (d.r :: d.w)[(d.r :: d.w).length - 1]'(by omega) = d.last :=
      PathBasics.getElem_last_of_getLast? d.trajectory_antipath.2.2 (by omega)
    rw [h0, hl] at hn
    exact hn

  obtain ⟨a, haA⟩ := hS.2.1.1
  rcases hEndR with hur | hvr
  · have hvw : v ∈ d.w := by
      rcases List.mem_cons.mp hvT with hvr' | hvw
      · exact absurd (hur.trans hvr'.symm) huv_ne
      · exact hvw
    have hvlast : v ≠ d.last := by
      intro he
      apply hrlast_non
      rw [← hur, ← he, SimpleGraph.compl_adj]
      exact ⟨huv_ne, huv_non⟩
    have hua : G.Adj u a := by
      rw [hur]
      exact d.optimal.1.2.2.1.2.1 a haA
    have hva : G.Adj v a := d.before_last_A_complete v hvw hvlast a haA
    have haQ : a ∉ Q := fun hamem => hQoutside a hamem (Or.inl (Or.inl haA))
    have hcrossA : ∀ z ∈ Q, (G.Adj z a ↔ z = u ∨ z = v) := by
      intro z hz
      rcases hQmem z hz with hzu | hzint | hzv
      · subst z
        exact iff_of_true hua (Or.inl rfl)
      · exact iff_of_false
          (hban₀.2.2.2.2 z hzint a (Or.inl (Or.inl haA)))
          (by
            intro h
            rcases h with h | h
            · subst z
              exact hTout u huT (Or.inl (PathBasics.interior_subset hzint))
            · subst z
              exact hTout v hvT (Or.inl (PathBasics.interior_subset hzint)))
      · subst z
        exact iff_of_true hva (Or.inr rfl)
    have hQ3 : 3 ≤ Q.length := by
      simp only [Q, List.length_cons, List.length_append, List.length_singleton,
        PathBasics.interior_length]
      rw [PathBasics.pathLength_eq] at hR5
      omega
    exact no_odd_path_closer hG hQ hQodd hQ3 haQ hcrossA
  · have huw : u ∈ d.w := by
      rcases List.mem_cons.mp huT with hur' | huw
      · exact absurd (hur'.trans hvr.symm) huv_ne
      · exact huw
    have hulast : u ≠ d.last := by
      intro he
      apply hrlast_non
      rw [← hvr, ← he, SimpleGraph.compl_adj]
      exact ⟨huv_ne.symm, fun hadj => huv_non hadj.symm⟩
    have hua : G.Adj u a := d.before_last_A_complete u huw hulast a haA
    have hva : G.Adj v a := by
      rw [hvr]
      exact d.optimal.1.2.2.1.2.1 a haA
    have haQ : a ∉ Q := fun hamem => hQoutside a hamem (Or.inl (Or.inl haA))
    have hcrossA : ∀ z ∈ Q, (G.Adj z a ↔ z = u ∨ z = v) := by
      intro z hz
      rcases hQmem z hz with hzu | hzint | hzv
      · subst z
        exact iff_of_true hua (Or.inl rfl)
      · exact iff_of_false
          (hban₀.2.2.2.2 z hzint a (Or.inl (Or.inl haA)))
          (by
            intro h
            rcases h with h | h
            · subst z
              exact hTout u huT (Or.inl (PathBasics.interior_subset hzint))
            · subst z
              exact hTout v hvT (Or.inl (PathBasics.interior_subset hzint)))
      · subst z
        exact iff_of_true hva (Or.inr rfl)
    have hQ3 : 3 ≤ Q.length := by
      simp only [Q, List.length_cons, List.length_append, List.length_singleton,
        PathBasics.interior_length]
      rw [PathBasics.pathLength_eq] at hR5
      omega
    exact no_odd_path_closer hG hQ hQodd hQ3 haQ hcrossA

end Workspace.ProofLemmas.Thm132Claim5Long
