import Workspace.ProofLemmas.Thm131LastCase
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The terminal-miss case in 13.1

After all earlier vertices of the trajectory see the right end of the
optimal banister, the only possible missing vertex is its terminal
right-star.  An earlier optimal banister into that terminal vertex is an
edge.  Applying 2.1 in the complement produces the larger complementary
staircase forbidden by strong maximality.
-/

namespace Workspace.ProofLemmas.Thm131LastMiss

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131OptimalLength
open Workspace.ProofLemmas.Thm131EdgeCases
open Workspace.ProofLemmas.Thm131LastCase
open Workspace.ProofLemmas.Thm131ComplementStars
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The path between the two vertices of a leap, whose interior is the
interior of the path on which the leap sits. -/
private theorem leap_inner_path {G : SimpleGraph V} {T : Set V}
    {P : List V} {p₀ pₙ u v : V}
    (hP : IsPathFrom G P p₀ pₙ) (hP5 : 5 ≤ pathLength P)
    (hPT : ∀ z ∈ P, z ∉ T) (huT : u ∈ T) (hvT : v ∈ T)
    (hleap : IsLeapForPath G P u v) :
    IsPathFrom G (u :: (interior P ++ [v])) u v ∧
      pathLength (u :: (interior P ++ [v])) = pathLength P := by
  obtain ⟨-, -, huv, hnuv, huadj, hvadj⟩ := hleap
  have hP6 : 6 ≤ P.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hP5
    omega
  have hIP : IsPathFrom G (interior P) (P[1]'(by omega))
      (P[P.length - 2]'(by omega)) :=
    Workspace.ProofLemmas.PathGlue.isPathFrom_interior hP.1 (by omega)
  have huFirst : G.Adj u (P[1]'(by omega)) :=
    (huadj 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hvLast : G.Adj v (P[P.length - 2]'(by omega)) :=
    (hvadj (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
  have huNot : u ∉ interior P := fun hm =>
    hPT u (Workspace.ProofLemmas.PathBasics.interior_subset hm) huT
  have hvNot : v ∉ interior P := fun hm =>
    hPT v (Workspace.ProofLemmas.PathBasics.interior_subset hm) hvT
  have huOther : ∀ z ∈ interior P, z ≠ P[1]'(by omega) → ¬ G.Adj u z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ 1 := by
      intro he
      exact hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (huadj k hk).mp hadj with h | h | h <;> omega
  have hvOther : ∀ z ∈ interior P, z ≠ P[P.length - 2]'(by omega) →
      ¬ G.Adj v z := by
    intro z hz hzne hadj
    obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hP.1 hz
    have hkne : k ≠ P.length - 2 := by
      intro he
      exact hzne (hP.1.2.1.getElem_inj_iff.mpr he)
    rcases (hvadj k hk).mp hadj with h | h | h <;> omega
  have hQ : IsPathFrom G (u :: (interior P ++ [v])) u v :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hIP huFirst hvLast
      hnuv huv huNot hvNot huOther hvOther
  refine ⟨hQ, ?_⟩
  rw [Workspace.ProofLemmas.PathAttach.pathLength_cons_append_singleton,
    Workspace.ProofLemmas.PathBasics.interior_length,
    Workspace.ProofLemmas.PathBasics.pathLength_eq]
  omega

/-- The complementary staircase at the end of claim (7) of the paper.  The
outer path records that the new left-class vertex `r` sees only the first
vertex of the displayed complement-banister. -/
private theorem staircase_compl_adjoin_stars
    (G : SimpleGraph V) (A B : Set V) (r b a last a₂ : V) (w : List V)
    (hS : StepConnected G A (∅ : Set V) B)
    (hr : IsLeftStar G A (∅ : Set V) B r)
    (hb : IsRightStar G A (∅ : Set V) B b)
    (ha : IsLeftStar G A (∅ : Set V) B a)
    (hlast : IsRightStar G A (∅ : Set V) B last)
    (hrb : ¬ G.Adj r b) (hab : G.Adj a b) (hrlast : G.Adj r last)
    (hblast : ¬ G.Adj b last)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbBefore : ∀ z ∈ w, z ≠ last → G.Adj b z)
    (hbnotw : b ∉ w)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hT3 : 3 ≤ pathLength (a :: w))
    (houter : IsPathFrom Gᶜ (r :: ((a :: w) ++ [a₂])) r a₂) :
    IsStaircase Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b}) a (a :: w) last := by
  classical
  let T : List V := a :: w
  have hT : IsPathFrom Gᶜ T a last := by simpa [T] using hanti
  have houterT : IsPathFrom Gᶜ (r :: (T ++ [a₂])) r a₂ := by
    simpa [T] using houter
  have hTpos : 0 < T.length := Workspace.ProofLemmas.PathBasics.path_length_pos hT.1
  have hT0 : T[0]'hTpos = a := by simp [T]
  have hrAdj : ∀ z ∈ T, (Gᶜ.Adj r z ↔ z = a) := by
    intro z hz
    obtain ⟨k, hk, hek⟩ := List.mem_iff_getElem.mp hz
    have hqk : k + 1 < (r :: (T ++ [a₂])).length := by simp; omega
    have hq0 : 0 < (r :: (T ++ [a₂])).length := by simp
    have helem : (r :: (T ++ [a₂]))[k + 1]'hqk = T[k]'hk := by
      simp only [List.getElem_cons_succ, List.getElem_append_left hk]
    constructor
    · intro hadj
      have hi := (Workspace.ProofLemmas.PathBasics.path_adj_iff houterT.1 hq0 hqk).mp (by
        simpa only [List.getElem_cons_zero, helem, hek] using hadj)
      have hk0 : k = 0 := by rcases hi with h | h <;> omega
      calc
        z = T[k]'hk := hek.symm
        _ = T[0]'hTpos := by
          apply hT.1.2.1.getElem_inj_iff.mpr
          exact hk0
        _ = a := hT0
    · intro hza
      have hk0 : k = 0 := by
        apply hT.1.2.1.getElem_inj_iff.mp
        calc
          T[k]'hk = z := hek
          _ = a := hza
          _ = T[0]'hTpos := hT0.symm
      have hadj : Gᶜ.Adj ((r :: (T ++ [a₂]))[0]'hq0)
          ((r :: (T ++ [a₂]))[k + 1]'hqk) :=
        (Workspace.ProofLemmas.PathBasics.path_adj_iff houterT.1 hq0 hqk).mpr
          (Or.inl (by omega))
      simpa only [List.getElem_cons_zero, helem, hek] using hadj
  have hrNotT : r ∉ T := by
    have hn := (List.nodup_cons.mp houterT.1.2.1).1
    intro hrt
    exact hn (List.mem_append_left [a₂] hrt)
  have hbNotT : b ∉ T := by
    intro hbt
    rcases List.mem_cons.mp (show b ∈ a :: w by simpa [T] using hbt) with hba | hbw
    · exact hab.ne' hba
    · exact hbnotw hbw
  have hToutOld : ∀ z ∈ T, z ∉ A ∪ B := by
    intro z hz hzAB
    rcases List.mem_cons.mp (show z ∈ a :: w by simpa [T] using hz) with hza | hzw
    · subst z
      exact ha.1 (by rcases hzAB with hzA | hzB; exact Or.inl (Or.inl hzA); exact Or.inl (Or.inr hzB))
    · rcases hzAB with hzA | hzB
      · exact bComplete_not_mem_strip hS (hwB z hzw) (Or.inl (Or.inl hzA))
      · exact bComplete_not_mem_strip hS (hwB z hzw) (Or.inl (Or.inr hzB))
  have hToutNew : ∀ z ∈ T, z ∉ (B ∪ {r}) ∪ (A ∪ {b}) ∪ (∅ : Set V) := by
    intro z hz hznew
    rcases hznew with ((hzB | hzr) | (hzA | hzb)) | hz0
    · exact hToutOld z hz (Or.inr hzB)
    · exact hrNotT (hzr ▸ hz)
    · exact hToutOld z hz (Or.inl hzA)
    · exact hbNotT (hzb ▸ hz)
    · exact Set.notMem_empty z hz0
  have hleftNew : IsLeftStar Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b}) a := by
    refine ⟨hToutNew a (by simp [T]), ?_, ?_⟩
    · intro z hz
      rcases hz with hzB | hzr
      · rw [SimpleGraph.compl_adj]
        exact ⟨fun he => ha.1 (he ▸ Or.inl (Or.inr hzB)),
          fun hadj => ha.2.2 z (Or.inl hzB) hadj⟩
      · subst z
        exact (hrAdj a (by simp [T])).2 rfl |>.symm
    · intro z hz hadj
      rcases hz with (hzA | hzb) | hz0
      · exact (G.compl_adj a z).mp hadj |>.2 (ha.2.1 z hzA)
      · subst z
        exact (G.compl_adj a b).mp hadj |>.2 hab
      · exact Set.notMem_empty z hz0
  have hrightNew : IsRightStar Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b}) last := by
    have hlastT : last ∈ T := Workspace.ProofLemmas.PathBasics.getLast_mem hT.2.2
    refine ⟨hToutNew last hlastT, ?_, ?_⟩
    · intro z hz
      rcases hz with hzA | hzb
      · rw [SimpleGraph.compl_adj]
        exact ⟨fun he => hlast.1 (he.symm ▸ Or.inl (Or.inl hzA)),
          fun hadj => hlast.2.2 z (Or.inl hzA) hadj⟩
      · subst z
        rw [SimpleGraph.compl_adj]
        have hlastw : last ∈ w := by
          have hwne : w ≠ [] := by
            intro hw
            subst w
            simp [T, pathLength] at hT3
          have hlastW : w.getLast? = some last := by
            simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
          exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastW
        exact ⟨fun he => hbnotw (he ▸ hlastw), fun hadj => hblast hadj.symm⟩
    · intro z hz hadj
      rcases hz with (hzB | hzr) | hz0
      · have hlastw : last ∈ w := by
          have hwne : w ≠ [] := by
            intro hw
            subst w
            simp [T, pathLength] at hT3
          have hlastW : w.getLast? = some last := by
            simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
          exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastW
        exact (G.compl_adj last z).mp hadj |>.2 (hwB last hlastw z hzB)
      · subst z
        exact (G.compl_adj last r).mp hadj |>.2 hrlast.symm
      · exact Set.notMem_empty z hz0
  have hInteriorAnti : Anticomplete Gᶜ {z : V | z ∈ interior T}
      ((B ∪ {r}) ∪ (A ∪ {b}) ∪ (∅ : Set V)) := by
    intro z hz u hu hadj
    have hzdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hT).mp hz
    have hzw : z ∈ w := by
      rcases List.mem_cons.mp (show z ∈ a :: w by simpa [T] using hzdata.1) with hza | hzw
      · exact absurd hza hzdata.2.1
      · exact hzw
    rcases hu with ((huB | hur) | (huA | hub)) | hu0
    · exact (G.compl_adj z u).mp hadj |>.2 (hwB z hzw u huB)
    · subst u
      exact hzdata.2.1 ((hrAdj z hzdata.1).mp hadj.symm)
    · exact (G.compl_adj z u).mp hadj |>.2 (hbeforeA z hzw hzdata.2.2 u huA)
    · subst u
      exact (G.compl_adj z b).mp hadj |>.2 (hbBefore z hzw hzdata.2.2).symm
    · exact Set.notMem_empty u hu0
  have hban : IsBanister Gᶜ (B ∪ {r}) (∅ : Set V) (A ∪ {b}) a T last :=
    ⟨hT, hToutNew, hleftNew, hrightNew, hInteriorAnti⟩
  exact ⟨stepConnected_compl_adjoin_stars G A B r b hS hr hb hrb,
    by simpa [T] using hban, by simpa [T] using hT3⟩

/-- If the right end sees every trajectory vertex except its terminal
right-star, strong maximality is contradicted. -/
theorem terminal_miss_absurd
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
    {b : V} (hb : IsRightStar G A C B b)
    {a : V} {R w : List V}
    (hopt : BOptimalBanister G A C B x a R b)
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z)
    (hRone : pathLength R = 1)
    {last : V} (hanti : IsAntipathFrom G (a :: w) a last)
    (hodd : Odd w.length) (hwlong : 1 < w.length)
    (hbeforeA : ∀ z ∈ w, z ≠ last → VertexComplete G z A)
    (hwB : ∀ z ∈ w, VertexComplete G z B)
    (hbnotw : b ∉ w)
    (hbBefore : ∀ z ∈ w, z ≠ last → G.Adj b z)
    (hbmiss : ¬ G.Adj b last)
    (hlast : IsRightStar G A C B last) : False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hab : G.Adj a b :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hopt.1.1 hRone
  have hReq : R = [a, b] := path_eq_pair_of_length_one hopt.1.1 hRone
  have hlastw : last ∈ w := by
    have hwne : w ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlastW : w.getLast? = some last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastW

  obtain ⟨i, hi, j, hj, habirth, hantiData, hidx⟩ :=
    trajectoryOfVertex_data hS hx hopt.1.2.2.1 htraj
  have hxjlast : x[j] = last := by
    exact Option.some.inj (hantiData.2.2.symm.trans hanti.2.2)
  have hji : j ≤ i := by
    obtain ⟨k, hk, hki, hxklast⟩ := hidx last hlastw
    have hkj : k = j := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      exact hxklast.trans hxjlast.symm
    omega

  let y : List V := x.take j
  have hylen : y.length = j := by simp [y, Nat.min_eq_left (Nat.le_of_lt hj)]
  have hyshort : y.length < x.length := by omega
  have hyseq : IsRightSequence G A C B y := by
    simpa [y] using rightSequence_take hx j
  have hxjanti : VertexAnticomplete G x[j] A := by
    simpa [hxjlast] using (show VertexAnticomplete G last A from
      fun z hz => hlast.2.2 z (Or.inl hz))
  obtain ⟨r₀, Q₀, hQ₀, q, hqy, hr₀q⟩ := hx.2.2 j hj hxjanti
  have hr₀nc : ¬ VertexComplete G r₀ {z : V | z ∈ y} := by
    intro hc
    exact hr₀q (hc q (by simpa [y] using hqy))
  obtain ⟨r, Q, ell, hell, hoptQ, hbirthQ, -⟩ :=
    exists_optimalBanister hyseq ⟨r₀, Q₀, hQ₀, hr₀nc⟩
  have hIH_y : ∀ (qseq : List V), qseq.length < y.length →
      IsRightSequence G A C B qseq →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (P : List V), BOptimalBanister G A C B qseq c P d →
      ∀ (z : List V), trajectoryOfVertex G A qseq c (c :: z) →
        TrajectoryConclusion G c P d z := by
    intro qseq hq hqseq d hd c P hP z hz
    exact hIH qseq (lt_trans hq hyshort) hqseq d hd c P hP z hz
  have hQone : pathLength Q = 1 :=
    optimal_banister_length_one hG hK4 heven h1br h2br hK hyseq hIH_y hoptQ
  have hQeq0 : Q = [r, x[j]] := path_eq_pair_of_length_one hoptQ.1.1 hQone
  have hQeq : Q = [r, last] := by simpa [hxjlast] using hQeq0
  have hQlast : IsBanister G A C B r Q last := by
    simpa [hxjlast] using hoptQ.1
  have hrlast : G.Adj r last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hQlast.1 hQone

  -- The birth of the auxiliary left-star in `y` is also a birth in `x`.
  have hellx : ell < x.length := by rw [hylen] at hell; omega
  have hyellx : y[ell]'hell = x[ell]'hellx := by simp [y]
  have hbirthQfull : birth G A C B x r x[ell] := by
    obtain ⟨hrleft, -, ell', hell', hell'eq, hell'non, hell'before⟩ := hbirthQ
    have hell'j : ell' < j := by simpa [hylen] using hell'
    have hell'x : ell' < x.length := by omega
    have htell' : y[ell']'hell' = x[ell']'hell'x := by simp [y]
    have hell'ell : ell' = ell := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      calc
        x[ell'] = y[ell'] := htell'.symm
        _ = y[ell] := hell'eq
        _ = x[ell] := hyellx
    subst ell'
    have hrncx : ¬ VertexComplete G r {z : V | z ∈ x} := by
      intro hc
      exact hell'non (by rw [hyellx]; exact hc x[ell] (List.getElem_mem hellx))
    refine ⟨hrleft, hrncx, ell, hellx, rfl, ?_, ?_⟩
    · simpa [hyellx] using hell'non
    · intro k hk
      have hky : k < y.length := by rw [hylen]; omega
      have htk : y[k]'hky = x[k]'(by omega) := by simp [y]
      simpa [htk] using hell'before k hk
  have hearlier : Earlier x x[ell] x[i] := by
    refine ⟨ell, i, hellx, hi, rfl, rfl, ?_⟩
    rw [hylen] at hell
    omega
  have hnolink := optimal_halves_not_linked hK.1.1.1.2.1.1 hopt hQlast
    hbirthQfull habirth hearlier
  have hsep := halves_anticomplete_of_not_linked hnolink
  have hbr : ¬ G.Adj b r := by
    apply hsep b (by rw [hReq]; simp) r (by rw [hQeq]; simp)

  have hCempty : C = ∅ := middle_empty_of_last_rightStar hG heven hK
    hopt.1.2.2.1 hlast hanti hodd hwlong hbeforeA hwB
  have hS0 : StepConnected G A (∅ : Set V) B := by simpa [hCempty] using hS
  have ha0 : IsLeftStar G A (∅ : Set V) B a := by
    simpa [hCempty] using hopt.1.2.2.1
  have hb0 : IsRightStar G A (∅ : Set V) B b := by
    simpa [hCempty] using hb
  have hr0 : IsLeftStar G A (∅ : Set V) B r := by
    simpa [hCempty] using hQlast.2.2.1
  have hlast0 : IsRightStar G A (∅ : Set V) B last := by
    simpa [hCempty] using hlast

  obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have ha₂A : a₂ ∈ A := hstep.2.1.2.1
  have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
  have hra₂ : G.Adj r a₂ := hr0.2.1 a₂ ha₂A
  have hrbne : r ≠ b := by
    intro he
    exact hb0.2.2 a₂ (Or.inl ha₂A) (he ▸ hra₂)
  have ha₂b₁ : ¬ G.Adj a₂ b₁ := by
    intro hadj
    have ha₂R := Workspace.ProofLemmas.PathBasics.head_mem hstep.2.1.1.2.1
    have hb₁R := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
    rcases (hstep.2.2.2 b₁ hb₁R a₂ ha₂R).mp hadj.symm with h | h
    · exact Set.disjoint_left.mp hS.1.1 ha₁A (h.1.symm ▸ hb₁B)
    · exact Set.disjoint_left.mp hS.1.1 ha₂A (h.2.symm ▸ hb₂B)

  let U : List V := b₁ :: ((a :: w) ++ [b])
  have hb₁aC : Gᶜ.Adj b₁ a := by
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hopt.1.2.2.1.1 (he.symm ▸ Or.inl (Or.inr hb₁B)),
      fun hadj => hopt.1.2.2.1.2.2 b₁ (Or.inl hb₁B) hadj.symm⟩
  have hblastC : Gᶜ.Adj b last := by
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hbnotw (he ▸ hlastw), hbmiss⟩
  have hb₁b : G.Adj b₁ b := (hb.2.1 b₁ hb₁B).symm
  have hb₁not : b₁ ∉ a :: w := by
    intro hm
    rcases List.mem_cons.mp hm with hba | hbw
    · exact hopt.1.2.2.1.1 (hba.symm ▸ Or.inl (Or.inr hb₁B))
    · exact bComplete_not_mem_strip hS (hwB b₁ hbw)
        (Or.inl (Or.inr hb₁B))
  have hbnot : b ∉ a :: w := by
    intro hm
    rcases List.mem_cons.mp hm with hba | hbw
    · exact hab.ne' hba
    · exact hbnotw hbw
  have hb₁other : ∀ z ∈ a :: w, z ≠ a → ¬ Gᶜ.Adj b₁ z := by
    intro z hz hza hadj
    have hzw : z ∈ w := (List.mem_cons.mp hz).resolve_left hza
    exact (G.compl_adj b₁ z).mp hadj |>.2 (hwB z hzw b₁ hb₁B).symm
  have hbother : ∀ z ∈ a :: w, z ≠ last → ¬ Gᶜ.Adj b z := by
    intro z hz hzlast hadj
    apply (G.compl_adj b z).mp hadj |>.2
    rcases List.mem_cons.mp hz with hza | hzw
    · subst z; exact hab.symm
    · exact hbBefore z hzw hzlast
  have hU : IsPathFrom Gᶜ U b₁ b := by
    simpa [U] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat
      hanti hb₁aC hblastC
      (fun hc => (G.compl_adj b₁ b).mp hc |>.2 hb₁b)
      hb₁b.ne hb₁not hbnot hb₁other hbother
  have hUodd : Odd (pathLength U) := by
    obtain ⟨k, hk⟩ := hodd
    refine ⟨k + 1, ?_⟩
    simp [U, pathLength]
    omega
  have hU5 : 5 ≤ pathLength U := by
    obtain ⟨k, hk⟩ := hodd
    simp [U, pathLength]
    omega

  let D : Set V := {r, a₂}
  have hDconn : ConnectedSet G D := by
    have hchain : List.IsChain G.Adj [r, a₂] := by simpa using hra₂
    have hset : D = {z : V | z ∈ [r, a₂]} := by
      ext z
      simp [D]
    rw [hset]
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isChain hchain
  have hDanti : AnticonnectedSet Gᶜ D := by
    simpa only [AnticonnectedSet, compl_compl] using hDconn
  have hrNotU : r ∉ U := by
    intro hru
    rcases List.mem_cons.mp (show r ∈ b₁ :: ((a :: w) ++ [b]) by simpa [U] using hru) with
      hrb₁ | hrrest
    · exact hr0.1 (hrb₁ ▸ Or.inl (Or.inr hb₁B))
    · rcases List.mem_append.mp hrrest with hrT | hrb'
      · rcases List.mem_cons.mp hrT with hra | hrw
        · have hraR : r ∈ Q := by rw [hQeq]; simp
          have haaR : a ∈ R := by rw [hReq]; simp
          exact (banisters_disjoint_of_halves_not_linked hK.1.1.1.2.1.1
            hopt.1 hQlast hnolink a haaR) (hra ▸ hraR)
        · obtain ⟨b', hb'B⟩ := hS.2.1.2
          exact hr0.2.2 b' (Or.inl hb'B) (hwB r hrw b' hb'B)
      · have : r = b := by simpa using hrb'
        exact hrbne this
  have ha₂NotU : a₂ ∉ U := by
    intro ha₂U
    rcases List.mem_cons.mp (show a₂ ∈ b₁ :: ((a :: w) ++ [b]) by simpa [U] using ha₂U) with
      ha₂b₁eq | hrest
    · exact Set.disjoint_left.mp hS.1.1 ha₂A (ha₂b₁eq ▸ hb₁B)
    · rcases List.mem_append.mp hrest with hT | ha₂b
      · rcases List.mem_cons.mp hT with ha₂a | ha₂w
        · exact hopt.1.2.2.1.1 (ha₂a ▸ Or.inl (Or.inl ha₂A))
        · exact bComplete_not_mem_strip hS (hwB a₂ ha₂w)
            (Or.inl (Or.inl ha₂A))
      · have : a₂ = b := by simpa using ha₂b
        exact hb.1 (this.symm ▸ Or.inl (Or.inl ha₂A))
  have hUD : ∀ z ∈ U, z ∉ D := by
    intro z hz hzD
    rcases hzD with hzr | hza₂
    · exact hrNotU (hzr ▸ hz)
    · exact ha₂NotU (hza₂ ▸ hz)
  have hb₁D : VertexComplete Gᶜ b₁ D := by
    intro z hz
    rcases hz with hzr | hza₂
    · subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hr0.1 (he ▸ Or.inl (Or.inr hb₁B)),
        fun hadj => hr0.2.2 b₁ (Or.inl hb₁B) hadj.symm⟩
    · subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => Set.disjoint_left.mp hS.1.1 ha₂A (he.symm ▸ hb₁B),
        fun hadj => ha₂b₁ hadj.symm⟩
  have hbD : VertexComplete Gᶜ b D := by
    intro z hz
    rcases hz with hzr | hza₂
    · subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨hrbne.symm, hbr⟩
    · subst z
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hb.1 (he.symm ▸ Or.inl (Or.inl ha₂A)),
        fun hadj => hb.2.2 a₂ (Or.inl ha₂A) hadj⟩
  have hIntU : SPGT.interior U = a :: w := by
    simp only [U, SPGT.interior, List.tail_cons]
    exact List.dropLast_concat
  have hNoInternalComplete : ∀ z ∈ SPGT.interior U,
      ¬ VertexComplete Gᶜ z D := by
    intro z hz hzc
    have hzT : z ∈ a :: w := by simpa [hIntU] using hz
    rcases List.mem_cons.mp hzT with hza | hzw
    · have hza₂G : G.Adj z a₂ := hza ▸ hopt.1.2.2.1.2.1 a₂ ha₂A
      exact (G.compl_adj z a₂).mp (hzc a₂ (Or.inr rfl)) |>.2 hza₂G
    · by_cases hzl : z = last
      · exact (G.compl_adj z r).mp (hzc r (Or.inl rfl)) |>.2 (hzl ▸ hrlast.symm)
      · exact (G.compl_adj z a₂).mp (hzc a₂ (Or.inr rfl)) |>.2
          (hbeforeA z hzw hzl a₂ ha₂A)
  have hNoCompleteEdge : ¬ ∃ u ∈ U, ∃ v ∈ U, EdgeComplete Gᶜ D u v := by
    rintro ⟨u, hu, v, hv, huv, huD, hvD⟩
    by_cases huI : u ∈ SPGT.interior U
    · exact hNoInternalComplete u huI huD
    by_cases hvI : v ∈ SPGT.interior U
    · exact hNoInternalComplete v hvI hvD
    have huEnd : u = b₁ ∨ u = b := by
      by_cases hub₁ : u = b₁
      · exact Or.inl hub₁
      right
      by_contra hub
      exact huI ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).2
        ⟨hu, hub₁, hub⟩)
    have hvEnd : v = b₁ ∨ v = b := by
      by_cases hvb₁ : v = b₁
      · exact Or.inl hvb₁
      right
      by_contra hvb
      exact hvI ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).2
        ⟨hv, hvb₁, hvb⟩)
    rcases huEnd with hub₁ | hub <;> rcases hvEnd with hvb₁ | hvb
    · exact huv.ne (hub₁.trans hvb₁.symm)
    · exact (G.compl_adj b₁ b).mp (hub₁ ▸ hvb ▸ huv) |>.2 hb₁b
    · exact (G.compl_adj b b₁).mp (hub ▸ hvb₁ ▸ huv) |>.2 hb₁b.symm
    · exact huv.ne (hub.trans hvb.symm)

  rcases Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ
      (Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG) D hDanti U b₁ b
      hU hUD hUodd hb₁D hbD with hedge | hleap | hshort
  · exact hNoCompleteEdge hedge
  · obtain ⟨-, u, huD, v, hvD, huv⟩ := hleap
    have huvFull := huv
    obtain ⟨-, -, huvne, -, -, hvadj⟩ := huv
    have hlastU : last ∈ U := by simp [U, hlastw]
    have hlastPen : last = U[U.length - 2]'(by
        rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hU5
        omega) :=
      (adj_last_iff_eq_penultimate hU (by
        rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hU5
        omega) hlastU).mp hblastC.symm
    have horient : u = r ∧ v = a₂ := by
      simp only [D, Set.mem_insert_iff, Set.mem_singleton_iff] at huD hvD
      rcases huD with hur | hua₂ <;> rcases hvD with hvr | hva₂
      · exact absurd (hur.trans hvr.symm) huvne
      · exact ⟨hur, hva₂⟩
      · exfalso
        subst u; subst v
        have hlenU : 6 ≤ U.length := by
          rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hU5
          omega
        have hrc : Gᶜ.Adj r (U[U.length - 2]'(by omega)) :=
          (hvadj (U.length - 2) (by omega)).2 (Or.inr (Or.inl rfl))
        rw [← hlastPen] at hrc
        exact (G.compl_adj r last).mp hrc |>.2 hrlast
      · exact absurd (hua₂.trans hva₂.symm) huvne
    obtain ⟨hur, hva₂⟩ := horient
    subst u; subst v
    have huD' : r ∈ D := Or.inl rfl
    have hvD' : a₂ ∈ D := Or.inr rfl
    obtain ⟨houter₀, -⟩ := leap_inner_path hU hU5 hUD huD' hvD' huvFull
    have houter : IsPathFrom Gᶜ (r :: ((a :: w) ++ [a₂])) r a₂ := by
      simpa only [hIntU] using houter₀
    have hT3 : 3 ≤ pathLength (a :: w) := by
      obtain ⟨k, hk⟩ := hodd
      simp [pathLength]
      omega
    have hstairs := staircase_compl_adjoin_stars G A B r b a last a₂ w
      hS0 hr0 hb0 ha0 hlast0 (fun hadj => hbr hadj.symm) hab hrlast hbmiss
      hbeforeA hwB hbBefore hbnotw hanti hT3 houter
    have hno : ¬ ∃ (A' C' B' : Set V) (a' : V) (P : List V) (b' : V),
        IsStaircase Gᶜ A' C' B' a' P b' ∧
          (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C') :=
      hK.2.resolve_left (by rw [hCempty]; simp)
    apply hno
    refine ⟨B ∪ {r}, ∅, A ∪ {b}, a, a :: w, last, hstairs, ?_⟩
    constructor
    · intro z hz
      rcases hz with (hzA | hzB) | hzC
      · exact Or.inl (Or.inr (Or.inl hzA))
      · exact Or.inl (Or.inl (Or.inl hzB))
      · exact absurd (hCempty ▸ hzC) (Set.notMem_empty z)
    · intro hback
      have hrnew : r ∈ (B ∪ {r}) ∪ (A ∪ {b}) ∪ (∅ : Set V) :=
        Or.inl (Or.inl (Or.inr rfl))
      rcases hback hrnew with (hrA | hrB) | hrC
      · exact hr0.1 (Or.inl (Or.inl hrA))
      · exact hr0.1 (Or.inl (Or.inr hrB))
      · exact absurd (hCempty ▸ hrC) (Set.notMem_empty r)
  · obtain ⟨hthree, -⟩ := hshort
    omega

end Workspace.ProofLemmas.Thm131LastMiss
