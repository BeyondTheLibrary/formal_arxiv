import Workspace.ProofLemmas.Thm131LastMiss
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

/-!
# Claim (4) of the printed proof of 13.1

PAPER (printed p. 80):

*"(4) If `n = 1` then the theorem holds.*

*For let `n = 1`, and choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂` with `a₁` nonadjacent
to `v_m`.  Suppose first that `a` has no neighbour in `R'`.  Now `a` is
`V`-complete, and either `w₁` is the unique `V`-complete vertex in `R'`, or `R'`
has length 1 and there is an odd antipath `Q` between `r'` and `w₁` with interior
in `V`.  In the first case, `a-a₁-r'-R'-w₁` is an odd path, its ends are
`V`-complete, its internal vertices are not, and the `V`-complete vertex `b₂` has
no neighbour in its interior, contrary to 2.2.  In the second case,
`a-r'-Q-w₁-a` is an odd antihole.  This proves that `a` has a neighbour in `R'`.
Now suppose it has a neighbour different from `r'`; then `R'` has length > 1, and
so `w₁` is the unique `V`-complete vertex in `R'`; and there is a path `P'` say
from `a` to `w₁` with interior in `R' \ r'`.  Since the ends of this path are
`V`-complete and its internal vertices are not, and the `V`-complete vertex `b₁`
has no neighbour in its interior, it is even by 2.2.  But it can be completed to
an odd hole via `w₁-b₁-R₁-a₁-a`, a contradiction.  This proves that `r'` is the
unique neighbour of `a` in `R'`.  Since `a-r'-R'-w₁-b₁-b-R-a` is not an odd hole,
it follows from (3) that `w₁` has a neighbour in `R`.  If `b` is its unique
neighbour in `R` then the theorem holds, so we assume not.  Then there is a path
`P` say from `w₁` to `a` with interior in `R \ b`.  Since `w₁-P-a-r'-R'-w₁` is a
hole it follows that `P` is even; but `P` can be completed via `a-a₁-R₁-b₁-w₁`, a
contradiction.  This proves (4)."*
-/

namespace Workspace.ProofLemmas.Thm131Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131EdgeCases
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Claim (4) of the printed proof: a trajectory with a single tail vertex
already forces the conclusion of 13.1. -/
theorem claim_four
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
    {b last : V} (hb : IsRightStar G A C B b)
    (hlast : IsRightStar G A C B last)
    {a : V} {P w : List V}
    (hopt : BOptimalBanister G A C B x a P b)
    (htraj : trajectoryOfVertex G A x a (a :: w))
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hwone : w.length = 1) :
    TrajectoryConclusion G a P b w := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hPodd : Odd (pathLength P) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a b P hopt.1).2
  have hPlenEq : P.length = pathLength P + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hopt.1.1.1
  have hP2 : 2 ≤ P.length := by obtain ⟨mm, hmm⟩ := hPodd; omega
  have hPpos : 0 < P.length := by omega
  have hP0 : P[0]'hPpos = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hopt.1.1.2.1 hPpos
  have hPlastElem : P[P.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hopt.1.1.2.2 hPpos
  have haP : a ∈ P := Workspace.ProofLemmas.PathBasics.head_mem hopt.1.1.2.1
  have hbP : b ∈ P := Workspace.ProofLemmas.PathBasics.getLast_mem hopt.1.1.2.2
  have hbane : b ≠ a :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hopt.1.1 (by omega)).symm
  have hPcons : P = a :: P.tail := by
    obtain ⟨hd, tl, hPeq⟩ : ∃ hd tl, P = hd :: tl := by
      cases hPc : P with
      | nil => exact absurd (hPc ▸ hopt.1.1.2.1) (by simp)
      | cons hd tl => exact ⟨hd, tl, rfl⟩
    subst hPeq
    have hhd : hd = a := by simpa using hopt.1.1.2.1
    simp [hhd]
  have hPtail : ∀ u ∈ P, u ≠ a → u ∈ P.tail := by
    intro u hu hua
    rw [hPcons] at hu
    rcases List.mem_cons.mp hu with h | h
    · exact absurd h hua
    · exact h
  have hbtail : b ∈ P.tail := hPtail b hbP hbane
  have hPinterior : ∀ u ∈ P, u ≠ a → u ≠ b → u ∈ interior P := by
    intro u hu hua hub
    exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hopt.1.1).2
      ⟨hu, hua, hub⟩
  have hantiOne : pathLength (a :: w) = 1 := by simp [pathLength, hwone]
  have hac : Gᶜ.Adj a last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hanti hantiOne
  have hanlast : ¬ G.Adj a last := hac.2
  have hlastw : last ∈ w := by
    have hwne : w ≠ [] := by
      intro hw
      subst w
      simp at hwone
    have hlastW : w.getLast? = some last := by
      simpa [List.getLast?_cons_of_ne_nil hwne] using hanti.2.2
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastW

  obtain ⟨i, hi, j, hj, habirth, hantiData, hidx⟩ :=
    trajectoryOfVertex_data hS hx hopt.1.2.2.1 htraj
  have hxjlast : x[j] = last :=
    Option.some.inj (hantiData.2.2.symm.trans hanti.2.2)
  have hji : j ≤ i := by
    obtain ⟨k, hk, hki, hxklast⟩ := hidx last hlastw
    have hkj : k = j := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      exact hxklast.trans hxjlast.symm
    omega
  have habirthFull := habirth
  obtain ⟨-, -, ib, hib, hibEq, hibNon, hibBefore⟩ := habirth
  have hibi : ib = i := by
    apply (List.Nodup.getElem_inj_iff hx.1.1).mp
    exact hibEq
  subst ib
  have hij : i = j := by
    by_contra hne
    have hji' : j < i := by omega
    exact hanlast (by simpa [hxjlast] using hibBefore j hji')
  subst j
  have hxilast : x[i] = last := hxjlast

  let y : List V := x.take i
  have hylen : y.length = i := by simp [y, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hyshort : y.length < x.length := by omega
  have hyseq : IsRightSequence G A C B y := by
    simpa [y] using rightSequence_take hx i
  have hxianti : VertexAnticomplete G x[i] A := by
    simpa [hxilast] using (show VertexAnticomplete G last A from
      fun z hz => hlast.2.2 z (Or.inl hz))
  obtain ⟨r₀, Q₀, hQ₀, q₀, hq₀y, hr₀q₀⟩ := hx.2.2 i hi hxianti
  have hr₀nc : ¬ VertexComplete G r₀ {z : V | z ∈ y} := by
    intro hc
    exact hr₀q₀ (hc q₀ (by simpa [y] using hq₀y))
  obtain ⟨r, Q, ell, hell, hoptQ, hbirthQ, -⟩ :=
    exists_optimalBanister hyseq ⟨r₀, Q₀, hQ₀, hr₀nc⟩
  have hIH_y : ∀ (qseq : List V), qseq.length < y.length →
      IsRightSequence G A C B qseq →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (T : List V), BOptimalBanister G A C B qseq c T d →
      ∀ (z : List V), trajectoryOfVertex G A qseq c (c :: z) →
        TrajectoryConclusion G c T d z := by
    intro qseq hq hqseq d hd c T hT z hz
    exact hIH qseq (lt_trans hq hyshort) hqseq d hd c T hT z hz
  have hQlast : IsBanister G A C B r Q last := by simpa [hxilast] using hoptQ.1

  -- Structure of the auxiliary banister `Q = r'-R'-w₁`.
  have hQodd : Odd (pathLength Q) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS r last Q hQlast).2
  have hQlen : Q.length = pathLength Q + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hQlast.1.1
  have hQ2 : 2 ≤ Q.length := by obtain ⟨m, hm⟩ := hQodd; omega
  have hrQ : r ∈ Q := Workspace.ProofLemmas.PathBasics.head_mem hQlast.1.2.1
  have hlastQ : last ∈ Q := Workspace.ProofLemmas.PathBasics.getLast_mem hQlast.1.2.2
  have hrlastne : r ≠ last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hQlast.1 (by omega)
  have hdropIff : ∀ z : V, z ∈ Q.dropLast ↔ (z ∈ Q ∧ z ≠ last) := fun z =>
    HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hQlast.1
  have hrdrop : r ∈ Q.dropLast := (hdropIff r).2 ⟨hrQ, hrlastne⟩
  have hdropCase : ∀ z ∈ Q.dropLast, z = r ∨ z ∈ interior Q := by
    intro z hz
    obtain ⟨hzQ, hzl⟩ := (hdropIff z).1 hz
    by_cases hzr : z = r
    · exact Or.inl hzr
    · exact Or.inr
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
          ⟨hzQ, hzr, hzl⟩)
  have hdropAntiB : ∀ z ∈ Q.dropLast, ∀ u ∈ B, ¬ G.Adj z u := by
    intro z hz u hu
    rcases hdropCase z hz with hzr | hzint
    · exact hzr ▸ hQlast.2.2.1.2.2 u (Or.inl hu)
    · exact hQlast.2.2.2.2 z hzint u (Or.inl (Or.inr hu))
  have hQ0 : Q[0]'(by omega) = r :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQlast.1.2.1 (by omega)
  have hQlastElem : Q[Q.length - 1]'(by omega) = last :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQlast.1.2.2 (by omega)

  -- Transfer the earlier birth into the full sequence, to obtain separation
  -- of the two banisters (claim (3)).
  have hellx : ell < x.length := by rw [hylen] at hell; omega
  have hyellx : y[ell]'hell = x[ell]'hellx := by simp [y]
  have hbirthQfull : birth G A C B x r x[ell] := by
    obtain ⟨hrleft, -, ell', hell', hell'eq, hell'non, hell'before⟩ := hbirthQ
    have hell'x : ell' < x.length := by
      have : ell' < i := by simpa [hylen] using hell'
      omega
    have htell' : y[ell']'hell' = x[ell']'hell'x := by simp [y]
    have hell'ell : ell' = ell := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      exact htell'.symm.trans (hell'eq.trans hyellx)
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
    exact hell
  have hnolink := optimal_halves_not_linked hK.1.1.1.2.1.1 hopt hQlast
    hbirthQfull habirthFull hearlier
  have hdisj := banisters_disjoint_of_halves_not_linked hK.1.1.1.2.1.1
    hopt.1 hQlast hnolink
  have hsep := halves_anticomplete_of_not_linked hnolink
  have hbr : ¬ G.Adj b r := hsep b hbtail r hrdrop
  have haNotQ : a ∉ Q := hdisj a haP
  have harne : a ≠ r := fun he => haNotQ (he ▸ hrQ)

  -- The trajectory `r'-v₁-⋯-v_m` and the inductive hypothesis at `r'`.
  obtain ⟨t, birthIndex, hbirthIndex, lastIndex, hlastIndex,
      htrajR, hbirthAgain, hantiR₀, htidx⟩ :=
    exists_trajectoryOfVertex_of_leftStar hS hyseq hoptQ.1.2.2.1 hoptQ.2.1
  let endR : V := y[lastIndex]
  have hantiR : IsAntipathFrom G (r :: t) r endR := by
    simpa [endR] using hantiR₀
  have hoptQlast : BOptimalBanister G A C B y r Q last := by
    simpa [hxilast] using hoptQ
  have hrec := hIH y hyshort hyseq last hlast r Q hoptQlast t htrajR
  have htodd : Odd t.length := hrec.1
  have htpos : 0 < t.length := by obtain ⟨k, hk⟩ := htodd; omega
  have htlast : endR ∈ t := by
    have htne : t ≠ [] := List.ne_nil_of_length_pos htpos
    have hlastT : t.getLast? = some endR := by
      simpa [List.getLast?_cons_of_ne_nil htne] using hantiR.2.2
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hlastT
  have htB : ∀ u ∈ t, VertexComplete G u B := by
    intro u hu
    obtain ⟨k, hk, -, hku⟩ := htidx u hu
    simpa [hku] using hyseq.1.2 y[k] (List.getElem_mem hk)
  have haT : VertexComplete G a {u : V | u ∈ t} := by
    intro u hu
    obtain ⟨k, hk, -, hku⟩ := htidx u hu
    have hki : k < i := by simpa [hylen] using hk
    have htake : y[k]'hk = x[k]'(by omega) := by simp [y]
    have hadj := hibBefore k hki
    rw [← htake, hku] at hadj
    exact hadj
  have htanti : AnticonnectedSet G {u : V | u ∈ t} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (HyperprismRungStructure.isPathList_tail hantiR.1 (by simp; omega))
  have hlastNotY : last ∉ y := by
    intro hm
    obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.mp hm
    have hklt : k < i := by simpa [hylen] using hk
    have htake : y[k]'hk = x[k]'(by omega) := by simp [y]
    have heq : x[k] = x[i] := by simpa [hxilast, htake] using hkeq
    exact (by omega : ¬ k = i) ((List.Nodup.getElem_inj_iff hx.1.1).mp heq)
  have hQtDisj : ∀ q ∈ Q, q ∉ t := by
    intro q hqQ hqt
    obtain ⟨k, hk, -, hkq⟩ := htidx q hqt
    have hqy : q ∈ y := by rw [← hkq]; exact List.getElem_mem hk
    by_cases hqr : q = r
    · exact htrajR.1.2.1 (hqr ▸ hqy)
    by_cases hqlast : q = last
    · exact hlastNotY (hqlast ▸ hqy)
    obtain ⟨b', hb'B⟩ := hS.2.1.2
    exact hQlast.2.2.2.2 q
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
        ⟨hqQ, hqr, hqlast⟩) b' (Or.inl (Or.inr hb'B)) (htB q hqt b' hb'B)

  -- PAPER: *"Suppose first that `a` has no neighbour in `R'`. …  This proves
  -- that `a` has a neighbour in `R'`."*
  have hnbex : ∃ z ∈ Q, G.Adj a z := by
    by_contra hnb
    push Not at hnb
    obtain ⟨a₁, ha₁A, henda₁⟩ := trajectory_last_misses_left htrajR hantiR
    obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
    rcases hrec.2 with hunique | halt
    · have ha₁r : G.Adj a₁ r := (hQlast.2.2.1.2.1 a₁ ha₁A).symm
      have ha₁notQ : a₁ ∉ Q := by
        intro hm
        exact hQlast.2.1 a₁ hm (Or.inl (Or.inl ha₁A))
      have ha₁other : ∀ q ∈ Q, q ≠ r → ¬ G.Adj a₁ q := by
        intro q hq hqr hadj
        by_cases hql : q = last
        · exact hlast.2.2 a₁ (Or.inl ha₁A) (hql ▸ hadj.symm)
        · exact hQlast.2.2.2.2 q
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
              ⟨hq, hqr, hql⟩) a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
      have ha₁Q : IsPathFrom G (a₁ :: Q) a₁ last :=
        Workspace.ProofLemmas.PathAttach.isPathFrom_cons hQlast.1 ha₁r ha₁notQ ha₁other
      have haa₁ : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
      have haNotA₁Q : a ∉ a₁ :: Q := by
        intro hm
        rcases List.mem_cons.mp hm with heq | hmQ
        · exact hopt.1.2.2.1.1 (heq ▸ Or.inl (Or.inl ha₁A))
        · exact haNotQ hmQ
      have haOther : ∀ q ∈ a₁ :: Q, q ≠ a₁ → ¬ G.Adj a q := by
        intro q hq hqa₁ hadj
        rcases List.mem_cons.mp hq with heq | hqQ
        · exact hqa₁ heq
        · exact hnb q hqQ hadj
      let L : List V := a :: a₁ :: Q
      have hL : IsPathFrom G L a last := by
        simpa [L] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons
          ha₁Q haa₁ haNotA₁Q haOther
      have hLodd : Odd (pathLength L) := by
        obtain ⟨m, hm⟩ := hQodd
        refine ⟨m + 1, ?_⟩
        simp only [L, pathLength, List.length_cons]
        omega
      have hLout : ∀ u ∈ L, u ∉ {q : V | q ∈ t} := by
        intro u hu hut
        simp only [L, List.mem_cons] at hu
        rcases hu with hua | hua₁ | huQ
        · subst u; exact G.irrefl (haT a hut)
        · exact bComplete_not_mem_strip hS (htB u hut)
            (hua₁ ▸ Or.inl (Or.inl ha₁A))
        · exact hQtDisj u huQ hut
      have hvT : VertexComplete G last {q : V | q ∈ t} := by
        intro q hq
        exact (hunique last hlastQ).2 rfl q hq
      have ha₁NotComplete : ¬ VertexComplete G a₁ {q : V | q ∈ t} := by
        intro hc
        exact henda₁ (hc endR htlast).symm
      have hcomplete : ∀ u ∈ L,
          VertexComplete G u {q : V | q ∈ t} → u = a ∨ u = last := by
        intro u hu hc
        simp only [L, List.mem_cons] at hu
        rcases hu with hua | hua₁ | huQ
        · exact Or.inl hua
        · exact absurd (hua₁ ▸ hc) ha₁NotComplete
        · exact Or.inr ((hunique u huQ).1 hc)
      have hnoedge : ¬ ∃ u ∈ L, ∃ q ∈ L,
          EdgeComplete G {s : V | s ∈ t} u q := by
        rintro ⟨u, hu, q, hq, huq, huT, hqT⟩
        rcases hcomplete u hu huT with hua | hul <;>
          rcases hcomplete q hq hqT with hqa | hql
        · exact huq.ne (hua.trans hqa.symm)
        · exact hanlast (hua ▸ hql ▸ huq)
        · exact hanlast (hul ▸ hqa ▸ huq.symm)
        · exact huq.ne (hul.trans hql.symm)
      have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
      have hb₂T : VertexComplete G b₂ {q : V | q ∈ t} := by
        intro q hq
        exact (htB q hq b₂ hb₂B).symm
      obtain ⟨u, huInt, hb₂u⟩ := Workspace.Statements.S02.SPGT.thm_2_2
        G hG {q : V | q ∈ t} htanti L a last hL hLout hLodd haT hvT
          hnoedge b₂ hb₂T
      have huL := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1 huInt
      simp only [L, List.mem_cons] at huL
      rcases huL.1 with hua | hua₁ | huQ
      · exact huL.2.1 hua
      · subst u
        have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
          intro hadj
          rcases (hstep.2.2.2 a₁
            (Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1) b₂
            (Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2)).1 hadj with
            ⟨-, hbad⟩ | ⟨hbad, -⟩
          · exact Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1
              (hbad ▸ hstep.2.1.2.2.1)
          · exact Set.disjoint_left.mp hS.1.1 ha₁A
              (hbad ▸ hstep.1.2.2.1)
        exact ha₁b₂ hb₂u.symm
      · by_cases hur : u = r
        · exact hQlast.2.2.1.2.2 b₂ (Or.inl hb₂B) (hur ▸ hb₂u.symm)
        · exact hQlast.2.2.2.2 u
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
              ⟨huQ, hur, huL.2.2⟩) b₂ (Or.inl (Or.inr hb₂B)) hb₂u.symm
    · obtain ⟨hQone, m, hmEven, hm1, hmt, hmanti⟩ := halt
      have hrlast : G.Adj r last :=
        Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one
          hQlast.1 hQone
      let U : List V := r :: (t.take m ++ [last])
      have hU : IsAntipathFrom G U r last := by
        exact ⟨by simpa [U] using hmanti, by simp [U],
          by simp [U, List.getLast?_cons_of_ne_nil]⟩
      have haUint : ∀ u ∈ interior U, u ∈ {q : V | q ∈ t} := by
        intro u hu
        have hd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).1 hu
        have humem := hd.1
        change u ∈ r :: (t.take m ++ [last]) at humem
        simp at humem
        rcases humem with hur | hut | hul
        · exact absurd hur hd.2.1
        · exact List.mem_of_mem_take hut
        · exact absurd hul hd.2.2
      have halastne : a ≠ last := hac.ne
      have hUeven := Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
        hG hrlast haT (hnb r hrQ) hanlast harne halastne hU haUint
      have hmle : m ≤ t.length := by omega
      have hUlen : pathLength U = m + 1 := by
        simp [U, pathLength, List.length_take, Nat.min_eq_left hmle]
      obtain ⟨ke, hke⟩ := hUeven
      obtain ⟨km, hkm⟩ := hmEven
      rw [hUlen] at hke
      omega

  -- PAPER: *"Now suppose it has a neighbour different from `r'` … This proves
  -- that `r'` is the unique neighbour of `a` in `R'`."*
  have haonly : ∀ z ∈ Q, G.Adj a z → z = r := by
    intro z hzQ hza
    by_contra hzr
    have hzl : z ≠ last := fun he => hanlast (he ▸ hza)
    have hzint : z ∈ interior Q :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
        ⟨hzQ, hzr, hzl⟩
    obtain ⟨kz, hkz, hkz1, hkz2, hkzz⟩ :=
      Workspace.ProofLemmas.PathBasics.exists_getElem_of_mem_interior hQlast.1.1 hzint
    have hQ4 : 4 ≤ Q.length := by
      obtain ⟨mm, hmm⟩ := hQodd
      have : Q.length ≠ 2 := by
        intro he
        omega
      omega
    -- the last neighbour of `a` along `R'`
    have hexn : ∃ k : ℕ, ∃ hk : k < Q.length, 1 ≤ k ∧ G.Adj a (Q[k]'hk) :=
      ⟨kz, hkz, hkz1, by rw [hkzz]; exact hza⟩
    obtain ⟨m, hm, hm1, hmadj, hmmax⟩ :
        ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ G.Adj a (Q[m]'hm) ∧
          ∀ (k : ℕ) (hk : k < Q.length), m < k → ¬ G.Adj a (Q[k]'hk) := by
      classical
      obtain ⟨mz, hmz, hmz1, hmzadj⟩ := hexn
      have hmzP : (fun k => ∃ hk : k < Q.length, 1 ≤ k ∧ G.Adj a (Q[k]'hk)) mz :=
        ⟨hmz, hmz1, hmzadj⟩
      have hspec := Nat.findGreatest_spec
        (P := fun k => ∃ hk : k < Q.length, 1 ≤ k ∧ G.Adj a (Q[k]'hk))
        (m := mz) (n := Q.length) (le_of_lt hmz) hmzP
      obtain ⟨hlt, h1, hadj⟩ := hspec
      refine ⟨_, hlt, h1, hadj, ?_⟩
      intro k hk hgt hadjk
      have hle : k ≤ Nat.findGreatest
          (fun k => ∃ hk : k < Q.length, 1 ≤ k ∧ G.Adj a (Q[k]'hk)) Q.length :=
        Nat.le_findGreatest (le_of_lt hk) ⟨hk, by omega, hadjk⟩
      omega
    have hmlt : m < Q.length - 1 := by
      rcases (by omega : m < Q.length - 1 ∨ m = Q.length - 1) with h | h
      · exact h
      · exact absurd (by rw [← hQlastElem]; exact (getElem_congr rfl h hm :
          Q[m] = Q[Q.length - 1]'(by omega)) ▸ hmadj) hanlast
    -- `P' = a-Q[m]-⋯-wₙ`
    set P' : List V := a :: Q.drop m with hP'def
    have hdroppath : IsPathList G (Q.drop m) :=
      Workspace.ProofLemmas.PathBasics.isPathList_drop hQlast.1.1 hm
    have hdroplen : (Q.drop m).length = Q.length - m := List.length_drop
    have hdropget : ∀ (k : ℕ) (hk : k < (Q.drop m).length),
        (Q.drop m)[k]'hk = Q[m + k]'(by rw [hdroplen] at hk; omega) := by
      intro k hk
      simp
    have hdropFrom : IsPathFrom G (Q.drop m) (Q[m]'hm) last := by
      refine ⟨hdroppath, ?_, ?_⟩
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [hdroplen]; omega)]
        rw [hdropget 0 (by rw [hdroplen]; omega)]
        simp
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by rw [hdroplen]; omega)]
        rw [hdropget ((Q.drop m).length - 1) (by rw [hdroplen]; omega)]
        have : m + ((Q.drop m).length - 1) = Q.length - 1 := by rw [hdroplen]; omega
        rw [(getElem_congr rfl this (by rw [hdroplen] at *; omega) :
          Q[m + ((Q.drop m).length - 1)]'(by rw [hdroplen] at *; omega)
            = Q[Q.length - 1]'(by omega))]
        exact congrArg some hQlastElem
    have hanotdrop : a ∉ Q.drop m := fun hmem => haNotQ (List.mem_of_mem_drop hmem)
    have haother : ∀ z' ∈ Q.drop m, z' ≠ Q[m]'hm → ¬ G.Adj a z' := by
      intro z' hz' hz'ne hadj
      obtain ⟨k, hk, hkz'⟩ := List.mem_iff_getElem.mp hz'
      rw [hdropget k hk] at hkz'
      have hmk : m + k < Q.length := by rw [hdroplen] at hk; omega
      have hk0 : k ≠ 0 := by
        intro he
        apply hz'ne
        subst he
        rw [← hkz']
        exact getElem_congr rfl (show m + 0 = m by omega) hmk
      exact hmmax (m + k) hmk (by omega) (by rw [hkz']; exact hadj)
    have hP' : IsPathFrom G P' a last :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_cons hdropFrom hmadj hanotdrop haother
    have hP'int : ∀ z' ∈ interior P', z' ∈ interior Q := by
      intro z' hz'
      have hd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP').1 hz'
      have : z' ∈ Q.drop m := by
        rcases List.mem_cons.mp (by simpa [hP'def] using hd.1) with h | h
        · exact absurd h hd.2.1
        · exact h
      obtain ⟨k, hk, hkz'⟩ := List.mem_iff_getElem.mp this
      rw [hdropget k hk] at hkz'
      rw [← hkz']
      exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQlast.1.1
        (by rw [hdroplen] at hk; omega) (by omega)
        (by
          have : z' ≠ last := hd.2.2
          rw [← hkz'] at this
          have hne : m + k ≠ Q.length - 1 := by
            intro he
            exact this ((getElem_congr rfl he (by rw [hdroplen] at hk; omega) :
              Q[m + k]'(by rw [hdroplen] at hk; omega)
                = Q[Q.length - 1]'(by omega)).trans hQlastElem)
          rw [hdroplen] at hk
          omega)
    -- the unique `V`-complete vertex of `R'` is `w₁`
    have hunique : ∀ q ∈ Q, (VertexComplete G q {u : V | u ∈ t} ↔ q = last) := by
      rcases hrec.2 with hu | halt
      · exact hu
      · exfalso
        obtain ⟨hQone, -⟩ := halt
        omega
    have hlastT : VertexComplete G last {u : V | u ∈ t} := (hunique last hlastQ).2 rfl
    have hP'out : ∀ u ∈ P', u ∉ {q : V | q ∈ t} := by
      intro u hu hut
      rcases List.mem_cons.mp (by simpa [hP'def] using hu) with h | h
      · exact G.irrefl (h ▸ haT u hut)
      · exact hQtDisj u (List.mem_of_mem_drop h) hut
    have hP'noedge : ¬ ∃ u ∈ P', ∃ v ∈ P', EdgeComplete G {q : V | q ∈ t} u v := by
      rintro ⟨u, hu, v, hv, huv, huT, hvT⟩
      have hkey : ∀ z' ∈ P', VertexComplete G z' {q : V | q ∈ t} → z' = a ∨ z' = last := by
        intro z' hz' hz'c
        rcases List.mem_cons.mp (by simpa [hP'def] using hz') with h | h
        · exact Or.inl h
        · exact Or.inr ((hunique z' (List.mem_of_mem_drop h)).1 hz'c)
      rcases hkey u hu huT with hua | hul <;> rcases hkey v hv hvT with hva | hvl
      · exact huv.ne (hua.trans hva.symm)
      · exact hanlast (hua ▸ hvl ▸ huv)
      · exact hanlast (hul ▸ hva ▸ huv.symm)
      · exact huv.ne (hul.trans hvl.symm)
    obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
    obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
    have hb₁B : b₁ ∈ B := hstep.1.2.2.1
    have hb₁T : VertexComplete G b₁ {q : V | q ∈ t} := fun q hq =>
      (htB q hq b₁ hb₁B).symm
    have hP'even : Even (pathLength P') := by
      rcases Nat.even_or_odd (pathLength P') with hE | hodd'
      · exact hE
      exfalso
      obtain ⟨u, huInt, hb₁u⟩ := Workspace.Statements.S02.SPGT.thm_2_2
        G hG {q : V | q ∈ t} htanti P' a last hP' hP'out hodd' haT hlastT
          hP'noedge b₁ hb₁T
      exact hQlast.2.2.2.2 u (hP'int u huInt) b₁ (Or.inl (Or.inr hb₁B)) hb₁u.symm
    -- PAPER: *"But it can be completed to an odd hole via `w₁-b₁-R₁-a₁-a`."*
    have ha₁a : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
    have hb₁last : G.Adj b₁ last := (hlast.2.1 b₁ hb₁B).symm
    have hR₁ : IsRungOfStrip G A C B a₁ R₁ b₁ := hstep.1
    have hR₁odd : Odd (pathLength R₁) :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a₀ b₀ R₀
        hK.1.1.2.1).1 a₁ R₁ b₁ hR₁
    have hlastnotR₁ : last ∉ R₁ := fun hmem =>
      bComplete_not_mem_strip hS hlast.2.1 (rung_mem_strip hR₁ last hmem)
    have hlastother : ∀ z' ∈ R₁, z' ≠ b₁ → ¬ G.Adj last z' := by
      intro z' hz' hz'b hadj
      have hz'strip := rung_mem_strip hR₁ z' hz'
      rcases hz'strip with (hz'A | hz'B) | hz'C
      · exact hlast.2.2 z' (Or.inl hz'A) hadj
      · exact hz'b (hR₁.2.2.2.2.1 z' hz' hz'B)
      · exact hlast.2.2 z' (Or.inr hz'C) hadj
    have hL₂' : IsPathFrom G (R₁ ++ [last]) a₁ last :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_concat hR₁.1 hb₁last.symm
        hlastnotR₁ hlastother
    have hanotR₁ : a ∉ R₁ ++ [last] := by
      intro hmem
      rcases List.mem_append.mp hmem with h | h
      · exact hopt.1.2.2.1.1 (rung_mem_strip hR₁ a h)
      · exact hac.ne (by simpa using h)
    have haotherR₁ : ∀ z' ∈ R₁ ++ [last], z' ≠ a₁ → ¬ G.Adj a z' := by
      intro z' hz' hz'a hadj
      rcases List.mem_append.mp hz' with h | h
      · have hz'strip := rung_mem_strip hR₁ z' h
        rcases hz'strip with (hz'A | hz'B) | hz'C
        · exact hz'a (hR₁.2.2.2.1 z' h hz'A)
        · exact hopt.1.2.2.1.2.2 z' (Or.inl hz'B) hadj
        · exact hopt.1.2.2.1.2.2 z' (Or.inr hz'C) hadj
      · exact hanlast ((by simpa using h : z' = last) ▸ hadj)
    have hL₂ : IsPathFrom G (a :: (R₁ ++ [last])) a last :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_cons hL₂' ha₁a hanotR₁ haotherR₁
    have hL₂int : SPGT.interior (a :: (R₁ ++ [last])) = R₁ := by
      simp only [SPGT.interior, List.tail_cons]
      exact List.dropLast_concat
    have hIntDisj : ∀ u ∈ interior P', u ∉ interior (a :: (R₁ ++ [last])) := by
      intro u hu hv
      rw [hL₂int] at hv
      exact hQlast.2.1 u
        (Workspace.ProofLemmas.PathBasics.interior_subset (hP'int u hu))
        (rung_mem_strip hR₁ u hv)
    have hIntAnti : ∀ u ∈ interior P', ∀ v ∈ interior (a :: (R₁ ++ [last])),
        ¬ G.Adj u v := by
      intro u hu v hv
      rw [hL₂int] at hv
      exact hQlast.2.2.2.2 u (hP'int u hu) v (rung_mem_strip hR₁ v hv)
    have hP'3 : 3 ≤ P'.length := by
      have : (Q.drop m).length = Q.length - m := hdroplen
      simp only [hP'def, List.length_cons]
      omega
    have hL₂3 : 3 ≤ (a :: (R₁ ++ [last])).length := by
      have := Workspace.ProofLemmas.PathBasics.path_length_pos hR₁.1.1
      simp only [List.length_cons, List.length_append]
      omega
    obtain ⟨hhole, hhlen⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
      hP' hL₂ hP'3 hL₂3 hIntDisj hIntAnti
    have hev := hG.1 _ hhole
    rw [hhlen] at hev
    have hR₁c : (a :: (R₁ ++ [last])).length = R₁.length + 2 := by simp
    have hR₁pos : 1 ≤ R₁.length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos hR₁.1.1
    have hL₂len : pathLength (a :: (R₁ ++ [last])) = pathLength R₁ + 2 := by
      unfold pathLength
      rw [hR₁c]
      omega
    obtain ⟨ke, hke⟩ := hev
    obtain ⟨kp, hkp⟩ := hP'even
    obtain ⟨kr, hkr⟩ := hR₁odd
    rw [hL₂len, hkp, hkr] at hke
    omega
  obtain ⟨z0, hz0Q, hz0adj⟩ := hnbex
  have har : G.Adj a r := (haonly z0 hz0Q hz0adj) ▸ hz0adj
  have hlastNotP : last ∉ P := fun h => hdisj last h hlastQ

  -- PAPER: *"Since `a-r'-R'-w₁-b₁-b-R-a` is not an odd hole, it follows from
  -- (3) that `w₁` has a neighbour in `R`."*
  have hL₁ : IsPathFrom G (a :: Q) a last :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_cons hQlast.1 har haNotQ
      (fun z hz hzr hadj => hzr (haonly z hz hadj))
  have hL₁int : SPGT.interior (a :: Q) = Q.dropLast := by
    simp [SPGT.interior]
  have hL₁len : pathLength (a :: Q) = pathLength Q + 1 := by
    have hQc : (a :: Q).length = Q.length + 1 := by simp
    unfold pathLength
    rw [hQc]
    omega
  have hL₁3 : 3 ≤ (a :: Q).length := by simp only [List.length_cons]; omega
  -- PAPER: *"choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`"*
  obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have hbb₁ : G.Adj b b₁ := hb.2.1 b₁ hb₁B
  have hlastb₁ : G.Adj last b₁ := hlast.2.1 b₁ hb₁B
  have ha₁a : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
  have hR₁ : IsRungOfStrip G A C B a₁ R₁ b₁ := hstep.1
  have hR₁odd : Odd (pathLength R₁) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hS a₀ b₀ R₀
      hK.1.1.2.1).1 a₁ R₁ b₁ hR₁
  have hlastnotR₁ : last ∉ R₁ := fun hmem =>
    bComplete_not_mem_strip hS hlast.2.1 (rung_mem_strip hR₁ last hmem)
  have hlastotherR₁ : ∀ z' ∈ R₁, z' ≠ b₁ → ¬ G.Adj last z' := by
    intro z' hz' hz'b hadj
    have hz'strip := rung_mem_strip hR₁ z' hz'
    rcases hz'strip with (hz'A | hz'B) | hz'C
    · exact hlast.2.2 z' (Or.inl hz'A) hadj
    · exact hz'b (hR₁.2.2.2.2.1 z' hz' hz'B)
    · exact hlast.2.2 z' (Or.inr hz'C) hadj
  have hL₂' : IsPathFrom G (R₁ ++ [last]) a₁ last :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_concat hR₁.1 hlastb₁
      hlastnotR₁ hlastotherR₁
  have hanotR₁ : a ∉ R₁ ++ [last] := by
    intro hmem
    rcases List.mem_append.mp hmem with h | h
    · exact hopt.1.2.2.1.1 (rung_mem_strip hR₁ a h)
    · exact hac.ne (by simpa using h)
  have haotherR₁ : ∀ z' ∈ R₁ ++ [last], z' ≠ a₁ → ¬ G.Adj a z' := by
    intro z' hz' hz'a hadj
    rcases List.mem_append.mp hz' with h | h
    · have hz'strip := rung_mem_strip hR₁ z' h
      rcases hz'strip with (hz'A | hz'B) | hz'C
      · exact hz'a (hR₁.2.2.2.1 z' h hz'A)
      · exact hopt.1.2.2.1.2.2 z' (Or.inl hz'B) hadj
      · exact hopt.1.2.2.1.2.2 z' (Or.inr hz'C) hadj
    · exact hanlast ((by simpa using h : z' = last) ▸ hadj)
  have hL₂ : IsPathFrom G (a :: (R₁ ++ [last])) a last :=
    Workspace.ProofLemmas.PathAttach.isPathFrom_cons hL₂' ha₁a hanotR₁ haotherR₁
  have hL₂int : SPGT.interior (a :: (R₁ ++ [last])) = R₁ := by
    simp only [SPGT.interior, List.tail_cons]
    exact List.dropLast_concat
  have hL₂3 : 3 ≤ (a :: (R₁ ++ [last])).length := by
    have := Workspace.ProofLemmas.PathBasics.path_length_pos hR₁.1.1
    simp only [List.length_cons, List.length_append]
    omega
  have hR₁c : (a :: (R₁ ++ [last])).length = R₁.length + 2 := by simp
  have hR₁pos : 1 ≤ R₁.length :=
    Workspace.ProofLemmas.PathBasics.path_length_pos hR₁.1.1
  have hL₂len : pathLength (a :: (R₁ ++ [last])) = pathLength R₁ + 2 := by
    unfold pathLength
    rw [hR₁c]
    omega

  -- the trajectory is the single vertex `w₁ = last`
  have hweq : w = [last] := by
    obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hwone
    have hul : last = u := by
      rw [hu] at hlastw
      simpa using hlastw
    rw [hu, ← hul]
  have hWiff : ∀ z : V, VertexComplete G z {u : V | u ∈ w} ↔ G.Adj z last := by
    intro z
    constructor
    · intro hc
      exact hc last hlastw
    · intro hadj u hu
      rw [hweq] at hu
      simpa using (by simpa using hu : u = last) ▸ hadj
  have hoddOne : Odd w.length := by rw [hwone]; exact ⟨0, rfl⟩

  -- PAPER: *"If `b` is its unique neighbour in `R` then the theorem holds, so we
  -- assume not."*
  by_cases huniq : ∀ z ∈ P, (G.Adj last z ↔ z = b)
  · refine ⟨hoddOne, Or.inl ?_⟩
    intro r' hr'
    constructor
    · intro hc
      exact (huniq r' hr').1 ((hWiff r').1 hc).symm
    · rintro rfl
      exact (hWiff r').2 ((huniq r' hr').2 rfl).symm
  · exfalso
    push Not at huniq
    -- PAPER: *"it follows from (3) that `w₁` has a neighbour in `R`"*
    have hlastnb : ∃ z ∈ P, G.Adj last z := by
      by_contra hno
      push Not at hno
      have hb₁notP : b₁ ∉ P := fun h => hopt.1.2.1 b₁ h (Or.inl (Or.inr hb₁B))
      have hb₁other : ∀ z ∈ P, z ≠ b → ¬ G.Adj b₁ z := by
        intro z hz hzb hadj
        by_cases hza : z = a
        · exact hopt.1.2.2.1.2.2 b₁ (Or.inl hb₁B) (hza ▸ hadj).symm
        · exact hopt.1.2.2.2.2 z (hPinterior z hz hza hzb) b₁
            (Or.inl (Or.inr hb₁B)) hadj.symm
      have hM1 : IsPathFrom G (P ++ [b₁]) a b₁ :=
        Workspace.ProofLemmas.PathAttach.isPathFrom_concat hopt.1.1 hbb₁.symm
          hb₁notP hb₁other
      have hlastnotM : last ∉ P ++ [b₁] := by
        intro hm
        rcases List.mem_append.mp hm with h | h
        · exact hlastNotP h
        · exact hlastb₁.ne (by simpa using h)
      have hlastotherM : ∀ z ∈ P ++ [b₁], z ≠ b₁ → ¬ G.Adj last z := by
        intro z hz hzb₁ hadj
        rcases List.mem_append.mp hz with h | h
        · exact hno z h hadj
        · exact hzb₁ (by simpa using h)
      have hM : IsPathFrom G ((P ++ [b₁]) ++ [last]) a last :=
        Workspace.ProofLemmas.PathAttach.isPathFrom_concat hM1 hlastb₁
          hlastnotM hlastotherM
      have hMint : ∀ u ∈ SPGT.interior ((P ++ [b₁]) ++ [last]),
          u ∈ P.tail ∨ u = b₁ := by
        intro u hu
        have hd :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hM).1 hu
        rcases List.mem_append.mp hd.1 with h | h
        · rcases List.mem_append.mp h with h1 | h1
          · exact Or.inl (hPtail u h1 hd.2.1)
          · exact Or.inr (by simpa using h1)
        · exact absurd (by simpa using h) hd.2.2
      have hIntDisj : ∀ u ∈ SPGT.interior (a :: Q),
          u ∉ SPGT.interior ((P ++ [b₁]) ++ [last]) := by
        intro u hu hv
        rw [hL₁int] at hu
        rcases hMint u hv with h | h
        · exact hdisj u (List.mem_of_mem_tail h) ((hdropIff u).1 hu).1
        · exact hQlast.2.1 u ((hdropIff u).1 hu).1 (h ▸ Or.inl (Or.inr hb₁B))
      have hIntAnti : ∀ u ∈ SPGT.interior (a :: Q),
          ∀ v ∈ SPGT.interior ((P ++ [b₁]) ++ [last]), ¬ G.Adj u v := by
        intro u hu v hv hadj
        rw [hL₁int] at hu
        rcases hMint v hv with h | h
        · exact hsep v h u hu hadj.symm
        · exact hdropAntiB u hu b₁ hb₁B (h ▸ hadj)
      have hM3 : 3 ≤ ((P ++ [b₁]) ++ [last]).length := by
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨hhole, hhlen⟩ :=
        Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths hL₁ hM hL₁3 hM3
          hIntDisj hIntAnti
      have hev := hG.1 _ hhole
      rw [hhlen] at hev
      have hMc : ((P ++ [b₁]) ++ [last]).length = P.length + 2 := by simp
      have hMlen : pathLength ((P ++ [b₁]) ++ [last]) = pathLength P + 2 := by
        unfold pathLength
        rw [hMc]
        omega
      obtain ⟨ke, hke⟩ := hev
      obtain ⟨kq, hkq⟩ := hQodd
      obtain ⟨kp, hkp⟩ := hPodd
      rw [hL₁len, hMlen, hkq, hkp] at hke
      omega
    -- PAPER: *"Then there is a path `P` say from `w₁` to `a` with interior in
    -- `R \ b`."*
    obtain ⟨z, hzP, hzadj⟩ := hlastnb
    have hexne : ∃ z ∈ P, G.Adj last z ∧ z ≠ b := by
      obtain ⟨u, huP, hu⟩ := huniq
      rcases hu with ⟨hua, hub⟩ | ⟨hua, hub⟩
      · exact ⟨u, huP, hua, hub⟩
      · exact ⟨z, hzP, hzadj, fun he => hua (by rw [hub, ← he]; exact hzadj)⟩
    obtain ⟨z', hz'P, hz'adj, hz'b⟩ := hexne
    have hex2 : ∃ k : ℕ, ∃ hk : k < P.length, G.Adj last (P[k]'hk) := by
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz'P
      exact ⟨k, hk, by rw [hkz]; exact hz'adj⟩
    obtain ⟨hmP, hmadj⟩ := Nat.find_spec hex2
    set m : ℕ := Nat.find hex2 with hmdef
    have hmmin : ∀ (k : ℕ) (hk : k < P.length), k < m → ¬ G.Adj last (P[k]'hk) := by
      intro k hk hlt hadj
      exact Nat.find_min hex2 hlt ⟨hk, hadj⟩
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h1
      · exfalso
        apply hanlast
        have : P[m]'hmP = a := by
          rw [(getElem_congr rfl h0 hmP : P[m]'hmP = P[0]'hPpos)]
          exact hP0
        exact (this ▸ hmadj).symm
      · exact h1
    have hmlt : m < P.length - 1 := by
      obtain ⟨kz, hkz, hkzeq⟩ := List.mem_iff_getElem.mp hz'P
      have hkzne : kz ≠ P.length - 1 := by
        intro he
        apply hz'b
        rw [← hkzeq]
        exact (getElem_congr rfl he hkz :
          P[kz]'hkz = P[P.length - 1]'(by omega)).trans hPlastElem
      have hmle : m ≤ kz := Nat.find_le ⟨hkz, by rw [hkzeq]; exact hz'adj⟩
      omega
    have htakelen : (P.take (m + 1)).length = m + 1 := by
      simp only [List.length_take]
      omega
    have htakeget : ∀ (k : ℕ) (hk : k < (P.take (m + 1)).length),
        (P.take (m + 1))[k]'hk = P[k]'(by rw [htakelen] at hk; omega) := by
      intro k hk
      simp
    have htakeFrom : IsPathFrom G (P.take (m + 1)) a (P[m]'hmP) := by
      refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hopt.1.1.1 (by omega),
        ?_, ?_⟩
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        rw [htakeget 0 (by omega)]
        rw [hP0]
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        rw [htakeget ((P.take (m + 1)).length - 1) (by omega)]
        exact congrArg some (getElem_congr rfl (by omega) (by omega))
    have hlastnottake : last ∉ P.take (m + 1) := fun h =>
      hlastNotP (List.mem_of_mem_take h)
    have hlastotherT : ∀ z ∈ P.take (m + 1), z ≠ P[m]'hmP → ¬ G.Adj last z := by
      intro z hz hzne hadj
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
      rw [htakeget k hk] at hkz
      have hkP : k < P.length := by rw [htakelen] at hk; omega
      have hkm : k < m := by
        rcases lt_or_ge k m with h | h
        · exact h
        · exfalso
          apply hzne
          rw [← hkz]
          have hkm2 : k = m := by rw [htakelen] at hk; omega
          exact getElem_congr rfl hkm2 hkP
      exact hmmin k hkP hkm (by rw [hkz]; exact hadj)
    have hT : IsPathFrom G (P.take (m + 1) ++ [last]) a last :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_concat htakeFrom hmadj
        hlastnottake hlastotherT
    have hTint : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]),
        u ∈ interior P := by
      intro u hu
      have hd :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hT).1 hu
      have hutake : u ∈ P.take (m + 1) := by
        rcases List.mem_append.mp hd.1 with h | h
        · exact h
        · exact absurd (by simpa using h) hd.2.2
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hutake
      rw [htakeget k hk] at hkz
      have hkP : k < P.length := by rw [htakelen] at hk; omega
      have hub : u ≠ b := by
        intro he
        have heq : P[k]'hkP = P[P.length - 1]'(by omega) := by
          rw [hkz, he, hPlastElem]
        have := (List.Nodup.getElem_inj_iff
          (Workspace.ProofLemmas.PathBasics.path_nodup hopt.1.1.1)).mp heq
        rw [htakelen] at hk
        omega
      exact hPinterior u (List.mem_of_mem_take hutake) hd.2.1 hub
    have hTtail : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]), u ∈ P.tail := by
      intro u hu
      have hd :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hT).1 hu
      exact hPtail u
        (Workspace.ProofLemmas.PathBasics.interior_subset (hTint u hu)) hd.2.1
    have hT3 : 3 ≤ (P.take (m + 1) ++ [last]).length := by
      simp only [List.length_append, List.length_singleton, htakelen]
      omega
    have hTlen : pathLength (P.take (m + 1) ++ [last]) = m + 1 := by
      have hTc : (P.take (m + 1) ++ [last]).length = m + 2 := by
        simp only [List.length_append, List.length_singleton, htakelen]
      unfold pathLength
      rw [hTc]
      omega
    -- PAPER: *"Since `w₁-P-a-r'-R'-w₁` is a hole it follows that `P` is even"*
    have hmodd : Odd m := by
      have hIntDisj : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]),
          u ∉ SPGT.interior (a :: Q) := by
        intro u hu hv
        rw [hL₁int] at hv
        exact hdisj u
          (Workspace.ProofLemmas.PathBasics.interior_subset (hTint u hu))
          ((hdropIff u).1 hv).1
      have hIntAnti : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]),
          ∀ v ∈ SPGT.interior (a :: Q), ¬ G.Adj u v := by
        intro u hu v hv
        rw [hL₁int] at hv
        exact hsep u (hTtail u hu) v hv
      obtain ⟨hhole, hhlen⟩ :=
        Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths hT hL₁ hT3 hL₁3
          hIntDisj hIntAnti
      have hev := hG.1 _ hhole
      rw [hhlen] at hev
      obtain ⟨ke, hke⟩ := hev
      obtain ⟨kq, hkq⟩ := hQodd
      rw [hTlen, hL₁len, hkq] at hke
      exact ⟨(m - 1) / 2, by omega⟩
    -- PAPER: *"but `P` can be completed via `a-a₁-R₁-b₁-w₁`, a contradiction"*
    have hIntDisj2 : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]),
        u ∉ SPGT.interior (a :: (R₁ ++ [last])) := by
      intro u hu hv
      rw [hL₂int] at hv
      exact hopt.1.2.1 u
        (Workspace.ProofLemmas.PathBasics.interior_subset (hTint u hu))
        (rung_mem_strip hR₁ u hv)
    have hIntAnti2 : ∀ u ∈ SPGT.interior (P.take (m + 1) ++ [last]),
        ∀ v ∈ SPGT.interior (a :: (R₁ ++ [last])), ¬ G.Adj u v := by
      intro u hu v hv
      rw [hL₂int] at hv
      exact hopt.1.2.2.2.2 u (hTint u hu) v (rung_mem_strip hR₁ v hv)
    obtain ⟨hhole, hhlen⟩ :=
      Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths hT hL₂ hT3 hL₂3
        hIntDisj2 hIntAnti2
    have hev := hG.1 _ hhole
    rw [hhlen] at hev
    obtain ⟨ke, hke⟩ := hev
    obtain ⟨kr, hkr⟩ := hR₁odd
    obtain ⟨km, hkm⟩ := hmodd
    rw [hTlen, hL₂len, hkr] at hke
    omega

end Workspace.ProofLemmas.Thm131Claim4
