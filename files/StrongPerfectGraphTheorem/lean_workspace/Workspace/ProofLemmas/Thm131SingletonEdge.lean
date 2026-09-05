import Workspace.ProofLemmas.Thm131LastMiss

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The singleton edge case in 13.1

The general singleton argument in the paper simplifies sharply after the
inductive optimal-length lemma: both relevant optimal banisters are edges.
The two Roussel--Rubio parity comparisons then reduce to paths on three and
four vertices.
-/

namespace Workspace.ProofLemmas.Thm131SingletonEdge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm131OptimalLength
open Workspace.ProofLemmas.Thm131EdgeCases
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A terminal miss is impossible when the trajectory has only one tail
vertex and the current optimal banister is an edge. -/
theorem singleton_edge_terminal_miss_absurd
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
    (hPone : pathLength P = 1)
    (hanti : IsAntipathFrom G (a :: w) a last)
    (hwone : w.length = 1)
    (hbnotw : b ∉ w) (hbmiss : ¬ G.Adj b last) : False := by
  classical
  have hS : StepConnected G A C B := hK.1.1.1
  have hPeq : P = [a, b] := path_eq_pair_of_length_one hopt.1.1 hPone
  have hab : G.Adj a b :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hopt.1.1 hPone
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
  have hQone : pathLength Q = 1 :=
    optimal_banister_length_one hG hK4 heven h1br h2br hK hyseq hIH_y hoptQ
  have hQeq₀ : Q = [r, x[i]] := path_eq_pair_of_length_one hoptQ.1.1 hQone
  have hQeq : Q = [r, last] := by simpa [hxilast] using hQeq₀
  have hQlast : IsBanister G A C B r Q last := by simpa [hxilast] using hoptQ.1
  have hrlast : G.Adj r last :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hQlast.1 hQone

  -- Transfer the earlier birth into the full sequence, to obtain separation
  -- of the two edge-banisters.
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
  have hbr : ¬ G.Adj b r :=
    hsep b (by rw [hPeq]; simp) r (by rw [hQeq]; simp)

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
  have haNotQ : a ∉ Q := hdisj a (by rw [hPeq]; simp)
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
    have hqint : q ∈ interior Q :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQlast.1).2
        ⟨hqQ, hqr, hqlast⟩
    obtain ⟨b', hb'B⟩ := hS.2.1.2
    exact hQlast.2.2.2.2 q hqint b' (Or.inl (Or.inr hb'B))
      (htB q hqt b' hb'B)

  -- First, the two left-star ends must be adjacent.
  have har : G.Adj a r := by
    by_contra harn
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
        · rcases (by rw [hQeq] at hqQ; simpa using hqQ) with hqr | hql
          · exact harn (hqr ▸ hadj)
          · exact hanlast (hql ▸ hadj)
      let L : List V := a :: a₁ :: Q
      have hL : IsPathFrom G L a last := by
        simpa [L] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons
          ha₁Q haa₁ haNotA₁Q haOther
      have hLodd : Odd (pathLength L) := by
        refine ⟨1, ?_⟩
        simp [L, hQeq, pathLength]
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
        exact (hunique last (by rw [hQeq]; simp)).2 rfl q hq
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
      have hb₂T : VertexComplete G b₂ {q : V | q ∈ t} := by
        intro q hq
        exact (htB q hq b₂ hstep.2.1.2.2.1).symm
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
      · rw [hQeq] at huQ
        simp at huQ
        rcases huQ with hur | hul
        · subst u
          exact hQlast.2.2.1.2.2 b₂ (Or.inl hstep.2.1.2.2.1) hb₂u.symm
        · exact huL.2.2 hul
    · obtain ⟨-, m, hmEven, hm1, hmt, hmanti⟩ := halt
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
      have harne : a ≠ r := fun heq => haNotQ
        (heq ▸ (by rw [hQeq]; simp))
      have halastne : a ≠ last := hac.ne
      have hUeven := Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
        hG hrlast haT harn hanlast harne halastne hU haUint
      have hmle : m ≤ t.length := by omega
      have hUlen : pathLength U = m + 1 := by
        simp [U, pathLength, List.length_take, Nat.min_eq_left hmle]
      obtain ⟨ke, hke⟩ := hUeven
      obtain ⟨km, hkm⟩ := hmEven
      rw [hUlen] at hke
      omega

  -- With both banisters edges, absence of the final edge closes a five-hole.
  obtain ⟨a₁, ha₁A⟩ := hS.2.1.1
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ := exists_step_with_left_end hS ha₁A
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have hL₁ : IsPathFrom G [a, r, last] a last := by
    have harne : a ≠ r := har.ne
    have hrlne : r ≠ last := hrlast.ne
    have halne : a ≠ last := hac.ne
    have hlasta : ¬ G.Adj last a := fun h => hanlast h.symm
    refine ⟨⟨by simp, by simp [harne, hrlne, halne], ?_⟩, rfl, by simp⟩
    intro p q hp hq
    simp only [List.length_cons, List.length_nil] at hp hq
    interval_cases p <;> interval_cases q <;>
      simp [har, har.symm, hrlast, hrlast.symm, hanlast, hlasta]
  have hdb₁ : G.Adj b b₁ := hb.2.1 b₁ hb₁B
  have hlb₁ : G.Adj last b₁ := hlast.2.1 b₁ hb₁B
  have hab₁ : ¬ G.Adj a b₁ := hopt.1.2.2.1.2.2 b₁ (Or.inl hb₁B)
  have hL₂ : IsPathFrom G [a, b, b₁, last] a last := by
    have habne := hab.ne
    have hbb₁ne := hdb₁.ne
    have hb₁lastne := hlb₁.ne'
    have halne := hac.ne
    have hb₁a : ¬ G.Adj b₁ a := fun h => hab₁ h.symm
    have hlasta : ¬ G.Adj last a := fun h => hanlast h.symm
    have hlastb : ¬ G.Adj last b := fun h => hbmiss h.symm
    have hab₁ne : a ≠ b₁ := by
      intro heq
      exact hopt.1.2.2.1.1 (heq ▸ Or.inl (Or.inr hb₁B))
    have hblastne : b ≠ last := by
      intro heq
      exact hbnotw (heq ▸ hlastw)
    refine ⟨⟨by simp, by simp [habne, hbb₁ne, hb₁lastne, halne, hab₁ne,
      hblastne], ?_⟩,
      rfl, by simp⟩
    intro p q hp hq
    simp only [List.length_cons, List.length_nil] at hp hq
    interval_cases p <;> interval_cases q <;>
      simp [hab, hab.symm, hdb₁, hdb₁.symm, hlb₁, hlb₁.symm,
        hab₁, hbmiss, hanlast, hb₁a, hlastb, hlasta]
  have hrbne : r ≠ b := by
    intro heq
    exact hb.2.2 a₁ (Or.inl ha₁A) (heq ▸ hQlast.2.2.1.2.1 a₁ ha₁A)
  have hIntDisj : ∀ u ∈ interior [a, r, last], u ∉ interior [a, b, b₁, last] := by
    intro u hu hv
    simp [Workspace.Types.Core.SPGT.interior] at hu hv
    subst u
    rcases hv with hrbEq | hrb₁Eq
    · exact hrbne hrbEq
    · exact hQlast.2.2.1.1 (hrb₁Eq ▸ Or.inl (Or.inr hb₁B))
  have hIntAnti : ∀ u ∈ interior [a, r, last], ∀ v ∈ interior [a, b, b₁, last],
      ¬ G.Adj u v := by
    intro u hu v hv
    simp [Workspace.Types.Core.SPGT.interior] at hu hv
    subst u
    rcases hv with hvb | hvb₁
    · subst v; exact fun hadj => hbr hadj.symm
    · subst v; exact hQlast.2.2.1.2.2 b₁ (Or.inl hb₁B)
  obtain ⟨hhole, hhlen⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
    hL₁ hL₂ (by simp) (by simp) hIntDisj hIntAnti
  have hev := hG.1 _ hhole
  rw [hhlen] at hev
  have hL₁len : pathLength [a, r, last] = 2 := by simp [pathLength]
  have hL₂len : pathLength [a, b, b₁, last] = 3 := by simp [pathLength]
  rw [hL₁len, hL₂len] at hev
  obtain ⟨ke, hke⟩ := hev
  omega

end Workspace.ProofLemmas.Thm131SingletonEdge
