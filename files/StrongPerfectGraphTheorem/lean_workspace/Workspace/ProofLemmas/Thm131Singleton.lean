import Workspace.ProofLemmas.Thm131Trajectory
import Workspace.ProofLemmas.Thm132Optimal
import Workspace.ProofLemmas.Thm132BanisterSeparation
import Workspace.ProofLemmas.Thm132BanisterAttachment
import Workspace.ProofLemmas.Thm132AdjoinBanister
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathAttach
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The singleton-trajectory induction step in 13.1

This is claim (4) of the printed proof, specialized to the only form needed by
the finite descent: the current optimal banister is the long banister of a
strongly maximal staircase.  The induction hypothesis is used on the earlier
optimal banister supplied by right-sequence axiom 3.
-/

namespace Workspace.ProofLemmas.Thm131Singleton

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm131Trajectory
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Optimal
open Workspace.ProofLemmas.Thm132BanisterSeparation
open Workspace.ProofLemmas.Thm132BanisterAttachment
open Workspace.ProofLemmas.Thm132AdjoinBanister

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The singleton trajectory cannot occur when the same optimal banister is
the long banister of a strongly maximal staircase. -/
theorem singleton_long_optimal_absurd
    {G : SimpleGraph V} (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (heven : ¬ ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsEvenPrism G s t R₁ R₂ R₃)
    (h1br : ¬ ∃ A' C' B' F Q : Set V, IsOneBreaker G A' C' B' F Q)
    (h2br : ¬ ∃ (A' C' B' : Set V) (a' : V) (R' : List V) (b' : V) (Q : Set V),
      IsTwoBreaker G A' C' B' a' R' b' Q)
    {A C B : Set V} {a b : V} {P x : List V}
    (hK : StronglyMaximalStaircase G A C B a P b)
    (hx : IsRightSequence G A C B x)
    (hopt : BOptimalBanister G A C B x a P b)
    (i : ℕ) (hi : i < x.length)
    (hbefore : ∀ (k : ℕ) (hk : k < i), G.Adj a x[k])
    (hnon : ¬ G.Adj a x[i])
    (hv : IsRightStar G A C B x[i])
    (hIH : ∀ (y : List V), y.length < x.length →
      IsRightSequence G A C B y →
      ∀ (d : V), IsRightStar G A C B d →
      ∀ (c : V) (Q : List V), BOptimalBanister G A C B y c Q d →
      ∀ (z : List V), trajectoryOfVertex G A y c (c :: z) →
        TrajectoryConclusion G c Q d z) : False := by
  classical
  let v : V := x[i]
  let y : List V := x.take i
  have hylen : y.length = i := by simp [y, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hyshort : y.length < x.length := by omega
  have hyseq : IsRightSequence G A C B y := by
    simpa [y] using rightSequence_take hx i
  have hv' : IsRightStar G A C B v := by simpa [v] using hv
  have hvanti : VertexAnticomplete G v A := by
    intro z hz
    exact hv'.2.2 z (Or.inl hz)
  obtain ⟨r₀, Q₀, hQ₀, q, hqy, hrq⟩ := hx.2.2 i hi (by simpa [v] using hvanti)
  have hr₀nc : ¬ VertexComplete G r₀ {z : V | z ∈ y} := by
    intro hc
    exact hrq (hc q (by simpa [y] using hqy))
  obtain ⟨r, Q, j, hj, hoptQ, hbirthQ, -⟩ :=
    exists_optimalBanister hyseq ⟨r₀, Q₀, hQ₀, hr₀nc⟩
  obtain ⟨z, birthIndex, hbirthIndex, lastIndex, hlastIndex,
      htraj, hbirthAgain, hanti, hzidx⟩ :=
    exists_trajectoryOfVertex_of_leftStar hK.1.1.1 hyseq
      hoptQ.1.2.2.1 hoptQ.2.1
  have hrec := hIH y hyshort hyseq v hv' r Q hoptQ z htraj
  have hzodd : Odd z.length := hrec.1
  let last : V := y[lastIndex]
  have hanti' : IsAntipathFrom G (r :: z) r last := by simpa [last] using hanti
  have hzB : ∀ u ∈ z, VertexComplete G u B := by
    intro u hu
    obtain ⟨k, hk, -, hku⟩ := hzidx u hu
    simpa [hku] using hyseq.1.2 y[k] (List.getElem_mem hk)
  have haZ : VertexComplete G a {u : V | u ∈ z} := by
    intro u hu
    obtain ⟨k, hk, -, hku⟩ := hzidx u hu
    have hki : k < i := by simpa [hylen] using hk
    have htake : y[k]'hk = x[k]'(by omega) := by simp [y]
    have hadj := hbefore k hki
    rw [← htake, hku] at hadj
    exact hadj

  -- Transfer the earlier birth from the initial segment to the full sequence.
  have hjx : j < x.length := by rw [hylen] at hj; omega
  have hyjx : y[j]'hj = x[j]'hjx := by simp [y]
  have hbirthQfull : birth G A C B x r x[j] := by
    obtain ⟨hrleft, -, j', hj', hj'eq, hj'non, hj'before⟩ := hbirthQ
    have hj'i : j' < i := by simpa [hylen] using hj'
    have hj'x : j' < x.length := by omega
    have htj' : y[j']'hj' = x[j']'hj'x := by simp [y]
    have hj'j : j' = j := by
      apply (List.Nodup.getElem_inj_iff hx.1.1).mp
      calc
        x[j'] = y[j'] := htj'.symm
        _ = y[j] := hj'eq
        _ = x[j] := hyjx
    subst j'
    have hrncx : ¬ VertexComplete G r {u : V | u ∈ x} := by
      intro hc
      exact hj'non (by rw [htj']; exact hc x[j] (List.getElem_mem hjx))
    refine ⟨hrleft, hrncx, j, hjx, rfl, ?_, ?_⟩
    · simpa [htj'] using hj'non
    · intro k hk
      have hky : k < y.length := by rw [hylen]; omega
      have htk : y[k]'hky = x[k]'(by omega) := by simp [y]
      simpa [htk] using hj'before k hk
  have habirth : birth G A C B x a v := by
    refine ⟨hopt.1.2.2.1, hopt.2.1, i, hi, by simp [v], hnon, ?_⟩
    intro k hk
    exact hbefore k hk
  have hearlier : Earlier x x[j] v := by
    refine ⟨j, i, hjx, hi, rfl, by simp [v], ?_⟩
    rw [hylen] at hj
    exact hj
  have hnolink := optimal_halves_not_linked hK.1.1.1.2.1.1 hopt hoptQ.1
    hbirthQfull habirth hearlier
  have hdisj := banisters_disjoint_of_halves_not_linked hK.1.1.1.2.1.1
    hopt.1 hoptQ.1 hnolink
  have hsep := halves_anticomplete_of_not_linked hnolink

  -- The last term of the earlier trajectory chooses the step used in both
  -- Roussel--Rubio parity arguments.
  obtain ⟨a₁, ha₁A, hlasta₁⟩ := trajectory_last_misses_left htraj hanti'
  obtain ⟨R₁, b₁, a₂, R₂, b₂, hstep⟩ :=
    exists_step_with_left_end hK.1.1.1 ha₁A

  have hzpos : 0 < z.length := by
    have := htraj
    rcases this with ⟨happ, ti, hti, z', hfirst, hztraj, hshape⟩
    have hzz : z' = z := (List.cons.inj hshape).2.symm
    have := hztraj.1.1
    simpa [hzz] using this
  have hzanti : AnticonnectedSet G {u : V | u ∈ z} := by
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (HyperprismRungStructure.isPathList_tail hanti'.1 (by simp; omega))
  have hlastz : last ∈ z := by
    have hzlast : z.getLast? = some last := by
      simpa [List.getLast?_cons_of_ne_nil (List.ne_nil_of_length_pos hzpos)] using hanti'.2.2
    exact Workspace.ProofLemmas.PathBasics.getLast_mem hzlast
  have ha_not_Q : a ∉ Q := hdisj a
    (Workspace.ProofLemmas.PathBasics.head_mem hopt.1.1.2.1)
  have hv_not_y : v ∉ y := by
    intro hvy
    obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hvy
    have hklt : k < i := by simpa [hylen] using hk
    have hykx : y[k]'hk = x[k]'(by omega) := by simp [y]
    have heq : x[k] = x[i] := by simpa [v, hykx] using hkv
    have := (List.Nodup.getElem_inj_iff hx.1.1).mp heq
    omega
  have hQZdisj : ∀ q ∈ Q, q ∉ z := by
    intro q hqQ hqz
    obtain ⟨k, hk, -, hkq⟩ := hzidx q hqz
    have hqy : q ∈ y := by rw [← hkq]; exact List.getElem_mem hk
    by_cases hqr : q = r
    · exact htraj.1.2.1 (hqr ▸ hqy)
    by_cases hqv : q = v
    · exact hv_not_y (hqv ▸ hqy)
    have hqint : q ∈ interior Q :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
        ⟨hqQ, hqr, hqv⟩
    obtain ⟨b₃, hb₃B⟩ := hK.1.1.1.2.1.2
    exact hoptQ.1.2.2.2.2 q hqint b₃ (Or.inl (Or.inr hb₃B))
      (hzB q hqz b₃ hb₃B)

  have haSome : ∃ q ∈ Q, G.Adj a q := by
    by_contra hnone
    push Not at hnone
    rcases hrec.2 with hunique | halt
    · -- `a-a₁-r-Q-v` is the odd path used with 2.2.
      have ha₁r : G.Adj a₁ r := (hoptQ.1.2.2.1.2.1 a₁ ha₁A).symm
      have ha₁_not_Q : a₁ ∉ Q := by
        intro hm
        exact hoptQ.1.2.1 a₁ hm (Or.inl (Or.inl ha₁A))
      have ha₁other : ∀ q ∈ Q, q ≠ r → ¬ G.Adj a₁ q := by
        intro q hq hqr hadj
        by_cases hqv : q = v
        · exact hv'.2.2 a₁ (Or.inl ha₁A) (hqv ▸ hadj.symm)
        · exact hoptQ.1.2.2.2.2 q
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
              ⟨hq, hqr, hqv⟩) a₁ (Or.inl (Or.inl ha₁A)) hadj.symm
      have ha₁Q : IsPathFrom G (a₁ :: Q) a₁ v :=
        Workspace.ProofLemmas.PathAttach.isPathFrom_cons hoptQ.1.1 ha₁r ha₁_not_Q
          ha₁other
      have haa₁ : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
      have ha_not_a₁Q : a ∉ a₁ :: Q := by
        intro hm
        rcases List.mem_cons.mp hm with heq | hmQ
        · exact hopt.1.2.2.1.1 (heq ▸ Or.inl (Or.inl ha₁A))
        · exact ha_not_Q hmQ
      have haother : ∀ q ∈ a₁ :: Q, q ≠ a₁ → ¬ G.Adj a q := by
        intro q hq hne
        rcases List.mem_cons.mp hq with heq | hqQ
        · exact absurd heq hne
        · exact hnone q hqQ
      let L : List V := a :: a₁ :: Q
      have hL : IsPathFrom G L a v := by
        simpa [L] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons
          ha₁Q haa₁ ha_not_a₁Q haother
      have hQodd : Odd (pathLength Q) :=
        (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
          r v Q hoptQ.1).2
      have hLodd : Odd (pathLength L) := by
        obtain ⟨k, hk⟩ := hQodd
        refine ⟨k + 1, ?_⟩
        simp only [L, pathLength, List.length_cons] at hk ⊢
        omega
      have hLout : ∀ u ∈ L, u ∉ {q : V | q ∈ z} := by
        intro u hu huz
        change u ∈ z at huz
        simp only [L, List.mem_cons] at hu
        rcases hu with hua | hua₁ | huQ
        · have hadj := haZ u huz
          rw [hua] at hadj
          exact G.irrefl hadj
        · exact bComplete_not_mem_strip hK.1.1.1 (hzB u huz)
            (hua₁ ▸ Or.inl (Or.inl ha₁A))
        · exact hQZdisj u huQ huz
      have hvZ : VertexComplete G v {q : V | q ∈ z} := by
        intro q hq
        exact (hunique v
          (Workspace.ProofLemmas.PathBasics.getLast_mem hoptQ.1.1.2.2)).2 rfl q hq
      have ha₁_not_complete : ¬ VertexComplete G a₁ {q : V | q ∈ z} := by
        intro hc
        exact hlasta₁ (hc last hlastz).symm
      have hcomplete : ∀ u ∈ L,
          VertexComplete G u {q : V | q ∈ z} → u = a ∨ u = v := by
        intro u hu hc
        simp only [L, List.mem_cons] at hu
        rcases hu with h | h | huQ
        · exact Or.inl h
        · exact absurd (h ▸ hc) ha₁_not_complete
        · exact Or.inr ((hunique u huQ).1 hc)
      have hnoedge : ¬ ∃ u ∈ L, ∃ q ∈ L,
          EdgeComplete G {s : V | s ∈ z} u q := by
        rintro ⟨u, hu, q, hq, huq, huZ, hqZ⟩
        rcases hcomplete u hu huZ with rfl | rfl <;>
          rcases hcomplete q hq hqZ with rfl | rfl
        · exact G.irrefl huq
        · exact hnon (by simpa [v] using huq)
        · exact hnon (by simpa [v] using huq.symm)
        · exact G.irrefl huq
      have hb₂Z : VertexComplete G b₂ {q : V | q ∈ z} := by
        intro q hq
        exact (hzB q hq b₂ hstep.2.1.2.2.1).symm
      obtain ⟨u, huInt, hb₂u⟩ := Workspace.Statements.S02.SPGT.thm_2_2
        G hG {q : V | q ∈ z} hzanti L a v hL hLout hLodd haZ hvZ hnoedge b₂ hb₂Z
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
            ⟨-, habad⟩ | ⟨habad, -⟩
          · exact Set.disjoint_left.mp hK.1.1.1.1.1 hstep.2.1.2.1
              (habad ▸ hstep.2.1.2.2.1)
          · exact Set.disjoint_left.mp hK.1.1.1.1.1 ha₁A
              (habad ▸ hstep.1.2.2.1)
        exact ha₁b₂ hb₂u.symm
      · by_cases hur : u = r
        · exact hoptQ.1.2.2.1.2.2 b₂ (Or.inl hstep.2.1.2.2.1)
            (hur ▸ hb₂u.symm)
        · have huv : u ≠ v := huL.2.2
          exact hoptQ.1.2.2.2.2 u
            ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
              ⟨huQ, hur, huv⟩) b₂ (Or.inl (Or.inr hstep.2.1.2.2.1)) hb₂u.symm
    · obtain ⟨hQone, m, hmEven, hm1, hmz, hmanti⟩ := halt
      let U : List V := r :: (z.take m ++ [v])
      have hU : IsAntipathFrom G U r v := by
        exact ⟨by simpa [U] using hmanti, by simp [U],
          by simp [U, List.getLast?_cons_of_ne_nil]⟩
      have hrv : G.Adj r v :=
        Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hoptQ.1.1 hQone
      have haUinterior : ∀ u ∈ interior U, u ∈ {q : V | q ∈ z} := by
        intro u hu
        have hud := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hU).1 hu
        have humem := hud.1
        change u ∈ r :: (z.take m ++ [v]) at humem
        simp at humem
        rcases humem with hur | huz | huv
        · exact absurd hur hud.2.1
        · exact List.mem_of_mem_take huz
        · exact absurd huv hud.2.2
      have har : ¬ G.Adj a r := hnone r
        (Workspace.ProofLemmas.PathBasics.head_mem hoptQ.1.1.2.1)
      have hav : ¬ G.Adj a v := by simpa [v] using hnon
      have hane_r : a ≠ r := fun heq => ha_not_Q
        (heq ▸ Workspace.ProofLemmas.PathBasics.head_mem hoptQ.1.1.2.1)
      have hane_v : a ≠ v := fun heq => har (heq ▸ hrv.symm)
      have hUeven := Workspace.ProofLemmas.AntiholeCompletion.even_pathLength_of_witness
        hG hrv haZ har hav hane_r hane_v hU haUinterior
      have hmle : m ≤ z.length := by omega
      have hUlen : pathLength U = m + 1 := by
        have hlen : U.length = m + 2 := by
          simp [U, List.length_take, Nat.min_eq_left hmle]
        rw [pathLength, hlen]
        omega
      obtain ⟨ke, hke⟩ := hUeven
      obtain ⟨km, hkm⟩ := hmEven
      rw [hUlen] at hke
      omega

  have haonly : ∀ q ∈ Q, (G.Adj a q ↔ q = r) := by
    have hav : ¬ G.Adj a v := by simpa [v] using hnon
    have honly : ∀ q ∈ Q, G.Adj a q → q = r := by
      intro q hqQ haq
      by_contra hqr
      have hqv : q ≠ v := fun h => hav (h ▸ haq)
      have hqint : q ∈ interior Q :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
          ⟨hqQ, hqr, hqv⟩
      have hQnotOne : pathLength Q ≠ 1 := by
        intro hone
        have hadj := Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one
          hoptQ.1.1 hone
        have hlen : Q.length = 2 := by
          have hqpos := Workspace.ProofLemmas.PathBasics.path_length_pos hoptQ.1.1.1
          rw [pathLength] at hone
          omega
        have hintlen : (interior Q).length = 0 := by
          rw [Workspace.ProofLemmas.PathBasics.interior_length]
          omega
        have hintnil : interior Q = [] := List.eq_nil_of_length_eq_zero hintlen
        rw [hintnil] at hqint
        exact List.not_mem_nil hqint
      have hunique : ∀ u ∈ Q,
          (VertexComplete G u {s : V | s ∈ z} ↔ u = v) := by
        rcases hrec.2 with hu | hu
        · exact hu
        · exact absurd hu.1 hQnotOne

      have hQlen : 2 ≤ Q.length := by
        have := hoptQ.1.1.1.1
        have hrnev : r ≠ v := by
          obtain ⟨a₃, ha₃A⟩ := hK.1.1.1.2.1.1
          intro heq
          have hra₃ := hoptQ.1.2.2.1.2.1 a₃ ha₃A
          rw [heq] at hra₃
          exact hv'.2.2 a₃ (Or.inl ha₃A) hra₃
        by_contra hlt
        have hqpos := Workspace.ProofLemmas.PathBasics.path_length_pos hoptQ.1.1.1
        have hlen : Q.length = 1 := by omega
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hlen
        have hur : u = r := by simpa using hoptQ.1.1.2.1
        have huv : u = v := by simpa using hoptQ.1.1.2.2
        exact hrnev (hur.symm.trans huv)
      have htailconn : ConnectedSet G {u : V | u ∈ Q.tail} :=
        Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
          (HyperprismRungStructure.isPathList_tail hoptQ.1.1.1 hQlen)
      have hqtail : q ∈ Q.tail :=
        (HyperprismRungStructure.mem_tail_iff_of_pathFrom hoptQ.1.1).2 ⟨hqQ, hqr⟩
      have hconn : ConnectedSet G ({u : V | u ∈ Q.tail} ∪ {a}) :=
        Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
          htailconn ⟨q, hqtail, haq⟩
      have hvQ : v ∈ Q := Workspace.ProofLemmas.PathBasics.getLast_mem hoptQ.1.1.2.2
      have hrnev : r ≠ v := by
        obtain ⟨a₃, ha₃A⟩ := hK.1.1.1.2.1.1
        intro heq
        have hra₃ := hoptQ.1.2.2.1.2.1 a₃ ha₃A
        rw [heq] at hra₃
        exact hv'.2.2 a₃ (Or.inl ha₃A) hra₃
      have hvTail : v ∈ Q.tail :=
        (HyperprismRungStructure.mem_tail_iff_of_pathFrom hoptQ.1.1).2 ⟨hvQ, hrnev.symm⟩
      obtain ⟨L, hL, hLmem⟩ :=
        Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected hconn
          (Or.inr rfl) (Or.inl hvTail)
      have hLintQ : ∀ u ∈ interior L, u ∈ Q ∧ u ≠ r ∧ u ≠ v := by
        intro u hu
        have hud := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1 hu
        rcases hLmem u hud.1 with huTail | hua
        · have hd := (HyperprismRungStructure.mem_tail_iff_of_pathFrom hoptQ.1.1).1 huTail
          exact ⟨hd.1, hd.2, hud.2.2⟩
        · exact absurd (Set.mem_singleton_iff.mp hua) hud.2.1
      have hL3 : 3 ≤ L.length := by
        have hac : Gᶜ.Adj a v := (G.compl_adj a v).mpr
          ⟨fun heq => ha_not_Q (heq ▸ hvQ), hav⟩
        exact Workspace.ProofLemmas.AntiholeCompletion.three_le_length_of_antipath
          (G := Gᶜ) (Workspace.ProofLemmas.PathBasics.isAntipathFrom_compl.mpr hL) hac
      have hLout : ∀ u ∈ L, u ∉ {s : V | s ∈ z} := by
        intro u hu huz
        change u ∈ z at huz
        rcases hLmem u hu with huTail | hua
        · exact hQZdisj u
            ((HyperprismRungStructure.mem_tail_iff_of_pathFrom hoptQ.1.1).1 huTail).1 huz
        · have hua' : u = a := Set.mem_singleton_iff.mp hua
          subst u
          exact G.irrefl (haZ a huz)
      have hcomplete : ∀ u ∈ L,
          VertexComplete G u {s : V | s ∈ z} → u = a ∨ u = v := by
        intro u hu hc
        rcases hLmem u hu with huTail | hua
        · exact Or.inr ((hunique u
            ((HyperprismRungStructure.mem_tail_iff_of_pathFrom hoptQ.1.1).1 huTail).1).1 hc)
        · exact Or.inl (Set.mem_singleton_iff.mp hua)
      have hnoedge : ¬ ∃ u ∈ L, ∃ s ∈ L,
          EdgeComplete G {t : V | t ∈ z} u s := by
        rintro ⟨u, hu, s, hs, hus, huZ, hsZ⟩
        rcases hcomplete u hu huZ with rfl | rfl <;>
          rcases hcomplete s hs hsZ with rfl | rfl
        · exact G.irrefl hus
        · exact hav hus
        · exact hav hus.symm
        · exact G.irrefl hus
      have hb₁Z : VertexComplete G b₁ {s : V | s ∈ z} := by
        intro s hs
        exact (hzB s hs b₁ hstep.1.2.2.1).symm
      have hb₁NoInt : ∀ u ∈ interior L, ¬ G.Adj b₁ u := by
        intro u hu hadj
        obtain ⟨huQ, hur, huv⟩ := hLintQ u hu
        exact hoptQ.1.2.2.2.2 u
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
            ⟨huQ, hur, huv⟩) b₁ (Or.inl (Or.inr hstep.1.2.2.1)) hadj.symm
      have hLeven : Even (pathLength L) := by
        rcases Nat.even_or_odd (pathLength L) with he | ho
        · exact he
        · obtain ⟨u, hu, hbu⟩ := Workspace.Statements.S02.SPGT.thm_2_2
            G hG {s : V | s ∈ z} hzanti L a v hL hLout ho haZ
              (by intro s hs; exact (hunique v hvQ).2 rfl s hs)
              hnoedge b₁ hb₁Z
          exact (hb₁NoInt u hu hbu).elim

      -- Complete `L` through the first rung.  This second path has odd
      -- length, contradicting Berge parity.
      have haa₁ : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
      have hvb₁ : G.Adj v b₁ := hv'.2.1 b₁ hstep.1.2.2.1
      have haR₁ : a ∉ R₁ := by
        intro hm
        exact hopt.1.2.2.1.1 (Thm131Trajectory.rung_mem_strip hstep.1 a hm)
      have hvR₁ : v ∉ R₁ := by
        intro hm
        exact hv'.1 (Thm131Trajectory.rung_mem_strip hstep.1 v hm)
      have ha_other_R₁ : ∀ u ∈ R₁, u ≠ a₁ → ¬ G.Adj a u := by
        intro u hu hune
        rcases Thm131Trajectory.rung_mem_strip hstep.1 u hu with (huA | huB) | huC
        · exact absurd (hstep.1.2.2.2.1 u hu huA) hune
        · exact hopt.1.2.2.1.2.2 u (Or.inl huB)
        · exact hopt.1.2.2.1.2.2 u (Or.inr huC)
      have hv_other_R₁ : ∀ u ∈ R₁, u ≠ b₁ → ¬ G.Adj v u := by
        intro u hu hune
        rcases Thm131Trajectory.rung_mem_strip hstep.1 u hu with (huA | huB) | huC
        · exact hv'.2.2 u (Or.inl huA)
        · exact absurd (hstep.1.2.2.2.2.1 u hu huB) hune
        · exact hv'.2.2 u (Or.inr huC)
      let M : List V := a :: (R₁ ++ [v])
      have hM : IsPathFrom G M a v := by
        simpa [M] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat
          hstep.1.1 haa₁ hvb₁ hav
          (fun heq => ha_not_Q (heq ▸ hvQ)) haR₁ hvR₁
          ha_other_R₁ hv_other_R₁
      have hR₁odd : Odd (pathLength R₁) :=
        (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
          a b P hopt.1).1 a₁ R₁ b₁ hstep.1
      have hModd : Odd (pathLength M) := by
        have ha₁_ne_b₁ : a₁ ≠ b₁ := by
          intro heq
          exact Set.disjoint_left.mp hK.1.1.1.1.1 ha₁A (heq ▸ hstep.1.2.2.1)
        have hRtwo : 2 ≤ R₁.length := by
          have hRpos := Workspace.ProofLemmas.PathBasics.path_length_pos hstep.1.1.1
          by_contra hlt
          have hone : R₁.length = 1 := by omega
          obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hone
          have hua : u = a₁ := by simpa using hstep.1.1.2.1
          have hub : u = b₁ := by simpa using hstep.1.1.2.2
          exact ha₁_ne_b₁ (hua.symm.trans hub)
        have hMlen : pathLength M = pathLength R₁ + 2 := by
          simp only [M, pathLength, List.length_cons, List.length_append, List.length_nil,
            Nat.add_zero]
          omega
        obtain ⟨k, hk⟩ := hR₁odd
        refine ⟨k + 1, ?_⟩
        rw [hMlen]
        omega
      have hM3 : 3 ≤ M.length := by
        have hRpos := Workspace.ProofLemmas.PathBasics.path_length_pos hstep.1.1.1
        have hMlength : M.length = R₁.length + 2 := by simp [M]
        rw [hMlength]
        omega
      have hIntDisj : ∀ u ∈ interior L, u ∉ interior M := by
        intro u hu huM
        obtain ⟨huQ, -, -⟩ := hLintQ u hu
        have huStrip : u ∈ A ∪ B ∪ C := by
          have hm := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hM).1 huM
          have hmmem := hm.1
          change u ∈ a :: (R₁ ++ [v]) at hmmem
          simp at hmmem
          rcases hmmem with hua | huR | huv'
          · exact absurd hua hm.2.1
          · exact Thm131Trajectory.rung_mem_strip hstep.1 u huR
          · exact absurd huv' hm.2.2
        exact hoptQ.1.2.1 u huQ huStrip
      have hIntAnti : ∀ u ∈ interior L, ∀ s ∈ interior M, ¬ G.Adj u s := by
        intro u hu s hs hadj
        obtain ⟨huQ, hur, huv⟩ := hLintQ u hu
        have huIntQ :=
          (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
            ⟨huQ, hur, huv⟩
        have hsStrip : s ∈ A ∪ B ∪ C := by
          have hm := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hM).1 hs
          have hmmem := hm.1
          change s ∈ a :: (R₁ ++ [v]) at hmmem
          simp at hmmem
          rcases hmmem with hsa | hsR | hsv
          · exact absurd hsa hm.2.1
          · exact Thm131Trajectory.rung_mem_strip hstep.1 s hsR
          · exact absurd hsv hm.2.2
        exact hoptQ.1.2.2.2.2 u huIntQ s hsStrip hadj
      obtain ⟨hhole, hhlen⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
        hL hM hL3 hM3 hIntDisj hIntAnti
      have hev := hG.1 _ hhole
      rw [hhlen] at hev
      obtain ⟨ke, hke⟩ := hLeven
      obtain ⟨ko, hko⟩ := hModd
      obtain ⟨kh, hkh⟩ := hev
      omega
    obtain ⟨q, hq, haq⟩ := haSome
    have hqr := honly q hq haq
    intro q' hq'
    constructor
    · exact honly q' hq'
    · rintro rfl
      exact hqr ▸ haq

  have hQodd : Odd (pathLength Q) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      r v Q hoptQ.1).2
  have hPodd : Odd (pathLength P) :=
    (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
      a b P hopt.1).2
  have hbnev : b ≠ v := by
    intro hbv
    apply hopt.2.2
    refine ⟨r, Q, ?_, hbirthQfull.2.1, x[j], v, hbirthQfull, habirth, hearlier⟩
    simpa [hbv] using hoptQ.1
  have hvOutside : v ∉ staircaseVertices A C B P :=
    bComplete_not_mem_staircase hK.1.1 hv'.2.1 hbnev.symm
  have hv_not_P : v ∉ P := fun hvP => hvOutside (Or.inl hvP)
  have har : G.Adj a r :=
    (haonly r (Workspace.ProofLemmas.PathBasics.head_mem hoptQ.1.1.2.1)).2 rfl
  have hL₁ : IsPathFrom G (a :: Q) a v := by
    refine Workspace.ProofLemmas.PathAttach.isPathFrom_cons hoptQ.1.1 har ha_not_Q ?_
    intro q hq hqr
    exact fun hadj => hqr ((haonly q hq).1 hadj)
  have hL₁even : Even (pathLength (a :: Q)) := by
    have hlen : pathLength (a :: Q) = pathLength Q + 1 := by
      have hQpos := Workspace.ProofLemmas.PathBasics.path_length_pos hoptQ.1.1.1
      simp only [pathLength, List.length_cons]
      omega
    obtain ⟨k, hk⟩ := hQodd
    refine ⟨k + 1, ?_⟩
    rw [hlen]
    omega
  have hL₁three : 3 ≤ (a :: Q).length := by
    have hrnev : r ≠ v := by
      obtain ⟨a₃, ha₃A⟩ := hK.1.1.1.2.1.1
      intro heq
      have hra₃ := hoptQ.1.2.2.1.2.1 a₃ ha₃A
      rw [heq] at hra₃
      exact hv'.2.2 a₃ (Or.inl ha₃A) hra₃
    have hQtwo : 2 ≤ Q.length := by
      have hQpos := Workspace.ProofLemmas.PathBasics.path_length_pos hoptQ.1.1.1
      by_contra hlt
      have hone : Q.length = 1 := by omega
      obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hone
      have hur : u = r := by simpa using hoptQ.1.1.2.1
      have huv : u = v := by simpa using hoptQ.1.1.2.2
      exact hrnev (hur.symm.trans huv)
    simp
    omega

  have hvSome : ∃ p ∈ P, G.Adj v p := by
    by_contra hnone
    push Not at hnone
    have hbb₁ : G.Adj b b₁ := hopt.1.2.2.2.1.2.1 b₁ hstep.1.2.2.1
    have hb₁_not_P : b₁ ∉ P := by
      intro hm
      exact hopt.1.2.1 b₁ hm (Or.inl (Or.inr hstep.1.2.2.1))
    have hb₁other : ∀ p ∈ P, p ≠ b → ¬ G.Adj b₁ p := by
      intro p hp hpb hadj
      by_cases hpa : p = a
      · exact hopt.1.2.2.1.2.2 b₁ (Or.inl hstep.1.2.2.1) (hpa ▸ hadj.symm)
      · exact hopt.1.2.2.2.2 p
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hopt.1.1).2
            ⟨hp, hpa, hpb⟩) b₁ (Or.inl (Or.inr hstep.1.2.2.1)) hadj.symm
    have hPb₁ : IsPathFrom G (P ++ [b₁]) a b₁ :=
      Workspace.ProofLemmas.PathAttach.isPathFrom_concat hopt.1.1 hbb₁.symm hb₁_not_P
        hb₁other
    have hvb₁ : G.Adj v b₁ := hv'.2.1 b₁ hstep.1.2.2.1
    have hv_not_Pb₁ : v ∉ P ++ [b₁] := by
      intro hm
      rcases List.mem_append.mp hm with hmP | hm
      · exact hv_not_P hmP
      · have hvb : v = b₁ := by simpa using hm
        exact hv'.1 (hvb ▸ Or.inl (Or.inr hstep.1.2.2.1))
    have hvother : ∀ p ∈ P ++ [b₁], p ≠ b₁ → ¬ G.Adj v p := by
      intro p hp hpne
      rcases List.mem_append.mp hp with hpP | hpB
      · exact hnone p hpP
      · exact absurd (by simpa using hpB) hpne
    let L₂ : List V := P ++ [b₁, v]
    have hL₂ : IsPathFrom G L₂ a v := by
      simpa [L₂, List.append_assoc] using
        Workspace.ProofLemmas.PathAttach.isPathFrom_concat hPb₁ hvb₁
          hv_not_Pb₁ hvother
    have hL₂odd : Odd (pathLength L₂) := by
      have hlen : pathLength L₂ = pathLength P + 2 := by
        have hPpos := Workspace.ProofLemmas.PathBasics.path_length_pos hopt.1.1.1
        simp only [L₂, pathLength, List.length_append, List.length_cons, List.length_nil]
        omega
      obtain ⟨k, hk⟩ := hPodd
      refine ⟨k + 1, ?_⟩
      rw [hlen]
      omega
    have hL₂three : 3 ≤ L₂.length := by
      have hPpos := Workspace.ProofLemmas.PathBasics.path_length_pos hopt.1.1.1
      simp [L₂]
      omega
    have hQdrop_b₁ : ∀ q ∈ Q.dropLast, ¬ G.Adj q b₁ := by
      intro q hq hadj
      have hd := (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hoptQ.1.1).1 hq
      by_cases hqr : q = r
      · exact hoptQ.1.2.2.1.2.2 b₁ (Or.inl hstep.1.2.2.1) (hqr ▸ hadj)
      have hqint := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hoptQ.1.1).2
        ⟨hd.1, hqr, hd.2⟩
      exact hoptQ.1.2.2.2.2 q hqint b₁
        (Or.inl (Or.inr hstep.1.2.2.1)) hadj
    have hIntDisj : ∀ q ∈ interior (a :: Q), q ∉ interior L₂ := by
      intro q hq hqL₂
      have hqd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₁).1 hq
      have hqQ : q ∈ Q := by
        rcases List.mem_cons.mp hqd.1 with hqa | hqQ
        · exact absurd hqa hqd.2.1
        · exact hqQ
      have hqL := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₂).1 hqL₂
      have hmem := hqL.1
      change q ∈ P ++ [b₁, v] at hmem
      simp at hmem
      rcases hmem with hqP | hqb₁ | hqv
      · exact hdisj q hqP hqQ
      · subst q
        exact hoptQ.1.2.1 b₁ hqQ (Or.inl (Or.inr hstep.1.2.2.1))
      · exact absurd hqv hqL.2.2
    have hIntAnti : ∀ q ∈ interior (a :: Q), ∀ p ∈ interior L₂,
        ¬ G.Adj q p := by
      intro q hq p hp hadj
      have hqd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₁).1 hq
      have hqQ : q ∈ Q := by
        rcases List.mem_cons.mp hqd.1 with hqa | hqQ
        · exact absurd hqa hqd.2.1
        · exact hqQ
      have hqDrop : q ∈ Q.dropLast :=
        (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hoptQ.1.1).2 ⟨hqQ, hqd.2.2⟩
      have hpd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₂).1 hp
      have hmem := hpd.1
      change p ∈ P ++ [b₁, v] at hmem
      simp at hmem
      rcases hmem with hpP | hpb₁ | hpv
      · have hpTail : p ∈ P.tail :=
          (HyperprismRungStructure.mem_tail_iff_of_pathFrom hopt.1.1).2 ⟨hpP, hpd.2.1⟩
        exact hsep p hpTail q hqDrop hadj.symm
      · subst p
        exact hQdrop_b₁ q hqDrop hadj
      · exact absurd hpv hpd.2.2
    obtain ⟨hhole, hhlen⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
      hL₁ hL₂ hL₁three hL₂three hIntDisj hIntAnti
    have hev := hG.1 _ hhole
    rw [hhlen] at hev
    obtain ⟨ke, hke⟩ := hL₁even
    obtain ⟨ko, hko⟩ := hL₂odd
    obtain ⟨kh, hkh⟩ := hev
    omega

  by_cases hvunique : ∀ p ∈ P, G.Adj v p → p = b
  · have hvonly : ∀ p ∈ P, (G.Adj p v ↔ p = b) := by
      obtain ⟨p₀, hp₀, hvp₀⟩ := hvSome
      have hp₀b := hvunique p₀ hp₀ hvp₀
      intro p hp
      constructor
      · intro hpv
        exact hvunique p hp hpv.symm
      · rintro rfl
        exact hp₀b ▸ hvp₀.symm
    exact attached_banister_contradicts_maximality hK.1 hoptQ.1 hdisj
      hvonly haonly hnolink
  · push Not at hvunique
    obtain ⟨p, hpP, hvp, hpneb⟩ := hvunique
    -- The last two holes in claim (4): first compare the path through `P`
    -- with `a-r-Q-v`, then compare it with the path through the rung `R₁`.
    have hPlen : 2 ≤ P.length := by
      obtain ⟨k, hk⟩ := hPodd
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hk
      omega
    have hPdropconn : ConnectedSet G {u : V | u ∈ P.dropLast} :=
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (HyperprismRungStructure.isPathList_dropLast hopt.1.1.1 hPlen)
    have hpDrop : p ∈ P.dropLast :=
      (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hopt.1.1).2 ⟨hpP, hpneb⟩
    have hconn : ConnectedSet G ({u : V | u ∈ P.dropLast} ∪ {v}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union_singleton
        hPdropconn ⟨p, hpDrop, hvp⟩
    have haP : a ∈ P := Workspace.ProofLemmas.PathBasics.head_mem hopt.1.1.2.1
    have haneb : a ≠ b := by
      obtain ⟨a₃, ha₃A⟩ := hK.1.1.1.2.1.1
      intro heq
      exact hopt.1.2.2.2.1.2.2 a₃ (Or.inl ha₃A)
        (heq ▸ hopt.1.2.2.1.2.1 a₃ ha₃A)
    have haDrop : a ∈ P.dropLast :=
      (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hopt.1.1).2 ⟨haP, haneb⟩
    obtain ⟨L, hL, hLmem⟩ :=
      Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected hconn
        (Or.inl haDrop) (Or.inr rfl)
    have hLintP : ∀ u ∈ interior L, u ∈ P.tail ∧ u ≠ b := by
      intro u hu
      have hd := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1 hu
      rcases hLmem u hd.1 with huDrop | huv
      · have hpdata := (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hopt.1.1).1 huDrop
        exact ⟨(HyperprismRungStructure.mem_tail_iff_of_pathFrom hopt.1.1).2
          ⟨hpdata.1, hd.2.1⟩, hpdata.2⟩
      · exact absurd (Set.mem_singleton_iff.mp huv) hd.2.2
    have hL3 : 3 ≤ L.length := by
      have hac : Gᶜ.Adj a v := (G.compl_adj a v).mpr
        ⟨fun heq => hv_not_P (heq ▸ haP), by simpa [v] using hnon⟩
      exact Workspace.ProofLemmas.AntiholeCompletion.three_le_length_of_antipath
        (G := Gᶜ) (Workspace.ProofLemmas.PathBasics.isAntipathFrom_compl.mpr hL) hac
    have hIntDisj : ∀ u ∈ interior L, u ∉ interior (a :: Q) := by
      intro u hu huQ
      obtain ⟨huTail, -⟩ := hLintP u hu
      have hdQ := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₁).1 huQ
      have huQmem : u ∈ Q := by
        rcases List.mem_cons.mp hdQ.1 with hua | huQmem
        · exact absurd hua hdQ.2.1
        · exact huQmem
      exact hdisj u (List.mem_of_mem_tail huTail) huQmem
    have hIntAnti : ∀ u ∈ interior L, ∀ q ∈ interior (a :: Q), ¬ G.Adj u q := by
      intro u hu q hq hadj
      obtain ⟨huTail, -⟩ := hLintP u hu
      have hdQ := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL₁).1 hq
      have hqQ : q ∈ Q := by
        rcases List.mem_cons.mp hdQ.1 with hqa | hqQ
        · exact absurd hqa hdQ.2.1
        · exact hqQ
      have hqDrop : q ∈ Q.dropLast :=
        (HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hoptQ.1.1).2 ⟨hqQ, hdQ.2.2⟩
      exact hsep u huTail q hqDrop hadj
    obtain ⟨hhole₁, hhlen₁⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
      hL hL₁ hL3 hL₁three hIntDisj hIntAnti
    have hsumEven := hG.1 _ hhole₁
    rw [hhlen₁] at hsumEven
    have hLeven : Even (pathLength L) := by
      obtain ⟨ks, hks⟩ := hsumEven
      obtain ⟨kq, hkq⟩ := hL₁even
      refine ⟨ks - kq, ?_⟩
      omega

    have haa₁ : G.Adj a a₁ := hopt.1.2.2.1.2.1 a₁ ha₁A
    have hvb₁ : G.Adj v b₁ := hv'.2.1 b₁ hstep.1.2.2.1
    have haR₁ : a ∉ R₁ := by
      intro hm
      exact hopt.1.2.2.1.1 (Thm131Trajectory.rung_mem_strip hstep.1 a hm)
    have hvR₁ : v ∉ R₁ := by
      intro hm
      exact hv'.1 (Thm131Trajectory.rung_mem_strip hstep.1 v hm)
    have ha_other_R₁ : ∀ u ∈ R₁, u ≠ a₁ → ¬ G.Adj a u := by
      intro u hu hune
      rcases Thm131Trajectory.rung_mem_strip hstep.1 u hu with (huA | huB) | huC
      · exact absurd (hstep.1.2.2.2.1 u hu huA) hune
      · exact hopt.1.2.2.1.2.2 u (Or.inl huB)
      · exact hopt.1.2.2.1.2.2 u (Or.inr huC)
    have hv_other_R₁ : ∀ u ∈ R₁, u ≠ b₁ → ¬ G.Adj v u := by
      intro u hu hune
      rcases Thm131Trajectory.rung_mem_strip hstep.1 u hu with (huA | huB) | huC
      · exact hv'.2.2 u (Or.inl huA)
      · exact absurd (hstep.1.2.2.2.2.1 u hu huB) hune
      · exact hv'.2.2 u (Or.inr huC)
    let M : List V := a :: (R₁ ++ [v])
    have hM : IsPathFrom G M a v := by
      simpa [M] using Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat
        hstep.1.1 haa₁ hvb₁ (by simpa [v] using hnon)
        (fun heq => hv_not_P (heq ▸ haP)) haR₁ hvR₁
        ha_other_R₁ hv_other_R₁
    have hR₁odd : Odd (pathLength R₁) :=
      (Workspace.Statements.S11.SPGT.thm_11_3 G hG heven A C B hK.1.1.1
        a b P hopt.1).1 a₁ R₁ b₁ hstep.1
    have hModd : Odd (pathLength M) := by
      have ha₁_ne_b₁ : a₁ ≠ b₁ := by
        intro heq
        exact Set.disjoint_left.mp hK.1.1.1.1.1 ha₁A (heq ▸ hstep.1.2.2.1)
      have hRtwo : 2 ≤ R₁.length := by
        have hRpos := Workspace.ProofLemmas.PathBasics.path_length_pos hstep.1.1.1
        by_contra hlt
        have hone : R₁.length = 1 := by omega
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hone
        have hua : u = a₁ := by simpa using hstep.1.1.2.1
        have hub : u = b₁ := by simpa using hstep.1.1.2.2
        exact ha₁_ne_b₁ (hua.symm.trans hub)
      have hMlen : pathLength M = pathLength R₁ + 2 := by
        simp only [M, pathLength, List.length_cons, List.length_append, List.length_nil]
        omega
      obtain ⟨k, hk⟩ := hR₁odd
      refine ⟨k + 1, ?_⟩
      rw [hMlen]
      omega
    have hM3 : 3 ≤ M.length := by
      have hRpos := Workspace.ProofLemmas.PathBasics.path_length_pos hstep.1.1.1
      have hMlength : M.length = R₁.length + 2 := by simp [M]
      rw [hMlength]
      omega
    have hLMdisj : ∀ u ∈ interior L, u ∉ interior M := by
      intro u hu huM
      obtain ⟨huTail, -⟩ := hLintP u hu
      have huP := List.mem_of_mem_tail huTail
      have hm := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hM).1 huM
      have hmmem := hm.1
      change u ∈ a :: (R₁ ++ [v]) at hmmem
      simp at hmmem
      rcases hmmem with hua | huR | huv
      · exact hm.2.1 hua
      · exact hopt.1.2.1 u huP (Thm131Trajectory.rung_mem_strip hstep.1 u huR)
      · exact hm.2.2 huv
    have hLManti : ∀ u ∈ interior L, ∀ s ∈ interior M, ¬ G.Adj u s := by
      intro u hu s hs hadj
      obtain ⟨huTail, hub⟩ := hLintP u hu
      have huP := List.mem_of_mem_tail huTail
      have hua : u ≠ a :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hL).1 hu |>.2.1
      have huIntP := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hopt.1.1).2
        ⟨huP, hua, hub⟩
      have hm := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hM).1 hs
      have hmmem := hm.1
      change s ∈ a :: (R₁ ++ [v]) at hmmem
      simp at hmmem
      rcases hmmem with hsa | hsR | hsv
      · exact hm.2.1 hsa
      · exact hopt.1.2.2.2.2 u huIntP s
          (Thm131Trajectory.rung_mem_strip hstep.1 s hsR) hadj
      · exact hm.2.2 hsv
    obtain ⟨hhole₂, hhlen₂⟩ := Workspace.ProofLemmas.TwoPathsHole.odd_hole_of_two_paths
      hL hM hL3 hM3 hLMdisj hLManti
    have hev := hG.1 _ hhole₂
    rw [hhlen₂] at hev
    obtain ⟨ke, hke⟩ := hLeven
    obtain ⟨ko, hko⟩ := hModd
    obtain ⟨kh, hkh⟩ := hev
    omega

end Workspace.ProofLemmas.Thm131Singleton
