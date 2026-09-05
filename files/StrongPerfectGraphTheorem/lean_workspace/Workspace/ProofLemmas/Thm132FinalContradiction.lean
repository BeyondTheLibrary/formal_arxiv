import Workspace.ProofLemmas.Thm132EndgameSetup
import Workspace.ProofLemmas.Thm132Infrastructure
import Workspace.ProofLemmas.Thm132Claim5Long
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_1

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! # The final trajectory dichotomy in the proof of 13.2. -/

namespace Workspace.ProofLemmas.Thm132FinalContradiction

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every `A`-vertex of a step-connected strip has a nonneighbour in `B`. -/
private theorem exists_B_nonneighbor {G : SimpleGraph V} {A C B : Set V}
    (hS : StepConnected G A C B) {a : V} (ha : a ∈ A) :
    ∃ b ∈ B, ¬ G.Adj a b := by
  obtain ⟨⟨hdAB, -, -⟩, -, -, hinstep, -⟩ := hS
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ :=
    hinstep a (Or.inl (Or.inl ha))
  obtain ⟨hr₁, hr₂, -, hcross⟩ := hstep
  have hne : ∀ x ∈ A, ∀ y ∈ B, x ≠ y := by
    intro x hx y hy hxy
    exact Set.disjoint_left.mp hdAB hx (hxy ▸ hy)
  rcases hmem with hmem | hmem
  · refine ⟨b₂, hr₂.2.2.1, ?_⟩
    intro hadj
    rcases (hcross a hmem b₂ (PathBasics.isPathFrom_ends_mem hr₂.1).2).mp hadj with
      ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hne a₂ hr₂.2.1 b₂ hr₂.2.2.1 h2.symm
    · exact hne a ha b₁ hr₁.2.2.1 h1
  · refine ⟨b₁, hr₁.2.2.1, ?_⟩
    intro hadj
    rcases (hcross b₁ (PathBasics.isPathFrom_ends_mem hr₁.1).2 a hmem).mp hadj.symm with
      ⟨h1, -⟩ | ⟨-, h2⟩
    · exact hne a₁ hr₁.2.1 b₁ hr₁.2.2.1 h1.symm
    · exact hne a ha b₂ hr₂.2.2.1 h2

/-- The two outcomes for the trajectory of the second optimal left end are
both impossible. -/
theorem endgame_contradiction
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
    (hPint : ∀ z, z ∈ interior P ↔ z ∈ interior R₀) : False := by
  classical
  obtain ⟨r', R', j, hj, hopt', hbirth', hjd, hR'one, hdisj, hsep, hnrr'⟩ :=
    Workspace.ProofLemmas.Thm132EndgameSetup.exists_second_configuration
      hG hK4 heven h1br h2br hK hx d hlast hwone P hP hPodd hPint
  obtain ⟨w, q, hq, zidx, hzidx, htraj, hbirthQ, hanti, hwidx⟩ :=
    Workspace.ProofLemmas.Thm132Infrastructure.exists_trajectoryOfVertex_of_leftStar
      hK.1.1.1 hx hopt'.1.2.2.1 hopt'.2.1
  have hqj : q = j := by
    obtain ⟨q', hq', hq'eq, hq'non, -⟩ := hbirthQ.2.2
    obtain ⟨j', hj', hj'eq, hj'non, -⟩ := hbirth'.2.2
    have hq'q : q' = q :=
      (List.Nodup.getElem_inj_iff hx.1.1 (hi := hq') (hj := hq)).mp hq'eq
    have hj'j : j' = j :=
      (List.Nodup.getElem_inj_iff hx.1.1 (hi := hj') (hj := hj)).mp hj'eq
    have hsame := Workspace.ProofLemmas.Thm132Optimal.birth_index_unique hx.1.1
      hbirthQ hbirth' hq' hj' hq'eq hq'non hj'eq hj'non
    omega
  subst q
  have hrW : VertexComplete G d.r {z : V | z ∈ w} := by
    obtain ⟨p, hp, hpeq, hpnon, hpBefore⟩ := d.birth_r.2.2
    have hpidx : p = d.birthIndex :=
      (List.Nodup.getElem_inj_iff hx.1.1 (hi := hp) (hj := d.birthIndex_lt)).mp hpeq
    subst p
    intro z hz
    obtain ⟨k, hk, hkj, hkz⟩ := hwidx z hz
    have hkb : k < d.birthIndex := by omega
    simpa [hkz] using hpBefore k hkb
  have hwB : ∀ z ∈ w, VertexComplete G z B := by
    intro z hz
    obtain ⟨k, hk, -, hkz⟩ := hwidx z hz
    simpa [hkz] using hx.1.2 x[k] (List.getElem_mem hk)
  have hwpos : 0 < w.length := by
    have ht := htraj
    obtain ⟨-, k, hk, wt, -, hwt, hshape⟩ := ht
    have hwtw : wt = w := (List.cons.inj hshape).2.symm
    subst wt
    exact hwt.1.1
  have hwantiList : IsPathList Gᶜ w :=
    HyperprismRungStructure.isPathList_tail hanti.1 (by simp; omega)
  let W : Set V := {z : V | z ∈ w}
  have hWanti : AnticonnectedSet G W :=
    Workspace.ProofLemmas.InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      hwantiList
  have hWout : ∀ z ∈ W, z ∉ A ∪ B ∪ C := by
    intro z hz
    exact Workspace.ProofLemmas.Thm132Infrastructure.bComplete_not_mem_strip
      hK.1.1.1 (hwB z hz)
  have hr'last : G.Adj r' d.last :=
    PathBasics.isPathFrom_ends_adj_of_length_one hopt'.1.1 hR'one
  have hwshapeD : d.w = [d.last] := by
    obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hwone
    have hc := d.trajectory_antipath.2.2
    rw [hz] at hc
    have hzl : z = d.last := by
      simpa [List.getLast?_cons_of_ne_nil (by simp : [z] ≠ [])] using hc
    simpa [hz, hzl]
  have hcompRW := PathBasics.isPathFrom_ends_adj_of_length_one d.trajectory_antipath (by
      rw [PathBasics.pathLength_eq]
      simp [hwshapeD])
  rw [SimpleGraph.compl_adj] at hcompRW
  have hrneLast : d.r ≠ d.last := hcompRW.1
  have hrw : ¬ G.Adj d.r d.last := hcompRW.2
  have h13 := Workspace.Statements.S13.SPGT.thm_13_1 G hG hK4 heven h1br h2br
    A C B a₀ b₀ R₀ hK x hx d.last hlast r' R' hopt' w htraj
  rcases h13.2 with hunique | hantipath
  · -- The unique-complete outcome contradicts 2.2.
    have hlastR' : d.last ∈ R' := PathBasics.getLast_mem hopt'.1.1.2.2
    have hr'R' : r' ∈ R' := PathBasics.head_mem hopt'.1.1.2.1
    have hlastW : VertexComplete G d.last W := (hunique d.last hlastR').2 rfl
    have hr'notW : ¬ VertexComplete G r' W := by
      intro hc
      exact hr'last.ne ((hunique r' hr'R').1 hc)
    have ht := htraj
    obtain ⟨-, k, hk, wt, -, hwt, hshape⟩ := ht
    have hwtw : wt = w := (List.cons.inj hshape).2.symm
    subst wt
    obtain ⟨vm, hvmLast, a₁, ha₁A, hvma⟩ := hwt.2.1
    have hvmW : vm ∈ W := PathBasics.getLast_mem hvmLast
    have ha₁notW : ¬ VertexComplete G a₁ W := by
      intro hc
      exact hvma (hc vm hvmW).symm
    have hr'a₁ : G.Adj r' a₁ := hopt'.1.2.2.1.2.1 a₁ ha₁A
    have ha₁r : G.Adj a₁ d.r := (d.optimal.1.2.2.1.2.1 a₁ ha₁A).symm
    have hlasta₁ : ¬ G.Adj d.last a₁ := hlast.2.2 a₁ (Or.inl ha₁A)
    have hr'neR : r' ≠ d.r := by
      intro he
      exact hrw (he ▸ hr'last)
    have hlastneR : d.last ≠ d.r := hrneLast.symm
    have hlastnea₁ : d.last ≠ a₁ := by
      intro he
      exact hlast.1 (he ▸ Or.inl (Or.inl ha₁A))
    have hnd : ([d.last, r', a₁, d.r] : List V).Nodup := by
      simp [hr'last.ne', hlastnea₁, hlastneR, hr'a₁.ne, hr'neR, ha₁r.ne]
    let L : List V := [d.last, r', a₁, d.r]
    have hL : IsPathFrom G L d.last d.r := by
      refine ⟨Workspace.ProofLemmas.PathGlue.isPathList_four hnd hr'last.symm hr'a₁ ha₁r
        hlasta₁ (fun h => hrw h.symm) (fun h => hnrr' h.symm), by simp [L], by simp [L]⟩
    have hLodd : Odd (pathLength L) := ⟨1, by simp [L, pathLength]⟩
    have hLW : ∀ z ∈ L, z ∉ W := by
      intro z hz hzW
      simp [L] at hz
      rcases hz with hz | hz | hz | hz
      · subst z
        exact G.irrefl (hlastW d.last hzW)
      · subst z
        obtain ⟨kk, hkk, -, hkkz⟩ := hwidx r' hzW
        exact htraj.1.2.1 (hkkz ▸ List.getElem_mem hkk)
      · subst z
        exact hWout a₁ hzW (Or.inl (Or.inl ha₁A))
      · subst z
        exact G.irrefl (hrW d.r hzW)
    have hcompleteEnds : ∀ z ∈ L, VertexComplete G z W →
        z = d.last ∨ z = d.r := by
      intro z hz hc
      simp [L] at hz
      rcases hz with hz | hz | hz | hz
      · exact Or.inl hz
      · exact absurd (hz ▸ hc) hr'notW
      · exact absurd (hz ▸ hc) ha₁notW
      · exact Or.inr hz
    have hnoedge : ¬ ∃ u ∈ L, ∃ v ∈ L, EdgeComplete G W u v := by
      rintro ⟨u, hu, v, hv, huv, huW, hvW⟩
      rcases hcompleteEnds u hu huW with rfl | rfl <;>
        rcases hcompleteEnds v hv hvW with rfl | rfl
      · exact G.irrefl huv
      · exact hrw huv.symm
      · exact hrw huv
      · exact G.irrefl huv
    obtain ⟨b₁, hb₁B, ha₁b₁⟩ := exists_B_nonneighbor hK.1.1.1 ha₁A
    have hb₁W : VertexComplete G b₁ W := by
      intro z hz
      exact (hwB z hz b₁ hb₁B).symm
    obtain ⟨z, hzint, hb₁z⟩ := Workspace.Statements.S02.SPGT.thm_2_2
      G hG W hWanti L d.last d.r hL hLW hLodd hlastW hrW hnoedge b₁ hb₁W
    have hzmem : z = r' ∨ z = a₁ := by simpa [L, SPGT.interior] using hzint
    rcases hzmem with rfl | rfl
    · exact hopt'.1.2.2.1.2.2 b₁ (Or.inl hb₁B) hb₁z.symm
    · exact ha₁b₁ hb₁z.symm
  · -- The antipath outcome closes through `r` to an odd antihole.
    obtain ⟨-, m, hmEven, hm1, hmw, hqpath⟩ := hantipath
    let Q : List V := r' :: (w.take m ++ [d.last])
    have hQ : IsPathFrom Gᶜ Q r' d.last := by
      refine ⟨by simpa [Q] using hqpath, by simp [Q], ?_⟩
      simp only [Q]
      rw [List.getLast?_cons_of_ne_nil (by simp : w.take m ++ [d.last] ≠ [])]
      exact List.getLast?_concat
    have htlen : (w.take m).length = m := by
      simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hmw)]
    have hQLength : Q.length = m + 2 := by simp [Q, htlen]
    have hQpathLength : pathLength Q = m + 1 := by
      rw [pathLength, hQLength]
      omega
    have hQodd : Odd (pathLength Q) := by
      obtain ⟨k, hk⟩ := hmEven
      refine ⟨k, ?_⟩
      rw [hQpathLength, hk]
      omega
    have hQ3 : 3 ≤ Q.length := by omega
    have hrneR' : d.r ≠ r' := by
      intro he
      exact hrw (he ▸ hr'last)
    have hrnotQ : d.r ∉ Q := by
      intro hz
      simp [Q] at hz
      rcases hz with hz | hz | hz
      · exact hrneR' hz
      · have hzW : d.r ∈ W := List.mem_of_mem_take hz
        exact G.irrefl (hrW d.r hzW)
      · exact hrneLast hz
    have hcross : ∀ z ∈ Q, (Gᶜ.Adj z d.r ↔ z = r' ∨ z = d.last) := by
      intro z hz
      constructor
      · intro hzr
        simp [Q] at hz
        rcases hz with hz | hz | hz
        · exact Or.inl hz
        · exfalso
          have hzW : z ∈ W := List.mem_of_mem_take hz
          rw [SimpleGraph.compl_adj] at hzr
          exact hzr.2 (hrW z hzW).symm
        · exact Or.inr hz
      · rintro (rfl | rfl)
        · rw [SimpleGraph.compl_adj]
          exact ⟨hrneR'.symm, fun h => hnrr' h.symm⟩
        · rw [SimpleGraph.compl_adj]
          exact ⟨hrneLast.symm, fun h => hrw h.symm⟩
    exact Workspace.ProofLemmas.Thm132Claim5Long.no_odd_path_closer
      (HoleBasics.berge_compl.mpr hG) hQ hQodd hQ3 hrnotQ hcross

end Workspace.ProofLemmas.Thm132FinalContradiction
