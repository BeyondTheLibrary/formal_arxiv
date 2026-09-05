import Workspace.ProofLemmas.Thm132Setup
import Workspace.Statements.S12.Thm_12_5

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Claim (2) of 13.2

For the canonical optimal edge `r-R-b₀` and the trajectory `r-w₁-⋯-wₙ`,
the right end `b₀` is complete to all trajectory vertices.  The second outcome
of 13.1 would give an antipath ending at `b₀`; its prefix has precisely the
diagonal pattern forbidden by 12.5.
-/

namespace Workspace.ProofLemmas.Thm132Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm132Infrastructure
open Workspace.ProofLemmas.Thm132Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem getElem_eq_of_index_eq {l : List V} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (hij : i = j) :
    l[i] = l[j] := by
  subst j
  rfl

private theorem take_pathFrom {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) {k : ℕ} (hk : k < p.length) :
    IsPathFrom G (p.take (k + 1)) u p[k] := by
  refine ⟨PathBasics.isPathList_take hp.1 (by omega), ?_, ?_⟩
  · obtain ⟨y, t, rfl⟩ := List.exists_cons_of_ne_nil hp.1.1
    rw [List.take_succ_cons]
    simpa using hp.2.1
  · have h := PathBasics.getLast?_slice p (i := 0) (j := k) (by omega) hk
    simpa using h

theorem leftStar_adj_rightEnd_outside
    {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ r : V} {R₀ : List V}
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hr : IsLeftStar G A C B r) (hrne : r ≠ a₀) (hrb : G.Adj r b₀) :
    r ∉ staircaseVertices A C B R₀ := by
  rintro (hrR | hrS)
  · have hrbne : r ≠ b₀ := hrb.ne
    have hrint : r ∈ interior R₀ :=
      (PathBasics.mem_interior_iff_of_pathFrom hK.2.1.1).mpr ⟨hrR, hrne, hrbne⟩
    obtain ⟨a, ha⟩ := hK.1.2.1.1
    exact hK.2.1.2.2.2.2 r hrint a (Or.inl (Or.inl ha)) (hr.2.1 a ha)
  · exact hr.1 hrS

/-- PAPER claim (2): `b₀` is complete to the trajectory tail. -/
theorem right_end_complete_trajectory
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
    {i : ℕ} (hi : i < x.length)
    (hprev : ∀ (j : ℕ) (hj : j < i), G.Adj x[j] a₀)
    (hbad : ¬ G.Adj x[i] a₀)
    (d : FirstBadData G A C B a₀ b₀ R₀ x i) :
    VertexComplete G b₀ {z : V | z ∈ d.w} := by
  classical
  have h13 := Workspace.Statements.S13.SPGT.thm_13_1 G hG hK4 heven h1br h2br
    A C B a₀ b₀ R₀ hK x hx b₀ hK.1.1.2.1.2.2.2.1
      d.r d.R d.optimal d.w d.trajectory
  rcases h13.2 with hunique | hshort
  · have hbmem : b₀ ∈ d.R :=
      (PathBasics.isPathFrom_ends_mem d.optimal.1.1).2
    exact (hunique b₀ hbmem).mpr rfl
  · obtain ⟨-, m, hmeven, hm1, hmlt, hQlist⟩ := hshort
    let Q : List V := d.r :: (d.w.take m ++ [b₀])
    let L : List V := d.r :: d.w.take m
    let wm : V := d.w[m - 1]
    have hmle : m ≤ d.w.length := le_of_lt hmlt
    have hQfrom : IsAntipathFrom G Q d.r b₀ := by
      refine ⟨by simpa [Q] using hQlist, by simp [Q], ?_⟩
      have ht : d.w.take m ++ [b₀] ≠ [] := by simp
      simp [Q, List.getLast?_cons_of_ne_nil ht]
    have hQlen : Q.length = m + 2 := by simp [Q, List.length_take, hmle]
    have hLlen : L.length = m + 1 := by simp [L, List.length_take, hmle]
    have hwmem : wm ∈ d.w := List.getElem_mem (by omega)
    have hwmLast : d.w[d.w.length - 1]'(by omega) = d.last := by
      have hc := d.trajectory_antipath.2.2
      have hwne : d.w ≠ [] := List.ne_nil_of_length_pos (by omega)
      have hc' : d.w.getLast? = some d.last := by
        simpa [List.getLast?_cons_of_ne_nil hwne] using hc
      exact PathBasics.getElem_last_of_getLast? hc' (by omega)
    have hwmneLast : wm ≠ d.last := by
      intro heq
      have he : d.w[m - 1]'(by omega) = d.w[d.w.length - 1]'(by omega) := by
        simpa [wm, heq] using hwmLast.symm
      have := (List.Nodup.getElem_inj_iff d.trajectory_antipath.1.2.1.tail).mp he
      omega
    have hwmA : VertexComplete G wm A := d.before_last_A_complete wm hwmem hwmneLast
    have hQm : Q[m]'(by omega) = wm := by
      cases m with
      | zero => omega
      | succ m => simp [Q, wm, hmle]
    have hQpen : Q[Q.length - 2]'(by omega) = wm := by
      have hind : Q.length - 2 = m := by omega
      exact (getElem_eq_of_index_eq (by omega) (by omega) hind).trans hQm
    have hQlast : ∀ z ∈ Q, (Gᶜ.Adj z b₀ ↔ z = wm) := by
      intro z hz
      simpa [hQpen] using
        (adj_last_iff_eq_penultimate hQfrom (by omega) hz)
    have hQeq : Q = L ++ [b₀] := by simp [Q, L]
    have hLfrom : IsAntipathFrom G L d.r wm := by
      have ht := take_pathFrom hQfrom (k := m) (by omega)
      have htake : Q.take (m + 1) = L := by
        simp [Q, L, List.take_append, List.length_take, hmle]
      rw [htake] at ht
      simpa [hQm] using ht
    have hrb : G.Adj d.r b₀ :=
      PathBasics.isPathFrom_ends_adj_of_length_one d.optimal.1.1 d.R_length_one
    have hrne : d.r ≠ a₀ := by
      intro hre
      obtain ⟨j', hj', hj'eq, hj'non, -⟩ := d.birth_r.2.2
      have hj'j : j' = d.birthIndex :=
        (List.Nodup.getElem_inj_iff hx.1.1).mp hj'eq
      subst j'
      exact hj'non (by simpa [hre] using (hprev d.birthIndex d.birth_before_bad).symm)
    have hrout := leftStar_adj_rightEnd_outside hK.1.1 d.optimal.1.2.2.1 hrne hrb
    have hrleft : LeftDiagonal G A C B a₀ R₀ b₀ d.r := by
      refine ⟨hrout, ?_⟩
      intro z hz
      rcases hz with hzA | rfl
      · exact d.optimal.1.2.2.1.2.1 z hzA
      · exact hrb
    have hrright : ¬ RightDiagonal G A C B a₀ R₀ b₀ d.r := by
      rintro ⟨-, hc⟩
      obtain ⟨b, hb⟩ := hK.1.1.1.2.1.2
      exact d.optimal.1.2.2.1.2.2 b (Or.inl hb) (hc b (Or.inl hb))
    have hwmout : wm ∉ staircaseVertices A C B R₀ :=
      bComplete_adj_left_not_mem_staircase hK.1.1
        (d.w_B_complete wm hwmem) (d.a₀_complete_w wm hwmem).symm
    have hwmright : RightDiagonal G A C B a₀ R₀ b₀ wm := by
      refine ⟨hwmout, ?_⟩
      intro z hz
      rcases hz with hzB | rfl
      · exact d.w_B_complete wm hwmem z hzB
      · exact (d.a₀_complete_w wm hwmem).symm
    have hwmBnon : ¬ G.Adj wm b₀ := by
      have hwmTake : wm ∈ d.w.take m := by
        have hk : m - 1 < (d.w.take m).length := by simp [hmle]; omega
        have he : (d.w.take m)[m - 1]'hk = wm := by simp [wm]
        exact he ▸ List.getElem_mem hk
      have hc : Gᶜ.Adj wm b₀ :=
        (hQlast wm (by simp [Q, hwmTake])).mpr rfl
      exact (G.compl_adj wm b₀).mp hc |>.2
    have hwmleft : ¬ LeftDiagonal G A C B a₀ R₀ b₀ wm := by
      rintro ⟨-, hc⟩
      exact hwmBnon (hc b₀ (Or.inr rfl))
    have hInt : ∀ z ∈ interior L,
        LeftDiagonal G A C B a₀ R₀ b₀ z ∧
          RightDiagonal G A C B a₀ R₀ b₀ z := by
      intro z hz
      have hzmemL := (PathBasics.mem_interior_iff_of_pathFrom hLfrom).mp hz |>.1
      have hzneR := (PathBasics.mem_interior_iff_of_pathFrom hLfrom).mp hz |>.2.1
      have hzneWm := (PathBasics.mem_interior_iff_of_pathFrom hLfrom).mp hz |>.2.2
      have hzwtake : z ∈ d.w.take m := by
        simpa [L, hzneR] using hzmemL
      have hzw : z ∈ d.w := List.mem_of_mem_take hzwtake
      obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hzwtake
      have hklt : k < m := by
        have hlenTake : (d.w.take m).length = m := by simp [hmle]
        omega
      have hkw : k < d.w.length := by omega
      have hkzW : d.w[k]'hkw = z := by
        calc
          d.w[k] = (d.w.take m)[k] := (List.getElem_take).symm
          _ = z := hkz
      have hzneLast : z ≠ d.last := by
        intro heq
        have he : d.w[k]'(by omega) = d.w[d.w.length - 1]'(by omega) := by
          exact hkzW.trans (heq.trans hwmLast.symm)
        have := (List.Nodup.getElem_inj_iff d.trajectory_antipath.1.2.1.tail).mp he
        omega
      have hzA := d.before_last_A_complete z hzw hzneLast
      have hzneB₀ : z ≠ b₀ := by
        rw [hQeq] at hQfrom
        exact (List.nodup_append.mp hQfrom.1.2.1).2.2 z hzmemL b₀ (by simp)
      have hzb₀ : G.Adj z b₀ := by
        by_contra hn
        have hc : Gᶜ.Adj z b₀ := (G.compl_adj z b₀).mpr ⟨hzneB₀, hn⟩
        have hzQ : z ∈ Q := by
          rw [hQeq]
          exact List.mem_append_left _ hzmemL
        exact hzneWm ((hQlast z hzQ).mp hc)
      have hzout := bComplete_adj_left_not_mem_staircase hK.1.1
        (d.w_B_complete z hzw) (d.a₀_complete_w z hzw).symm
      constructor
      · refine ⟨hzout, ?_⟩
        intro y hy
        rcases hy with hyA | rfl
        · exact hzA y hyA
        · exact hzb₀
      · refine ⟨hzout, ?_⟩
        intro y hy
        rcases hy with hyB | rfl
        · exact d.w_B_complete z hzw y hyB
        · exact (d.a₀_complete_w z hzw).symm
    have hends := Workspace.Statements.S12.SPGT.thm_12_5 G hG hK4 heven h1br h2br
      A C B a₀ b₀ R₀ hK L d.r wm hLfrom hInt
        ⟨hrleft, hrright⟩ ⟨hwmright, hwmleft⟩
    obtain ⟨a, ha⟩ := hK.1.1.1.2.1.1
    exact False.elim (hends.2.2.2 a (Or.inl ha) (hwmA a ha))

end Workspace.ProofLemmas.Thm132Claim2
