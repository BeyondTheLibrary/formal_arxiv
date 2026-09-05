import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S15.Thm_15_7
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.WheelConverse
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm203Prelim
import Workspace.ProofLemmas.Thm203AntipathTools

/-!
# 20.3, step (3), the second case: `x_{t−1}` has no neighbour in `A_{t−3} ∪ V(R \ q)`

PAPER (printed p. 127):

> *"So `x_{t−1}` has no neighbours in `A_{t−3} ∪ V(R \ q)`.  Now the antipath
> `z-q-Q-x_{t−1}` is odd, and all its internal vertices have neighbours in
> `A_{t−3} ∪ V(R \ q)`, and its ends do not, so by 13.6 it has length 3, that is, `Q` has
> length 2 (let its middle vertex be `x_i`); and there is an odd path `P` between `q, x_i`
> with interior in `A_{t−3} ∪ V(R \ q)`.  Let `C` be the hole `z-x_{t−1}-q-P-x_i-z`; then
> `C` has length `≥ 6`.  By 15.7 there is no antihole of length `≥ 6` containing
> `q, x_i, x_{t−1}`.  If `q` is not `Y`-complete then an antipath between `q, x_t` with
> interior in `Y` can be completed to such an antihole via `x_t-x_{t−1}-x_i-q`, so `q` is
> `Y`-complete; and if `z` is not `Y`-complete, an antipath between `z` and `x_t` with
> interior in `Y` can be extended to such an antihole, via `x_t-x_{t−1}-x_i-q-z`.  So `z`
> is also `Y`-complete.  Hence the hole `C` contains at least three `Y`-complete edges,
> namely `x_i z`, `z x_{t−1}` and `x_{t−1} q`, a contradiction."*

The "contradiction" is with the standing assumption of the proof of 20.3, namely that `z`
is not `Y`-complete or `G` has no wheel with hub `Y`.  So the *positive* content of the
paragraph — what is proved here — is exactly 20.3's conclusion.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm203Step3CaseB

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Step (3), case `x_{t−1}` has no neighbour in `A_{t−3} ∪ V(R \ q)`.** -/
theorem case_no_nbr {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hqA2 : q ∈ wheelSystemA G z A₀ x (t - 2))
    (hqt : G.Adj q (x t)) (hqt1 : G.Adj q (x (t - 1)))
    {SR : Set V} (hSRcon : ConnectedSet G SR)
    (hSRsub : SR ⊆ wheelSystemA G z A₀ x (t - 2))
    (hA3SR : wheelSystemA G z A₀ x (t - 3) ⊆ SR)
    (hqSR : ∃ s ∈ SR, G.Adj q s)
    (hx1SR : ∀ s ∈ SR, ¬ G.Adj (x (t - 1)) s)
    {Q : List V} (hQ : IsAntipathFrom G Q (x (t - 1)) q)
    (hQint : ∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2))
    (hQeven : Even (pathLength Q)) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  have hF6 : InF6 G := hG.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  -- ### elementary memberships
  have hxA2 : ∀ j ≤ t, x j ∉ wheelSystemA G z A₀ x (t - 2) := fun j hj =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj
  have hzA2 : z ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hxSR : ∀ j ≤ t, x j ∉ SR := fun j hj h => hxA2 j hj (hSRsub h)
  have hzSR : z ∉ SR := fun h => hzA2 (hSRsub h)
  have hzNadjSR : ∀ s ∈ SR, ¬ G.Adj z s := fun s hs =>
    WheelSystemBasics.wheelSystemA_no_nbr (hSRsub hs)
  have hqSRnot : q ∉ SR := fun h => hx1SR q h hqt1.symm
  have hqY : q ∉ Y := fun hy =>
    Thm203Prelim.Y_notMem_wheelSystemA hVC (by omega : t - 2 < t) hy hqA2
  have hqnez : q ≠ z := fun h => hzA2 (h ▸ hqA2)
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA2
  have hqnex : ∀ j ≤ t, q ≠ x j := fun j hj h => hxA2 j hj (h ▸ hqA2)
  -- ### `X_{t−2}`-membership consequences
  have hX2adjz : ∀ y ∈ wheelSystemX x (t - 2), G.Adj z y := by
    rintro y ⟨j, hj, rfl⟩
    exact hzadj j (by omega)
  have hX2nbrSR : ∀ y ∈ wheelSystemX x (t - 2), ∃ a ∈ SR, G.Adj y a := by
    rintro y ⟨j, hj, rfl⟩
    obtain ⟨a, ha, hadj⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
      (i := j) (k := t - 3) (by omega) (by omega) (by omega)
    exact ⟨a, hA3SR ha, hadj⟩
  have hX2notSR : ∀ y ∈ wheelSystemX x (t - 2), y ∉ SR := by
    rintro y ⟨j, hj, rfl⟩
    exact hxSR j (by omega)
  have hX2Y : ∀ y ∈ wheelSystemX x (t - 2), VertexComplete G y Y := by
    rintro y ⟨j, hj, rfl⟩
    exact hVC j (by omega)
  -- ### the vertices of `Q`
  have hQp : IsPathFrom Gᶜ Q (x (t - 1)) q := hQ
  have hQmem : ∀ y ∈ Q, y = x (t - 1) ∨ y = q ∨ y ∈ wheelSystemX x (t - 2) := by
    intro y hy
    by_cases h1 : y = x (t - 1)
    · exact Or.inl h1
    by_cases h2 : y = q
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQint y
      ((PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hy, h1, h2⟩)))
  have hzQ : z ∉ Q := by
    intro hmem
    rcases hQmem z hmem with h | h | h
    · exact G.irrefl (h ▸ hzadj (t - 1) (by omega))
    · exact hqnez h.symm
    · exact G.irrefl (hX2adjz z h)
  -- ### PAPER: "the antipath `z-q-Q-x_{t−1}` is odd"
  have hQr : IsPathFrom Gᶜ Q.reverse q (x (t - 1)) := PathBasics.isPathFrom_reverse hQp
  have hZQ : IsPathFrom Gᶜ (z :: Q.reverse) z (x (t - 1)) := by
    refine PathAttach.isPathFrom_cons hQr ?_ (by simpa using hzQ) ?_
    · rw [SimpleGraph.compl_adj]; exact ⟨fun h => hqnez h.symm, hzq⟩
    · intro y hy hyq
      have hy' : y ∈ Q := by simpa using hy
      rw [SimpleGraph.compl_adj]
      rintro ⟨-, hnadj⟩
      rcases hQmem y hy' with h | h | h
      · exact hnadj (h ▸ hzadj (t - 1) (by omega))
      · exact hyq h
      · exact hnadj (hX2adjz y h)
  have hZQlen : pathLength (z :: Q.reverse) = Q.length := by
    rw [PathBasics.pathLength_cons]; simp
  have hQnlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  have hZQodd : Odd (pathLength (z :: Q.reverse)) := by
    obtain ⟨k, hk⟩ := hQeven
    exact ⟨k, by omega⟩
  have hZQmem : ∀ y ∈ z :: Q.reverse, y = z ∨ y ∈ Q := by
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hZQnotSR : ∀ y ∈ z :: Q.reverse, y ∉ SR := by
    intro y hy
    rcases hZQmem y hy with h | h
    · exact h ▸ hzSR
    · rcases hQmem y h with h' | h' | h'
      · exact h' ▸ hxSR (t - 1) (by omega)
      · exact h' ▸ hqSRnot
      · exact hX2notSR y h'
  have hZQintSR : ∀ y ∈ SPGT.interior (z :: Q.reverse), ∃ a ∈ SR, G.Adj y a := by
    intro y hy
    obtain ⟨hymem, hyz, hy1⟩ := (PathBasics.mem_interior_iff_of_pathFrom hZQ).mp hy
    rcases hZQmem y hymem with h | h
    · exact absurd h hyz
    · rcases hQmem y h with h' | h' | h'
      · exact absurd h' hy1
      · exact h' ▸ hqSR
      · exact hX2nbrSR y h'
  -- ### PAPER: "so by 13.6 it has length 3, ... and there is an odd path `P` ..."
  obtain ⟨hlen3, c, d, hcd, P, hP, hPodd, hPint⟩ :=
    Thm203AntipathTools.antipath_middle_of_odd hF5 hSRcon hZQ hZQodd
      (hzadj (t - 1) (by omega)) hZQnotSR hzNadjSR hx1SR hZQintSR
  -- so `Q` has length `2`
  have hQlen3 : Q.length = 3 := by omega
  obtain ⟨a0, m, a2, hQeq0⟩ := PrismBasics.length_eq_three hQlen3
  have ha0 : a0 = x (t - 1) := by rw [hQeq0] at hQp; simpa using hQp.2.1
  have ha2 : a2 = q := by rw [hQeq0] at hQp; simpa using hQp.2.2
  rw [ha0, ha2] at hQeq0
  have hQeq : Q = [x (t - 1), m, q] := hQeq0
  have hQ' : IsPathFrom Gᶜ [x (t - 1), m, q] (x (t - 1)) q := by rw [← hQeq]; exact hQp
  have hmX2 : m ∈ wheelSystemX x (t - 2) := by
    refine hQint m ?_
    rw [hQeq]
    show m ∈ [x (t - 1), m, q].tail.dropLast
    simp
  -- the interior of the long antipath is `[q, m]`
  have hintZQ : SPGT.interior (z :: Q.reverse) = [q, m] := by
    rw [hQeq]
    rfl
  rw [hintZQ] at hcd
  have hqc : q = c := by injection hcd
  have hmd : m = d := by
    injection hcd with h1 h2
    injection h2
  rw [← hqc, ← hmd] at hP
  -- ### adjacency facts read off `Q = x_{t−1}-m-q`
  have hcompladj : ∀ {u v : V}, Gᶜ.Adj u v → u ≠ v ∧ ¬ G.Adj u v := by
    intro u v h; rwa [SimpleGraph.compl_adj] at h
  have hcompl1 : Gᶜ.Adj (x (t - 1)) m := by
    have h := PathBasics.path_adj_succ hQ'.1 (i := 0) (by simp)
    simpa using h
  have hcompl2 : Gᶜ.Adj m q := by
    have h := PathBasics.path_adj_succ hQ'.1 (i := 1) (by simp)
    simpa using h
  have hx1m : ¬ G.Adj (x (t - 1)) m := (hcompladj hcompl1).2
  have hmq : ¬ G.Adj m q := (hcompladj hcompl2).2
  have hmnex1 : m ≠ x (t - 1) := fun h => (hcompladj hcompl1).1 h.symm
  have hmneq : m ≠ q := (hcompladj hcompl2).1
  have hmnez : m ≠ z := by
    obtain ⟨j, hj, rfl⟩ := hmX2
    intro h
    exact G.irrefl (h ▸ hzadj j (by omega))
  have hmY : m ∉ Y := by
    obtain ⟨j, hj, rfl⟩ := hmX2
    exact hxY j (by omega)
  have hmYC : VertexComplete G m Y := hX2Y m hmX2
  have hxtm : G.Adj (x t) m := hXc m hmX2
  have hzm : G.Adj z m := hX2adjz m hmX2
  have hx1nez : x (t - 1) ≠ z := (hws.2.2.1 (t - 1) (by omega)).2
  -- ### PAPER: "Let `C` be the hole `z-x_{t−1}-q-P-x_i-z`; then `C` has length `≥ 6`."
  have hPlen1 : pathLength P ≠ 1 := fun h =>
    hmq (PathBasics.isPathFrom_ends_adj_of_length_one hP h).symm
  have hPlen3 : 3 ≤ pathLength P := by
    obtain ⟨k, hk⟩ := hPodd
    have hpos : 0 < P.length := PathBasics.path_length_pos hP.1
    have := PathBasics.pathLength_eq P
    omega
  have hPmem : ∀ y ∈ P, y = q ∨ y = m ∨ y ∈ SR := by
    intro y hy
    by_cases h1 : y = q
    · exact Or.inl h1
    by_cases h2 : y = m
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hPint y
      ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hy, h1, h2⟩)))
  have hzP : z ∉ P := by
    intro hmem
    rcases hPmem z hmem with h | h | h
    · exact hqnez h.symm
    · exact hmnez h.symm
    · exact hzSR h
  have hx1P : x (t - 1) ∉ P := by
    intro hmem
    rcases hPmem (x (t - 1)) hmem with h | h | h
    · exact hqnex (t - 1) (by omega) h.symm
    · exact hmnex1 h.symm
    · exact hxSR (t - 1) (by omega) h
  have hC : IsHoleList G (z :: x (t - 1) :: P) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hP (by omega) hqt1.symm hzm
      (hzadj (t - 1) (by omega)).symm hx1P hzP hx1m (fun h => hzq h) ?_ ?_
    · intro y hy
      exact hx1SR y (hPint y hy)
    · intro y hy
      exact hzNadjSR y (hPint y hy)
  have hClen : holeLength (z :: x (t - 1) :: P) = P.length + 2 := by
    simp [holeLength]
  have hPnlen : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  have hClen6 : 6 ≤ holeLength (z :: x (t - 1) :: P) := by omega
  have hCmem : ∀ y ∈ z :: x (t - 1) :: P, y = z ∨ y = x (t - 1) ∨ y ∈ P := by
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · exact Or.inl h
    rcases List.mem_cons.mp h with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  have hCY : ∀ y ∈ z :: x (t - 1) :: P, y ∉ Y := by
    intro y hy
    rcases hCmem y hy with h | h | h
    · exact h ▸ hzY
    · exact h ▸ hxY (t - 1) (by omega)
    · rcases hPmem y h with h' | h' | h'
      · exact h' ▸ hqY
      · exact h' ▸ hmY
      · intro hyY
        exact Thm203Prelim.Y_notMem_wheelSystemA hVC (by omega : t - 2 < t) hyY
          (hSRsub h')
  -- ### PAPER: "By 15.7 there is no antihole of length `≥ 6` containing `q, x_i, x_{t−1}`."
  have hqC : q ∈ z :: x (t - 1) :: P := by
    have := (PathBasics.isPathFrom_ends_mem hP).1
    simp [this]
  have hmC : m ∈ z :: x (t - 1) :: P := by
    have := (PathBasics.isPathFrom_ends_mem hP).2
    simp [this]
  have hx1C : x (t - 1) ∈ z :: x (t - 1) :: P := by simp
  have hno_antihole : ∀ D : List V, IsAntiholeList G D → 4 < holeLength D →
      q ∈ D → m ∈ D → x (t - 1) ∈ D → False := by
    intro D hD hDlen hqD hmD hx1D
    have h157 := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hF6
      (z :: x (t - 1) :: P) D hC (by omega) hD hDlen
    have hsub : ({q, m, x (t - 1)} : Set V) ⊆
        {w : V | w ∈ z :: x (t - 1) :: P} ∩ {w : V | w ∈ D} := by
      rintro y (rfl | rfl | rfl)
      · exact ⟨hqC, hqD⟩
      · exact ⟨hmC, hmD⟩
      · exact ⟨hx1C, hx1D⟩
    have hcard : ({q, m, x (t - 1)} : Set V).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨q, m, x (t - 1), hmneq.symm,
        fun h => hqnex (t - 1) (by omega) h, hmnex1, rfl⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  -- ### PAPER: "If `q` is not `Y`-complete then ... so `q` is `Y`-complete"
  have hqYC : VertexComplete G q Y := by
    by_contra hqnc
    obtain ⟨y1, hy1, hqy1⟩ : ∃ y ∈ Y, ¬ G.Adj q y := by
      by_contra hc; push_neg at hc; exact hqnc fun y hy => hc y hy
    obtain ⟨y2, hy2, hty2⟩ : ∃ y ∈ Y, ¬ G.Adj (x t) y := by
      by_contra hc; push_neg at hc; exact hnVC fun y hy => hc y hy
    obtain ⟨D, hD, hDint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hYanti hqY (hxY t le_rfl)
        ⟨y1, hy1, hqy1⟩ ⟨y2, hy2, hty2⟩
    have hDp : IsPathFrom Gᶜ D q (x t) := hD
    have hDmem : ∀ y ∈ D, y = q ∨ y = x t ∨ y ∈ Y := by
      intro y hy
      by_cases h1 : y = q
      · exact Or.inl h1
      by_cases h2 : y = x t
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (hDint y
        ((PathBasics.mem_interior_iff_of_pathFrom hDp).mpr ⟨hy, h1, h2⟩)))
    have hDlen0 : pathLength D ≠ 0 := by
      intro h0
      have hpos : 0 < D.length := PathBasics.path_length_pos hDp.1
      have hlen1 : D.length = 1 := by have := PathBasics.pathLength_eq D; omega
      obtain ⟨a, ha⟩ : ∃ a, D = [a] := by
        cases D with
        | nil => simp at hlen1
        | cons b tl => cases tl with
          | nil => exact ⟨b, rfl⟩
          | cons c tl' => simp at hlen1
      subst ha
      have e1 : a = q := by simpa using hDp.2.1
      have e2 : a = x t := by simpa using hDp.2.2
      exact hqnex t le_rfl (e1.symm.trans e2)
    have hDlen1 : pathLength D ≠ 1 := by
      intro h1
      have hadj := PathBasics.isPathFrom_ends_adj_of_length_one hDp h1
      rw [SimpleGraph.compl_adj] at hadj
      exact hadj.2 hqt
    have hmD : m ∉ D := by
      intro hmem
      rcases hDmem m hmem with h | h | h
      · exact hmneq h
      · exact G.irrefl (h ▸ hxtm)
      · exact hmY h
    have hx1D : x (t - 1) ∉ D := by
      intro hmem
      rcases hDmem (x (t - 1)) hmem with h | h | h
      · exact hqnex (t - 1) (by omega) h.symm
      · have := hinj (t - 1) (by omega) t le_rfl h; omega
      · exact hxY (t - 1) (by omega) h
    -- the antihole `x_{t−1}-x_i-q-D-x_t-x_{t−1}`
    have hAH : IsHoleList Gᶜ (x (t - 1) :: m :: D) := by
      refine PrismBasics.isHoleList_of_path_add_two_vertices hDp (by omega) hcompl2 ?_ ?_
        hmD hx1D ?_ ?_ ?_ ?_
      · rw [SimpleGraph.compl_adj]
        exact ⟨fun h => by have := hinj (t - 1) (by omega) t le_rfl h; omega,
          fun h => hnonadj h.symm⟩
      · exact hcompl1.symm
      · rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩; exact hn hxtm.symm
      · rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩; exact hn hqt1.symm
      · intro y hy
        rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
        exact hn (hmYC y (hDint y hy))
      · intro y hy
        rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
        exact hn ((hVC (t - 1) (by omega)) y (hDint y hy))
    have hAHlen : holeLength (x (t - 1) :: m :: D) = D.length + 2 := by simp [holeLength]
    have hDnlen : D.length = pathLength D + 1 :=
      PathBasics.length_eq_pathLength_add_one hDp.1
    have hAHeven : Even (holeLength (x (t - 1) :: m :: D)) := hBerge.2 _ hAH
    have hAHlen6 : 4 < holeLength (x (t - 1) :: m :: D) := by
      obtain ⟨k, hk⟩ := hAHeven
      omega
    exact hno_antihole (x (t - 1) :: m :: D) hAH hAHlen6
      (by simp [(PathBasics.isPathFrom_ends_mem hDp).1]) (by simp) (by simp)
  -- ### PAPER: "and if `z` is not `Y`-complete, ... So `z` is also `Y`-complete."
  have hzYC : VertexComplete G z Y := by
    by_contra hznc
    obtain ⟨y1, hy1, hzy1⟩ : ∃ y ∈ Y, ¬ G.Adj z y := by
      by_contra hc; push_neg at hc; exact hznc fun y hy => hc y hy
    obtain ⟨y2, hy2, hty2⟩ : ∃ y ∈ Y, ¬ G.Adj (x t) y := by
      by_contra hc; push_neg at hc; exact hnVC fun y hy => hc y hy
    obtain ⟨D, hD, hDint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hYanti hzY (hxY t le_rfl)
        ⟨y1, hy1, hzy1⟩ ⟨y2, hy2, hty2⟩
    have hDp : IsPathFrom Gᶜ D z (x t) := hD
    have hDmem : ∀ y ∈ D, y = z ∨ y = x t ∨ y ∈ Y := by
      intro y hy
      by_cases h1 : y = z
      · exact Or.inl h1
      by_cases h2 : y = x t
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr (hDint y
        ((PathBasics.mem_interior_iff_of_pathFrom hDp).mpr ⟨hy, h1, h2⟩)))
    have hDlen1 : pathLength D ≠ 1 := by
      intro h1
      have hadj := PathBasics.isPathFrom_ends_adj_of_length_one hDp h1
      rw [SimpleGraph.compl_adj] at hadj
      exact hadj.2 (hzadj t le_rfl)
    have hDlen0 : pathLength D ≠ 0 := by
      intro h0
      have hpos : 0 < D.length := PathBasics.path_length_pos hDp.1
      have hlen1 : D.length = 1 := by have := PathBasics.pathLength_eq D; omega
      obtain ⟨a, ha⟩ : ∃ a, D = [a] := by
        cases D with
        | nil => simp at hlen1
        | cons b tl => cases tl with
          | nil => exact ⟨b, rfl⟩
          | cons c tl' => simp at hlen1
      subst ha
      have e1 : a = z := by simpa using hDp.2.1
      have e2 : a = x t := by simpa using hDp.2.2
      exact hx1nez (by
        exact absurd (e1.symm.trans e2) (fun h => G.irrefl (h ▸ hzadj t le_rfl)))
    have hx1D : x (t - 1) ∉ D := by
      intro hmem
      rcases hDmem (x (t - 1)) hmem with h | h | h
      · exact (hws.2.2.1 (t - 1) (by omega)).2 h
      · have := hinj (t - 1) (by omega) t le_rfl h; omega
      · exact hxY (t - 1) (by omega) h
    have hmD : m ∉ D := by
      intro hmem
      rcases hDmem m hmem with h | h | h
      · exact hmnez h
      · exact G.irrefl (h ▸ hxtm)
      · exact hmY h
    have hqD : q ∉ D := by
      intro hmem
      rcases hDmem q hmem with h | h | h
      · exact hqnez h
      · exact hqnex t le_rfl h
      · exact hqY h
    -- the path `z-D-x_t-x_{t−1}-x_i` of `Ḡ`
    have hD1 : IsPathFrom Gᶜ (D ++ [x (t - 1)]) z (x (t - 1)) := by
      refine PathAttach.isPathFrom_concat hDp ?_ hx1D ?_
      · rw [SimpleGraph.compl_adj]
        exact ⟨fun h => by have := hinj (t - 1) (by omega) t le_rfl h; omega,
          fun h => hnonadj h.symm⟩
      · intro y hy hyt
        rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
        rcases hDmem y hy with h | h | h
        · exact hn (h ▸ (hzadj (t - 1) (by omega)).symm)
        · exact hyt h
        · exact hn ((hVC (t - 1) (by omega)) y h)
    have hD1mem : ∀ y ∈ D ++ [x (t - 1)], y ∈ D ∨ y = x (t - 1) := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl h
      · exact Or.inr (by simpa using h)
    have hmD1 : m ∉ D ++ [x (t - 1)] := by
      intro hmem
      rcases hD1mem m hmem with h | h
      · exact hmD h
      · exact hmnex1 h
    have hD2 : IsPathFrom Gᶜ ((D ++ [x (t - 1)]) ++ [m]) z m := by
      refine PathAttach.isPathFrom_concat hD1 hcompl1.symm hmD1 ?_
      · intro y hy hy1
        rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
        rcases hD1mem y hy with h | h
        · rcases hDmem y h with h' | h' | h'
          · exact hn (h' ▸ hzm.symm)
          · exact hn (h' ▸ hxtm.symm)
          · exact hn (hmYC y h')
        · exact hy1 h
    have hD2mem : ∀ y ∈ (D ++ [x (t - 1)]) ++ [m], y ∈ D ∨ y = x (t - 1) ∨ y = m := by
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · rcases hD1mem y h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (by simpa using h))
    have hqD2 : q ∉ (D ++ [x (t - 1)]) ++ [m] := by
      intro hmem
      rcases hD2mem q hmem with h | h | h
      · exact hqD h
      · exact hqnex (t - 1) (by omega) h
      · exact hmneq h.symm
    have hD2len : ((D ++ [x (t - 1)]) ++ [m]).length = D.length + 2 := by simp
    have hDnlen : D.length = pathLength D + 1 :=
      PathBasics.length_eq_pathLength_add_one hDp.1
    have hD2plen : pathLength ((D ++ [x (t - 1)]) ++ [m]) = pathLength D + 2 := by
      have h1 := PathBasics.pathLength_eq ((D ++ [x (t - 1)]) ++ [m])
      have h2 := PathBasics.pathLength_eq D
      have hpos : 0 < D.length := PathBasics.path_length_pos hDp.1
      omega
    have hAH : IsHoleList Gᶜ (q :: ((D ++ [x (t - 1)]) ++ [m])) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hD2 (by omega) ?_ hcompl2.symm hqD2 ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨hqnez, fun h => hzq h.symm⟩
      · intro y hy
        obtain ⟨hymem, hyz, hym⟩ :=
          (PathBasics.mem_interior_iff_of_pathFrom hD2).mp hy
        rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
        rcases hD2mem y hymem with h | h | h
        · rcases hDmem y h with h' | h' | h'
          · exact hyz h'
          · exact hn (h' ▸ hqt)
          · exact hn (hqYC y h')
        · exact hn (h ▸ hqt1)
        · exact hym h
    have hAHlen : holeLength (q :: ((D ++ [x (t - 1)]) ++ [m])) = D.length + 3 := by
      simp [holeLength]
    have hAHlen6 : 4 < holeLength (q :: ((D ++ [x (t - 1)]) ++ [m])) := by omega
    exact hno_antihole _ hAH hAHlen6 (by simp) (by simp) (by simp)
  -- ### PAPER: "Hence the hole `C` contains at least three `Y`-complete edges"
  have hx1YC : VertexComplete G (x (t - 1)) Y := hVC (t - 1) (by omega)
  have h3 : 3 ≤ OptimalWheelChoice.yEdgeCount G Y (z :: x (t - 1) :: P) := by
    rw [OptimalWheelChoice.yEdgeCount_def]
    have hsub : ({s(m, z), s(z, x (t - 1)), s(x (t - 1), q)} : Set (Sym2 V)) ⊆
        {e : Sym2 V | ∃ u ∈ z :: x (t - 1) :: P, ∃ v ∈ z :: x (t - 1) :: P,
          e = s(u, v) ∧ EdgeComplete G Y u v} := by
      rintro e (rfl | rfl | rfl)
      · exact ⟨m, hmC, z, by simp, rfl, hzm.symm, hmYC, hzYC⟩
      · exact ⟨z, by simp, x (t - 1), hx1C, rfl, hzadj (t - 1) (by omega), hzYC, hx1YC⟩
      · exact ⟨x (t - 1), hx1C, q, hqC, rfl, hqt1.symm, hx1YC, hqYC⟩
    have hcard : ({s(m, z), s(z, x (t - 1)), s(x (t - 1), q)} : Set (Sym2 V)).ncard = 3 := by
      refine Set.ncard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h => absurd h hmnez, fun h => absurd h hmnex1⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun h => absurd h hmnex1, fun h => absurd h hmneq⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun _ => Ne.symm (hqnex (t - 1) (by omega)), fun h => absurd h.symm hqnez⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  exact ⟨hzYC, z :: x (t - 1) :: P,
    WheelConverse.isWheel_of_three_yEdges hC hClen6 hYne hYanti hCY h3⟩

end Workspace.ProofLemmas.Thm203Step3CaseB
