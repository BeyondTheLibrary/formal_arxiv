import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm203Prelim

/-!
# 20.3, the final paragraph

PAPER (printed p. 127):

> *"From (3) and the choice of `R` it follows that `x_t` has no neighbours in
> `A_{t−3} ∪ V(R \ q)`.  Let `Q` be an antipath between `q` and `x_{t−1}` with interior
> in `X_{t−2}`.  Then `z-q-Q-x_{t−1}-x_t` is an antipath of length `≥ 4`, and its ends
> have no neighbours in the connected set `A_{t−3} ∪ V(R \ q)`, and its internal vertices
> do, so by 13.6 it has even length, that is, `Q` is even.  The antipath
> `x_t-x_{t−1}-Q-q` is therefore odd, and its internal vertices have neighbours in
> `A_{t−3}`, and `z` is complete to its interior and anticomplete to `A_{t−3}`, so by 2.2
> applied in `Ḡ`, it follows that one of its ends, and hence `q` has a neighbour in
> `A_{t−3}`.  From the maximality of `A_{t−3}` it follows that `q` is `X_{t−3}`-complete
> and therefore nonadjacent to `x_{t−2}`."*

`q_has_nbr_in_A3` is that paragraph up to and including *"hence `q` has a neighbour in
`A_{t−3}`"*.  The set `A_{t−3} ∪ V(R \ q)` enters only through the five properties the
paragraph uses of it, which are the hypotheses `hScon`, `hSsub`, `hA3S`, `hqS`, `hxtS`:
it is connected, it lies inside `A_{t−2}`, it includes `A_{t−3}`, `q` has a neighbour in
it, and `x_t` has none.

`q_is_X3_complete` is the last sentence, and `endgame_data` packages the paragraph's
output in exactly the shape `Thm203Step1.exists_diamond_endgame` consumes.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm203Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `Ḡ`-anticonnectedness is `G`-connectedness. -/
theorem anticonnected_compl {G : SimpleGraph V} {S : Set V} (h : ConnectedSet G S) :
    AnticonnectedSet Gᶜ S := by
  show ConnectedSet Gᶜᶜ S
  rwa [compl_compl]

/-- Being `Ḡ`-complete to `S` means being distinct from and nonadjacent to every vertex
of `S`. -/
theorem vertexComplete_compl_iff {G : SimpleGraph V} {v : V} {S : Set V} :
    VertexComplete Gᶜ v S ↔ ∀ s ∈ S, v ≠ s ∧ ¬ G.Adj v s := by
  constructor
  · intro h s hs
    have h2 := h s hs
    rw [SimpleGraph.compl_adj] at h2
    exact h2
  · intro h s hs
    rw [SimpleGraph.compl_adj]
    exact h s hs

/-- **The final paragraph of 20.3**, up to *"hence `q` has a neighbour in `A_{t−3}`"*. -/
theorem q_has_nbr_in_A3 {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hqA : q ∈ wheelSystemA G z A₀ x (t - 2))
    (hqt : G.Adj q (x t)) (hqt1 : G.Adj q (x (t - 1)))
    {S : Set V} (hScon : ConnectedSet G S)
    (hSsub : S ⊆ wheelSystemA G z A₀ x (t - 2))
    (hA3S : wheelSystemA G z A₀ x (t - 3) ⊆ S)
    (hqS : ∃ s ∈ S, G.Adj q s)
    (hxtS : ∀ s ∈ S, ¬ G.Adj (x t) s)
    (hnbr1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a) :
    ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  obtain ⟨hws, -, -, -, -, -, ht3, hXc, -⟩ := id hd
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  -- ### elementary memberships
  have hzA2 : z ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hxA2 : ∀ j ≤ t, x j ∉ wheelSystemA G z A₀ x (t - 2) := fun j hj =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj
  have hxA3 : ∀ j ≤ t, x j ∉ wheelSystemA G z A₀ x (t - 3) := fun j hj =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj
  have hzS : z ∉ S := fun h => hzA2 (hSsub h)
  have hxS : ∀ j ≤ t, x j ∉ S := fun j hj h => hxA2 j hj (hSsub h)
  have hzNadjS : ∀ s ∈ S, ¬ G.Adj z s := fun s hs =>
    WheelSystemBasics.wheelSystemA_no_nbr (hSsub hs)
  have hqnotS : q ∉ S := fun h => hxtS q h hqt.symm
  have hqA3 : q ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hqnotS (hA3S h)
  have hzA3 : z ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hzS (hA3S h)
  have hzNadjA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj z a := fun a ha =>
    hzNadjS a (hA3S ha)
  have hxtA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a := fun a ha =>
    hxtS a (hA3S ha)
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA
  have hqnez : q ≠ z := fun h => hzA2 (h ▸ hqA)
  -- ### `q` and `x_{t−1}` lie outside `X_{t−2}` and each has a `Ḡ`-neighbour in it
  have hqX2 : q ∉ wheelSystemX x (t - 2) := by
    rintro ⟨j, hj, rfl⟩
    exact hxA2 j (by omega) hqA
  have hx1X2 : x (t - 1) ∉ wheelSystemX x (t - 2) := by
    rintro ⟨j, hj, hje⟩
    have := hinj (t - 1) (by omega) j (by omega) hje
    omega
  have hqnc : ¬ VertexComplete G q (wheelSystemX x (t - 2)) :=
    WheelSystemBasics.wheelSystemA_no_complete hqA
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hws.2.2.2.2.2.1 (t - 1) (by omega) (by omega)
    have he : t - 1 - 1 = t - 2 := by omega
    rwa [he] at h
  have hqnn : ∃ w ∈ wheelSystemX x (t - 2), ¬ G.Adj q w := by
    by_contra hcon
    push_neg at hcon
    exact hqnc fun w hw => hcon w hw
  have hx1nn : ∃ w ∈ wheelSystemX x (t - 2), ¬ G.Adj (x (t - 1)) w := by
    by_contra hcon
    push_neg at hcon
    exact hx1nc fun w hw => hcon w hw
  have hX2anti : AnticonnectedSet G (wheelSystemX x (t - 2)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)
  -- ### PAPER: "Let `Q` be an antipath between `q` and `x_{t−1}` with interior in `X_{t−2}`."
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hX2anti hqX2 hx1X2 hqnn hx1nn
  have hQp : IsPathFrom Gᶜ Q q (x (t - 1)) := hQ
  have hQmem : ∀ w ∈ Q, w = q ∨ w = x (t - 1) ∨ w ∈ wheelSystemX x (t - 2) := by
    intro w hw
    by_cases h1 : w = q
    · exact Or.inl h1
    by_cases h2 : w = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQint w
      ((PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hw, h1, h2⟩)))
  -- every vertex of `Q` other than `q` is adjacent to `z`
  have hzadjQ : ∀ w ∈ Q, w ≠ q → G.Adj z w := by
    intro w hw hwq
    rcases hQmem w hw with h | h | h
    · exact absurd h hwq
    · exact h ▸ hzadj (t - 1) (by omega)
    · obtain ⟨j, hj, hje⟩ := h
      exact hje ▸ hzadj j (by omega)
  -- every vertex of `Q` other than `x_{t−1}` is adjacent to `x_t`
  have hxtadjQ : ∀ w ∈ Q, w ≠ x (t - 1) → G.Adj (x t) w := by
    intro w hw hw1
    rcases hQmem w hw with h | h | h
    · exact h ▸ hqt.symm
    · exact absurd h hw1
    · exact hXc w h
  have hQnotS : ∀ w ∈ Q, w ∉ S := by
    intro w hw
    rcases hQmem w hw with h | h | h
    · exact h ▸ hqnotS
    · exact h ▸ hxS (t - 1) (by omega)
    · obtain ⟨j, hj, hje⟩ := h
      exact hje ▸ hxS j (by omega)
  have hQnotA3 : ∀ w ∈ Q, w ∉ wheelSystemA G z A₀ x (t - 3) := fun w hw hmem =>
    hQnotS w hw (hA3S hmem)
  have hzQ : z ∉ Q := by
    intro hmem
    rcases hQmem z hmem with h | h | h
    · exact hqnez h.symm
    · exact G.irrefl (h ▸ hzadj (t - 1) (by omega))
    · obtain ⟨j, hj, hje⟩ := h
      exact G.irrefl (hje ▸ hzadj j (by omega))
  have hxtQ : x t ∉ Q := by
    intro hmem
    rcases hQmem (x t) hmem with h | h | h
    · exact hxA2 t le_rfl (h ▸ hqA)
    · have := hinj t le_rfl (t - 1) (by omega) h
      omega
    · obtain ⟨j, hj, hje⟩ := h
      have := hinj t le_rfl j (by omega) hje
      omega
  -- ### the length of `Q`
  have hqnex1 : q ≠ x (t - 1) := fun h => hxA2 (t - 1) (by omega) (h ▸ hqA)
  have hQlen0 : pathLength Q ≠ 0 := by
    intro h0
    have hpos : 0 < Q.length := PathBasics.path_length_pos hQp.1
    have hlen1 : Q.length = 1 := by
      have := PathBasics.pathLength_eq Q; omega
    obtain ⟨a, ha⟩ : ∃ a, Q = [a] := by
      cases Q with
      | nil => simp at hlen1
      | cons b tl =>
        cases tl with
        | nil => exact ⟨b, rfl⟩
        | cons c tl' => simp at hlen1
    subst ha
    have h0' : a = q := by simpa using hQp.2.1
    have h1' : a = x (t - 1) := by simpa using hQp.2.2
    exact hqnex1 (h0'.symm.trans h1')
  have hQlen1 : pathLength Q ≠ 1 := by
    intro h1
    have hadj := PathBasics.isPathFrom_ends_adj_of_length_one hQp h1
    rw [SimpleGraph.compl_adj] at hadj
    exact hadj.2 hqt1
  have hQlen2 : 2 ≤ pathLength Q := by omega
  have hQnlen : Q.length = pathLength Q + 1 :=
    PathBasics.length_eq_pathLength_add_one hQp.1
  -- ### every vertex of `Q` has a neighbour in `A_{t−3}` (except possibly `q`), hence in `S`
  have hnbrA3 : ∀ w ∈ Q, w ≠ q →
      ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj w a := by
    intro w hw hwq
    rcases hQmem w hw with h | h | h
    · exact absurd h hwq
    · subst h; exact hnbr1
    · obtain ⟨j, hj, hje⟩ := h
      subst hje
      exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (i := j) (k := t - 3)
        (by omega) (by omega) (by omega)
  have hnbrS : ∀ w ∈ Q, ∃ s ∈ S, G.Adj w s := by
    intro w hw
    by_cases hwq : w = q
    · subst hwq; exact hqS
    · obtain ⟨a, ha, hadj⟩ := hnbrA3 w hw hwq
      exact ⟨a, hA3S ha, hadj⟩
  -- ### PAPER: "Then `z-q-Q-x_{t−1}-x_t` is an antipath of length `≥ 4`"
  have hP : IsPathFrom Gᶜ (z :: (Q ++ [x t])) z (x t) := by
    refine PathAttach.isPathFrom_cons_concat hQp ?_ ?_ ?_ ?_ hzQ hxtQ ?_ ?_
    · rw [SimpleGraph.compl_adj]; exact ⟨fun h => hqnez h.symm, hzq⟩
    · rw [SimpleGraph.compl_adj]
      exact ⟨fun h => by have := hinj t le_rfl (t - 1) (by omega) h; omega, hnonadj⟩
    · rw [SimpleGraph.compl_adj]
      rintro ⟨-, hnadj⟩
      exact hnadj (hzadj t le_rfl)
    · intro h
      exact G.irrefl (h ▸ hzadj t le_rfl)
    · intro w hw hwq
      rw [SimpleGraph.compl_adj]
      rintro ⟨-, hnadj⟩
      exact hnadj (hzadjQ w hw hwq)
    · intro w hw hw1
      rw [SimpleGraph.compl_adj]
      rintro ⟨-, hnadj⟩
      exact hnadj (hxtadjQ w hw hw1)
  have hPlen : pathLength (z :: (Q ++ [x t])) = Q.length + 1 :=
    PathAttach.pathLength_cons_append_singleton z (x t) Q
  have hPlen4 : 4 ≤ pathLength (z :: (Q ++ [x t])) := by omega
  -- ### PAPER: "so by 13.6 it has even length, that is, `Q` is even"
  have hPeven : Even (pathLength (z :: (Q ++ [x t]))) := by
    rcases Nat.even_or_odd (pathLength (z :: (Q ++ [x t]))) with hev | hodd
    · exact hev
    exfalso
    have hXP : S ⊆ {v : V | v ∈ z :: (Q ++ [x t])}ᶜ := by
      intro s hs hmem
      simp only [Set.mem_setOf_eq, PathAttach.mem_cons_append_singleton] at hmem
      rcases hmem with h | h | h
      · exact hzS (h ▸ hs)
      · exact hQnotS s h hs
      · exact hxS t le_rfl (h ▸ hs)
    have hzC : VertexComplete Gᶜ z S :=
      vertexComplete_compl_iff.mpr fun s hs => ⟨fun h => hzS (h ▸ hs), hzNadjS s hs⟩
    have hxtC : VertexComplete Gᶜ (x t) S :=
      vertexComplete_compl_iff.mpr fun s hs =>
        ⟨fun h => hxS t le_rfl (h ▸ hs), hxtS s hs⟩
    -- only the two ends are `Ḡ`-complete to `S`
    have hends : ∀ w ∈ z :: (Q ++ [x t]), VertexComplete Gᶜ w S → w = z ∨ w = x t := by
      intro w hw hwC
      rcases PathAttach.mem_cons_append_singleton.mp hw with h | h | h
      · exact Or.inl h
      · exfalso
        obtain ⟨s, hs, hadj⟩ := hnbrS w h
        exact (vertexComplete_compl_iff.mp hwC s hs).2 hadj
      · exact Or.inr h
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 Gᶜ
        (ClassLemmas.inF5_compl.mpr hF5) (z :: (Q ++ [x t])) z (x t) hP hodd S hXP
        (anticonnected_compl hScon) hzC hxtC with h1 | h2
    · obtain ⟨u, hu, v, hv, hadj, huC, hvC⟩ := h1
      rcases hends u hu huC with rfl | rfl <;> rcases hends v hv hvC with hv' | hv'
      · exact Gᶜ.irrefl (hv' ▸ hadj)
      · rw [hv', SimpleGraph.compl_adj] at hadj
        exact hadj.2 (hzadj t le_rfl)
      · rw [hv', SimpleGraph.compl_adj] at hadj
        exact hadj.2 (hzadj t le_rfl).symm
      · exact Gᶜ.irrefl (hv' ▸ hadj)
    · omega
  have hQeven : Even (pathLength Q) := by
    obtain ⟨k, hk⟩ := hPeven
    exact ⟨k - 1, by omega⟩
  -- ### PAPER: "The antipath `x_t-x_{t−1}-Q-q` is therefore odd"
  by_contra hqno
  push_neg at hqno
  have hQr : IsPathFrom Gᶜ Q.reverse (x (t - 1)) q := PathBasics.isPathFrom_reverse hQp
  have hP2 : IsPathFrom Gᶜ (x t :: Q.reverse) (x t) q := by
    refine PathAttach.isPathFrom_cons hQr ?_ (by simpa using hxtQ) ?_
    · rw [SimpleGraph.compl_adj]
      exact ⟨fun h => by have := hinj t le_rfl (t - 1) (by omega) h; omega, hnonadj⟩
    · intro w hw hw1
      rw [SimpleGraph.compl_adj]
      rintro ⟨-, hnadj⟩
      exact hnadj (hxtadjQ w (by simpa using hw) hw1)
  have hP2mem : ∀ w ∈ x t :: Q.reverse, w = x t ∨ w ∈ Q := by
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hP2len : pathLength (x t :: Q.reverse) = Q.length := by
    rw [PathBasics.pathLength_cons]
    simp
  have hP2odd : Odd (pathLength (x t :: Q.reverse)) := by
    obtain ⟨k, hk⟩ := hQeven
    exact ⟨k, by omega⟩
  have hxtC3 : VertexComplete Gᶜ (x t) (wheelSystemA G z A₀ x (t - 3)) :=
    vertexComplete_compl_iff.mpr fun a ha =>
      ⟨fun h => hxA3 t le_rfl (h ▸ ha), hxtA3 a ha⟩
  have hqC3 : VertexComplete Gᶜ q (wheelSystemA G z A₀ x (t - 3)) :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hqA3 (h ▸ ha), hqno a ha⟩
  have hzC3 : VertexComplete Gᶜ z (wheelSystemA G z A₀ x (t - 3)) :=
    vertexComplete_compl_iff.mpr fun a ha => ⟨fun h => hzA3 (h ▸ ha), hzNadjA3 a ha⟩
  have hends2 : ∀ w ∈ x t :: Q.reverse,
      VertexComplete Gᶜ w (wheelSystemA G z A₀ x (t - 3)) → w = x t ∨ w = q := by
    intro w hw hwC
    rcases hP2mem w hw with h | h
    · exact Or.inl h
    by_cases hwq : w = q
    · exact Or.inr hwq
    · exfalso
      obtain ⟨a, ha, hadj⟩ := hnbrA3 w h hwq
      exact (vertexComplete_compl_iff.mp hwC a ha).2 hadj
  have hnoedge : ¬ ∃ u ∈ x t :: Q.reverse, ∃ v ∈ x t :: Q.reverse,
      EdgeComplete Gᶜ (wheelSystemA G z A₀ x (t - 3)) u v := by
    rintro ⟨u, hu, v, hv, hadj, huC, hvC⟩
    rcases hends2 u hu huC with rfl | rfl <;> rcases hends2 v hv hvC with hv' | hv'
    · exact Gᶜ.irrefl (hv' ▸ hadj)
    · rw [hv', SimpleGraph.compl_adj] at hadj
      exact hadj.2 hqt.symm
    · rw [hv', SimpleGraph.compl_adj] at hadj
      exact hadj.2 hqt
    · exact Gᶜ.irrefl (hv' ▸ hadj)
  have hpX : ∀ w ∈ x t :: Q.reverse, w ∉ wheelSystemA G z A₀ x (t - 3) := by
    intro w hw
    rcases hP2mem w hw with h | h
    · exact h ▸ hxA3 t le_rfl
    · exact hQnotA3 w h
  -- ### PAPER: "so by 2.2 applied in `Ḡ`, ... one of its ends ... has a neighbour in `A_{t−3}`"
  obtain ⟨w, hwint, hzw⟩ :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_2 Gᶜ (HoleBasics.berge_compl.mpr hBerge)
      (wheelSystemA G z A₀ x (t - 3))
      (anticonnected_compl (WheelSystemBasics.connectedSet_wheelSystemA hframe.1))
      (x t :: Q.reverse) (x t) q hP2 hpX hP2odd hxtC3 hqC3 hnoedge z hzC3
  rw [PathBasics.mem_interior_iff_of_pathFrom hP2] at hwint
  obtain ⟨hwmem, hwxt, hwq⟩ := hwint
  rcases hP2mem w hwmem with h | h
  · exact hwxt h
  · rw [SimpleGraph.compl_adj] at hzw
    exact hzw.2 (hzadjQ w h hwq)

/-- **The last sentence of the paragraph**: *"From the maximality of `A_{t−3}` it follows
that `q` is `X_{t−3}`-complete and therefore nonadjacent to `x_{t−2}`."* -/
theorem q_is_X3_complete {G : SimpleGraph V} {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hqA : q ∈ wheelSystemA G z A₀ x (t - 2))
    (hqA3 : q ∉ wheelSystemA G z A₀ x (t - 3))
    (hnbr : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b) :
    VertexComplete G q (wheelSystemX x (t - 3)) ∧ ¬ G.Adj q (x (t - 2)) := by
  obtain ⟨hws, -, -, -, -, -, ht3, -, -⟩ := id hd
  have hzq : ¬ G.Adj z q := WheelSystemBasics.wheelSystemA_no_nbr hqA
  have hcomp : VertexComplete G q (wheelSystemX x (t - 3)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega) hzq hqA3 hnbr
  refine ⟨hcomp, ?_⟩
  intro hadj
  refine WheelSystemBasics.wheelSystemA_no_complete hqA ?_
  rintro w ⟨j, hj, rfl⟩
  rcases Nat.lt_or_ge j (t - 2) with hlt | hge
  · exact hcomp (x j) (WheelSystemBasics.mem_wheelSystemX.2 ⟨j, by omega, rfl⟩)
  · have hje : j = t - 2 := by omega
    subst hje
    exact hadj

end Workspace.ProofLemmas.Thm203Endgame
