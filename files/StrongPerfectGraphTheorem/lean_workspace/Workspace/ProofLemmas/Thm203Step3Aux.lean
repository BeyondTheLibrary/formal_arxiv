import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm203Prelim
import Workspace.ProofLemmas.Thm203AntipathTools
import Workspace.ProofLemmas.Thm203Endgame

/-!
# 20.3, step (3): the `Y`-square alternative, which the paper runs twice

PAPER (printed p. 126), first with `w = q` and then verbatim again with `w = r₂`:

> *"Suppose first that every antipath between `x_{t−1}` and `q` with interior in `X_{t−2}`
> is odd, and let `Q` be such an antipath.  Since all internal vertices of `Q` have
> neighbours in `A_{t−3}`, and `z` is complete to its interior and anticomplete to
> `A_{t−3}`, it follows from 2.2 applied in `Ḡ` that one end of `Q` has a neighbour in
> `A_{t−3}`.  By hypothesis, `x_{t−1}` does not, so `q` does.  From the maximality of
> `A_{t−3}` it follows that `q` is `X_{t−3}`-complete; and since `q ∈ A_{t−2}` and is
> therefore not `X_{t−2}`-complete, `q` is nonadjacent to `x_{t−2}`.  Now by assumption,
> every antipath between `x_{t−1}` and `q` with interior in `X_{t−2}` is odd, and so
> `x_{t−2}` is adjacent to `x_{t−1}`.  But then `x₀,…,x_{t−1}` is a `Y ∪ {x_t}`-square of
> height `t − 1`, a contradiction."*

`square_from_all_odd` is that paragraph in positive form: the conclusion is the
`Y ∪ {x_t}`-square that the paper feeds to the hypothesis `hnone` of 20.3.

`exists_even_antipath` is the resulting *"So we may assume some antipath `Q` between
`x_{t−1}` and `w` with interior in `X_{t−2}` is even"*.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm203Step3Aux

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Given a vertex `w ∈ A_{t−2}` adjacent to `x_{t−1}`, there **is** an antipath between
`x_{t−1}` and `w` with interior in `X_{t−2}`. -/
theorem exists_antipath_to_A2 {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (hws : IsWheelSystem G z A₀ x t) (ht : 4 ≤ t)
    {w : V} (hwA2 : w ∈ wheelSystemA G z A₀ x (t - 2)) :
    ∃ Q : List V, IsAntipathFrom G Q (x (t - 1)) w ∧
      ∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2) := by
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hwX2 : w ∉ wheelSystemX x (t - 2) := by
    rintro ⟨j, hj, rfl⟩
    exact Thm203Prelim.x_notMem_wheelSystemA hws (by omega : j ≤ t) hwA2
  have hx1X2 : x (t - 1) ∉ wheelSystemX x (t - 2) := by
    rintro ⟨j, hj, hje⟩
    have := hinj (t - 1) (by omega) j (by omega) hje
    omega
  have hwnc : ¬ VertexComplete G w (wheelSystemX x (t - 2)) :=
    WheelSystemBasics.wheelSystemA_no_complete hwA2
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hws.2.2.2.2.2.1 (t - 1) (by omega) (by omega)
    have he : t - 1 - 1 = t - 2 := by omega
    rwa [he] at h
  have hwnn : ∃ y ∈ wheelSystemX x (t - 2), ¬ G.Adj w y := by
    by_contra hcon
    push_neg at hcon
    exact hwnc fun y hy => hcon y hy
  have hx1nn : ∃ y ∈ wheelSystemX x (t - 2), ¬ G.Adj (x (t - 1)) y := by
    by_contra hcon
    push_neg at hcon
    exact hx1nc fun y hy => hcon y hy
  exact InducedPathExtraction.exists_antipath_interior_in
    (Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)) hx1X2 hwX2 hx1nn hwnn

/-- **The `Y`-square paragraph of step (3)**, in positive form. -/
theorem square_from_all_odd {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hno1 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a)
    {w : V} (hwA2 : w ∈ wheelSystemA G z A₀ x (t - 2))
    (hw1 : G.Adj (x (t - 1)) w)
    (hodd : ∀ Q : List V, IsAntipathFrom G Q (x (t - 1)) w →
      (∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2)) → Odd (pathLength Q)) :
    ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y' := by
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  -- `w ∉ A_{t−3}`, since `x_{t−1}` has no neighbour there
  have hwA3 : w ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hno1 w h hw1
  have hzw : ¬ G.Adj z w := WheelSystemBasics.wheelSystemA_no_nbr hwA2
  -- PAPER: "let `Q` be such an antipath"
  obtain ⟨Q, hQ, hQint⟩ := exists_antipath_to_A2 hws ht hwA2
  have hQp : IsPathFrom Gᶜ Q (x (t - 1)) w := hQ
  have hQmem : ∀ y ∈ Q, y = x (t - 1) ∨ y = w ∨ y ∈ wheelSystemX x (t - 2) := by
    intro y hy
    by_cases h1 : y = x (t - 1)
    · exact Or.inl h1
    by_cases h2 : y = w
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQint y
      ((PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hy, h1, h2⟩)))
  have hQnotA3 : ∀ y ∈ Q, y ∉ wheelSystemA G z A₀ x (t - 3) := by
    intro y hy
    rcases hQmem y hy with h | h | h
    · exact h ▸ Thm203Prelim.x_notMem_wheelSystemA hws (by omega : t - 1 ≤ t)
    · exact h ▸ hwA3
    · obtain ⟨j, hj, hje⟩ := h
      exact hje ▸ Thm203Prelim.x_notMem_wheelSystemA hws (by omega : j ≤ t)
  have hintT : ∀ y ∈ SPGT.interior Q, ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj y a := by
    intro y hy
    obtain ⟨j, hj, hje⟩ := hQint y hy
    subst hje
    exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (i := j) (k := t - 3)
      (by omega) (by omega) (by omega)
  have hintz : ∀ y ∈ SPGT.interior Q, G.Adj z y := by
    intro y hy
    obtain ⟨j, hj, hje⟩ := hQint y hy
    exact hje ▸ hzadj j (by omega)
  -- PAPER: "by 2.2 applied in `Ḡ` ... one end of `Q` has a neighbour in `A_{t−3}`"
  have hend := Thm203AntipathTools.exists_end_nbr_of_odd_antipath hBerge
    (WheelSystemBasics.connectedSet_wheelSystemA hframe.1)
    (Thm203Prelim.z_notMem_wheelSystemA hws (by omega))
    (fun a ha => WheelSystemBasics.wheelSystemA_no_nbr ha)
    hQ (hodd Q hQ hQint) hw1 hQnotA3 hintT hintz
  have hwnbr : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj w a := by
    rcases hend with ⟨a, ha, hadj⟩ | h
    · exact absurd hadj (hno1 a ha)
    · exact h
  -- PAPER: "`w` is `X_{t−3}`-complete ... and therefore nonadjacent to `x_{t−2}`"
  obtain ⟨-, hwx2⟩ := Thm203Endgame.q_is_X3_complete hframe hd ht hwA2 hwA3 hwnbr
  -- PAPER: "and so `x_{t−2}` is adjacent to `x_{t−1}`"
  have hadj12 : G.Adj (x (t - 1)) (x (t - 2)) := by
    by_contra hnadj
    -- otherwise `x_{t−1}-x_{t−2}-w` is an even antipath with interior in `X_{t−2}`
    have hne12 : x (t - 1) ≠ x (t - 2) := by
      intro h
      have := hinj (t - 1) (by omega) (t - 2) (by omega) h
      omega
    have hne2w : x (t - 2) ≠ w := fun h =>
      Thm203Prelim.x_notMem_wheelSystemA hws (by omega : t - 2 ≤ t) (h ▸ hwA2)
    have hne1w : x (t - 1) ≠ w := fun h =>
      Thm203Prelim.x_notMem_wheelSystemA hws (by omega : t - 1 ≤ t) (h ▸ hwA2)
    have hpair : IsPathFrom Gᶜ [x (t - 2), w] (x (t - 2)) w := by
      refine ⟨PathBasics.isPathList_pair ?_, rfl, rfl⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨hne2w, fun h => hwx2 h.symm⟩
    have hcons : IsPathFrom Gᶜ (x (t - 1) :: [x (t - 2), w]) (x (t - 1)) w := by
      refine PathAttach.isPathFrom_cons hpair ?_ ?_ ?_
      · rw [SimpleGraph.compl_adj]; exact ⟨hne12, hnadj⟩
      · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil]
        push_neg
        exact ⟨hne12, hne1w, by simp⟩
      · intro y hy hy2
        rcases List.mem_cons.mp hy with h | h
        · exact absurd h hy2
        · rw [List.mem_singleton] at h
          subst h
          rw [SimpleGraph.compl_adj]
          rintro ⟨-, hnadj'⟩
          exact hnadj' hw1
    have hoddQ := hodd (x (t - 1) :: [x (t - 2), w]) hcons (by
      intro y hy
      have : SPGT.interior (x (t - 1) :: [x (t - 2), w]) = [x (t - 2)] := rfl
      rw [this] at hy
      rw [List.mem_singleton] at hy
      exact hy ▸ WheelSystemBasics.self_mem_wheelSystemX x (le_refl (t - 2)))
    have : pathLength (x (t - 1) :: [x (t - 2), w]) = 2 := rfl
    rw [this] at hoddQ
    exact (Nat.not_odd_iff_even.mpr (by decide)) hoddQ
  -- PAPER: "But then `x₀,…,x_{t−1}` is a `Y ∪ {x_t}`-square of height `t − 1`"
  refine ⟨Y ∪ {x t}, ?_, Set.subset_union_left, x,
    Thm203AntipathTools.ysquare_truncate_union hd ht hadj12 hno1
      ⟨w, hwA2, hw1.symm, hwnbr⟩⟩
  exact YDiamondTruncation.anticonnected_union_singleton hYanti (hxY t le_rfl) hnVC

/-- **The conclusion the paper draws**: *"So we may assume some antipath `Q` between
`x_{t−1}` and `w` with interior in `X_{t−2}` is even."* -/
theorem exists_even_antipath {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hno1 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a)
    {w : V} (hwA2 : w ∈ wheelSystemA G z A₀ x (t - 2))
    (hw1 : G.Adj (x (t - 1)) w)
    (hnone : ¬ ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') :
    ∃ Q : List V, IsAntipathFrom G Q (x (t - 1)) w ∧
      (∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2)) ∧ Even (pathLength Q) := by
  by_contra hcon
  push_neg at hcon
  refine hnone (square_from_all_odd hG hframe hd ht hno1 hwA2 hw1 ?_)
  intro Q hQ hQint
  exact Nat.not_even_iff_odd.mp (hcon Q hQ hQint)

end Workspace.ProofLemmas.Thm203Step3Aux
