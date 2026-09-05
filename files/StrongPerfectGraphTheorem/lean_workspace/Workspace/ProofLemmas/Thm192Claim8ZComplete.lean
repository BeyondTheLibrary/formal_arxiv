import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim8Basics
import Workspace.ProofLemmas.Thm192Claim8Unique
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S13.Thm_13_6

/-!
# Claim (8) of 19.2: `z` is `Y`-complete

PAPER (printed p. 121):

> *"Suppose that `z` is not `Y`-complete; and therefore `Y₀ ∪ {z}` is anticonnected, and
> `x₂` is `Y₀`-complete by (2).  Choose `h` with `1 ≤ h < k` minimum such that `f_h` is
> adjacent to `y` (this exists since `f_k` is not the unique neighbour of `y` in `A`).  The
> path `x₂-f₁-⋯-f_h-y` is even, since it can be completed to a hole via `y-z-x₂`, and
> therefore the path `x₂-f₁-⋯-f_h-y-x₁` is odd (this is a path since `f_k` is the unique
> neighbour of `x₁` in `A`); and the ends of this path are `Y₀ ∪ {z}`-complete, and its
> internal vertices are not.  By 13.6 it has length 3.  So `f₁` is adjacent to `y` and `x₂`.
> If `f₁` is not `Y₀`-complete, then an antipath between `f₁, y` with interior in `Y₀` can
> be completed to an antihole via `y-x₂-x₁-f₁`, which shares the vertices `x₁, x₂, f₁` with
> the hole `C₁`, contrary to 15.7; while if `f₁` is `Y`-complete, then an antipath between
> `z, y` with interior in `Y₀` can be completed to an antihole via `y-x₂-x₁-f₁-z`, again
> contrary to 15.7.  This proves that `z` is `Y`-complete."*

Two small departures from the printed text, both simplifications:

* *"`x₂` is `Y₀`-complete by (2)"* is read off claim (2) directly: its right-hand disjunct
  asserts `z` is `Y`-complete, which is exactly what is being assumed false here.
* the 13.6 application uses `X = Y₀ ∪ {z}` as printed; the vertex `y` of the path is not
  `X`-complete because `Y` is anticonnected and `Y₀` is nonempty, so `y` has a nonneighbour
  in `Y₀`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8ZComplete

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A five-element list with exactly its four consecutive edges is an induced path. -/
theorem isPathList_five {G : SimpleGraph V} {a b c d e : V}
    (hnd : [a, b, c, d, e].Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d) (h4 : G.Adj d e)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj a e)
    (n4 : ¬ G.Adj b d) (n5 : ¬ G.Adj b e) (n6 : ¬ G.Adj c e) :
    IsPathList G [a, b, c, d, e] := by
  have key : ∀ i j : ℕ, i < 5 → j < 5 →
      ∀ (hi : i < [a, b, c, d, e].length) (hj : j < [a, b, c, d, e].length),
        (G.Adj ([a, b, c, d, e][i]'hi) ([a, b, c, d, e][j]'hj) ↔
          (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi5 hj5
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h3 (by first | omega | simp | tauto)
      | exact iff_of_true h4 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_true h3.symm (by first | omega | simp | tauto)
      | exact iff_of_true h4.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false n2 (by first | omega | simp | tauto)
      | exact iff_of_false n3 (by first | omega | simp | tauto)
      | exact iff_of_false n4 (by first | omega | simp | tauto)
      | exact iff_of_false n5 (by first | omega | simp | tauto)
      | exact iff_of_false n6 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n4 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n5 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n6 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩



/-- *"This proves that `z` is `Y`-complete."* -/
theorem zComplete (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hx20 : G.Adj (x 2) (x 0)) (h2y : ¬ G.Adj (x 2) y)
    (R : List V) (f₁ fk : V) (hR : IsPathFrom G R f₁ fk) (hRA : {w : V | w ∈ R} = A)
    (h0f₁ : G.Adj (x 0) f₁) (h2f₁ : G.Adj (x 2) f₁) (h1fk : G.Adj (x 1) fk)
    (hyfk : G.Adj y fk) (hfne : f₁ ≠ fk)
    (hu2 : ∀ a ∈ A, G.Adj (x 2) a → a = f₁) (hu1 : ∀ a ∈ A, G.Adj (x 1) a → a = fk)
    (hnuy : ∃ a ∈ A, a ≠ fk ∧ G.Adj y a) :
    VertexComplete G z Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  -- standing bookkeeping (as in `Thm192Claim8Endgame`)
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hzA : ∀ g ∈ A, ¬ G.Adj z g := fun g hg => wheelSystemA_no_z g (hAsub hg)
  have hxA : ∀ j : ℕ, j ≤ 2 → x j ∉ A := fun j hj hm => hzA _ hm (hzx j hj)
  have hzAmem : z ∉ A := Thm192Claim8Basics.z_notMem hws hAsub
  have hyA : y ∉ A := fun hm => hzA _ hm hyz.symm
  have hnoc : ∀ g ∈ A, ¬ (G.Adj (x 0) g ∧ G.Adj (x 1) g) := by
    intro g hg hc
    exact Thm192Claim8Basics.no_X1_complete hAsub g hg ⟨hc.1.symm, hc.2.symm⟩
  have hx21 : ¬ G.Adj (x 2) (x 1) := by
    intro hadj
    refine hws.2.2.2.2.2.1 2 (by omega) (by omega) ?_
    rw [show (2 : ℕ) - 1 = 1 from rfl, wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hx20
    · exact hadj
  have hx01 : ¬ G.Adj (x 0) (x 1) := x0_not_adj_x1 hws
  have hxne : ∀ i j : ℕ, i ≤ 2 → j ≤ 2 → i ≠ j → x i ≠ x j := by
    intro i j hi hj hij he
    exact hij (hws.2.1 i hi j hj he)
  have hxz : ∀ j : ℕ, j ≤ 2 → x j ≠ z := fun j hj => (hws.2.2.1 j hj).2
  have hf₁A : f₁ ∈ A := by rw [← hRA]; exact List.mem_of_mem_head? hR.2.1
  have hfkA : fk ∈ A := by rw [← hRA]; exact List.mem_of_mem_getLast? hR.2.2
  have hRmemA : ∀ w ∈ R, w ∈ A := fun w hw => by rw [← hRA]; exact hw
  have hAmemR : ∀ w ∈ A, w ∈ R := fun w hw => by rw [← hRA] at hw; exact hw
  have hYA : ∀ w ∈ Y, w ∉ A := by
    intro w hwY hwA
    exact hnoc w hwA ⟨hHyp.2.2.1 w hwY, hHyp.2.2.2.1 w hwY⟩
  have h1f₁ : ¬ G.Adj (x 1) f₁ := fun h => hnoc f₁ hf₁A ⟨h0f₁, h⟩
  have hy1 : G.Adj y (x 1) := (hHyp.2.2.2.1 y hyY).symm
  -- lengths
  have hpos : 0 < R.length := List.length_pos_iff.mpr hR.1.1
  have h0R : R[0]'hpos = f₁ := PathBasics.getElem_zero_of_head? hR.2.1 hpos
  have hlR : R[R.length - 1]'(by omega) = fk :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hpos
  have hnd : R.Nodup := hR.1.2.1
  have hlen2 : 2 ≤ R.length := by
    by_contra hcon
    refine hfne ?_
    rw [← h0R, ← hlR]
    exact (HoleArithmetic.getElem_congr_idx R _ _ (by omega)).symm
  -- the path `S = x₂-f₁-⋯-f_k` and the hole `C₁`
  have hx2R : x 2 ∉ R := fun h => hxA 2 (by omega) (hRmemA _ h)
  have hS : IsPathFrom G (x 2 :: R) (x 2) fk :=
    PathAttach.isPathFrom_cons hR h2f₁ hx2R
      (fun w hw hwne hadj => hwne (hu2 w (hRmemA w hw) hadj))
  have hSmem : ∀ w ∈ (x 2 :: R), w = x 2 ∨ w ∈ A := by
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · exact Or.inl h
    · exact Or.inr (hRmemA w h)
  have hintS : SPGT.interior (x 2 :: R) = R.dropLast := by simp [SPGT.interior]
  have hintSA : ∀ w ∈ SPGT.interior (x 2 :: R), w ∈ A ∧ w ≠ fk := by
    intro w hw
    rw [hintS] at hw
    have hdl : R.dropLast = (R.drop 0).take (R.length - 2 - 0 + 1) := by
      rw [List.dropLast_eq_take]
      simp only [List.drop_zero]
      congr 1
      omega
    rw [hdl] at hw
    have hmem : w ∈ {w : V | w ∈ R} \ {fk} := by
      rw [← Thm192Claim8Unique.init_eq hR hlen2]; exact hw
    exact ⟨hRmemA w hmem.1, hmem.2⟩
  have hzS : z ∉ (x 2 :: R) := by
    intro hc
    rcases hSmem z hc with h | h
    · exact hxz 2 (by omega) h.symm
    · exact hzAmem h
  have hx1S : x 1 ∉ (x 2 :: R) := by
    intro hc
    rcases hSmem (x 1) hc with h | h
    · exact hxne 1 2 (by omega) (by omega) (by omega) h
    · exact hxA 1 (by omega) h
  have hD : IsHoleList G (x 1 :: z :: (x 2 :: R)) := by
    refine PrismBasics.isHoleList_of_path_add_two_vertices hS ?_ (hzx 2 (by omega)) h1fk
      (hzx 1 (by omega)) hzS hx1S (hzA fk hfkA) (fun hc => hx21 hc.symm) ?_ ?_
    · rw [PathBasics.pathLength_eq]
      simp only [List.length_cons]
      omega
    · intro w hw
      exact hzA w (hintSA w hw).1
    · intro w hw hadj
      exact (hintSA w hw).2 (hu1 w (hintSA w hw).1 hadj)
  have hDlen : (x 1 :: z :: (x 2 :: R)).length = R.length + 3 := by simp
  have hDlen4 : 4 < holeLength (x 1 :: z :: (x 2 :: R)) := by
    have h4 := hD.1
    simp only [holeLength, hDlen] at *
    omega
  have hx1D : x 1 ∈ (x 1 :: z :: (x 2 :: R)) := List.mem_cons_self
  have hx2D : x 2 ∈ (x 1 :: z :: (x 2 :: R)) := by simp
  have hf₁D : f₁ ∈ (x 1 :: z :: (x 2 :: R)) := by
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (hAmemR f₁ hf₁A)))
  -- now suppose `z` is not `Y`-complete
  by_contra hzYc
  obtain ⟨y', hy'Y, hzy'⟩ : ∃ w ∈ Y, ¬ G.Adj z w := by
    by_contra hcon
    push_neg at hcon
    exact hzYc (fun w hw => hcon w hw)
  have hy'ney : y' ≠ y := fun he => hzy' (by rw [he]; exact hyz.symm)
  have hy'0 : y' ∈ Y \ {y} := ⟨hy'Y, by simpa using hy'ney⟩
  have hY0anti : AnticonnectedSet G (Y \ {y}) :=
    hY0.resolve_left (fun he => by rw [he] at hy'0; exact hy'0)
  have h2Y0 : VertexComplete G (x 2) (Y \ {y}) := by
    rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
      hL | hRt
    · exact hL.1
    · exact absurd hRt.1 hzYc
  obtain ⟨w₀, hw₀Y, hw₀ney, hyw₀⟩ :=
    Thm192Claim8Basics.exists_nonadj_of_anticonnected hHyp.2.1 hyY hy'Y (Ne.symm hy'ney)
  have hw₀0 : w₀ ∈ Y \ {y} := ⟨hw₀Y, by simpa using hw₀ney⟩
  have hzY0 : z ∉ Y \ {y} := fun hc => (hHyp.1 z hc.1).1 rfl
  have hyY0 : y ∉ Y \ {y} := fun hc => hc.2 rfl
  have hf₁Y0 : f₁ ∉ Y \ {y} := fun hc => hYA f₁ hc.1 hf₁A
  have hx1Y0 : VertexComplete G (x 1) (Y \ {y}) := fun w hw => hHyp.2.2.2.1 w hw.1
  -- the two antihole contradictions
  have hkey : G.Adj y f₁ → False := by
    intro hyf₁
    by_cases hcase : VertexComplete G f₁ (Y \ {y})
    · obtain ⟨Q, hQ, hQint⟩ := InducedPathExtraction.exists_antipath_interior_in hY0anti
        hzY0 hyY0 ⟨y', hy'0, hzy'⟩ ⟨w₀, hw₀0, hyw₀⟩
      have hR₅ : IsAntipathFrom G [y, x 2, x 1, f₁, z] y z := by
        refine ⟨isPathList_five (G := Gᶜ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl, rfl⟩
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or, not_false_eq_true, or_false]
          exact ⟨⟨fun h => (hHyp.1 y hyY).2.2.2 h, fun h => (hHyp.1 y hyY).2.2.1 h,
              fun h => hyA (by rw [h]; exact hf₁A), fun h => (hHyp.1 y hyY).1 h⟩,
            ⟨hxne 2 1 (by omega) (by omega) (by omega),
              fun h => hxA 2 (by omega) (by rw [h]; exact hf₁A), hxz 2 (by omega)⟩,
            ⟨fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A), hxz 1 (by omega)⟩,
            fun h => hzAmem (by rw [← h]; exact hf₁A)⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun h => (hHyp.1 y hyY).2.2.2 h, fun h => h2y h.symm⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨hxne 2 1 (by omega) (by omega) (by omega), hx21⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A), h1f₁⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun h => hzAmem (by rw [← h]; exact hf₁A), fun h => hzA f₁ hf₁A h.symm⟩
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 hy1
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 hyf₁
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 hyz
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 h2f₁
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 (hzx 2 (by omega)).symm
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 (hzx 1 (by omega)).symm
      refine Thm192Infra.antipathExtendToAntihole hG.1 hyz.symm hQ hQint hR₅ (by simp) ?_
        hD hDlen4 (c₀ := x 2) (c₁ := x 1) (c₂ := f₁)
        (hxne 2 1 (by omega) (by omega) (by omega))
        (fun h => hxA 2 (by omega) (by rw [h]; exact hf₁A))
        (fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A))
        hx2D hx1D hf₁D ?_ ?_ ?_
      · intro w hw
        simp only [SPGT.interior, List.tail_cons, List.dropLast_cons_cons,
          List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl | rfl
        · exact h2Y0
        · exact hx1Y0
        · exact hcase
      · exact List.mem_append_right _ (by simp [SPGT.interior])
      · exact List.mem_append_right _ (by simp [SPGT.interior])
      · exact List.mem_append_right _ (by simp [SPGT.interior])
    · have hf₁w : ∃ w ∈ Y \ {y}, ¬ G.Adj f₁ w := by
        by_contra hcon
        push_neg at hcon
        exact hcase hcon
      obtain ⟨Q, hQ, hQint⟩ := InducedPathExtraction.exists_antipath_interior_in hY0anti
        hf₁Y0 hyY0 hf₁w ⟨w₀, hw₀0, hyw₀⟩
      have hR₄ : IsAntipathFrom G [y, x 2, x 1, f₁] y f₁ := by
        refine ⟨PathGlue.isPathList_four (G := Gᶜ) ?_ ?_ ?_ ?_ ?_ ?_ ?_, rfl, rfl⟩
        · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
            and_true, not_or, not_false_eq_true, or_false]
          exact ⟨⟨fun h => (hHyp.1 y hyY).2.2.2 h, fun h => (hHyp.1 y hyY).2.2.1 h,
              fun h => hyA (by rw [h]; exact hf₁A)⟩,
            ⟨hxne 2 1 (by omega) (by omega) (by omega),
              fun h => hxA 2 (by omega) (by rw [h]; exact hf₁A)⟩,
            fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A)⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun h => (hHyp.1 y hyY).2.2.2 h, fun h => h2y h.symm⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨hxne 2 1 (by omega) (by omega) (by omega), hx21⟩
        · exact (SimpleGraph.compl_adj G _ _).mpr
            ⟨fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A), h1f₁⟩
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 hy1
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 hyf₁
        · exact fun h => ((SimpleGraph.compl_adj G _ _).mp h).2 h2f₁
      refine Thm192Infra.antipathExtendToAntihole hG.1 hyf₁.symm hQ hQint hR₄ (by simp) ?_
        hD hDlen4 (c₀ := x 2) (c₁ := x 1) (c₂ := f₁)
        (hxne 2 1 (by omega) (by omega) (by omega))
        (fun h => hxA 2 (by omega) (by rw [h]; exact hf₁A))
        (fun h => hxA 1 (by omega) (by rw [h]; exact hf₁A))
        hx2D hx1D hf₁D ?_ ?_ ?_
      · intro w hw
        simp only [SPGT.interior, List.tail_cons, List.dropLast_cons_cons,
          List.dropLast_singleton, List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact h2Y0
        · exact hx1Y0
      · exact List.mem_append_right _ (by simp [SPGT.interior])
      · exact List.mem_append_right _ (by simp [SPGT.interior])
      · exact List.mem_append_left _ (PathBasics.head_mem hQ.2.1)
  -- *"Choose `h` with `1 ≤ h < k` minimum such that `f_h` is adjacent to `y`."*
  have hex : ∃ i : ℕ, ∃ hi : i < R.length, i < R.length - 1 ∧ G.Adj y (R[i]'hi) := by
    obtain ⟨a, haA, hane, hya⟩ := hnuy
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp (hAmemR a haA)
    refine ⟨k, hk, ?_, hya⟩
    rcases Nat.lt_or_ge k (R.length - 1) with h | h
    · exact h
    · exact absurd (by rw [← hlR]; exact HoleArithmetic.getElem_congr_idx R _ _ (by omega))
        hane
  obtain ⟨hi₀lt, hi₀k, hyi₀⟩ := Nat.find_spec hex
  set i₀ := Nat.find hex with hi₀def
  have hmin : ∀ j, j < i₀ → ∀ hj : j < R.length, ¬ G.Adj y (R[j]'hj) := by
    intro j hj hjl hadj
    exact Nat.find_min hex hj ⟨hjl, by omega, hadj⟩
  have hi₀zero : i₀ = 0 := by
    by_contra hne0
    have hi₀pos : 0 < i₀ := Nat.pos_of_ne_zero hne0
    have hp0 : IsPathFrom G ((R.drop 0).take (i₀ - 0 + 1)) (R[0]'(by omega))
        (R[i₀]'hi₀lt) := PathBasics.isPathFrom_slice hR.1 hi₀pos hi₀lt
    rw [h0R] at hp0
    have hp0mem : ∀ w ∈ (R.drop 0).take (i₀ - 0 + 1),
        ∃ (k : ℕ) (hk : k < R.length), k ≤ i₀ ∧ R[k]'hk = w := by
      intro w hw
      obtain ⟨k, hk, -, h2, h3⟩ := (PathBasics.mem_slice_iff R (by omega) hi₀lt).mp hw
      exact ⟨k, hk, h2, h3⟩
    have hp0A : ∀ w ∈ (R.drop 0).take (i₀ - 0 + 1), w ∈ A := by
      intro w hw
      obtain ⟨k, hk, -, rfl⟩ := hp0mem w hw
      exact hRmemA _ (List.getElem_mem hk)
    have hp0nefk : ∀ w ∈ (R.drop 0).take (i₀ - 0 + 1), w ≠ fk := by
      intro w hw he
      obtain ⟨k, hk, hki, rfl⟩ := hp0mem w hw
      rw [← hlR] at he
      have : k = R.length - 1 := (List.Nodup.getElem_inj_iff hnd).mp he
      omega
    have hp0y : ∀ w ∈ (R.drop 0).take (i₀ - 0 + 1), w ≠ R[i₀]'hi₀lt → ¬ G.Adj y w := by
      intro w hw hwne hadj
      obtain ⟨k, hk, hki, rfl⟩ := hp0mem w hw
      rcases Nat.lt_or_ge k i₀ with h | h
      · exact hmin k h hk hadj
      · exact hwne (HoleArithmetic.getElem_congr_idx R _ _ (by omega))
    have hx2p0 : x 2 ∉ (R.drop 0).take (i₀ - 0 + 1) :=
      fun hc => hxA 2 (by omega) (hp0A _ hc)
    have hyp0 : y ∉ (R.drop 0).take (i₀ - 0 + 1) := fun hc => hyA (hp0A _ hc)
    have hQ1 : IsPathFrom G (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) (x 2) y := by
      refine PathAttach.isPathFrom_cons_concat hp0 h2f₁ hyi₀ (fun h => h2y h)
        (fun h => (hHyp.1 y hyY).2.2.2 h.symm) hx2p0 hyp0 ?_ hp0y
      intro w hw hwne hadj
      exact hwne (hu2 w (hp0A w hw) hadj)
    have hQ1len : (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])).length = i₀ + 3 := by
      rw [PathAttach.length_cons_append_singleton, PathBasics.length_slice R (by omega) hi₀lt]
      omega
    have hQ1int : SPGT.interior (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y]))
        = (R.drop 0).take (i₀ - 0 + 1) := by simp [SPGT.interior]
    have hQ1mem : ∀ w ∈ (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])),
        w = x 2 ∨ w ∈ A ∨ w = y := by
      intro w hw
      rcases PathAttach.mem_cons_append_singleton.mp hw with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (hp0A w h))
      · exact Or.inr (Or.inr h)
    have hzQ1 : z ∉ (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) := by
      intro hc
      rcases hQ1mem z hc with h | h | h
      · exact hxz 2 (by omega) h.symm
      · exact hzAmem h
      · exact (hHyp.1 y hyY).1 h.symm
    have hx1Q1 : x 1 ∉ (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) := by
      intro hc
      rcases hQ1mem (x 1) hc with h | h | h
      · exact hxne 1 2 (by omega) (by omega) (by omega) h
      · exact hxA 1 (by omega) h
      · exact (hHyp.1 y hyY).2.2.1 h.symm
    -- the hole `z-x₂-f₁-⋯-f_h-y-z` gives the parity
    have hhole : IsHoleList G (z :: (x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y]))) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hQ1 ?_ (hzx 2 (by omega)) hyz.symm
        hzQ1 ?_
      · rw [PathBasics.pathLength_eq, hQ1len]; omega
      · intro w hw
        rw [hQ1int] at hw
        exact hzA w (hp0A w hw)
    have hi₀even : Even i₀ := by
      have heven := hBerge.1 _ hhole
      simp only [holeLength, List.length_cons, hQ1len] at heven
      rcases heven with ⟨m, hm⟩
      exact ⟨m - 2, by omega⟩
    -- *"the path `x₂-f₁-⋯-f_h-y-x₁` is odd"*
    have hQ2 : IsPathFrom G
        ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1]) (x 2) (x 1) := by
      refine PathAttach.isPathFrom_concat hQ1 hy1.symm hx1Q1 ?_
      intro w hw hwne hadj
      rcases hQ1mem w hw with h | h | h
      · exact hx21 (by rw [h] at hadj; exact hadj.symm)
      · exact hp0nefk w (by
          rcases PathAttach.mem_cons_append_singleton.mp hw with h' | h' | h'
          · exact absurd (h' ▸ h) (fun hc => hxA 2 (by omega) hc)
          · exact h'
          · exact absurd h' hwne) (hu1 w h hadj)
      · exact hwne h
    have hQ2len : pathLength ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1])
        = i₀ + 3 := by
      simp only [pathLength, List.length_append, List.length_singleton, hQ1len]
      omega
    have hQ2odd : Odd (pathLength
        ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1])) := by
      rw [hQ2len]
      rcases hi₀even with ⟨m, hm⟩
      exact ⟨m + 1, by omega⟩
    have hQ2mem : ∀ w ∈ ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1]),
        w = x 2 ∨ w ∈ A ∨ w = y ∨ w = x 1 := by
      intro w hw
      rcases List.mem_append.mp hw with h | h
      · rcases hQ1mem w h with h' | h' | h'
        · exact Or.inl h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
    -- 13.6 with `X = Y₀ ∪ {z}`
    have hXanti : AnticonnectedSet G ((Y \ {y}) ∪ {z}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hY0anti
        ⟨y', hy'0, (SimpleGraph.compl_adj G _ _).mpr ⟨fun h => hzY0 (by rw [h]; exact hy'0),
          hzy'⟩⟩
    have hXP : ((Y \ {y}) ∪ {z}) ⊆
        {v : V | v ∈ ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1])}ᶜ := by
      intro v hv hmem
      rcases hv with hv | hv
      · rcases hQ2mem v hmem with h | h | h | h
        · exact (hHyp.1 v hv.1).2.2.2 h
        · exact hYA v hv.1 h
        · exact hv.2 (by simpa using h)
        · exact (hHyp.1 v hv.1).2.2.1 h
      · have hvz : v = z := by simpa using hv
        subst hvz
        rcases hQ2mem v hmem with h | h | h | h
        · exact hxz 2 (by omega) h.symm
        · exact hzAmem h
        · exact (hHyp.1 y hyY).1 h.symm
        · exact hxz 1 (by omega) h.symm
    have hcompl : ∀ w : V, VertexComplete G w (Y \ {y}) → G.Adj w z →
        VertexComplete G w ((Y \ {y}) ∪ {z}) := by
      intro w hw hz v hv
      rcases hv with hv | hv
      · exact hw v hv
      · rw [show v = z from by simpa using hv]; exact hz
    rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 _ (x 2) (x 1) hQ2 hQ2odd
        ((Y \ {y}) ∪ {z}) hXP hXanti (hcompl _ h2Y0 (hzx 2 (by omega)).symm)
        (hcompl _ hx1Y0 (hzx 1 (by omega)).symm) with
      ⟨u, hu, v, hv, hedge⟩ | ⟨h3, -⟩
    · have hXc : ∀ w ∈ ((x 2 :: (((R.drop 0).take (i₀ - 0 + 1)) ++ [y])) ++ [x 1]),
          VertexComplete G w ((Y \ {y}) ∪ {z}) → w = x 2 ∨ w = x 1 := by
        intro w hw hwc
        have hwz : G.Adj w z := hwc z (Or.inr rfl)
        rcases hQ2mem w hw with h | h | h | h
        · exact Or.inl h
        · exact absurd hwz (fun hc => hzA w h hc.symm)
        · exact absurd (hwc w₀ (Or.inl hw₀0)) (by rw [h]; exact hyw₀)
        · exact Or.inr h
      rcases hXc u hu hedge.2.1 with h | h <;> rcases hXc v hv hedge.2.2 with h' | h'
      · exact absurd (h ▸ h' ▸ hedge.1) G.irrefl
      · exact hx21 (h ▸ h' ▸ hedge.1)
      · exact hx21 (h ▸ h' ▸ hedge.1).symm
      · exact absurd (h ▸ h' ▸ hedge.1) G.irrefl
    · rw [hQ2len] at h3
      omega
  refine hkey ?_
  rw [← h0R]
  have : R[i₀]'hi₀lt = R[0]'(by omega) :=
    HoleArithmetic.getElem_congr_idx R _ _ (by omega)
  rw [← this]
  exact hyi₀

end Workspace.ProofLemmas.Thm192Claim8ZComplete
