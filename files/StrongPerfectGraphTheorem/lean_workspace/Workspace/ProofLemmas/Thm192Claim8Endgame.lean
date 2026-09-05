import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Claim4
import Workspace.ProofLemmas.Thm192Claim8Basics
import Workspace.ProofLemmas.Thm192Claim8Unique
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm232ClosingCompletePair
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S13.Thm_13_6

/-!
# Claim (8) of 19.2: the closing contradiction

PAPER (printed p. 121):

> *"In the hole `C₁`, `z, x₁` are `Y`-complete and `x₂, f_k` are not; so since `G ∈ F₇`, no
> other vertex of `C₁` is `Y`-complete.  By 2.10, `Y` contains a leap or hat for `C₁`.  From
> a hypothesis of the theorem, every vertex in `Y` has a neighbour in `A ∪ {x₂}`, so there
> is no hat, and hence there exist nonadjacent `y₁, y₂` in `Y` such that
> `y₁-x₂-f₁-⋯-f_k-y₂` is a path.  Since both ends of this path are `{x₀,x₁}`-complete, and
> no internal vertex is `{x₀,x₁}`-complete, this contradicts 13.6.  This proves (8)."*

The hole `C₁ = z-x₂-f₁-⋯-f_k-x₁-z` is written with its `Y`-complete edge `x₁z` at the front,
as `x₁ :: z :: (x₂ :: R)`, which is the shape `Thm232ClosingCompletePair.pair_segment` and
`only_pair` recognise; those two carry the *"since `G ∈ F₇`"* step through 2.3.

*"`f_k` is not `Y`-complete"* is derived here from claim (4) rather than from the printed
paragraph 3: once `z` is `Y`-complete, claim (4) says no edge of an `x₀`--`x₁` path with
interior in `A` is `Y`-complete, and the last edge of any such path is `f_k x₁`, because
`f_k` is the only neighbour of `x₁` in `A`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The closing contradiction of claim (8). -/
theorem endgame (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Concl192 G z A₀ x Y)
    (hx20 : G.Adj (x 2) (x 0)) (h2y : ¬ G.Adj (x 2) y)
    (R : List V) (f₁ fk : V) (hR : IsPathFrom G R f₁ fk) (hRA : {w : V | w ∈ R} = A)
    (h0f₁ : G.Adj (x 0) f₁) (h2f₁ : G.Adj (x 2) f₁) (h1fk : G.Adj (x 1) fk)
    (hyfk : G.Adj y fk) (hfne : f₁ ≠ fk)
    (hu2 : ∀ a ∈ A, G.Adj (x 2) a → a = f₁) (hu1 : ∀ a ∈ A, G.Adj (x 1) a → a = fk)
    (hzY : VertexComplete G z Y) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  -- standing bookkeeping
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
  -- `Y` is disjoint from `A ∪ {z, x₀, x₁, x₂}`
  have hYA : ∀ w ∈ Y, w ∉ A := by
    intro w hwY hwA
    exact hnoc w hwA ⟨hHyp.2.2.1 w hwY, hHyp.2.2.2.1 w hwY⟩
  -- lengths
  have hpos : 0 < R.length := List.length_pos_iff.mpr hR.1.1
  have h0R : R[0]'hpos = f₁ := PathBasics.getElem_zero_of_head? hR.2.1 hpos
  have hlR : R[R.length - 1]'(by omega) = fk :=
    PathBasics.getElem_last_of_getLast? hR.2.2 hpos
  have hlen2 : 2 ≤ R.length := by
    by_contra hcon
    refine hfne ?_
    rw [← h0R, ← hlR]
    exact (HoleArithmetic.getElem_congr_idx R _ _ (by omega)).symm
  -- the path `S = x₂-f₁-⋯-f_k`
  have hx2R : x 2 ∉ R := fun h => hxA 2 (by omega) (hRmemA _ h)
  have hS : IsPathFrom G (x 2 :: R) (x 2) fk :=
    PathAttach.isPathFrom_cons hR h2f₁ hx2R
      (fun w hw hwne hadj => hwne (hu2 w (hRmemA w hw) hadj))
  have hSmem : ∀ w ∈ (x 2 :: R), w = x 2 ∨ w ∈ A := by
    intro w hw
    rcases List.mem_cons.mp hw with h | h
    · exact Or.inl h
    · exact Or.inr (hRmemA w h)
  have hintS : SPGT.interior (x 2 :: R) = R.dropLast := by
    simp [SPGT.interior]
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
  -- the hole `C₁ = x₁-z-x₂-f₁-⋯-f_k`
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
  have hRodd : Odd R.length := by
    have heven := hBerge.1 _ hD
    simp only [holeLength, hDlen] at heven
    rcases heven with ⟨m, hm⟩
    exact ⟨m - 2, by omega⟩
  have hRlen3 : 3 ≤ R.length := by
    rcases hRodd with ⟨m, hm⟩
    omega
  have hD6 : 6 ≤ (x 1 :: z :: (x 2 :: R)).length := by rw [hDlen]; omega
  -- *"`f_k` is not `Y`-complete"*, from claim (4)
  have hfkNotY : ¬ VertexComplete G fk Y := by
    obtain ⟨P, hP, hPint⟩ := MinimalConnectedIsPath.exists_path_interior_in hA.2.1
      (hxA 0 (by omega)) (hxA 1 (by omega)) ⟨f₁, hf₁A, h0f₁⟩ ⟨fk, hfkA, h1fk⟩
    have hPlen : 3 ≤ P.length :=
      MinimalConnectedIsPath.three_le_length_of_not_adj hP
        (hxne 0 1 (by omega) (by omega) (by omega)) hx01
    have hPn1 : P.length - 1 < P.length := by omega
    have hPn2 : P.length - 2 < P.length := by omega
    have hPL : P[P.length - 1]'hPn1 = x 1 :=
      PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    have hpnint : (P[P.length - 2]'hPn2) ∈ SPGT.interior P :=
      PathBasics.getElem_mem_interior hP.1 hPn2 (by omega) (by omega)
    have hpnadj : G.Adj (P[P.length - 2]'hPn2) (P[P.length - 1]'hPn1) := by
      have h := PathBasics.path_adj_succ hP.1 (i := P.length - 2) (by omega)
      have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hPn1 :=
        HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
      rwa [hidx] at h
    have hpnfk : (P[P.length - 2]'hPn2) = fk :=
      hu1 _ (hPint _ hpnint) (by rw [← hPL]; exact hpnadj.symm)
    have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin hcex P hP hPint hPlen
    intro hc
    refine h4.2.1 hzY (P.length - 2) (by omega) ⟨PathBasics.path_adj_succ hP.1 (by omega),
      by rw [hpnfk]; exact hc, ?_⟩
    have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hPn1 :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hPL]
    exact hHyp.2.2.2.1
  -- membership decoder for the rim
  have hDmem : ∀ w ∈ (x 1 :: z :: (x 2 :: R)), w = x 1 ∨ w = z ∨ w = x 2 ∨ w ∈ A := by
    intro w hw
    rcases List.mem_cons.mp hw with h | hw
    · exact Or.inl h
    rcases List.mem_cons.mp hw with h | hw
    · exact Or.inr (Or.inl h)
    · rcases hSmem w hw with h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
  have hDY : ∀ w ∈ (x 1 :: z :: (x 2 :: R)), w ∉ Y := by
    intro w hw hwY
    rcases hDmem w hw with h | h | h | h
    · exact (hHyp.1 w hwY).2.2.1 h
    · exact (hHyp.1 w hwY).1 h
    · exact (hHyp.1 w hwY).2.2.2 h
    · exact hYA w hwY h
  have hx1D : x 1 ∈ (x 1 :: z :: (x 2 :: R)) := List.mem_cons_self
  have hzD : z ∈ (x 1 :: z :: (x 2 :: R)) := by simp
  have hx2D : x 2 ∈ (x 1 :: z :: (x 2 :: R)) := by simp
  have hAD : ∀ a ∈ A, a ∈ (x 1 :: z :: (x 2 :: R)) := by
    intro a ha
    simp only [List.mem_cons]
    exact Or.inr (Or.inr (Or.inr (hAmemR a ha)))
  -- the only `Y`-complete vertices of the rim are `x₁` and `z`
  have hedge : EdgeComplete G Y (x 1) z :=
    ⟨(hzx 1 (by omega)).symm, hHyp.2.2.2.1, hzY⟩
  have hseg : IsSegment G (x 1 :: z :: (x 2 :: R)) Y [x 1, z] :=
    Thm232ClosingCompletePair.pair_segment hD hD6 hS hHyp.2.2.2.1 hzY
      hHyp.2.2.2.2.1 hfkNotY
  have honly : ∀ w ∈ (x 1 :: z :: (x 2 :: R)), VertexComplete G w Y → w = x 1 ∨ w = z := by
    refine Thm232ClosingCompletePair.only_pair hBerge hD hD6 ⟨y, hyY⟩ hHyp.2.1 hDY
      (fun hw => hG.2.1 ⟨_, _, hw⟩) hx1D hzD hedge hseg ?_ ?_
    · intro w hw hadj hwc
      rcases hDmem w hw with h | h | h | h
      · exact absurd (h ▸ hadj) G.irrefl
      · exact h
      · exact absurd (h ▸ hadj) (fun hc => hx21 hc.symm)
      · exact absurd (hu1 w h hadj ▸ hwc) hfkNotY
    · intro w hw hadj hwc
      rcases hDmem w hw with h | h | h | h
      · exact h
      · exact absurd (h ▸ hadj) G.irrefl
      · exact absurd (h ▸ hwc) hHyp.2.2.2.2.1
      · exact absurd hadj (hzA w h)
  -- the closing 13.6 contradiction, for either orientation of the leap
  have kill : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → ¬ G.Adj a b → G.Adj a (x 2) → G.Adj b fk →
      (∀ w ∈ (x 1 :: z :: (x 2 :: R)), G.Adj a w → w = x 1 ∨ w = z ∨ w = x 2) →
      (∀ w ∈ (x 1 :: z :: (x 2 :: R)), G.Adj b w → w = x 1 ∨ w = z ∨ w = fk) →
      False := by
    intro a haY b hbY hab hnab ha2 hbk hAonly hBonly
    have haS : a ∉ (x 2 :: R) := by
      intro hc
      rcases hSmem a hc with h | h
      · exact (hHyp.1 a haY).2.2.2 h
      · exact hYA a haY h
    have hbS : b ∉ (x 2 :: R) := by
      intro hc
      rcases hSmem b hc with h | h
      · exact (hHyp.1 b hbY).2.2.2 h
      · exact hYA b hbY h
    have hQ : IsPathFrom G (a :: ((x 2 :: R) ++ [b])) a b := by
      refine PathAttach.isPathFrom_cons_concat hS ha2 hbk hnab hab haS hbS ?_ ?_
      · intro w hw hwne hadj
        rcases hAonly w (by simp only [List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp hw))) hadj with
          h | h | h
        · exact hx1S (h ▸ hw)
        · exact hzS (h ▸ hw)
        · exact hwne h
      · intro w hw hwne hadj
        rcases hBonly w (by simp only [List.mem_cons]; exact Or.inr (Or.inr (List.mem_cons.mp hw))) hadj with
          h | h | h
        · exact hx1S (h ▸ hw)
        · exact hzS (h ▸ hw)
        · exact hwne h
    have hQlen : pathLength (a :: ((x 2 :: R) ++ [b])) = R.length + 2 := by
      rw [PathAttach.pathLength_cons_append_singleton]
      simp
    have hQodd : Odd (pathLength (a :: ((x 2 :: R) ++ [b]))) := by
      rw [hQlen]
      rcases hRodd with ⟨m, hm⟩
      exact ⟨m + 1, by omega⟩
    have hQmem : ∀ w ∈ (a :: ((x 2 :: R) ++ [b])), w = a ∨ w = b ∨ w = x 2 ∨ w ∈ A := by
      intro w hw
      rcases PathAttach.mem_cons_append_singleton.mp hw with h | h | h
      · exact Or.inl h
      · rcases hSmem w h with h' | h'
        · exact Or.inr (Or.inr (Or.inl h'))
        · exact Or.inr (Or.inr (Or.inr h'))
      · exact Or.inr (Or.inl h)
    have hXP : ({x 0, x 1} : Set V) ⊆ {v : V | v ∈ (a :: ((x 2 :: R) ++ [b]))}ᶜ := by
      intro v hv hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hQmem v hmem with h | h | h | h
      · rcases hv with rfl | rfl
        · exact (hHyp.1 a haY).2.1 h.symm
        · exact (hHyp.1 a haY).2.2.1 h.symm
      · rcases hv with rfl | rfl
        · exact (hHyp.1 b hbY).2.1 h.symm
        · exact (hHyp.1 b hbY).2.2.1 h.symm
      · rcases hv with rfl | rfl
        · exact hxne 0 2 (by omega) (by omega) (by omega) h
        · exact hxne 1 2 (by omega) (by omega) (by omega) h
      · rcases hv with rfl | rfl
        · exact hxA 0 (by omega) h
        · exact hxA 1 (by omega) h
    have hXanti : AnticonnectedSet G ({x 0, x 1} : Set V) :=
      Thm192Claim8Unique.anticonnected_pair
        (hxne 0 1 (by omega) (by omega) (by omega)) hx01
    have hcomplete : ∀ w ∈ Y, VertexComplete G w ({x 0, x 1} : Set V) := by
      intro w hwY v hv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
      rcases hv with rfl | rfl
      · exact (hHyp.2.2.1 w hwY).symm
      · exact (hHyp.2.2.2.1 w hwY).symm
    have hnotcomplete : ∀ w ∈ (a :: ((x 2 :: R) ++ [b])),
        VertexComplete G w ({x 0, x 1} : Set V) → w = a ∨ w = b := by
      intro w hw hwc
      rcases hQmem w hw with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (hwc (x 1) (by simp)) (by rw [h]; exact fun hc => hx21 hc)
      · exact absurd (hnoc w h ⟨(hwc (x 0) (by simp)).symm, (hwc (x 1) (by simp)).symm⟩)
          (fun hc => hc)
    rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 _ a b hQ hQodd
        ({x 0, x 1} : Set V) hXP hXanti (hcomplete a haY) (hcomplete b hbY) with
      ⟨u, hu, v, hv, hedge'⟩ | ⟨h3, -⟩
    · rcases hnotcomplete u hu hedge'.2.1 with h | h <;>
        rcases hnotcomplete v hv hedge'.2.2 with h' | h'
      · exact absurd (h ▸ h' ▸ hedge'.1) G.irrefl
      · exact hnab (h ▸ h' ▸ hedge'.1)
      · exact hnab (h ▸ h' ▸ hedge'.1).symm
      · exact absurd (h ▸ h' ▸ hedge'.1) G.irrefl
    · rw [hQlen] at h3
      omega
  -- *"By 2.10, `Y` contains a leap or hat for `C₁`."*
  have hDlen4 : 4 < holeLength (x 1 :: z :: (x 2 :: R)) := by
    simp only [holeLength, hDlen]
    omega
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y hHyp.2.1
      (x 1 :: z :: (x 2 :: R)) hD hDY hDlen4 (x 1) z hx1D hzD ((hzx 1 (by omega)).symm)
      hHyp.2.2.2.1 hzY honly with ⟨h, hhY, hhat⟩ | ⟨a, haY, b, hbY, hleap⟩
  · -- no hat: every vertex of `Y` has a neighbour in `A ∪ {x₂}`
    by_cases hc2 : G.Adj h (x 2)
    · exact hhat.2.2.2.2.2.2 (x 2) hx2D
        (hxne 2 1 (by omega) (by omega) (by omega))
        (fun he => hxz 2 (by omega) he) hc2
    · obtain ⟨g, hgA, hg⟩ := hA.2.2.2.2.2.1 h hhY hc2
      exact hhat.2.2.2.2.2.2 g (hAD g hgA) (fun he => hxA 1 (by omega) (he ▸ hgA))
        (fun he => hzAmem (he ▸ hgA)) hg
  · -- a leap at the edge `x₁z`
    have haD : a ∉ (x 1 :: z :: (x 2 :: R)) := fun hc => hDY a hc haY
    have hbD : b ∉ (x 1 :: z :: (x 2 :: R)) := fun hc => hDY b hc hbY
    have hzNbr : ∀ w ∈ (x 1 :: z :: (x 2 :: R)), G.Adj z w → w ≠ x 1 → w = x 2 := by
      intro w hw hadj hne
      rcases hDmem w hw with h | h | h | h
      · exact absurd h hne
      · subst h; exact absurd hadj G.irrefl
      · exact h
      · exact absurd hadj (hzA w h)
    have hx1Nbr : ∀ w ∈ (x 1 :: z :: (x 2 :: R)), G.Adj (x 1) w → w ≠ z → w = fk := by
      intro w hw hadj hne
      rcases hDmem w hw with h | h | h | h
      · subst h; exact absurd hadj G.irrefl
      · exact absurd h hne
      · subst h; exact absurd hadj (fun hc => hx21 hc.symm)
      · exact hu1 w h hadj
    rcases hleap with hl | hl
    · obtain ⟨s, t, hsD, hzs, hsu, hsv, has, htD, h1t, htu, htv, hbt, -, -, -, -,
        hAn, hBn, hab, hnab⟩ := Thm192Claim8Basics.leap_pair hl haD hbD
      have hs2 : s = x 2 := hzNbr s hsD hzs hsu
      have htk : t = fk := hx1Nbr t htD h1t htv
      refine kill a haY b hbY hab hnab (hs2 ▸ has) (htk ▸ hbt) ?_ ?_
      · intro w hw hadj
        rcases hAn w hw hadj with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (hs2 ▸ h))
      · intro w hw hadj
        rcases hBn w hw hadj with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (htk ▸ h))
    · obtain ⟨s, t, hsD, h1s, hsu, hsv, has, htD, hzt, htu, htv, hbt, -, -, -, -,
        hAn, hBn, hab, hnab⟩ := Thm192Claim8Basics.leap_pair hl haD hbD
      have hsk : s = fk := hx1Nbr s hsD h1s hsu
      have ht2 : t = x 2 := hzNbr t htD hzt htv
      refine kill b hbY a haY hab.symm (fun hc => hnab hc.symm) (ht2 ▸ hbt) (hsk ▸ has) ?_ ?_
      · intro w hw hadj
        rcases hBn w hw hadj with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (ht2 ▸ h))
      · intro w hw hadj
        rcases hAn w hw hadj with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr (hsk ▸ h))

end Workspace.ProofLemmas.Thm192Claim8Endgame
