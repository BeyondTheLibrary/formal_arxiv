import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.Thm192Claim4
import Workspace.ProofLemmas.Thm192Claim10
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S17.Thm_17_3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim11

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Unpacking a leap for a hole

`IsLeapForHole G c u v a b` is stated through an unnamed rotation of `c`; all the printed
argument ever uses is *"`a` has exactly three neighbours on the hole, namely `u`, `v` and the
neighbour `s` of `v` other than `u`; `b` has exactly three, namely `u`, `v` and the neighbour
`t` of `u` other than `v`; and `a`, `b` are distinct and nonadjacent"*.  This lemma extracts
exactly that, without ever identifying the rotation. -/
private theorem leap_pair {G : SimpleGraph V} {C : List V} {u v a b : V}
    (hleap : IsLeapForHole G C u v a b) (ha : a ∉ C) (hb : b ∉ C) :
    ∃ s t : V,
      s ∈ C ∧ G.Adj v s ∧ s ≠ u ∧ s ≠ v ∧
      t ∈ C ∧ G.Adj u t ∧ t ≠ u ∧ t ≠ v ∧
      (∀ w ∈ C, G.Adj a w → w = u ∨ w = v ∨ w = s) ∧
      (∀ w ∈ C, G.Adj b w → w = u ∨ w = v ∨ w = t) ∧
      a ≠ b ∧ ¬ G.Adj a b := by
  obtain ⟨hC, i, hhd, hlst, hlp⟩ := hleap
  obtain ⟨hpath, hlen2, hab, hnadj, hA, hB⟩ := hlp
  have hrlen : (C.rotate i).length = C.length := List.length_rotate ..
  have hn4 : 4 ≤ (C.rotate i).length := by rw [hrlen]; exact hC.1
  have hpos : 0 < (C.rotate i).length := by omega
  have hr0 : (C.rotate i)[0]'(by omega) = v :=
    PathBasics.getElem_zero_of_head? hhd hpos
  have hrn : (C.rotate i)[(C.rotate i).length - 1]'(by omega) = u :=
    PathBasics.getElem_last_of_getLast? hlst hpos
  have hmemr : ∀ w : V, w ∈ C.rotate i ↔ w ∈ C := fun w => List.mem_rotate
  have huC : u ∈ C := (hmemr u).mp (by rw [← hrn]; exact List.getElem_mem _)
  have hvC : v ∈ C := (hmemr v).mp (by rw [← hr0]; exact List.getElem_mem _)
  have hau : a ≠ u := fun h => ha (h ▸ huC)
  have hav : a ≠ v := fun h => ha (h ▸ hvC)
  have hbu : b ≠ u := fun h => hb (h ▸ huC)
  have hbv : b ≠ v := fun h => hb (h ▸ hvC)
  -- deleting the edge `uv` does not change adjacency at `a` or at `b`
  have hdelA : ∀ w : V, ((G.deleteEdges {s(u, v)}).Adj a w ↔ G.Adj a w) := by
    intro w
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · refine fun h => ⟨h, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hau h1
      · exact hav h1
  have hdelB : ∀ w : V, ((G.deleteEdges {s(u, v)}).Adj b w ↔ G.Adj b w) := by
    intro w
    rw [SimpleGraph.deleteEdges_adj]
    constructor
    · exact fun h => h.1
    · refine fun h => ⟨h, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hbu h1
      · exact hbv h1
  refine ⟨(C.rotate i)[1]'(by omega), (C.rotate i)[(C.rotate i).length - 2]'(by omega),
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_,
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_, ?_, ?_, hab, ?_⟩
  · -- `G.Adj v (r[1])`
    have h := PathBasics.path_adj_succ hpath (i := 0) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    rw [← hr0]
    exact h'
  · -- `r[1] ≠ u = r[n-1]`
    intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · -- `r[1] ≠ v = r[0]`
    intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · -- `G.Adj u (r[n-2])`
    have h := PathBasics.path_adj_succ hpath (i := (C.rotate i).length - 2) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    have hidx : (C.rotate i)[(C.rotate i).length - 2 + 1]'(by omega)
        = (C.rotate i)[(C.rotate i).length - 1]'(by omega) :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hrn] at h'
    exact h'.symm
  · -- `r[n-2] ≠ u = r[n-1]`
    intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · -- `r[n-2] ≠ v = r[0]`
    intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · -- the neighbours of `a`
    intro w hw hadj
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem ((hmemr w).mpr hw)
    have hiff := hA j hj
    rw [hjw] at hiff
    have := hiff.mp ((hdelA w).mpr hadj)
    rcases this with h | h | h
    · subst h
      refine Or.inr (Or.inl ?_)
      rw [← hjw, ← hr0]
    · subst h
      refine Or.inr (Or.inr ?_)
      rw [← hjw]
    · subst h
      refine Or.inl ?_
      rw [← hjw, ← hrn]
  · -- the neighbours of `b`
    intro w hw hadj
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem ((hmemr w).mpr hw)
    have hiff := hB j hj
    rw [hjw] at hiff
    have := hiff.mp ((hdelB w).mpr hadj)
    rcases this with h | h | h
    · subst h
      refine Or.inr (Or.inl ?_)
      rw [← hjw, ← hr0]
    · subst h
      refine Or.inr (Or.inr ?_)
      rw [← hjw]
    · subst h
      refine Or.inl ?_
      rw [← hjw, ← hrn]
  · -- `a`, `b` nonadjacent in `G`
    intro hcon
    exact hnadj ((hdelA b).mpr hcon)

/-- A singleton is anticonnected. -/
private theorem anticonnected_singleton {G : SimpleGraph V} (v : V) :
    AnticonnectedSet G ({v} : Set V) := by
  intro p q
  exact (Subtype.ext (p.2.trans q.2.symm) ▸ SimpleGraph.Reachable.refl p)

/-- Claim **(11)** of the printed proof: *"`z` is not `Y₀`-complete, and `x₂` is
`Y₀`-complete and nonadjacent to `y`."* -/
theorem claim11 (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (hcex : ¬ Thm192Setup.Concl192 G z A₀ x Y)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hchoice : VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})))
    (f : V) (hfA : f ∈ A) (hfconn : ConnectedSet G (A \ {f})) (hfC : f ∉ P)
    (hfadj : G.Adj (x 2) f) (hfuniq : ∀ a ∈ A, G.Adj (x 2) a → a = f)
    (f₁ : V) (hf₁A : f₁ ∈ A) (hf₁adj : G.Adj (x 1) f₁)
    (hf₁uniq : ∀ a ∈ A, G.Adj (x 1) a → a = f₁)
    (hx2noP : ∀ w ∈ SPGT.interior P, ¬ G.Adj (x 2) w) (hff₁ : f ≠ f₁)
    (Q : List V) (hQ : IsPathFrom G Q f f₁) (hQA : ∀ w ∈ Q, w ∈ A)
    (hC₁ : IsHoleList G (z :: x 2 :: (Q ++ [x 1]))) :
    ¬ VertexComplete G z (Y \ {y}) ∧
      VertexComplete G (x 2) (Y \ {y}) ∧ ¬ G.Adj (x 2) y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hInF5 : InF5 G := hG.1.1
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  -- basic bookkeeping about `z`, the `xⱼ`, `Y` and `A₁`
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hxA1 : ∀ j : ℕ, j ≤ 2 → x j ∉ wheelSystemA G z A₀ x 1 := fun j hj h =>
    Thm192Setup.wheelSystemA_no_z _ h (hzx j hj)
  have hzA1 : z ∉ wheelSystemA G z A₀ x 1 := by
    intro h
    refine Thm192Setup.wheelSystemA_no_complete _ h ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact hzx 0 (by omega)
    · exact hzx 1 (by omega)
  have hYA1 : ∀ w ∈ Y, w ∉ wheelSystemA G z A₀ x 1 := by
    intro w hw h
    refine Thm192Setup.wheelSystemA_no_complete _ h ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact (hHyp.2.2.1 w hw).symm
    · exact (hHyp.2.2.2.1 w hw).symm
  obtain ⟨hyz', hyx0, hyx1, hyx2⟩ := hHyp.1 y hyY
  have hyA : y ∉ A := fun h => Thm192Setup.wheelSystemA_no_z _ (hAsub h) hyz.symm
  have hx2A : x 2 ∉ A := fun h => hxA1 2 (by omega) (hAsub h)
  have hx1A : x 1 ∉ A := fun h => hxA1 1 (by omega) (hAsub h)
  have hx0A : x 0 ∉ A := fun h => hxA1 0 (by omega) (hAsub h)
  have hzAmem : z ∉ A := fun h => hzA1 (hAsub h)
  have hYA : ∀ w ∈ Y, w ∉ A := fun w hw h => hYA1 w hw (hAsub h)
  have hzAdjA : ∀ w ∈ A, ¬ G.Adj z w := fun w hw =>
    Thm192Setup.wheelSystemA_no_z _ (hAsub hw)
  have hnoX1complete : ∀ w ∈ A, ¬ (G.Adj w (x 0) ∧ G.Adj w (x 1)) := by
    intro w hw hcon
    refine Thm192Setup.wheelSystemA_no_complete _ (hAsub hw) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact hcon.1
    · exact hcon.2
  have hx2nex1 : x 2 ≠ x 1 := by
    intro h; have := hws.2.1 2 (by omega) 1 (by omega) h; omega
  have hx2nex0 : x 2 ≠ x 0 := by
    intro h; have := hws.2.1 2 (by omega) 0 (by omega) h; omega
  have hx01 : ¬ G.Adj (x 0) (x 1) := Thm192Setup.x0_not_adj_x1 hws
  -- claim (10)
  obtain ⟨hx2x0, hx2x1⟩ := Thm192Claim10.claim10 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz
    hY0 A hA hAmin hcex P hP hPint hPlen hchoice f hfA hfconn hfC hfadj hfuniq
  -- `Q` bookkeeping
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hQ0f : Q[0]'hQpos = f := PathBasics.getElem_zero_of_head? hQ.2.1 hQpos
  have hQlastf₁ : Q[Q.length - 1]'(by omega) = f₁ :=
    PathBasics.getElem_last_of_getLast? hQ.2.2 hQpos
  have hQlen2 : 2 ≤ Q.length := by
    by_contra hc
    refine hff₁ ?_
    rw [← hQ0f, ← hQlastf₁]
    exact HoleArithmetic.getElem_congr_idx Q hQpos (by omega) (by omega)
  have hx2f₁ : ¬ G.Adj (x 2) f₁ := fun h => hff₁ (hfuniq f₁ hf₁A h).symm
  have hx2nef₁ : x 2 ≠ f₁ := fun h => hx2A (h ▸ hf₁A)
  have hznef₁ : z ≠ f₁ := fun h => hzAmem (h ▸ hf₁A)
  have hznef : z ≠ f := fun h => hzAmem (h ▸ hfA)
  have hzf₁ : ¬ G.Adj z f₁ := hzAdjA f₁ hf₁A
  -- membership decomposition for the hole `C₁`
  have hx1nex0 : x 1 ≠ x 0 := by
    intro h; have := hws.2.1 1 (by omega) 0 (by omega) h; omega
  have hmemC₁ : ∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), w = z ∨ w = x 2 ∨ w ∈ Q ∨ w = x 1 := by
    intro w hw
    simp only [List.mem_cons, List.mem_append] at hw
    tauto
  have hzC₁ : z ∈ (z :: x 2 :: (Q ++ [x 1])) := List.mem_cons_self
  have hx2C₁ : x 2 ∈ (z :: x 2 :: (Q ++ [x 1])) := List.mem_cons_of_mem _ List.mem_cons_self
  have hx1C₁ : x 1 ∈ (z :: x 2 :: (Q ++ [x 1])) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ (by simp)))
  have hf₁C₁ : f₁ ∈ (z :: x 2 :: (Q ++ [x 1])) := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ ?_))
    rw [← hQlastf₁]; exact List.getElem_mem _
  -- the two hole-neighbour facts
  have hnbrz : ∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), G.Adj z w → w = x 2 ∨ w = x 1 := by
    intro w hw hadj
    rcases hmemC₁ w hw with h | h | h | h
    · exact absurd (h ▸ hadj) G.irrefl
    · exact Or.inl h
    · exact absurd hadj (hzAdjA w (hQA w h))
    · exact Or.inr h
  have hnbrx1 : ∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), G.Adj (x 1) w → w = f₁ ∨ w = z := by
    intro w hw hadj
    rcases hmemC₁ w hw with h | h | h | h
    · exact Or.inr h
    · exact absurd (h ▸ hadj) (fun hc => hx2x1 hc.symm)
    · exact Or.inl (hf₁uniq w (hQA w h) hadj)
    · exact absurd (h ▸ hadj) G.irrefl
  -- ##################  the main reductio  ##################
  have hznot : ¬ VertexComplete G z (Y \ {y}) := by
    intro hzY0
    -- `z` is `Y`-complete
    have hzY : VertexComplete G z Y := by
      intro w hw
      by_cases hwy : w = y
      · rw [hwy]; exact hyz.symm
      · exact hzY0 w ⟨hw, by simpa using hwy⟩
    -- `f₁ = pₙ`, and by (4) `f₁` is not `Y`-complete
    have hn2 : P.length - 2 < P.length := by omega
    have hn1 : P.length - 1 < P.length := by omega
    have hP0 : P[0]'(by omega) = x 0 :=
      PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have hPn : P[P.length - 1]'hn1 = x 1 :=
      PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    have hadjn : G.Adj (P[P.length - 2]'hn2) (P[P.length - 1]'hn1) := by
      have h := PathBasics.path_adj_succ hP.1 (i := P.length - 2) (by omega)
      have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hn1 :=
        HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
      rwa [hidx] at h
    have hpnint : (P[P.length - 2]'hn2) ∈ SPGT.interior P := by
      rw [PathBasics.mem_interior_iff_of_pathFrom hP]
      refine ⟨List.getElem_mem _, ?_, ?_⟩
      · rw [← hP0]
        exact PathBasics.path_ne_of_ne_index hP.1 hn2 (by omega) (by omega)
      · rw [← hPn]
        exact PathBasics.path_ne_of_ne_index hP.1 hn2 hn1 (by omega)
    have hpnf₁ : (P[P.length - 2]'hn2) = f₁ :=
      hf₁uniq _ (hPint _ hpnint) (by rw [← hPn]; exact hadjn.symm)
    have h4 := Thm192Claim4.claim4 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA
      hAmin hcex P hP hPint hPlen
    have hf₁notY : ¬ VertexComplete G f₁ Y := by
      intro hc
      refine h4.2.1 hzY (P.length - 2) (by omega) ⟨?_, ?_, ?_⟩
      · exact PathBasics.path_adj_succ hP.1 (by omega)
      · rw [hpnf₁]; exact hc
      · have hidx : P[P.length - 2 + 1]'(by omega) = P[P.length - 1]'hn1 :=
          HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
        rw [hidx, hPn]
        exact hHyp.2.2.2.1
    -- ### the set `F = A ∪ {x₂}` and the two applications of 17.3
    have hFconn : ConnectedSet G (A ∪ ({x 2} : Set V)) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hA.2.1 ⟨f, hfA, hfadj⟩
    have hFdiff : (A ∪ ({x 2} : Set V)) \ {x 2} = A := by
      ext w
      simp only [Set.mem_diff, Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hne⟩
        · exact h
        · exact absurd h hne
      · intro h
        exact ⟨Or.inl h, fun hw => hx2A (hw ▸ h)⟩
    have hFa : ConnectedSet G ((A ∪ ({x 2} : Set V)) \ {x 2}) := by
      rw [hFdiff]; exact hA.2.1
    have hx2F : x 2 ∈ A ∪ ({x 2} : Set V) := Or.inr rfl
    have hf₁F : f₁ ∈ A ∪ ({x 2} : Set V) := Or.inl hf₁A
    have hzF : z ∉ A ∪ ({x 2} : Set V) := by
      rintro (h | h)
      · exact hzAmem h
      · exact (hzx 2 (by omega)).ne (by simpa using h)
    have hx1F : x 1 ∉ A ∪ ({x 2} : Set V) := by
      rintro (h | h)
      · exact hx1A h
      · exact hx2nex1 (show x 1 = x 2 from h).symm
    -- the 3-edge path `x₂-z-x₁-f₁`
    have hzx1path : IsPathFrom G [z, x 1] z (x 1) :=
      ⟨PathBasics.isPathList_pair (hzx 1 (by omega)), rfl, rfl⟩
    have hp4 : IsPathFrom G (x 2 :: ([z, x 1] ++ [f₁])) (x 2) f₁ := by
      refine PathAttach.isPathFrom_cons_concat hzx1path ((hzx 2 (by omega)).symm)
        hf₁adj.symm hx2f₁ hx2nef₁ ?_ ?_ ?_ ?_
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · exact (hzx 2 (by omega)).ne h.symm
        · exact hx2nex1 h
      · intro hmem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        rcases hmem with h | h
        · exact hznef₁ h.symm
        · exact hx1A (h ▸ hf₁A)
      · intro w hw hwz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with h | h
        · exact absurd h hwz
        · rw [h]; exact hx2x1
      · intro w hw hw1
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with h | h
        · rw [h]; exact fun hc => hzf₁ hc.symm
        · exact absurd h hw1
    have hpath4 : IsPathList G [x 2, z, x 1, f₁] := hp4.1
    have hdisjFY : Disjoint (A ∪ ({x 2} : Set V)) Y := by
      rw [Set.disjoint_left]
      rintro w (h | h) hwY
      · exact hYA w hwY h
      · exact (hHyp.1 w hwY).2.2.2 h
    have ha₀F : {g ∈ A ∪ ({x 2} : Set V) | G.Adj z g} = ({x 2} : Set V) := by
      refine Thm192Infra.uniqueNeighbourSetForm.mpr ⟨hx2F, (hzx 2 (by omega)), ?_⟩
      rintro w (h | h) hadj
      · exact absurd hadj (hzAdjA w h)
      · exact h
    have hb₀F : {g ∈ A ∪ ({x 2} : Set V) | G.Adj (x 1) g} = ({f₁} : Set V) := by
      refine Thm192Infra.uniqueNeighbourSetForm.mpr ⟨hf₁F, hf₁adj, ?_⟩
      rintro w (h | h) hadj
      · exact hf₁uniq w h hadj
      · exact absurd (show G.Adj (x 1) (x 2) from (show w = x 2 from h) ▸ hadj)
          (fun hc => hx2x1 hc.symm)
    have hzFY : z ∉ (A ∪ ({x 2} : Set V)) ∪ Y := by
      rintro (h | h)
      · exact hzF h
      · exact (hHyp.1 z h).1 rfl
    have hx1FY : x 1 ∉ (A ∪ ({x 2} : Set V)) ∪ Y := by
      rintro (h | h)
      · exact hx1F h
      · exact (hHyp.1 (x 1) h).2.2.1 rfl
    -- **first application of 17.3**, with the anticonnected set `Y`
    obtain ⟨w₀, hw₀Y, hw₀anti⟩ :=
      _root_.Workspace.Statements.S17.SPGT.thm_17_3 G hG (A ∪ ({x 2} : Set V)) Y
        hdisjFY hFconn hHyp.2.1 z (x 1) (x 2) f₁ hzFY hx1FY
        hx2F hf₁F hpath4 hzY hHyp.2.2.2.1 hHyp.2.2.2.2.1 hf₁notY ha₀F hb₀F hFa
    rw [hFdiff] at hw₀anti
    -- `w₀ ≠ y`, because `y` has a neighbour in `A`
    obtain ⟨ay, hayA, hyay⟩ := hA.2.2.2.2.2.2
    have hw₀ney : w₀ ≠ y := by
      intro h
      exact hw₀anti ay hayA (by rw [h]; exact hyay)
    have hw₀Y0 : w₀ ∈ Y \ {y} := ⟨hw₀Y, by simpa using hw₀ney⟩
    -- so there is no `Y₀`-complete vertex in `A`
    have hnoY0 : ∀ a ∈ A, ¬ VertexComplete G a (Y \ {y}) := by
      intro a haA hac
      exact hw₀anti a haA (hac w₀ hw₀Y0).symm
    -- ### by (2), `x₂` is `Y₀`-complete and nonadjacent to `y`
    have h2 := Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
    obtain ⟨hx2Y0, hx2ny⟩ : VertexComplete G (x 2) (Y \ {y}) ∧ ¬ G.Adj (x 2) y := by
      rcases h2 with h | ⟨-, P', hP', hP'int, hcard⟩
      · exact h
      · exfalso
        have hne : ({e : Sym2 V | ∃ u ∈ P', ∃ v ∈ P', e = s(u, v) ∧
            EdgeComplete G (Y \ {y}) u v}).Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by omega)
        obtain ⟨e, u, hu, v, hv, heq, hadjuv, hcu, hcv⟩ := hne
        have hkey : ∀ w ∈ P', VertexComplete G w (Y \ {y}) → w = x 0 ∨ w = x 1 := by
          intro w hw hwc
          by_contra hcon
          rw [not_or] at hcon
          exact hnoY0 w
            (hP'int w ((PathBasics.mem_interior_iff_of_pathFrom hP').mpr
              ⟨hw, hcon.1, hcon.2⟩)) hwc
        rcases hkey u hu hcu with h | h <;> rcases hkey v hv hcv with h' | h'
        · exact hadjuv.ne (h.trans h'.symm)
        · rw [h, h'] at hadjuv; exact hx01 hadjuv
        · rw [h, h'] at hadjuv; exact hx01 hadjuv.symm
        · exact hadjuv.ne (h.trans h'.symm)
    -- **second application of 17.3**, with the anticonnected set `{y}`
    have hyf₁ : G.Adj f₁ y := by
      by_contra hnadj
      have hdisjFy : Disjoint (A ∪ ({x 2} : Set V)) ({y} : Set V) := by
        rw [Set.disjoint_left]
        rintro w (h | h) hwy
        · exact hyA ((show w = y from hwy) ▸ h)
        · exact hyx2 ((show w = y from hwy).symm.trans (show w = x 2 from h))
      have hzFy : z ∉ (A ∪ ({x 2} : Set V)) ∪ ({y} : Set V) := by
        rintro (h | h)
        · exact hzF h
        · exact hyz' (show z = y from h).symm
      have hx1Fy : x 1 ∉ (A ∪ ({x 2} : Set V)) ∪ ({y} : Set V) := by
        rintro (h | h)
        · exact hx1F h
        · exact hyx1 (show x 1 = y from h).symm
      have hzy : VertexComplete G z ({y} : Set V) := by
        intro w hw; rw [show w = y from hw]; exact hyz.symm
      have hx1y : VertexComplete G (x 1) ({y} : Set V) := by
        intro w hw; rw [show w = y from hw]; exact hHyp.2.2.2.1 y hyY
      obtain ⟨w₁, hw₁, hw₁anti⟩ :=
        _root_.Workspace.Statements.S17.SPGT.thm_17_3 G hG (A ∪ ({x 2} : Set V))
          ({y} : Set V) hdisjFy hFconn (anticonnected_singleton y) z (x 1) (x 2) f₁
          hzFy hx1Fy hx2F hf₁F hpath4 hzy hx1y
          (fun hc => hx2ny (hc y rfl)) (fun hc => hnadj (hc y rfl)) ha₀F hb₀F hFa
      rw [hFdiff] at hw₁anti
      rw [show w₁ = y from hw₁] at hw₁anti
      exact hw₁anti ay hayA hyay
    -- ### 2.10 applied to the hole `C₁` at the `Y`-complete edge `zx₁`
    have hC₁len : 4 < holeLength (z :: x 2 :: (Q ++ [x 1])) := by
      simp only [holeLength, List.length_cons, List.length_append, List.length_nil]
      omega
    have hnotY : ∀ w ∈ A, ¬ VertexComplete G w Y := by
      intro w hw hc
      exact hnoY0 w hw (fun v hv => hc v hv.1)
    have honly : ∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), VertexComplete G w Y →
        w = z ∨ w = x 1 := by
      intro w hw hwc
      rcases hmemC₁ w hw with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hwc) hHyp.2.2.2.2.1
      · exact absurd hwc (hnotY w (hQA w h))
      · exact Or.inr h
    have hcX : ∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), w ∉ Y := by
      intro w hw hwY
      rcases hmemC₁ w hw with h | h | h | h
      · exact (hHyp.1 w hwY).1 h
      · exact (hHyp.1 w hwY).2.2.2 h
      · exact hYA w hwY (hQA w h)
      · exact (hHyp.1 w hwY).2.2.1 h
    have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y hHyp.2.1
      (z :: x 2 :: (Q ++ [x 1])) hC₁ hcX hC₁len z (x 1) hzC₁ hx1C₁ (hzx 1 (by omega))
      hzY hHyp.2.2.2.1 honly
    -- ### no hat
    have hnohat : ∀ h ∈ Y, ¬ IsHatForHole G (z :: x 2 :: (Q ++ [x 1])) z (x 1) h := by
      intro h hhY hhat
      by_cases hhy : h = y
      · refine hhat.2.2.2.2.2.2 f₁ hf₁C₁ hznef₁.symm ?_ ?_
        · exact fun hc => hx1A (hc ▸ hf₁A)
        · rw [hhy]; exact hyf₁.symm
      · refine hhat.2.2.2.2.2.2 (x 2) hx2C₁ (fun hc => (hzx 2 (by omega)).ne hc.symm)
          hx2nex1 ?_
        exact (hx2Y0 h ⟨hhY, by simpa using hhy⟩).symm
    -- ### so there is a leap
    obtain ⟨hh, hhY, hhat⟩ | ⟨a, haY, b, hbY, hleap⟩ := h210
    · exact hnohat hh hhY hhat
    have haC₁ : a ∉ (z :: x 2 :: (Q ++ [x 1])) := fun h => hcX a h haY
    have hbC₁ : b ∉ (z :: x 2 :: (Q ++ [x 1])) := fun h => hcX b h hbY
    -- normalise the two orientations of the leap into `(c, d)`:
    -- `c`'s only hole-neighbours are `z, x₁, f₁`; `d`'s are `z, x₁, x₂`.
    obtain ⟨c, d, hcY, hdY, hcd, hncd, hcnbr, hdnbr⟩ :
        ∃ c d : V, c ∈ Y ∧ d ∈ Y ∧ c ≠ d ∧ ¬ G.Adj c d ∧
          (∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), G.Adj c w → w = z ∨ w = x 1 ∨ w = f₁) ∧
          (∀ w ∈ (z :: x 2 :: (Q ++ [x 1])), G.Adj d w → w = z ∨ w = x 1 ∨ w = x 2) := by
      rcases hleap with hl | hl
      · -- `u = z`, `v = x₁`: `s` is the neighbour of `x₁` other than `z`, i.e. `f₁`;
        -- `t` is the neighbour of `z` other than `x₁`, i.e. `x₂`.
        obtain ⟨s, t, hsC, hvs, hsu, hsv, htC, hut, htu, htv, hAn, hBn, hab, hnab⟩ :=
          leap_pair hl haC₁ hbC₁
        have hs : s = f₁ := by
          rcases hnbrx1 s hsC hvs with h | h
          · exact h
          · exact absurd h hsu
        have ht : t = x 2 := by
          rcases hnbrz t htC hut with h | h
          · exact h
          · exact absurd h htv
        refine ⟨a, b, haY, hbY, hab, hnab, ?_, ?_⟩
        · intro w hw hadj
          rcases hAn w hw hadj with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (by rw [h, hs]))
        · intro w hw hadj
          rcases hBn w hw hadj with h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (by rw [h, ht]))
      · -- `u = x₁`, `v = z`: `s` is the neighbour of `z` other than `x₁`, i.e. `x₂`;
        -- `t` is the neighbour of `x₁` other than `z`, i.e. `f₁`.
        obtain ⟨s, t, hsC, hvs, hsu, hsv, htC, hut, htu, htv, hAn, hBn, hab, hnab⟩ :=
          leap_pair hl haC₁ hbC₁
        have hs : s = x 2 := by
          rcases hnbrz s hsC hvs with h | h
          · exact h
          · exact absurd h hsu
        have ht : t = f₁ := by
          rcases hnbrx1 t htC hut with h | h
          · exact h
          · exact absurd h htv
        refine ⟨b, a, hbY, haY, hab.symm, fun hc => hnab hc.symm, ?_, ?_⟩
        · intro w hw hadj
          rcases hBn w hw hadj with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr (by rw [h, ht]))
        · intro w hw hadj
          rcases hAn w hw hadj with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr (by rw [h, hs]))
    -- `c = y`, since `c` is not adjacent to `x₂` while every member of `Y₀` is
    have hcy : c = y := by
      by_contra hcne
      have hcY0 : c ∈ Y \ {y} := ⟨hcY, by simpa using hcne⟩
      rcases hcnbr (x 2) hx2C₁ (hx2Y0 c hcY0).symm with h | h | h
      · exact (hzx 2 (by omega)).ne h.symm
      · exact hx2nex1 h
      · exact hx2nef₁ h
    have hdney : d ≠ y := fun h => hcd (hcy.trans h.symm)
    have hdY0 : d ∈ Y \ {y} := ⟨hdY, by simpa using hdney⟩
    have hdx2 : G.Adj d (x 2) := (hx2Y0 d hdY0).symm
    have hdA : d ∉ A := hYA d hdY
    have hynbr : ∀ w ∈ Q, G.Adj y w → w = f₁ := by
      intro w hw hadj
      rcases hcnbr w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ hw))) (by rw [hcy]; exact hadj) with h | h | h
      · exact absurd (h ▸ hQA w hw) hzAmem
      · exact absurd (h ▸ hQA w hw) hx1A
      · exact h
    have hdnbrQ : ∀ w ∈ Q, ¬ G.Adj d w := by
      intro w hw hadj
      rcases hdnbr w (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_append_left _ hw))) hadj with h | h | h
      · exact hzAmem (h ▸ hQA w hw)
      · exact hx1A (h ▸ hQA w hw)
      · exact hx2A (h ▸ hQA w hw)
    have hydny : ¬ G.Adj y d := by rw [← hcy]; exact hncd
    -- ### the path `y-f₁-Q-f-x₂-d`
    have hQrev : IsPathFrom G Q.reverse f₁ f := PathBasics.isPathFrom_reverse hQ
    have hmemrev : ∀ w : V, w ∈ Q.reverse ↔ w ∈ Q := fun w => List.mem_reverse
    have hR1 : IsPathFrom G (Q.reverse ++ [x 2]) f₁ (x 2) := by
      refine PathAttach.isPathFrom_concat hQrev hfadj
        (fun h => hx2A (hQA _ ((hmemrev _).mp h))) ?_
      intro w hw hwf hadj
      exact hwf (hfuniq w (hQA w ((hmemrev w).mp hw)) hadj)
    have hdR1 : d ∉ Q.reverse ++ [x 2] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · exact hdA (hQA _ ((hmemrev _).mp h))
      · exact (hHyp.1 d hdY).2.2.2 (by simpa using h)
    have hR2 : IsPathFrom G ((Q.reverse ++ [x 2]) ++ [d]) f₁ d := by
      refine PathAttach.isPathFrom_concat hR1 hdx2 hdR1 ?_
      intro w hw hw2 hadj
      rcases List.mem_append.mp hw with h | h
      · exact hdnbrQ w ((hmemrev w).mp h) hadj
      · exact hw2 (by simpa using h)
    have hyR2 : y ∉ (Q.reverse ++ [x 2]) ++ [d] := by
      intro h
      rcases List.mem_append.mp h with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hyA (hQA _ ((hmemrev _).mp h))
        · exact hyx2 (by simpa using h)
      · exact hdney (show y = d from by simpa using h).symm
    have hpathfin : IsPathFrom G (y :: ((Q.reverse ++ [x 2]) ++ [d])) y d := by
      refine PathAttach.isPathFrom_cons hR2 hyf₁.symm hyR2 ?_
      intro w hw hwf₁ hadj
      rcases List.mem_append.mp hw with h | h
      · rcases List.mem_append.mp h with h | h
        · exact hwf₁ (hynbr w ((hmemrev w).mp h) hadj)
        · have hw2 : w = x 2 := by simpa using h
          rw [hw2] at hadj
          exact hx2ny hadj.symm
      · have hwd : w = d := by simpa using h
        rw [hwd] at hadj
        exact hydny hadj
    -- length and parity
    have hlenfin : (y :: ((Q.reverse ++ [x 2]) ++ [d])).length = Q.length + 3 := by
      simp only [List.length_cons, List.length_append, List.length_nil,
        List.length_reverse]
    have hplenfin : pathLength (y :: ((Q.reverse ++ [x 2]) ++ [d])) = Q.length + 2 := by
      rw [PathBasics.pathLength_eq, hlenfin]
      omega
    have hQodd : Odd (Q.length + 2) := by
      have heven : Even (holeLength (z :: x 2 :: (Q ++ [x 1]))) :=
        hBerge.1 _ hC₁
      have hlen : holeLength (z :: x 2 :: (Q ++ [x 1])) = Q.length + 3 := by
        simp only [holeLength, List.length_cons, List.length_append, List.length_nil]
      rw [hlen] at heven
      obtain ⟨m, hm⟩ := heven
      exact ⟨m - 1, by omega⟩
    -- the anticonnected set `{x₀, x₁}`
    have hX01set : ({x 0, x 1} : Set V) = ({x 0} : Set V) ∪ {x 1} := by
      ext w; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    have hX01 : AnticonnectedSet G ({x 0, x 1} : Set V) := by
      rw [hX01set]
      refine ConnectedSetUnionAttach.connectedSet_union_singleton
        (anticonnected_singleton (G := G) (x 0)) ⟨x 0, rfl, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨hx1nex0, fun h => hx01 h.symm⟩
    have hXP : ({x 0, x 1} : Set V) ⊆ {v : V | v ∈ y :: ((Q.reverse ++ [x 2]) ++ [d])}ᶜ := by
      intro w hw hmem
      have hcases : w = y ∨ w ∈ Q ∨ w = x 2 ∨ w = d := by
        rcases List.mem_cons.mp hmem with h | h
        · exact Or.inl h
        rcases List.mem_append.mp h with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr (Or.inl ((hmemrev w).mp h))
          · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
        · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · rcases hcases with h | h | h | h
        · exact hyx0 h.symm
        · exact hx0A (hQA _ h)
        · exact hx2nex0 h.symm
        · exact (hHyp.1 d hdY).2.1 h.symm
      · rcases hcases with h | h | h | h
        · exact hyx1 h.symm
        · exact hx1A (hQA _ h)
        · exact hx2nex1 h.symm
        · exact (hHyp.1 d hdY).2.2.1 h.symm
    have hycomp : VertexComplete G y ({x 0, x 1} : Set V) := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact (hHyp.2.2.1 y hyY).symm
      · exact (hHyp.2.2.2.1 y hyY).symm
    have hdcomp : VertexComplete G d ({x 0, x 1} : Set V) := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl
      · exact (hHyp.2.2.1 d hdY).symm
      · exact (hHyp.2.2.2.1 d hdY).symm
    have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hInF5
      (y :: ((Q.reverse ++ [x 2]) ++ [d])) y d hpathfin (by rw [hplenfin]; exact hQodd)
      ({x 0, x 1} : Set V) hXP hX01 hycomp hdcomp
    rcases h136 with ⟨u, hu, v, hv, hedge⟩ | ⟨hl3, -⟩
    · -- the only `{x₀,x₁}`-complete vertices of the path are its two ends `y`, `d`
      have hends : ∀ w ∈ (y :: ((Q.reverse ++ [x 2]) ++ [d])),
          VertexComplete G w ({x 0, x 1} : Set V) → w = y ∨ w = d := by
        intro w hw hwc
        have hcases : w = y ∨ w ∈ Q ∨ w = x 2 ∨ w = d := by
          rcases List.mem_cons.mp hw with h | h
          · exact Or.inl h
          rcases List.mem_append.mp h with h | h
          · rcases List.mem_append.mp h with h | h
            · exact Or.inr (Or.inl ((hmemrev w).mp h))
            · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
          · exact Or.inr (Or.inr (Or.inr (by simpa using h)))
        rcases hcases with h | h | h | h
        · exact Or.inl h
        · exact absurd ⟨hwc (x 0) (by simp), hwc (x 1) (by simp)⟩ (hnoX1complete w (hQA w h))
        · exact absurd (by rw [← h]; exact hwc (x 0) (by simp)) hx2x0
        · exact Or.inr h
      rcases hends u hu hedge.2.1 with rfl | rfl
      · rcases hends v hv hedge.2.2 with rfl | rfl
        · exact G.irrefl hedge.1
        · exact hydny hedge.1
      · rcases hends v hv hedge.2.2 with rfl | rfl
        · exact hydny hedge.1.symm
        · exact G.irrefl hedge.1
    · rw [hplenfin] at hl3
      omega
  -- ################## the claim follows from (2) ##################
  refine ⟨hznot, ?_, ?_⟩
  · rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      with h | ⟨hzY, -⟩
    · exact h.1
    · exact absurd (fun w hw => hzY w hw.1) hznot
  · rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin
      with h | ⟨hzY, -⟩
    · exact h.2
    · exact absurd (fun w hw => hzY w hw.1) hznot

end Workspace.ProofLemmas.Thm192Claim11
