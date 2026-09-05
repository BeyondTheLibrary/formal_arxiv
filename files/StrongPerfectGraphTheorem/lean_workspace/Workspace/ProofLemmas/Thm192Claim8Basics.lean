import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.Thm192Claim2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleArithmetic

/-!
# Small general facts used by claim (8) of 19.2

Three groups:

* `exists_nonadj_of_anticonnected` — an anticonnected set with two distinct members gives each
  of them a nonneighbour in the set.  This is what feeds
  `InducedPathExtraction.exists_antipath_interior_in` at every *"let `Q` be an antipath
  between `u,v` with interior in `Y₀`"* of the printed proof.
* `leap_pair` — the extractor for `IsLeapForHole`, in the form claim (8) needs: besides the
  *"`a`'s hole neighbours are among `u, v, s`"* bound it also returns `G.Adj a s`, since the
  printed proof of (8) builds the path `y₁-x₂-f₁-⋯-f_k-y₂` out of the leap.
* `hole_zP`, `P_length_ge_five`, `choiceOfPath` — the *"let us choose `p₁,…,pₙ` and `C` such
  that either `x₂` is `Y₀`-complete or `(C,Y₀)` is a wheel"* package, re-derived for a path
  `P` **chosen by the caller**, which is what claim (8) needs when it applies claim (7) to
  the path `x₀-f₁-⋯-f_k-x₁` built out of `A`.  The transfer is legitimate because claim (2)'s
  `Y₀`-complete edge has both ends in `{x₀,x₁} ∪ A`, and `A` is contained in the caller's
  path.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Claim8Basics

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In an anticonnected set, a vertex with a companion has a nonneighbour in the set. -/
theorem exists_nonadj_of_anticonnected {G : SimpleGraph V} {S : Set V}
    (hS : AnticonnectedSet G S) {u w : V} (hu : u ∈ S) (hw : w ∈ S) (hne : u ≠ w) :
    ∃ v ∈ S, v ≠ u ∧ ¬ G.Adj u v := by
  obtain ⟨p⟩ := hS ⟨u, hu⟩ ⟨w, hw⟩
  have hlen : 0 < p.length := by
    rcases Nat.eq_zero_or_pos p.length with h | h
    · exact absurd (congrArg Subtype.val (SimpleGraph.Walk.eq_of_length_eq_zero h)) hne
    · exact h
  have hadj := p.adj_getVert_succ (i := 0) hlen
  rw [SimpleGraph.Walk.getVert_zero] at hadj
  have hadj' : Gᶜ.Adj u ((p.getVert 1 : ↥S) : V) := hadj
  refine ⟨((p.getVert 1 : ↥S) : V), (p.getVert 1).2, ?_, ?_⟩
  · exact fun he => ((SimpleGraph.compl_adj G u _).mp hadj').1 he.symm
  · exact ((SimpleGraph.compl_adj G u _).mp hadj').2

/-- The extractor for `IsLeapForHole`, returning also the two adjacencies. -/
theorem leap_pair {G : SimpleGraph V} {C : List V} {u v a b : V}
    (hleap : IsLeapForHole G C u v a b) (ha : a ∉ C) (hb : b ∉ C) :
    ∃ s t : V,
      s ∈ C ∧ G.Adj v s ∧ s ≠ u ∧ s ≠ v ∧ G.Adj a s ∧
      t ∈ C ∧ G.Adj u t ∧ t ≠ u ∧ t ≠ v ∧ G.Adj b t ∧
      G.Adj a u ∧ G.Adj a v ∧ G.Adj b u ∧ G.Adj b v ∧
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
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_, ?_,
    (hmemr _).mp (List.getElem_mem _), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hab, ?_⟩
  · have h := PathBasics.path_adj_succ hpath (i := 0) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    rw [← hr0]
    exact h'
  · intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · exact (hdelA _).mp ((hA 1 (by omega)).mpr (Or.inr (Or.inl rfl)))
  · have h := PathBasics.path_adj_succ hpath (i := (C.rotate i).length - 2) (by omega)
    have h' := (SimpleGraph.deleteEdges_adj.mp h).1
    have hidx : (C.rotate i)[(C.rotate i).length - 2 + 1]'(by omega)
        = (C.rotate i)[(C.rotate i).length - 1]'(by omega) :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hrn] at h'
    exact h'.symm
  · intro hcon
    rw [← hrn] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · intro hcon
    rw [← hr0] at hcon
    exact PathBasics.path_ne_of_ne_index hpath (by omega) (by omega) (by omega) hcon
  · exact (hdelB _).mp ((hB _ (by omega)).mpr (Or.inr (Or.inl rfl)))
  · rw [← hrn]
    exact (hdelA _).mp ((hA _ (by omega)).mpr (Or.inr (Or.inr rfl)))
  · rw [← hr0]
    exact (hdelA _).mp ((hA 0 (by omega)).mpr (Or.inl rfl))
  · rw [← hrn]
    exact (hdelB _).mp ((hB _ (by omega)).mpr (Or.inr (Or.inr rfl)))
  · rw [← hr0]
    exact (hdelB _).mp ((hB 0 (by omega)).mpr (Or.inl rfl))
  · intro w hw hadj
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
  · intro w hw hadj
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
  · intro hcon
    exact hnadj ((hdelA b).mpr hcon)


/-! ### The rim `z-x₀-P-x₁-z` and the choice of claim (2), for a caller-chosen path -/

/-- `z ∉ A` whenever `A ⊆ A₁`: `z` is `{x₀,x₁}`-complete. -/
theorem z_notMem {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {A : Set V}
    (hws : IsWheelSystem G z A₀ x 2) (hAsub : A ⊆ wheelSystemA G z A₀ x 1) : z ∉ A := by
  intro hz
  refine Thm192Setup.wheelSystemA_no_complete _ (hAsub hz) ?_
  rw [Thm192Setup.wheelSystemX_one]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact hws.2.2.2.2.2.2 0 (by omega)
  · exact hws.2.2.2.2.2.2 1 (by omega)

/-- No vertex of `A ⊆ A₁` is `{x₀,x₁}`-complete. -/
theorem no_X1_complete {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {A : Set V}
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1) :
    ∀ a ∈ A, ¬ (G.Adj a (x 0) ∧ G.Adj a (x 1)) := by
  intro a ha hc
  refine Thm192Setup.wheelSystemA_no_complete _ (hAsub ha) ?_
  rw [Thm192Setup.wheelSystemX_one]
  intro w hw
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
  rcases hw with rfl | rfl
  · exact hc.1
  · exact hc.2

/-- `z ∉ P` for any `x₀`--`x₁` path with interior in `A`. -/
theorem z_notMem_path {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {A : Set V}
    {P : List V} (hws : IsWheelSystem G z A₀ x 2) (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    (hP : IsPathFrom G P (x 0) (x 1)) (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) : z ∉ P := by
  intro hzP
  by_cases h0 : z = x 0
  · exact (hws.2.2.1 0 (by omega)).2 h0.symm
  by_cases h1 : z = x 1
  · exact (hws.2.2.1 1 (by omega)).2 h1.symm
  · exact z_notMem hws hAsub
      (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hzP, h0, h1⟩))

/-- *"let `C` be the hole `z-x₀-p₁-⋯-pₙ-x₁-z`"*. -/
theorem hole_zP {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {A : Set V}
    {P : List V} (hws : IsWheelSystem G z A₀ x 2) (hAsub : A ⊆ wheelSystemA G z A₀ x 1)
    (hP : IsPathFrom G P (x 0) (x 1)) (hPint : ∀ w ∈ SPGT.interior P, w ∈ A)
    (hPlen : 3 ≤ P.length) : IsHoleList G (z :: P) := by
  refine PrismBasics.isHoleList_of_path_add_vertex hP (by rw [PathBasics.pathLength_eq]; omega)
    (hws.2.2.2.2.2.2 0 (by omega)) (hws.2.2.2.2.2.2 1 (by omega))
    (z_notMem_path hws hAsub hP hPint) ?_
  intro w hw
  exact Thm192Setup.wheelSystemA_no_z _ (hAsub (hPint w hw))

/-- The rim has at least six vertices, so `P` has at least five. -/
theorem P_length_ge_five {G : SimpleGraph V} (hB : Berge G) {z : V} {A₀ : Set V}
    {x : ℕ → V} {A : Set V} {P : List V} (hws : IsWheelSystem G z A₀ x 2)
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length) : 5 ≤ P.length := by
  have hhole := hole_zP hws hAsub hP hPint hPlen
  have heven := hB.1 _ hhole
  simp only [holeLength, List.length_cons] at heven
  have hne3 : P.length ≠ 3 := by
    intro h3
    have hpos : 0 < P.length := by omega
    have h0 : P[0]'hpos = x 0 := PathBasics.getElem_zero_of_head? hP.2.1 hpos
    have hl : P[P.length - 1]'(by omega) = x 1 :=
      PathBasics.getElem_last_of_getLast? hP.2.2 hpos
    have h01 := PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
    have h12 := PathBasics.path_adj_succ hP.1 (i := 1) (by omega)
    rw [h0] at h01
    have hidx : P[1 + 1]'(by omega) = P[P.length - 1]'(by omega) :=
      HoleArithmetic.getElem_congr_idx _ _ _ (by omega)
    rw [hidx, hl] at h12
    exact no_X1_complete hAsub _
      (hPint _ (PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)))
      ⟨h01.symm, h12⟩
  rcases heven with ⟨m, hm⟩
  omega

/-- *"Let us choose `p₁,…,pₙ` and `C` such that either `x₂` is `Y₀`-complete or `(C,Y₀)`
is a wheel (this is possible by (2))."* — for a path `P` chosen by the caller, provided
`A` is contained in `P`.  Claim (2)'s `Y₀`-complete edge has both ends in `{x₀,x₁} ∪ A`,
hence in `P`, and its two `Y₀`-complete interior vertices lie in `A`, hence in the interior
of `P`. -/
theorem choiceOfPath (G : SimpleGraph V) (hG : InF7 G) (z : V) (A₀ : Set V)
    (hframe : IsFrame G z A₀) (x : ℕ → V) (hws : IsWheelSystem G z A₀ x 2)
    (Y : Set V) (hHyp : Hyp192 G z A₀ x Y)
    (ih : (∀ Y' : Set V, Y'.ncard < Y.ncard → Hyp192 G z A₀ x Y' → Concl192 G z A₀ x Y') ∧
      Workspace.ProofLemmas.Thm192Setup.IHInduced G Y.ncard)
    (y : V) (hyY : y ∈ Y) (hyz : G.Adj y z)
    (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    (A : Set V) (hA : GoodA G z A₀ x Y y A)
    (hAmin : ∀ B : Set V, GoodA G z A₀ x Y y B → A.ncard ≤ B.ncard)
    (P : List V) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A) (hPlen : 3 ≤ P.length)
    (hAP : ∀ a ∈ A, a ∈ P) :
    VertexComplete G (x 2) (Y \ {y}) ∨
      (IsWheel G (z :: P) (Y \ {y}) ∧
        ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
          VertexComplete G c (Y \ {y}) ∧ VertexComplete G d (Y \ {y})) := by
  classical
  have hAsub : A ⊆ wheelSystemA G z A₀ x 1 := hA.1
  have hzx : ∀ j : ℕ, j ≤ 2 → G.Adj z (x j) := fun j hj => hws.2.2.2.2.2.2 j hj
  have hxA : ∀ j : ℕ, j ≤ 2 → x j ∉ A := fun j hj hm =>
    Thm192Setup.wheelSystemA_no_z _ (hAsub hm) (hzx j hj)
  have hx01 : ¬ G.Adj (x 0) (x 1) := Thm192Setup.x0_not_adj_x1 hws
  have hne01 : x 0 ≠ x 1 := by
    intro h; have := hws.2.1 0 (by omega) 1 (by omega) h; omega
  -- `A` lands inside the interior of `P`
  have hAint : ∀ a ∈ A, a ∈ SPGT.interior P := by
    intro a ha
    refine (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hAP a ha, ?_, ?_⟩
    · exact fun he => hxA 0 (by omega) (he ▸ ha)
    · exact fun he => hxA 1 (by omega) (he ▸ ha)
  rcases Thm192Claim2.claim2 G hG z A₀ hframe x hws Y hHyp ih y hyY hyz hY0 A hA hAmin with
    hL | ⟨hzY, P', hP', hP'int, hedges⟩
  · exact Or.inl hL.1
  by_cases hY0e : Y \ {y} = ∅
  · refine Or.inl ?_
    rw [hY0e]
    intro v hv
    exact absurd hv (Set.notMem_empty v)
  have hY0anti : AnticonnectedSet G (Y \ {y}) := hY0.resolve_left hY0e
  have hY0ne : (Y \ {y}).Nonempty := Set.nonempty_iff_ne_empty.mpr hY0e
  obtain ⟨c, hcI', d, hdI', hcd, hcY, hdY⟩ :=
    Thm192Infra.two_complete_in_interior hws hAsub hP' hP'int hedges
  refine Or.inr ⟨?_, c, hAint c (hP'int c hcI'), d, hAint d (hP'int d hdI'), hcd, hcY, hdY⟩
  have hhole : IsHoleList G (z :: P) := hole_zP hws hAsub hP hPint hPlen
  have hlen5 : 5 ≤ P.length := P_length_ge_five hG.1.1.1.1 hws hAsub hP hPint hPlen
  have hzP : z ∉ P := z_notMem_path hws hAsub hP hPint
  have hYA1 : ∀ w ∈ Y, w ∉ wheelSystemA G z A₀ x 1 := by
    intro w hw hmem
    refine Thm192Setup.wheelSystemA_no_complete _ hmem ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact (hHyp.2.2.1 w hw).symm
    · exact (hHyp.2.2.2.1 w hw).symm
  have hdisj : ∀ v ∈ z :: P, v ∉ Y \ {y} := by
    intro v hv hvY0
    rcases List.mem_cons.mp hv with heq | hvP
    · exact (hHyp.1 v hvY0.1).1 heq
    by_cases h0 : v = x 0
    · exact (hHyp.1 v hvY0.1).2.1 h0
    by_cases h1 : v = x 1
    · exact (hHyp.1 v hvY0.1).2.2.1 h1
    · exact hYA1 v hvY0.1
        (hAsub (hPint v ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hvP, h0, h1⟩)))
  -- one `Y₀`-complete edge with both ends on `P`
  have hSne : {e : Sym2 V | ∃ u ∈ P', ∃ v ∈ P', e = s(u, v) ∧
      EdgeComplete G (Y \ {y}) u v}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨e, u, huP', v, hvP', -, hedge⟩ := hSne
  have hmemP : ∀ w ∈ P', w ∈ P := by
    intro w hw
    by_cases h0 : w = x 0
    · rw [h0]; exact (PathBasics.isPathFrom_ends_mem hP).1
    by_cases h1 : w = x 1
    · rw [h1]; exact (PathBasics.isPathFrom_ends_mem hP).2
    · exact hAP w (hP'int w
        ((PathBasics.mem_interior_iff_of_pathFrom hP').mpr ⟨hw, h0, h1⟩))
  have huP : u ∈ P := hmemP u huP'
  have hvP : v ∈ P := hmemP v hvP'
  have hzu : z ≠ u := fun h => hzP (h ▸ huP)
  have hzv : z ≠ v := fun h => hzP (h ▸ hvP)
  have hx0P : x 0 ∈ P := (PathBasics.isPathFrom_ends_mem hP).1
  have hx1P : x 1 ∈ P := (PathBasics.isPathFrom_ends_mem hP).2
  have hedgeZ : ∀ w : V, (w = x 0 ∨ w = x 1) → EdgeComplete G (Y \ {y}) z w := by
    intro w hw
    rcases hw with rfl | rfl
    · exact ⟨hzx 0 (by omega), fun q hq => hzY q hq.1, fun q hq => hHyp.2.2.1 q hq.1⟩
    · exact ⟨hzx 1 (by omega), fun q hq => hzY q hq.1, fun q hq => hHyp.2.2.2.1 q hq.1⟩
  have hlen6 : 6 ≤ holeLength (z :: P) := by
    simp only [holeLength, List.length_cons]; omega
  by_cases hc0 : x 0 = u ∨ x 0 = v
  · have h1u : x 1 ≠ u := by
      rintro rfl
      rcases hc0 with h | h
      · exact hne01 (h.trans rfl)
      · exact hx01 (by rw [h]; exact hedge.1.symm)
    have h1v : x 1 ≠ v := by
      rintro rfl
      rcases hc0 with h | h
      · exact hx01 (by rw [h]; exact hedge.1)
      · exact hne01 (h.trans rfl)
    exact ⟨⟨hhole, hlen6⟩, ⟨hY0ne, hY0anti, hdisj⟩,
      z, x 1, u, v, List.mem_cons_self, List.mem_cons_of_mem _ hx1P,
      List.mem_cons_of_mem _ huP, List.mem_cons_of_mem _ hvP,
      hedgeZ (x 1) (Or.inr rfl), hedge, hzu, hzv, h1u, h1v⟩
  · push_neg at hc0
    exact ⟨⟨hhole, hlen6⟩, ⟨hY0ne, hY0anti, hdisj⟩,
      z, x 0, u, v, List.mem_cons_self, List.mem_cons_of_mem _ hx0P,
      List.mem_cons_of_mem _ huP, List.mem_cons_of_mem _ hvP,
      hedgeZ (x 0) (Or.inl rfl), hedge, hzu, hzv, hc0.1, hc0.2⟩

end Workspace.ProofLemmas.Thm192Claim8Basics
