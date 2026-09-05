import Workspace.ProofLemmas.Thm192Claim7Aux
import Workspace.ProofLemmas.Thm192Claim7GapReflection
import Workspace.ProofLemmas.Thm192Claim7ShortCut
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_7
import Workspace.Statements.S18.Thm_18_2

/-!
# The separated-index case of claim (7) of 19.2

PAPER (printed p. 120, claim (7), the case `x₂` `Y₀`-complete):

> *"We recall that `i` is maximum such that `x₂` is adjacent to `pᵢ`.  Since `y` is adjacent
> to `pₙ`, we may choose `j` with `i ≤ j ≤ n` minimum such that `y` is adjacent to `pⱼ`.
> From the hole `z-x₂-pᵢ-⋯-pⱼ-y-z` we see that `j` is odd.  Suppose `j ≠ i`.  Then the path
> `x₂-pᵢ-⋯-pⱼ-y` is even and has length `≥ 4`.  By 13.7 with anticonnected sets `{x₀,x₁}`,
> `Y₀ ∪ {z}` we deduce that `Y₀ ∪ {z}` is not anticonnected, and hence `z` is `Y`-complete.
> Consequently, by (4), no edge of `x₀-p₁-⋯-pₙ-x₁` is `Y`-complete, and in particular `pₙ`
> is not `Y`-complete, and therefore not `Y₀`-complete (since `pₙ` is adjacent to `y`).
> Since there is no `Y`-complete edge in the odd path `pⱼ-⋯-pₙ-x₁`, and the `Y`-complete
> vertex `z` has no neighbour in its interior, it follows from 2.2 that `pⱼ` is not
> `Y`-complete and hence not `Y₀`-complete.  By 18.2 with sets `{x₀,x₁}`, `Y₀`, since the
> `{x₀,x₁} ∪ Y₀`-complete vertex `z` has no neighbours in `A`, it follows that there are an
> odd number of `Y₀`-complete edges in the path `x₂-pᵢ-⋯-pⱼ-y`.  Since `y` is not
> `Y₀`-complete, they all belong to the path `x₂-pᵢ-⋯-pⱼ`.  Since `x₂z, zx₁` are both
> `Y₀`-complete edges and `x₁pₙ` is not, it follows that `pⱼ, pₙ` have opposite wheel-parity
> with respect to the wheel `(C₁,Y₀)`, where `C₁` is `z-x₂-pᵢ-⋯-pₙ-x₁-z`.  But `pⱼ, pₙ` are
> both not `Y₀`-complete, and so `(C₁,Y₀)` is an odd wheel, contrary to `G ∈ F₇`."*

Two points where the printed argument is silent and this file is not.

* The paper never says why `Y₀` is nonempty here.  It is: were `Y = {y}`, then `pⱼ` would
  be `Y`-complete because `y` is adjacent to `pⱼ`, and the 2.2 step above already shows
  that `pⱼ` is not `Y`-complete.  So the degenerate case dies with the same 2.2 step, and
  the reading of `hY0` as *"`Y \ {y}` is empty or anticonnected"* costs nothing.
* The parities `"j is odd"` and `"n is odd"` are used here only through the two evenness
  facts they come from: the hole `z-x₂-pᵢ-⋯-pⱼ-y-z` has even length, so `j - i` is even,
  and the hole `C₁` has even length, so `n - i` is even.  Those are the forms the counting
  needs, and they avoid having to fix the paper's absolute indexing.

Positions in `C₁ = z :: x₂ :: pᵢ-⋯-pₙ-x₁`: `0` is `z`, `1` is `x₂`, `m - i + 2` is `pₘ`,
`C₁.length - 2` is `pₙ` and `C₁.length - 1` is `x₁`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm192Claim7Separated

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm192Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (7)): the whole displayed paragraph above. -/
theorem separated_contact {G : SimpleGraph V} (hG : InF7 G)
    {z : V} {A₀ : Set V} {x : ℕ → V} (hws : IsWheelSystem G z A₀ x 2)
    {Y : Set V} (hHyp : Hyp192 G z A₀ x Y) {y : V} (hyY : y ∈ Y)
    (hyz : G.Adj y z) (hY0 : Y \ {y} = ∅ ∨ AnticonnectedSet G (Y \ {y}))
    {P : List V} (hP : IsPathFrom G P (x 0) (x 1))
    (hPI : ∀ w ∈ SPGT.interior P, w ∈ wheelSystemA G z A₀ x 1)
    (hP5 : 5 ≤ P.length)
    (hx2c : VertexComplete G (x 2) (Y \ {y})) (hx2y : ¬ G.Adj (x 2) y)
    (hx20 : ¬ G.Adj (x 2) (x 0)) (hx21 : ¬ G.Adj (x 2) (x 1))
    (hno : VertexComplete G z Y → ∀ k (hk : k + 1 < P.length),
      ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk))
    (hyI : ∃ w ∈ SPGT.interior P, G.Adj y w)
    {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hxI : G.Adj (x 2) (P[i]'(by omega)))
    (hlast : ∀ k (hk : k < P.length), i ≤ k → (G.Adj (x 2) (P[k]'hk) ↔ k = i))
    {j : ℕ} (hj : j + 1 < P.length) (hij : i < j)
    (hyj : G.Adj y (P[j]'(by omega)))
    (hmin : ∀ k (hk : k < P.length), i ≤ k → k < j → ¬ G.Adj y (P[k]'hk)) : False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hzP, hx2P, hCP, -⟩ :=
    Thm192Claim6Basics.path_facts hBerge hws Set.Subset.rfl hP hPI (by omega)
  have hYout := Thm192Claim6Basics.Y_disjoint_path hHyp Set.Subset.rfl hP hPI
  have hlastP : (P[P.length - 1]'(by omega)) = x 1 :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have h0P : (P[0]'(by omega)) = x 0 := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hzint : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w :=
    fun w hw => wheelSystemA_no_z w (hPI w hw)
  have hnopair : ∀ m (hm : m < P.length), 0 < m → m + 1 < P.length →
      ¬ (G.Adj (P[m]'hm) (x 0) ∧ G.Adj (P[m]'hm) (x 1)) :=
    fun m hm h1 h2 => Thm192Claim6Basics.no_pair_complete (A := wheelSystemA G z A₀ x 1)
      Set.Subset.rfl _ (hPI _ (PathBasics.getElem_mem_interior hP.1 hm h1 h2))
  have hzx0 : G.Adj z (x 0) := hws.2.2.2.2.2.2 0 (by omega)
  have hzx1 : G.Adj z (x 1) := hws.2.2.2.2.2.2 1 (by omega)
  have hzx2 : G.Adj z (x 2) := hws.2.2.2.2.2.2 2 le_rfl
  -- ###  the two holes  ###
  set sl : List V := (P.drop i).take (j - i + 1) with hsldef
  have hslmem : ∀ w ∈ sl, ∃ m, ∃ hm : m < P.length, i ≤ m ∧ m ≤ j ∧ (P[m]'hm) = w :=
    fun w hw => (PathBasics.mem_slice_iff P (le_of_lt hij) (show j < P.length by omega)).mp hw
  have hslint : ∀ w ∈ sl, w ∈ SPGT.interior P := by
    intro w hw
    obtain ⟨m, hm, him, hmj, rfl⟩ := hslmem w hw
    exact PathBasics.getElem_mem_interior hP.1 hm (by omega) (by omega)
  have hslP : ∀ w ∈ sl, w ∈ P := fun w hw => PathBasics.interior_subset (hslint w hw)
  have hslen : sl.length = j - i + 1 := PathBasics.length_slice P (le_of_lt hij) (by omega)
  set Q : List V := x 2 :: sl with hQdef
  have hQlen : Q.length = j - i + 2 := by simp [hQdef, hslen]
  have hQp : IsPathFrom G Q (x 2) (P[j]'(show j < P.length by omega)) := by
    refine Thm192Claim7Aux.isPathFrom_cons
      (PathBasics.isPathFrom_slice hP.1 hij (show j < P.length by omega)) hxI
      (fun hmem => hx2P (hslP _ hmem)) ?_
    intro w hw hwne
    obtain ⟨m, hm, him, hmj, rfl⟩ := hslmem w hw
    exact fun hadj => hwne (hP.1.2.1.getElem_inj_iff.mpr ((hlast m hm him).mp hadj))
  have hyP : y ∉ P := fun hmem => hYout y hmem hyY
  have hynex2 : y ≠ x 2 := (hHyp.1 y hyY).2.2.2
  set W : List V := Q ++ [y] with hWdef
  have hWlen : W.length = j - i + 3 := by simp [hWdef, hQlen]
  have hWp : IsPathFrom G W (x 2) y := by
    refine Thm192Claim7Aux.isPathFrom_snoc hQp hyj ?_ ?_
    · intro hmem
      rcases List.mem_cons.mp hmem with he | he
      · exact hynex2 he
      · exact hyP (hslP _ he)
    · intro w hw hwne
      rcases List.mem_cons.mp hw with he | he
      · rw [he]; exact fun hadj => hx2y hadj.symm
      · obtain ⟨m, hm, him, hmj, rfl⟩ := hslmem w he
        intro hadj
        rcases Nat.lt_or_ge m j with hlt | hge
        · exact hmin m hm him hlt hadj
        · exact hwne (hP.1.2.1.getElem_inj_iff.mpr (by omega))
  have hWint : SPGT.interior W = sl := by simp [SPGT.interior, hWdef, hQdef]
  -- PAPER: *"the hole `z-x₂-pᵢ-⋯-pⱼ-y-z`"*
  have hH : IsHoleList G (z :: W) := by
    refine PrismBasics.isHoleList_of_path_add_vertex hWp ?_ hzx2 hyz.symm ?_ ?_
    · rw [PathBasics.pathLength_eq, hWlen]; omega
    · intro hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · rcases List.mem_cons.mp hmem with he | he
        · exact (hws.2.2.1 2 le_rfl).2 he.symm
        · exact hzP (hslP _ he)
      · exact (hHyp.1 y hyY).1 (show z = y by simpa using hmem).symm
    · rw [hWint]; exact fun w hw => hzint w (hslint w hw)
  have hjieven : Even (j - i) := by
    have := hBerge.1 _ hH
    simp only [holeLength, List.length_cons, hWlen] at this
    obtain ⟨r, hr⟩ := this; exact ⟨r - 2, by omega⟩
  -- PAPER: *"`C₁` is `z-x₂-pᵢ-⋯-pₙ-x₁-z`"*
  set C₁ : List V := z :: x 2 :: P.drop i with hC₁def
  have hC₁len : C₁.length = P.length - i + 2 := by simp [hC₁def]
  have hC₁ : IsHoleList G C₁ :=
    Thm192Infra.holeFromCut hP hPI (fun w hw => wheelSystemA_no_z w hw) hzx0 hzx1 hzx2
      hzP hx2P hi (by omega) hlast
  have hnieven : Even (P.length - i) := by
    have := hBerge.1 _ hC₁
    simp only [holeLength, hC₁len] at this
    obtain ⟨r, hr⟩ := this; exact ⟨r - 1, by omega⟩
  have hji2 : i + 2 ≤ j := by
    obtain ⟨r, hr⟩ := hjieven; omega
  have hL6 : 6 ≤ C₁.length := by omega
  have hn : 0 < C₁.length := by omega
  -- reading `C₁` off `P`
  have hC1P : ∀ m (hm : m < P.length) (him : i ≤ m) (ht : m - i + 2 < C₁.length),
      (C₁[m - i + 2]'ht) = (P[m]'hm) := fun m hm him ht =>
    Thm192Claim7ShortCut.cut_getElem hm him ht
  have hC1zero : ∀ (h : 0 < C₁.length), (C₁[0]'h) = z := fun h => by simp [hC₁def]
  have hC1one : ∀ (h : 1 < C₁.length), (C₁[1]'h) = x 2 := fun h => by simp [hC₁def]
  have hC1last : ∀ (h : C₁.length - 1 < C₁.length), (C₁[C₁.length - 1]'h) = x 1 := by
    intro h
    rw [Thm192Claim7Aux.getElem_idx_congr (l := C₁)
      (show C₁.length - 1 = (P.length - 1) - i + 2 by omega) h (by omega),
      hC1P (P.length - 1) (by omega) (by omega) (by omega)]
    exact hlastP
  have hC1pen : ∀ (h : C₁.length - 2 < C₁.length),
      (C₁[C₁.length - 2]'h) = (P[P.length - 2]'(show P.length - 2 < P.length by omega)) := by
    intro h
    rw [Thm192Claim7Aux.getElem_idx_congr (l := C₁)
      (show C₁.length - 2 = (P.length - 2) - i + 2 by omega) h (by omega)]
    exact hC1P (P.length - 2) (by omega) (by omega) (by omega)
  have hmemP : ∀ m (hm : m < P.length), i ≤ m → (P[m]'hm) ∈ C₁ := by
    intro m hm him
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    rw [List.mem_iff_getElem]
    exact ⟨m - i, by simp only [List.length_drop]; omega, by
      rw [List.getElem_drop]
      exact hP.1.2.1.getElem_inj_iff.mpr (by omega)⟩
  have hCY : ∀ w ∈ C₁, w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with hw | hw
    · exact (hHyp.1 w hwY).1 hw
    rcases List.mem_cons.mp hw with hw | hw
    · exact (hHyp.1 w hwY).2.2.2 hw
    · exact hYout w (List.mem_of_mem_drop hw) hwY
  -- ###  Step A: `z` is `Y`-complete  ###
  have hX01 : AnticonnectedSet G ({x 0, x 1} : Set V) :=
    Thm192Claim7Aux.anticonnected_pair
      (fun he => by have := hws.2.1 0 (by omega) 1 (by omega) he; omega)
      (x0_not_adj_x1 hws)
  have hYx01 : ∀ w ∈ Y, VertexComplete G w ({x 0, x 1} : Set V) := by
    intro w hw v hv
    rcases (by simpa using hv : v = x 0 ∨ v = x 1) with rfl | rfl
    · exact (hHyp.2.2.1 w hw).symm
    · exact (hHyp.2.2.2.1 w hw).symm
  have hzY : VertexComplete G z Y := by
    by_contra hzn
    have hY0e : (Y \ {y}).Nonempty := by
      rcases Set.eq_empty_or_nonempty (Y \ {y}) with he | hne
      · exact absurd (fun w hw => by
          by_cases hwy : w = y
          · exact hwy ▸ hyz.symm
          · exact absurd (Set.eq_empty_iff_forall_notMem.mp he w ⟨hw, hwy⟩) (by simp)) hzn
      · exact hne
    have hY0a : AnticonnectedSet G (Y \ {y}) := by
      rcases hY0 with he | ha
      · exact absurd (he ▸ hY0e) (by simp)
      · exact ha
    have hzn0 : ¬ VertexComplete G z (Y \ {y}) := by
      intro hc
      exact hzn (fun w hw => by
        by_cases hwy : w = y
        · exact hwy ▸ hyz.symm
        · exact hc w ⟨hw, hwy⟩)
    have hXa : AnticonnectedSet G ((Y \ {y}) ∪ {z}) :=
      KiteTailBasics.anticonnectedSet_union_singleton hY0a hzn0
    have hyY0 : ¬ VertexComplete G y (Y \ {y}) :=
      Thm192Claim7Aux.exists_nonneighbour_of_anticonnected hHyp.2.1 hyY hY0e
    have hWmem : ∀ w ∈ W, w = x 2 ∨ (∃ m, ∃ hm : m < P.length, i ≤ m ∧ m ≤ j ∧
        (P[m]'hm) = w) ∨ w = y := by
      intro w hw
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_cons.mp hw with he | hw
        · exact Or.inl he
        · exact Or.inr (Or.inl (hslmem w hw))
      · exact Or.inr (Or.inr (by simpa using hw))
    have hx2Xc : VertexComplete G (x 2) ((Y \ {y}) ∪ {z}) := by
      intro w hw
      rcases hw with hw | hw
      · exact hx2c w hw
      · exact (by simpa using hw : w = z) ▸ hzx2.symm
    have hXuniq : ∀ u ∈ W, (VertexComplete G u ((Y \ {y}) ∪ {z}) ↔ u = x 2) := by
      intro u hu
      refine ⟨fun hc => ?_, fun he => he ▸ hx2Xc⟩
      rcases hWmem u hu with he | ⟨m, hm, him, hmj, rfl⟩ | he
      · exact he
      · exact absurd (hc z (Or.inr rfl)).symm
          (hzint _ (PathBasics.getElem_mem_interior hP.1 hm (by omega) (by omega)))
      · exact absurd (fun w hw => he ▸ hc w (Or.inl hw)) hyY0
    have hYuniq : ∀ u ∈ W, (VertexComplete G u ({x 0, x 1} : Set V) ↔ u = y) := by
      intro u hu
      refine ⟨fun hc => ?_, fun he => he ▸ hYx01 y hyY⟩
      rcases hWmem u hu with he | ⟨m, hm, him, hmj, rfl⟩ | he
      · exact absurd (he ▸ hc (x 0) (by simp)) hx20
      · exact absurd ⟨hc (x 0) (by simp), hc (x 1) (by simp)⟩
          (hnopair m hm (by omega) (by omega))
      · exact he
    have hdisj : Disjoint ((Y \ {y}) ∪ {z}) ({x 0, x 1} : Set V) := by
      rw [Set.disjoint_left]
      rintro w (hw | hw) hv
      · rcases (by simpa using hv : w = x 0 ∨ w = x 1) with rfl | rfl
        · exact (hHyp.1 _ hw.1).2.1 rfl
        · exact (hHyp.1 _ hw.1).2.2.1 rfl
      · have he : w = z := by simpa using hw
        rcases (by simpa using hv : w = x 0 ∨ w = x 1) with h | h
        · exact (hws.2.2.1 0 (by omega)).2 (h ▸ he)
        · exact (hws.2.2.1 1 (by omega)).2 (h ▸ he)
    have hcompl : Complete G ((Y \ {y}) ∪ {z}) ({x 0, x 1} : Set V) := by
      rintro w (hw | hw)
      · exact hYx01 w hw.1
      · have he : w = z := by simpa using hw
        intro v hv
        rcases (by simpa using hv : v = x 0 ∨ v = x 1) with rfl | rfl
        · exact he ▸ hzx0
        · exact he ▸ hzx1
    have h137 := Workspace.Statements.S13.SPGT.thm_13_7 G hG.1.1 _ _ hdisj
      ⟨z, Or.inr rfl⟩ ⟨x 0, by simp⟩ hXa hX01 hcompl W (x 2) y hWp.1
      (by rw [PathBasics.pathLength_eq, hWlen]; obtain ⟨r, hr⟩ := hjieven; exact ⟨r + 1, by omega⟩)
      (by rw [PathBasics.pathLength_eq, hWlen]; omega) hWp.2.1 hWp.2.2 hXuniq hYuniq
    have := h137.1
    rw [PathBasics.pathLength_eq, hWlen] at this
    omega
  -- ###  Step B: `pⱼ` and `pₙ` are not `Y₀`-complete  ###
  have hnoP := hno hzY
  have hx1Y : VertexComplete G (x 1) Y := hHyp.2.2.2.1
  have hpjY : ¬ VertexComplete G (P[j]'(show j < P.length by omega)) Y := by
    intro hpj
    have hdrop : IsPathFrom G (P.drop j) (P[j]'(by omega))
        (P[P.length - 1]'(by omega)) := Thm192Claim7Aux.isPathFrom_drop hP.1 hj
    have hnoedge : ¬ ∃ u ∈ P.drop j, ∃ v ∈ P.drop j, EdgeComplete G Y u v := by
      rintro ⟨u, hu, v, hv, hE⟩
      obtain ⟨a, ha, hja, rfl⟩ := Thm192Claim7Aux.mem_drop_index hu
      obtain ⟨b, hb, hjb, rfl⟩ := Thm192Claim7Aux.mem_drop_index hv
      rcases (PathBasics.path_adj_iff hP.1 ha hb).mp hE.1 with rfl | rfl
      · exact hnoP a hb hE
      · exact hnoP b ha (WheelParity.edgeComplete_symm hE)
    obtain ⟨w, hw, hzw⟩ := Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hHyp.2.1
      (P.drop j) _ _ hdrop (fun w hw => hYout w (List.mem_of_mem_drop hw))
      (by rw [PathBasics.pathLength_eq, List.length_drop]
          obtain ⟨r, hr⟩ := hnieven; obtain ⟨s, hs⟩ := hjieven; exact ⟨r - s - 1, by omega⟩)
      hpj (by rw [hlastP]; exact hx1Y) hnoedge z hzY
    rw [PathBasics.mem_interior_iff_of_pathFrom hdrop] at hw
    obtain ⟨m, hm, hjm, rfl⟩ := Thm192Claim7Aux.mem_drop_index hw.1
    refine hzint _ (PathBasics.getElem_mem_interior hP.1 hm (by omega) ?_) hzw
    by_contra hcon
    exact hw.2.2 (hP.1.2.1.getElem_inj_iff.mpr (by omega))
  have hY0e : (Y \ {y}).Nonempty := by
    rcases Set.eq_empty_or_nonempty (Y \ {y}) with he | hne
    · exact absurd (fun w hw => by
        by_cases hwy : w = y
        · exact hwy ▸ hyj.symm
        · exact absurd (Set.eq_empty_iff_forall_notMem.mp he w ⟨hw, hwy⟩) (by simp)) hpjY
    · exact hne
  have hY0a : AnticonnectedSet G (Y \ {y}) := by
    rcases hY0 with he | ha
    · exact absurd (he ▸ hY0e) (by simp)
    · exact ha
  have hyY0 : ¬ VertexComplete G y (Y \ {y}) :=
    Thm192Claim7Aux.exists_nonneighbour_of_anticonnected hHyp.2.1 hyY hY0e
  have hpjY0 : ¬ VertexComplete G (P[j]'(show j < P.length by omega)) (Y \ {y}) := by
    intro hc
    exact hpjY (fun w hw => by
      by_cases hwy : w = y
      · exact hwy ▸ hyj.symm
      · exact hc w ⟨hw, hwy⟩)
  have hypn : G.Adj y (P[P.length - 2]'(show P.length - 2 < P.length by omega)) := by
    rcases Thm192Claim7GapReflection.right_contact hG hws hHyp hyY hyz hP hP5 hPI hx21
      ⟨⟨_, PathBasics.getElem_mem_interior hP.1 (show i < P.length by omega) hi hin, hxI⟩,
        hyI⟩ with h | h
    · exact absurd h.symm hx2y
    · exact h
  have hpnY : ¬ VertexComplete G (P[P.length - 2]'(show P.length - 2 < P.length by omega)) Y := by
    intro hc
    refine hnoP (P.length - 2) (by omega) ⟨PathBasics.path_adj_succ hP.1 (by omega), hc, ?_⟩
    rw [Thm192Claim7Aux.getElem_idx_congr (l := P)
      (show P.length - 2 + 1 = P.length - 1 by omega) (by omega) (by omega), hlastP]
    exact hx1Y
  have hpnY0 : ¬ VertexComplete G (P[P.length - 2]'(show P.length - 2 < P.length by omega))
      (Y \ {y}) := by
    intro hc
    exact hpnY (fun w hw => by
      by_cases hwy : w = y
      · exact hwy ▸ hypn.symm
      · exact hc w ⟨hw, hwy⟩)
  -- ###  Step C: 18.2 counts the `Y₀`-complete edges of `x₂-pᵢ-⋯-pⱼ-y`  ###
  have hzY0 : VertexComplete G z (Y \ {y}) := fun w hw => hzY w hw.1
  have hQP : ∀ s (hs : s + 1 < Q.length) {m : ℕ} (h : m < P.length), m = i + s →
      (Q[s + 1]'hs) = (P[m]'h) := by
    intro s hs m h he
    show ((P.drop i).take (j - i + 1))[s]'(by
      simp only [List.length_take, List.length_drop]; omega) = _
    exact PathBasics.getElem_slice' P _ h he
  have hWy : ∀ (h : Q.length < W.length), (W[Q.length]'h) = y := by
    intro h
    show (Q ++ [y])[Q.length]'(by omega) = y
    simp
  have hWQ : ∀ s (hs : s < Q.length) (h : s < W.length), (W[s]'h) = (Q[s]'hs) :=
    fun s hs h => List.getElem_append_left hs
  have hidx : {t : ℕ | ∃ h : t + 1 < W.length,
        EdgeComplete G (Y \ {y}) (W[t]'(by omega)) (W[t + 1]'h)}
      = {t : ℕ | ∃ h : t + 1 < Q.length,
        EdgeComplete G (Y \ {y}) (Q[t]'(by omega)) (Q[t + 1]'h)} := by
    ext t
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h, hE⟩
      have ht : t + 1 < Q.length := by
        by_contra hcon
        have hteq : t + 1 = Q.length := by simp only [hWlen, hQlen] at h ⊢; omega
        refine hyY0 ?_
        have hv : (W[t + 1]'h) = y := by
          rw [Thm192Claim7Aux.getElem_idx_congr (l := W) hteq h (by omega)]
          exact hWy _
        exact hv ▸ hE.2.2
      rw [hWQ t (by omega) (by omega), hWQ (t + 1) ht h] at hE
      exact ⟨ht, hE⟩
    · rintro ⟨h, hE⟩
      have h' : t + 1 < W.length := by simp only [hWlen, hQlen] at h ⊢; omega
      refine ⟨h', ?_⟩
      rw [hWQ t (by omega) (by omega), hWQ (t + 1) h h']
      exact hE
  have hdisj2 : Disjoint (Y \ {y}) ({x 0, x 1} : Set V) := by
    rw [Set.disjoint_left]
    intro w hw hv
    rcases (by simpa using hv : w = x 0 ∨ w = x 1) with rfl | rfl
    · exact (hHyp.1 _ hw.1).2.1 rfl
    · exact (hHyp.1 _ hw.1).2.2.1 rfl
  have hWmem : ∀ w ∈ W, w = x 2 ∨ (∃ m, ∃ hm : m < P.length, i ≤ m ∧ m ≤ j ∧
      (P[m]'hm) = w) ∨ w = y := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_cons.mp hw with he | hw
      · exact Or.inl he
      · exact Or.inr (Or.inl (hslmem w hw))
    · exact Or.inr (Or.inr (by simpa using hw))
  have hYuniq : ∀ w ∈ W, (VertexComplete G w ({x 0, x 1} : Set V) ↔ w = y) := by
    intro u hu
    refine ⟨fun hc => ?_, fun he => he ▸ hYx01 y hyY⟩
    rcases hWmem u hu with he | ⟨m, hm, him, hmj, rfl⟩ | he
    · exact absurd (he ▸ hc (x 0) (by simp)) hx20
    · exact absurd ⟨hc (x 0) (by simp), hc (x 1) (by simp)⟩ (hnopair m hm (by omega) (by omega))
    · exact he
  have hQlast : Q.getLast? = some (P[j]'(show j < P.length by omega)) := hQp.2.2
  have hWdl : W.dropLast = Q := by simp [hWdef]
  have hlast1 : W.dropLast.getLast? = some (P[j]'(show j < P.length by omega)) := by
    rw [hWdl]; exact hQlast
  have hlast2 : W.dropLast.dropLast.getLast?
      = some (P[j - 1]'(show j - 1 < P.length by omega)) := by
    rw [hWdl, List.dropLast_eq_take,
      Thm192Claim7Aux.getLast?_take (show 0 < Q.length - 1 by omega) (by omega),
      List.getElem?_eq_getElem (show Q.length - 1 - 1 < Q.length by omega)]
    congr 1
    rw [Thm192Claim7Aux.getElem_idx_congr (l := Q)
      (show Q.length - 1 - 1 = (j - i - 1) + 1 by omega) (by omega) (by omega),
      hQP (j - i - 1) (by omega) (show j - 1 < P.length by omega) (by omega)]
  have hzX01 : VertexComplete G z ({x 0, x 1} : Set V) := by
    intro v hv
    rcases (by simpa using hv : v = x 0 ∨ v = x 1) with rfl | rfl
    · exact hzx0
    · exact hzx1
  have hzpj : ¬ G.Adj z (P[j]'(show j < P.length by omega)) :=
    hzint _ (PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega))
  have hzpj1 : ¬ G.Adj z (P[j - 1]'(show j - 1 < P.length by omega)) :=
    hzint _ (PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega))
  have h182 := Workspace.Statements.S18.SPGT.thm_18_2 G hG (Y \ {y}) ({x 0, x 1} : Set V)
    hdisj2 hY0e ⟨x 0, by simp⟩ hY0a hX01 (fun w hw => hYx01 w hw.1) W (x 2) _ _ y hWp.1
    (by rw [PathBasics.pathLength_eq, hWlen]; obtain ⟨r, hr⟩ := hjieven; exact ⟨r + 1, by omega⟩)
    (by rw [PathBasics.pathLength_eq, hWlen]; omega) hWp.2.1 hWp.2.2 hlast1 hlast2
    hx2c hyY0 hYuniq ⟨z, hzX01, hzpj, hzpj1⟩
  -- PAPER: *"there are an odd number of `Y₀`-complete edges in the path `x₂-pᵢ-⋯-pⱼ-y`"*
  have hoddW : Odd {e : Sym2 V | ∃ u ∈ W, ∃ v ∈ W,
      e = s(u, v) ∧ EdgeComplete G (Y \ {y}) u v}.ncard := by
    rcases h182 with h | ⟨h3, -⟩
    · exact h
    · rw [hWlen] at h3; omega
  -- PAPER: *"Since `y` is not `Y₀`-complete, they all belong to the path `x₂-pᵢ-⋯-pⱼ`."*
  have hoddQ : Odd {t : ℕ | ∃ h : t + 1 < Q.length,
      EdgeComplete G (Y \ {y}) (Q[t]'(by omega)) (Q[t + 1]'h)}.ncard := by
    rw [← hidx, ← Thm192Claim7Aux.ncard_pathEdges (Y := Y \ {y}) hWp.1]
    exact hoddW
  -- ###  Step D: the wheel `(C₁, Y₀)` and its parities  ###
  have hQmem : ∀ s (hs : s < Q.length),
      (Q[s]'hs) ∈ C₁ ∧ (Q[s]'hs) ≠ x 1 ∧ (Q[s]'hs) ≠ z := by
    intro s hs
    rcases s with _ | s
    · have he : (Q[0]'hs) = x 2 := rfl
      refine ⟨by rw [he]; simp [hC₁def], ?_, ?_⟩
      · rw [he]; exact fun hc => by have := hws.2.1 2 le_rfl 1 (by omega) hc; omega
      · rw [he]; exact (hws.2.2.1 2 le_rfl).2
    · have he : (Q[s + 1]'hs) = (P[i + s]'(show i + s < P.length by omega)) :=
        hQP s hs _ rfl
      refine ⟨by rw [he]; exact hmemP _ _ (by omega), ?_, ?_⟩
      · rw [he, ← hlastP]
        exact fun hc => by have := hP.1.2.1.getElem_inj_iff.mp hc; omega
      · rw [he]; exact fun hc => hzP (hc ▸ List.getElem_mem _)
  have hx1Y0 : VertexComplete G (x 1) (Y \ {y}) := fun w hw => hx1Y w hw.1
  have hEx1z : EdgeComplete G (Y \ {y}) (x 1) z := ⟨hzx1.symm, hx1Y0, hzY0⟩
  have hx1C : x 1 ∈ C₁ := by
    have h := hmemP (P.length - 1) (by omega) (by omega)
    rwa [hlastP] at h
  have hWheel : IsWheel G C₁ (Y \ {y}) := by
    obtain ⟨t, ht, hEt⟩ : ∃ t, ∃ h : t + 1 < Q.length,
        EdgeComplete G (Y \ {y}) (Q[t]'(by omega)) (Q[t + 1]'h) := by
      have hne : {t : ℕ | ∃ h : t + 1 < Q.length,
          EdgeComplete G (Y \ {y}) (Q[t]'(by omega)) (Q[t + 1]'h)}.Nonempty := by
        by_contra hemp
        rw [Set.not_nonempty_iff_eq_empty] at hemp
        rw [hemp, Set.ncard_empty] at hoddQ
        simp at hoddQ
      obtain ⟨t, hmem⟩ := hne
      exact ⟨t, hmem.1, hmem.2⟩
    refine ⟨⟨hC₁, by simpa [holeLength] using hL6⟩,
      ⟨hY0e, hY0a, fun v hv => fun hvY => hCY v hv hvY.1⟩,
      x 1, z, _, _, ?_, ?_, (hQmem t (by omega)).1, (hQmem (t + 1) ht).1, hEx1z, hEt,
      ?_, ?_, ?_, ?_⟩
    · exact hx1C
    · simp [hC₁def]
    · exact fun hc => (hQmem t (by omega)).2.1 hc.symm
    · exact fun hc => (hQmem (t + 1) ht).2.1 hc.symm
    · exact fun hc => (hQmem t (by omega)).2.2 hc.symm
    · exact fun hc => (hQmem (t + 1) ht).2.2 hc.symm
  -- the three cyclic edges the paper names
  have hce0 : WheelParity.CycEdge G (Y \ {y}) C₁ 0 :=
    ⟨z, x 2, by rw [Nat.zero_mod, List.getElem?_eq_getElem hn, hC1zero],
      by rw [Nat.mod_eq_of_lt (show 0 + 1 < C₁.length by omega),
        List.getElem?_eq_getElem (show 0 + 1 < C₁.length by omega),
        Thm192Claim7Aux.getElem_idx_congr (l := C₁) (show 0 + 1 = 1 from rfl)
          (show 0 + 1 < C₁.length by omega) (show 1 < C₁.length by omega), hC1one],
      ⟨hzx2, hzY0, hx2c⟩⟩
  have hcelast : WheelParity.CycEdge G (Y \ {y}) C₁ (C₁.length - 1) :=
    ⟨x 1, z, by
      rw [Nat.mod_eq_of_lt (show C₁.length - 1 < C₁.length by omega),
        List.getElem?_eq_getElem (show C₁.length - 1 < C₁.length by omega), hC1last],
      by
      rw [show C₁.length - 1 + 1 = C₁.length by omega, Nat.mod_self,
        List.getElem?_eq_getElem hn, hC1zero],
      hEx1z⟩
  have hcen2 : ¬ WheelParity.CycEdge G (Y \ {y}) C₁ (C₁.length - 2) := by
    rintro ⟨u, v, hu, -, hE⟩
    rw [Nat.mod_eq_of_lt (show C₁.length - 2 < C₁.length by omega),
      List.getElem?_eq_getElem (show C₁.length - 2 < C₁.length by omega), hC1pen] at hu
    exact hpnY0 (by rw [Option.some.inj hu]; exact hE.2.1)
  -- PAPER: *"`x₂z`, `zx₁` are both `Y₀`-complete edges and `x₁pₙ` is not"*
  have hcnt1 : WheelParity.cycCount G (Y \ {y}) C₁ 1 = 1 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, WheelParity.cycCount_succ,
      WheelParity.cycCount_zero, if_pos hce0]
  have hpre : Q <+: C₁.rotate 1 := by
    have hr : C₁.rotate 1 = (x 2 :: P.drop i) ++ [z] := by simp [hC₁def]
    rw [hr]
    obtain ⟨u, hu⟩ : sl <+: (P.drop i ++ [z]) :=
      (List.take_prefix _ _).trans (List.prefix_append _ _)
    refine ⟨u, ?_⟩
    show (x 2 :: sl) ++ u = (x 2 :: P.drop i) ++ [z]
    simp only [List.cons_append, hu]
  have harc := WheelParity.arc_count (G := G) (Y := Y \ {y}) hC₁ hpre rfl
    (show 2 ≤ Q.length by omega) (show Q.length + 1 ≤ C₁.length by omega)
  rw [hcnt1, show 1 + (Q.length - 1) = j - i + 2 by omega] at harc
  have hevenTot : WheelParity.cycCount G (Y \ {y}) C₁ C₁.length % 2 = 0 :=
    Nat.even_iff.mp (WheelBasics.even_cycCount_of_wheel hBerge hWheel)
  have e1 : WheelParity.cycCount G (Y \ {y}) C₁ (C₁.length - 1)
      = WheelParity.cycCount G (Y \ {y}) C₁ (C₁.length - 2) := by
    have h := WheelParity.cycCount_succ (G := G) (Y := Y \ {y}) (C := C₁) (C₁.length - 2)
    rw [if_neg hcen2, show C₁.length - 2 + 1 = C₁.length - 1 by omega] at h
    omega
  have e2 : WheelParity.cycCount G (Y \ {y}) C₁ C₁.length
      = WheelParity.cycCount G (Y \ {y}) C₁ (C₁.length - 1) + 1 := by
    have h := WheelParity.cycCount_succ (G := G) (Y := Y \ {y}) (C := C₁) (C₁.length - 1)
    rw [if_pos hcelast, show C₁.length - 1 + 1 = C₁.length by omega] at h
    omega
  have hKodd : WheelParity.cycCount G (Y \ {y}) C₁ (C₁.length - 2) % 2 = 1 := by omega
  have hJeven : WheelParity.cycCount G (Y \ {y}) C₁ (j - i + 2) % 2 = 0 := by
    have hq := Nat.odd_iff.mp hoddQ
    omega
  -- PAPER: *"`pⱼ, pₙ` have opposite wheel-parity ... but are both not `Y₀`-complete"*
  have hJK : j - i + 2 ≤ C₁.length - 2 := by omega
  rcases eq_or_lt_of_le hJK with heq | hlt
  · rw [heq] at hJeven; omega
  · have hpj : (C₁[j - i + 2]'(by omega)) = (P[j]'(show j < P.length by omega)) :=
      hC1P j (by omega) (by omega) (by omega)
    have hne : (C₁[j - i + 2]'(show j - i + 2 < C₁.length by omega))
        ≠ (C₁[C₁.length - 2]'(show C₁.length - 2 < C₁.length by omega)) := by
      intro he
      have := hC₁.2.1.getElem_inj_iff.mp he
      omega
    have hns : ¬ SameWheelParity G C₁ (Y \ {y})
        (C₁[j - i + 2]'(show j - i + 2 < C₁.length by omega))
        (C₁[C₁.length - 2]'(show C₁.length - 2 < C₁.length by omega)) := by
      rw [WheelParity.sameWheelParity_iff hC₁
        (WheelBasics.even_cycCount_of_wheel hBerge hWheel) (by omega) (by omega) (by omega)]
      omega
    refine Thm192Infra.oddWheelFromParities hG hWheel ?_ ?_
      ⟨hne, List.getElem_mem _, List.getElem_mem _, hns⟩
    · rw [hpj]; exact hpjY0
    · rw [hC1pen]; exact hpnY0
