import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.RestrictGraph
import Workspace.ProofLemmas.PendantTransport
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.ProofLemmas.SubpathIsSlice
import Workspace.ProofLemmas.Thm29Aux
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S02.Thm_2_2

/-!
# 2.9, the odd-hole branch

PAPER (printed p. 11, second paragraph of the proof of 2.9):

> *"Assume first that there is an odd hole `C` of length `≥ 7` in `G₀`.  It necessarily uses
> `y`, and the neighbours of `y` in `C` are `Y`-complete, and no other vertices of `C \ y` are
> `Y`-complete.  Hence there is an odd path `Q` in `G \ Y` of length `≥ 5`, with both ends
> `Y`-complete and no internal vertices `Y`-complete.  So the ends of `Q` belong to `X ∪ {pₙ}`
> and its interior to `V(P) \ {pₙ}`.  By 2.1 `Y` contains a leap for `Q`; so there is an odd
> path `R` of length `≥ 5` with ends (`y₁, y₂` say) in `Y` and with interior in
> `V(P) \ {pₙ}`.  Since `R` cannot be completed to a hole via `y₂-pₙ-y₁` it follows that `pₙ`
> has a neighbour in `R*`, and so `pₙ₋₁` belongs to `R`.  If also `p₁` belongs to `R` then the
> theorem holds, so we may assume it does not.  Since `R` is odd and `P` is even it follows
> that `p₂` also does not belong to `R`, and so `p₁` has no neighbour in `R*`; yet the ends of
> `R` are `X`-complete and its internal vertices are not, contrary to 2.2.  This completes the
> case when there is an odd hole in `G₀` of length `≥ 7`."*

The auxiliary graph `G₀ = (G \ Y) + y` with `N(y) = X ∪ {pₙ}` is
`Workspace.ProofLemmas.Thm29Aux.cG0`; everything about it goes through the three adjacency
lemmas `cG0_adj_inl`, `cG0_adj_inr`, `cG0_adj_inr'` and the two `mem_*` decoders.

Map from the printed sentences to the Lean proof:

* *"It necessarily uses `y`"* — `hyC` inside `exists_odd_path`, by `exists_eq_map_inl` +
  `isHoleList_map_inl` + `RestrictGraph.isHoleList_of_restrict` against `hG.1`.
* *"the neighbours of `y` in `C` are `Y`-complete, and no other vertices of `C \ y` are"* —
  `HoleMinusVertexPath.adj_head_iff` after rotating `y` to position `0`
  (`HoleArithmetic.exists_rotate_head`).
* *"Hence there is an odd path `Q` in `G \ Y` of length `≥ 5` …"* and *"So the ends of `Q`
  belong to `X ∪ {pₙ}` and its interior to `V(P) \ {pₙ}`"* — `exists_odd_path`.
* *"By 2.1 `Y` contains a leap for `Q`"* — `thm_2_1`, with the other two alternatives killed.
* *"so there is an odd path `R` of length `≥ 5` …"* — `PathGlue.isPathFrom_interior` +
  `PathAttach.isPathFrom_cons_concat`.
* *"Since `R` cannot be completed to a hole via `y₂-pₙ-y₁` …"* — `PathGlue.glue_hole` with the
  one-vertex path `[pₙ]`.
* *"and so `pₙ₋₁` belongs to `R`"* — `PathBasics.path_adj_iff` on `P`.
* *"If also `p₁` belongs to `R` … Since `R` is odd and `P` is even …"* —
  `SubpathIsSlice.exists_index_of_subpath` turns `R*` into a contiguous block `p[r], …` of
  `P`, and the parity of `r` is one `omega`.
* *"contrary to 2.2"* — `thm_2_2` instantiated at `v := p₁`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm29OddHole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport
open Workspace.Statements.S02.SPGT

/-! ## Every old vertex of a hole of `G₀` lies in the kept set -/

/-- A vertex of `V` outside `W = V(P) ∪ X` is isolated in `G₀` (it has no `G₀`-neighbour at
all: `cG0_adj_inl` fails outside `W`, and `cG0_adj_inr` needs membership in
`X ∪ {pₙ} ⊆ W`), while a hole vertex is adjacent to its cyclic successor. -/
private theorem mem_cW_of_mem_hole {V : Type*} {G : SimpleGraph V} {p : List V} {X : Set V}
    {pn : V} {C : List (V ⊕ Unit)} (hC : IsHoleList (Thm29Aux.cG0 G p X pn) C)
    (hpn : pn ∈ p) {z : V} (hz : (Sum.inl z : V ⊕ Unit) ∈ C) : z ∈ Thm29Aux.cW p X := by
  obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hz
  have h4 := hC.1
  have hpos : 0 < C.length := by omega
  have hj : (i + 1) % C.length < C.length := Nat.mod_lt _ hpos
  have hadj := (HoleBasics.hole_adj_iff hC hi hj).mpr (Or.inl rfl)
  rw [hieq] at hadj
  obtain ⟨w, hw⟩ : ∃ w, ((C)[(i + 1) % C.length]'hj) = w := ⟨_, rfl⟩
  rw [hw] at hadj
  cases w with
  | inl b => exact Thm29Aux.mem_cW.mpr ((Thm29Aux.cG0_adj_inl z b).mp hadj).2.1
  | inr t =>
      rcases (Thm29Aux.cG0_adj_inr z t).mp hadj with h | h
      · exact Thm29Aux.mem_cW.mpr (Or.inr h)
      · exact Thm29Aux.mem_cW.mpr (Or.inl (by rw [h]; exact hpn))

/-! ## The odd path `Q` -/

/-- *"It necessarily uses `y`, and the neighbours of `y` in `C` are `Y`-complete, and no other
vertices of `C \ y` are `Y`-complete.  Hence there is an odd path `Q` in `G \ Y` of length
`≥ 5`, with both ends `Y`-complete and no internal vertices `Y`-complete.  So the ends of `Q`
belong to `X ∪ {pₙ}` and its interior to `V(P) \ {pₙ}`."*

Everything except the `Y`-completeness bookkeeping, which is done at the call site from
`hcompl` and `hYuniq`. -/
private theorem exists_odd_path {V : Type*} {G : SimpleGraph V} (hG : Berge G) {X : Set V}
    {p : List V} {pn : V} (hpn : pn ∈ p)
    {C : List (V ⊕ Unit)} (hC : IsHoleList (Thm29Aux.cG0 G p X pn) C)
    (hCodd : Odd (holeLength C)) (hC7 : 7 ≤ holeLength C) :
    ∃ (Q : List V) (q₁ qm : V), IsPathFrom G Q q₁ qm ∧
      pathLength Q = C.length - 2 ∧
      (q₁ ∈ X ∨ q₁ = pn) ∧ (qm ∈ X ∨ qm = pn) ∧
      (∀ z ∈ Q, z ∈ Thm29Aux.cW p X) ∧
      (∀ z ∈ SPGT.interior Q, z ∈ p ∧ z ≠ pn) := by
  classical
  have hC7' : 7 ≤ C.length := hC7
  have hCodd' : Odd C.length := hCodd
  -- *"It necessarily uses `y`."*
  have hyC : (Sum.inr () : V ⊕ Unit) ∈ C := by
    by_contra hy
    have hall : ∀ x ∈ C, x ≠ (Sum.inr () : V ⊕ Unit) := by
      intro x hx hxe
      exact hy (by rw [← hxe]; exact hx)
    obtain ⟨C₀, hC₀, hC₀len⟩ := exists_eq_map_inl hall
    have hhole0 : IsHoleList (Thm29Aux.cG G p X) C₀ :=
      (isHoleList_map_inl (Thm29Aux.cG G p X) (Thm29Aux.cS X pn) C₀).mpr
        (by rw [← hC₀]; exact hC)
    have hholeG : IsHoleList G C₀ :=
      RestrictGraph.isHoleList_of_restrict (G := G) (W := Thm29Aux.cW p X) hhole0
    have hev : Even C₀.length := hG.1 C₀ hholeG
    rw [Nat.even_iff] at hev
    rw [Nat.odd_iff] at hCodd'
    omega
  -- *"put `y` at position 0"*
  obtain ⟨rr, hrr⟩ := HoleArithmetic.exists_rotate_head hyC
  obtain ⟨D, hDhole, hDlen, hDmem, hD0⟩ :
      ∃ D : List (V ⊕ Unit), IsHoleList (Thm29Aux.cG0 G p X pn) D ∧ D.length = C.length ∧
        (∀ x, x ∈ D ↔ x ∈ C) ∧
        ∀ (h : 0 < D.length), ((D)[0]'h) = (Sum.inr () : V ⊕ Unit) :=
    ⟨C.rotate rr, HoleBasics.isHoleList_rotate hC rr, List.length_rotate ..,
      fun _ => List.mem_rotate, hrr⟩
  have hDpos : 0 < D.length := by omega
  have hD5 : 5 ≤ D.length := by omega
  have hy0 : ((D)[0]'hDpos) = (Sum.inr () : V ⊕ Unit) := hD0 hDpos
  -- *"`C \ y` is a path"*
  have htail : IsPathFrom (Thm29Aux.cG0 G p X pn) D.tail ((D)[1]'(by omega))
      ((D)[D.length - 1]'(by omega)) := HoleMinusVertexPath.isPathFrom_tail hDhole hD5
  have htaillen : D.tail.length = D.length - 1 := by simp
  have hmemtail := HoleMinusVertexPath.mem_tail_iff hDhole hD5
  -- *"push it down to `G`"*
  have hnoinr : ∀ x ∈ D.tail, x ≠ (Sum.inr () : V ⊕ Unit) := by
    intro x hx hxe
    exact ((hmemtail x).mp hx).2 (hxe.trans hy0.symm)
  obtain ⟨Q, hQeq, hQlen0⟩ := exists_eq_map_inl hnoinr
  have hQlen : Q.length = D.length - 1 := by omega
  have hQ6 : 6 ≤ Q.length := by omega
  have hheadmem : ((D)[1]'(by omega)) ∈ D.tail := List.mem_of_mem_head? htail.2.1
  have hlastmem : ((D)[D.length - 1]'(by omega)) ∈ D.tail :=
    List.mem_of_mem_getLast? htail.2.2
  rw [hQeq] at hheadmem hlastmem
  obtain ⟨q₁, hq₁Q, hq₁⟩ := List.mem_map.mp hheadmem
  obtain ⟨qm, hqmQ, hqm⟩ := List.mem_map.mp hlastmem
  have hQpathG0 : IsPathFrom (Thm29Aux.cG0 G p X pn) (Q.map Sum.inl) (Sum.inl q₁)
      (Sum.inl qm) := by
    rw [hq₁, hqm, ← hQeq]; exact htail
  have hQpathcG : IsPathFrom (Thm29Aux.cG G p X) Q q₁ qm :=
    (isPathFrom_map_inl (Thm29Aux.cG G p X) (Thm29Aux.cS X pn) Q q₁ qm).mpr hQpathG0
  have hQD : ∀ z ∈ Q, (Sum.inl z : V ⊕ Unit) ∈ D := by
    intro z hz
    have h1 : (Sum.inl z : V ⊕ Unit) ∈ Q.map Sum.inl := List.mem_map.mpr ⟨z, hz, rfl⟩
    rw [← hQeq] at h1
    exact List.mem_of_mem_tail h1
  have hQW : ∀ z ∈ Q, z ∈ Thm29Aux.cW p X := fun z hz =>
    mem_cW_of_mem_hole hC hpn ((hDmem _).mp (hQD z hz))
  have hQG : IsPathFrom G Q q₁ qm :=
    (RestrictGraph.isPathFrom_iff_of_subset (G := G) (W := Thm29Aux.cW p X) hQW).mp hQpathcG
  -- *"the ends of `Q` belong to `X ∪ {pₙ}`"*
  have hq₁mem : q₁ ∈ X ∨ q₁ = pn := by
    have h : (Thm29Aux.cG0 G p X pn).Adj ((D)[0]'hDpos) ((D)[1]'(by omega)) :=
      (HoleMinusVertexPath.adj_head_iff hDhole hD5 (show (1 : ℕ) < D.length by omega)).mpr
        (Or.inl rfl)
    rw [hy0, ← hq₁] at h
    exact (Thm29Aux.cG0_adj_inr' q₁ ()).mp h
  have hqmmem : qm ∈ X ∨ qm = pn := by
    have h : (Thm29Aux.cG0 G p X pn).Adj ((D)[0]'hDpos) ((D)[D.length - 1]'(by omega)) :=
      (HoleMinusVertexPath.adj_head_iff hDhole hD5
        (show D.length - 1 < D.length by omega)).mpr (Or.inr rfl)
    rw [hy0, ← hqm] at h
    exact (Thm29Aux.cG0_adj_inr' qm ()).mp h
  -- *"and its interior to `V(P) \ {pₙ}`"*
  have hint : ∀ z ∈ SPGT.interior Q, z ∈ p ∧ z ≠ pn := by
    intro z hz
    have hzQ : z ∈ Q := PathBasics.interior_subset hz
    have hzW := hQW z hzQ
    have hne := (PathBasics.mem_interior_iff_of_pathFrom hQG).mp hz
    have hnotXpn : ¬ (z ∈ X ∨ z = pn) := by
      intro hcon
      have hadjz : (Thm29Aux.cG0 G p X pn).Adj (Sum.inr () : V ⊕ Unit) (Sum.inl z) :=
        (Thm29Aux.cG0_adj_inr' z ()).mpr hcon
      obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem (hQD z hzQ)
      rw [← hy0, ← hieq] at hadjz
      rcases (HoleMinusVertexPath.adj_head_iff hDhole hD5 hi).mp hadjz with h1 | h1
      · refine hne.2.1 ?_
        have hzz : (Sum.inl z : V ⊕ Unit) = ((D)[1]'(by omega)) := by
          rw [← hieq]; exact HoleArithmetic.getElem_congr_idx D hi (by omega) h1
        rw [← hq₁] at hzz
        exact Sum.inl_injective hzz
      · refine hne.2.2 ?_
        have hzz : (Sum.inl z : V ⊕ Unit) = ((D)[D.length - 1]'(by omega)) := by
          rw [← hieq]; exact HoleArithmetic.getElem_congr_idx D hi (by omega) h1
        rw [← hqm] at hzz
        exact Sum.inl_injective hzz
    refine ⟨?_, ?_⟩
    · rcases Thm29Aux.mem_cW.mp hzW with h | h
      · exact h
      · exact absurd (Or.inl h) hnotXpn
    · intro hcon
      exact hnotXpn (Or.inr hcon)
  exact ⟨Q, q₁, qm, hQG, by simp only [pathLength]; omega, hq₁mem, hqmmem, hQW, hint⟩

/-! ## The odd-hole branch of 2.9 -/

/-- **2.9, odd-hole branch.**  If the auxiliary graph `G₀ = (G \ Y) + y` has an odd hole of
length `≥ 7`, then alternative 2 of 2.9 holds. -/
theorem branch_oddhole {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    {p : List V} {p₁ pn : V} (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (heven : Even (pathLength p)) (h4 : 4 ≤ pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pn))
    {C : List (V ⊕ Unit)} (hC : IsHoleList (Thm29Aux.cG0 G p X pn) C)
    (hCodd : Odd (holeLength C)) (hC7 : 7 ≤ holeLength C) :
    ∃ y₁ ∈ Y, ∃ y₂ ∈ Y, ¬ G.Adj y₁ y₂ ∧ IsPathList G (y₁ :: (p.dropLast ++ [y₂])) := by
  classical
  have hC7' : 7 ≤ C.length := hC7
  have hCodd' : Odd C.length := hCodd
  have hCoddm : C.length % 2 = 1 := Nat.odd_iff.mp hCodd'
  have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp
  have hplen5 : 5 ≤ p.length := by omega
  have hpevenm : pathLength p % 2 = 0 := Nat.even_iff.mp heven
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hp0 : (p[0]'(by omega)) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
  have hplast : (p[p.length - 1]'(by omega)) = pn :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hc => hpXY w hw (Or.inl hc)
  have hpY : ∀ w ∈ p, w ∉ Y := fun w hw hc => hpXY w hw (Or.inr hc)
  have hXnY : ∀ x ∈ X, x ∉ Y := fun x hx hc => (Set.disjoint_left.mp hXY) hx hc
  have hYnX : ∀ y ∈ Y, y ∉ X := fun y hy hc => (Set.disjoint_left.mp hXY) hc hy
  have hpnY : VertexComplete G pn Y := (hYuniq pn hpnmem).mpr rfl
  have hnd : p.Nodup := hp.2.1
  have hpinj : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
      ((p[i]'hi) = (p[j]'hj)) ↔ i = j := fun i j hi hj => hnd.getElem_inj_iff
  -- the odd path `Q`
  obtain ⟨Q, q₁, qm, hQG, hQpl, hq₁mem, hqmmem, hQW, hQint⟩ :=
    exists_odd_path hG hpnmem hC hCodd hC7
  have hQl : IsPathList G Q := hQG.1
  have hQlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQl
  have hQpl5 : 5 ≤ pathLength Q := by omega
  have hQoddm : pathLength Q % 2 = 1 := by omega
  have hQoddp : Odd (pathLength Q) := Nat.odd_iff.mpr hQoddm
  have hQ3 : 3 ≤ Q.length := by omega
  have hQY : ∀ z ∈ Q, z ∉ Y := by
    intro z hz
    rcases Thm29Aux.mem_cW.mp (hQW z hz) with h | h
    · exact hpY z h
    · exact hXnY z h
  have hq₁c : VertexComplete G q₁ Y := by
    rcases hq₁mem with h | h
    · exact hcompl q₁ h
    · rw [h]; exact hpnY
  have hqmc : VertexComplete G qm Y := by
    rcases hqmmem with h | h
    · exact hcompl qm h
    · rw [h]; exact hpnY
  have hintnc : ∀ z ∈ SPGT.interior Q, ¬ VertexComplete G z Y := by
    intro z hz hc
    obtain ⟨hzp, hzn⟩ := hQint z hz
    exact hzn ((hYuniq z hzp).mp hc)
  have hq0 : (Q[0]'(by omega)) = q₁ := PathBasics.getElem_zero_of_head? hQG.2.1 (by omega)
  have hqn : (Q[Q.length - 1]'(by omega)) = qm :=
    PathBasics.getElem_last_of_getLast? hQG.2.2 (by omega)
  -- *"By 2.1 `Y` contains a leap for `Q`"*
  rcases thm_2_1 G hG Y hYa Q q₁ qm hQG hQY hQoddp hq₁c hqmc with
    hc1 | ⟨-, y₁, hy₁Y, y₂, hy₂Y, hleap⟩ | ⟨hc3, -⟩
  · -- no edge of `Q` is `Y`-complete: the only `Y`-complete vertices are its two ends
    exfalso
    obtain ⟨u, hu, v, hv, hadjuv, huc, hvc⟩ := hc1
    have hclass : ∀ w ∈ Q, VertexComplete G w Y → w = q₁ ∨ w = qm := by
      intro w hw hwc
      by_contra hcon
      push Not at hcon
      exact hintnc w ((PathBasics.mem_interior_iff_of_pathFrom hQG).mpr
        ⟨hw, hcon.1, hcon.2⟩) hwc
    have hends : ¬ G.Adj q₁ qm := by
      rw [← hq0, ← hqn]
      exact PathBasics.path_ends_not_adj hQl hQ3
    have h1 := hclass u hu huc
    have h2 := hclass v hv hvc
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hadjuv
    · exact G.irrefl hadjuv
    · exact hends hadjuv
    · exact hends hadjuv.symm
    · exact G.irrefl hadjuv
  · -- the leap branch
    obtain ⟨-, hQ2, hy12ne, hy12nadj, hAd, hBd⟩ := hleap
    -- *"so there is an odd path `R` of length `≥ 5` with ends `y₁, y₂` in `Y`"*
    have hM : IsPathFrom G (SPGT.interior Q) (Q[1]'(by omega))
        (Q[Q.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hQl hQ3
    have hMlen : (SPGT.interior Q).length = Q.length - 2 := PathBasics.interior_length Q
    have hMlen4 : 4 ≤ (SPGT.interior Q).length := by omega
    have hLeven : (SPGT.interior Q).length % 2 = 0 := by omega
    have hMsubQ : ∀ z ∈ SPGT.interior Q, z ∈ Q := fun z hz => PathBasics.interior_subset hz
    have hMidx : ∀ z ∈ SPGT.interior Q, ∃ (k : ℕ) (hk : k < Q.length),
        1 ≤ k ∧ k + 2 ≤ Q.length ∧ (Q[k]'hk) = z :=
      fun z hz => PathBasics.exists_getElem_of_mem_interior hQl hz
    have hy₁M : y₁ ∉ SPGT.interior Q := fun h => hQY y₁ (hMsubQ y₁ h) hy₁Y
    have hy₂M : y₂ ∉ SPGT.interior Q := fun h => hQY y₂ (hMsubQ y₂ h) hy₂Y
    have hadjy₁ : G.Adj y₁ (Q[1]'(by omega)) := (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have hadjy₂ : G.Adj y₂ (Q[Q.length - 2]'(by omega)) :=
      (hBd (Q.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    have hy₁other : ∀ x ∈ SPGT.interior Q, x ≠ (Q[1]'(by omega)) → ¬ G.Adj y₁ x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := hMidx x hx
      have hcase := (hAd k hk).mp hadj
      exact hxne (HoleArithmetic.getElem_congr_idx Q hk (by omega) (by omega))
    have hy₂other : ∀ x ∈ SPGT.interior Q, x ≠ (Q[Q.length - 2]'(by omega)) →
        ¬ G.Adj y₂ x := by
      intro x hx hxne hadj
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := hMidx x hx
      have hcase := (hBd k hk).mp hadj
      exact hxne (HoleArithmetic.getElem_congr_idx Q hk (by omega) (by omega))
    have hR : IsPathFrom G (y₁ :: (SPGT.interior Q ++ [y₂])) y₁ y₂ :=
      PathAttach.isPathFrom_cons_concat hM hadjy₁ hadjy₂ hy12nadj hy12ne hy₁M hy₂M
        hy₁other hy₂other
    have hRmem : ∀ x ∈ (y₁ :: (SPGT.interior Q ++ [y₂])),
        x = y₁ ∨ x ∈ SPGT.interior Q ∨ x = y₂ :=
      fun x hx => PathAttach.mem_cons_append_singleton.mp hx
    have hRint : SPGT.interior (y₁ :: (SPGT.interior Q ++ [y₂])) = SPGT.interior Q := by
      simp [SPGT.interior]
    have hRpl : pathLength (y₁ :: (SPGT.interior Q ++ [y₂])) = (SPGT.interior Q).length + 1 :=
      PathAttach.pathLength_cons_append_singleton y₁ y₂ (SPGT.interior Q)
    have hy₁p : y₁ ∉ p := fun h => hpY y₁ h hy₁Y
    have hy₂p : y₂ ∉ p := fun h => hpY y₂ h hy₂Y
    -- *"Since `R` cannot be completed to a hole via `y₂-pₙ-y₁` it follows that `pₙ` has a
    -- neighbour in `R*`"*
    have hpnnbr : ∃ w ∈ SPGT.interior Q, G.Adj pn w := by
      by_contra hcon
      push Not at hcon
      have hpnpath : IsPathFrom G [pn] pn pn :=
        ⟨PathBasics.isPathList_singleton G pn, rfl, rfl⟩
      have hdisj : ∀ x ∈ (y₁ :: (SPGT.interior Q ++ [y₂])), x ∉ ([pn] : List V) := by
        intro x hx hxpn
        have hxe : x = pn := by simpa using hxpn
        rcases hRmem x hx with h | h | h
        · exact hpY pn hpnmem (by rw [← hxe, h]; exact hy₁Y)
        · exact (hQint x h).2 hxe
        · exact hpY pn hpnmem (by rw [← hxe, h]; exact hy₂Y)
      have hcross : ∀ x ∈ (y₁ :: (SPGT.interior Q ++ [y₂])), ∀ z ∈ ([pn] : List V),
          (G.Adj x z ↔ (x = y₂ ∧ z = pn) ∨ (x = y₁ ∧ z = pn)) := by
        intro x hx z hz
        have hze : z = pn := by simpa using hz
        subst hze
        rcases hRmem x hx with h | h | h
        · rw [h]
          exact iff_of_true (hpnY y₁ hy₁Y).symm (Or.inr ⟨rfl, rfl⟩)
        · refine iff_of_false (fun hadj => hcon x h hadj.symm) ?_
          rintro (⟨he, -⟩ | ⟨he, -⟩)
          · exact hQY x (hMsubQ x h) (by rw [he]; exact hy₂Y)
          · exact hQY x (hMsubQ x h) (by rw [he]; exact hy₁Y)
        · rw [h]
          exact iff_of_true (hpnY y₂ hy₂Y).symm (Or.inl ⟨rfl, rfl⟩)
      have hlen4 : 4 ≤ (y₁ :: (SPGT.interior Q ++ [y₂])).length + ([pn] : List V).length := by
        simp only [List.length_cons, List.length_append, List.length_nil]
        omega
      have hhole : IsHoleList G ((y₁ :: (SPGT.interior Q ++ [y₂])) ++ [pn]) :=
        PathGlue.glue_hole hR hpnpath hdisj hcross hlen4
      have hev : Even ((y₁ :: (SPGT.interior Q ++ [y₂])) ++ [pn]).length := hG.1 _ hhole
      rw [Nat.even_iff] at hev
      simp only [List.length_append, List.length_cons, List.length_nil] at hev
      omega
    -- *"and so `pₙ₋₁` belongs to `R`"*
    obtain ⟨w, hwM, hadjpnw⟩ := hpnnbr
    obtain ⟨hwp, hwne⟩ := hQint w hwM
    obtain ⟨kw, hkw, hkweq⟩ := List.getElem_of_mem hwp
    have hkwval : kw = p.length - 2 := by
      have hadj' : G.Adj (p[p.length - 1]'(by omega)) (p[kw]'hkw) := by
        rw [hplast, hkweq]; exact hadjpnw
      have hcase := (PathBasics.path_adj_iff hp (by omega) hkw).mp hadj'
      omega
    have hpn2M : (p[p.length - 2]'(by omega)) ∈ SPGT.interior Q := by
      have heq : (p[p.length - 2]'(show p.length - 2 < p.length by omega)) = w :=
        (HoleArithmetic.getElem_congr_idx p (by omega) hkw hkwval.symm).trans hkweq
      rw [heq]; exact hwM
    -- *"`R*` is a contiguous slice of `P`"*
    have hMsubp : ∀ z ∈ SPGT.interior Q, z ∈ p := fun z hz => (hQint z hz).1
    obtain ⟨r, hrle, hrmem, hror⟩ := SubpathIsSlice.exists_index_of_subpath hp hM.1 hMsubp
    have hslice1 : r ≤ p.length - 2 ∧ p.length - 2 < r + (SPGT.interior Q).length := by
      obtain ⟨k, hk, hk1, hk2, hkeq⟩ := (hrmem _).mp hpn2M
      have hkv : k = p.length - 2 := (hpinj k (p.length - 2) hk (by omega)).mp hkeq
      omega
    have hslice2 : ¬ (r ≤ p.length - 1 ∧ p.length - 1 < r + (SPGT.interior Q).length) := by
      rintro ⟨ha, hb⟩
      have hpnM : pn ∈ SPGT.interior Q :=
        (hrmem pn).mpr ⟨p.length - 1, by omega, ha, hb, hplast⟩
      exact (hQint pn hpnM).2 rfl
    have hrL : r + (SPGT.interior Q).length = p.length - 1 := by omega
    have hreven : r % 2 = 0 := by omega
    by_cases hr0 : r = 0
    · -- *"If also `p₁` belongs to `R` then the theorem holds"*
      subst hr0
      have hLeq : (SPGT.interior Q).length = p.length - 1 := by omega
      have hslice : (p.drop 0).take (SPGT.interior Q).length = p.dropLast := by
        rw [List.drop_zero, hLeq, ← List.dropLast_eq_take]
      rcases hror with he | he
      · rw [hslice] at he
        refine ⟨y₁, hy₁Y, y₂, hy₂Y, hy12nadj, ?_⟩
        rw [← he]
        exact hR.1
      · rw [hslice] at he
        refine ⟨y₂, hy₂Y, y₁, hy₁Y, fun hadj => hy12nadj hadj.symm, ?_⟩
        rw [← he]
        have hrev := PathBasics.isPathList_reverse hR.1
        have heq2 : (y₁ :: (SPGT.interior Q ++ [y₂])).reverse
            = y₂ :: ((SPGT.interior Q).reverse ++ [y₁]) := by simp
        rw [heq2] at hrev
        exact hrev
    · -- *"so we may assume it does not.  Since `R` is odd and `P` is even it follows that `p₂`
      -- also does not belong to `R`, and so `p₁` has no neighbour in `R*`"*
      exfalso
      have hr2 : 2 ≤ r := by omega
      have hp₁notM : p₁ ∉ SPGT.interior Q := by
        intro hcon
        obtain ⟨k, hk, hk1, hk2, hkeq⟩ := (hrmem p₁).mp hcon
        rw [← hp0] at hkeq
        have hkv : k = 0 := (hpinj k 0 hk (by omega)).mp hkeq
        omega
      have hp1notM : (p[1]'(show (1 : ℕ) < p.length by omega)) ∉ SPGT.interior Q := by
        intro hcon
        obtain ⟨k, hk, hk1, hk2, hkeq⟩ := (hrmem _).mp hcon
        have hkv : k = 1 := (hpinj k 1 hk (by omega)).mp hkeq
        omega
      have hp₁nonbr : ∀ z ∈ SPGT.interior Q, ¬ G.Adj p₁ z := by
        intro z hz hadj
        obtain ⟨hzp, -⟩ := hQint z hz
        obtain ⟨kz, hkz, hkzeq⟩ := List.getElem_of_mem hzp
        have hadj' : G.Adj (p[0]'(by omega)) (p[kz]'hkz) := by
          rw [hp0, hkzeq]; exact hadj
        have hcase := (PathBasics.path_adj_iff hp (by omega) hkz).mp hadj'
        refine hp1notM ?_
        have heq3 : (p[1]'(show (1 : ℕ) < p.length by omega)) = z :=
          (HoleArithmetic.getElem_congr_idx p (by omega) hkz (by omega)).trans hkzeq
        rw [heq3]; exact hz
      -- *"yet the ends of `R` are `X`-complete and its internal vertices are not,
      -- contrary to 2.2"*
      have hRnotX : ∀ z ∈ (y₁ :: (SPGT.interior Q ++ [y₂])), z ∉ X := by
        intro z hz
        rcases hRmem z hz with h | h | h
        · rw [h]; exact hYnX y₁ hy₁Y
        · exact hpX z (hQint z h).1
        · rw [h]; exact hYnX y₂ hy₂Y
      have hy₁X : VertexComplete G y₁ X := fun x hx => (hcompl x hx y₁ hy₁Y).symm
      have hy₂X : VertexComplete G y₂ X := fun x hx => (hcompl x hx y₂ hy₂Y).symm
      have hRoddp : Odd (pathLength (y₁ :: (SPGT.interior Q ++ [y₂]))) := by
        rw [hRpl, Nat.odd_iff]; omega
      have hnoedgeR : ¬ ∃ u ∈ (y₁ :: (SPGT.interior Q ++ [y₂])),
          ∃ v ∈ (y₁ :: (SPGT.interior Q ++ [y₂])), EdgeComplete G X u v := by
        rintro ⟨u, hu, v, hv, hadjuv, huc, hvc⟩
        have hclass : ∀ z ∈ (y₁ :: (SPGT.interior Q ++ [y₂])), VertexComplete G z X →
            z = y₁ ∨ z = y₂ := by
          intro z hz hzc
          rcases hRmem z hz with h | h | h
          · exact Or.inl h
          · exfalso
            have hzp := (hQint z h).1
            have hzp₁ := (hXuniq z hzp).mp hzc
            exact hp₁notM (by rw [← hzp₁]; exact h)
          · exact Or.inr h
        have h1 := hclass u hu huc
        have h2 := hclass v hv hvc
        rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] at hadjuv
        · exact G.irrefl hadjuv
        · exact hy12nadj hadjuv
        · exact hy12nadj hadjuv.symm
        · exact G.irrefl hadjuv
      have h22 := thm_2_2 G hG X hXa (y₁ :: (SPGT.interior Q ++ [y₂])) y₁ y₂ hR hRnotX
        hRoddp hy₁X hy₂X hnoedgeR
      obtain ⟨z, hz, hadjz⟩ := h22 p₁ ((hXuniq p₁ hp₁mem).mpr rfl)
      rw [hRint] at hz
      exact hp₁nonbr z hz hadjz
  · -- `pathLength Q = 3` contradicts `5 ≤ pathLength Q`
    exact absurd hc3 (by omega)

end Workspace.ProofLemmas.Thm29OddHole
