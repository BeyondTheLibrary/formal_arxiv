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
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.ProofLemmas.Thm29Aux

/-!
# 2.9, the odd-antihole branch

This module proves the **last paragraph** of the printed proof of 2.9:

> *"Since an odd hole of length 5 is also an odd antihole, we may assume that there is an odd
> antihole in `G₀`, say `D`.  Again `D` must use `y`, and uses exactly two nonneighbours of `y`;
> so in `G` there is an odd antipath `Q` between adjacent vertices of `P \ pₙ` (say `u` and `v`),
> and with interior in `X ∪ {pₙ}`.  Since `u` and `v` are not `Y`-complete, they are also joined
> by an antipath `R` with interior in `Y`, and `R` must also be odd since its union with `Q` is
> an antihole.  Since `R` cannot be completed to an antihole via `v-pₙ-u` it follows that `pₙ` is
> adjacent to one of `u,v`, and hence we may assume that `u = pₙ₋₂` and `v = pₙ₋₁`.  Since `P` has
> length `≥ 4` it follows that `u,v` are also joined by an antipath with interior in `X`, say `S`,
> and again `S` is odd since its union with `R` is an antihole.  But `S` can be completed to an
> antihole via `v-p₁-u`, a contradiction.  This proves 2.9."*

The paragraph ends in a contradiction, so the conclusion of `branch_antihole` is `False`.

The auxiliary graph `G₀ = (G \ Y) + y` (with `N(y) = X ∪ {pₙ}`) is
`Workspace.ProofLemmas.Thm29Aux.cG0`; everything below goes through its three adjacency `Iff`s
(`cG0_adj_inl`, `cG0_adj_inr`, `cG0_adj_inr'`) and never unfolds the definition.

Three moves recur and are isolated as private lemmas at the head of the file:

* `adj_head_interior` / `adj_last_interior` — *on an induced path an end is adjacent to exactly
  one interior vertex, namely the one next to it*;
* `glue_antihole` — *the union of two antipaths between the same pair `u,v`, whose interiors are
  `G`-complete to each other, is an antihole of length `|Q| + |R|`* (used for `Q ∪ R` and for
  `S ∪ R`);
* `close_antipath` — *an antipath between `u,v` closes into an antihole through one extra vertex
  `w` nonadjacent to `u` and `v` and complete to the antipath's interior* (used for `v-pₙ-u` and
  for `v-p₁-u`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm29OddAntihole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

section Helpers

variable {V : Type*}

/-- **On an induced path the first end is adjacent to exactly one interior vertex**, namely
`r[1]`.  (Stated for an arbitrary graph `H`, so the antipath form is the same lemma at `Gᶜ`.) -/
private theorem adj_head_interior {H : SimpleGraph V} {r : List V} {a b : V}
    (hr : IsPathFrom H r a b) (h3 : 3 ≤ r.length) {z : V} (hz : z ∈ SPGT.interior r) :
    (H.Adj a z ↔ z = (r[1]'(by omega))) := by
  have hrl : IsPathList H r := hr.1
  have hpos : 0 < r.length := by omega
  have h0 : (r[0]'hpos) = a := PathBasics.getElem_zero_of_head? hr.2.1 hpos
  obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hrl hz
  constructor
  · intro hadj
    rw [← h0] at hadj
    have hcc := (PathBasics.path_adj_iff hrl hpos hk).mp hadj
    exact hrl.2.1.getElem_inj_iff.mpr (by omega)
  · intro heq
    have hk' : k = 1 := hrl.2.1.getElem_inj_iff.mp heq
    rw [← h0]
    exact (PathBasics.path_adj_iff hrl hpos hk).mpr (by omega)

/-- **On an induced path the last end is adjacent to exactly one interior vertex**, namely
`r[|r|-2]`. -/
private theorem adj_last_interior {H : SimpleGraph V} {r : List V} {a b : V}
    (hr : IsPathFrom H r a b) (h3 : 3 ≤ r.length) {z : V} (hz : z ∈ SPGT.interior r) :
    (H.Adj b z ↔ z = (r[r.length - 2]'(by omega))) := by
  have hrl : IsPathList H r := hr.1
  have hpos : 0 < r.length := by omega
  have hlt : r.length - 1 < r.length := by omega
  have hn : (r[r.length - 1]'hlt) = b := PathBasics.getElem_last_of_getLast? hr.2.2 hpos
  obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hrl hz
  constructor
  · intro hadj
    rw [← hn] at hadj
    have hcc := (PathBasics.path_adj_iff hrl hlt hk).mp hadj
    exact hrl.2.1.getElem_inj_iff.mpr (by omega)
  · intro heq
    have hk' : k = r.length - 2 := hrl.2.1.getElem_inj_iff.mp heq
    rw [← hn]
    exact (PathBasics.path_adj_iff hrl hlt hk).mpr (by omega)

/-- **The union of two antipaths between the same pair of vertices is an antihole.**  The paper's
*"`R` must also be odd since its union with `Q` is an antihole"* (and, later, *"`S` is odd since
its union with `R` is an antihole"*).

The hole is `Q ++ (R*)ᵣₑᵥ`, so its length is exactly `pathLength Q + pathLength R`; the only
input beyond disjointness is that the two interiors are `G`-complete to each other (which in
`Gᶜ` means anticomplete). -/
private theorem glue_antihole {G : SimpleGraph V} {Q R : List V} {u v : V}
    (hQ : IsAntipathFrom G Q u v) (hR : IsAntipathFrom G R u v)
    (hQ3 : 3 ≤ Q.length) (hR3 : 3 ≤ R.length)
    (hdisj : ∀ x ∈ Q, x ∉ SPGT.interior R)
    (hcr : ∀ x ∈ SPGT.interior Q, ∀ z ∈ SPGT.interior R, G.Adj x z) :
    IsHoleList Gᶜ (Q ++ (SPGT.interior R).reverse) ∧
      holeLength (Q ++ (SPGT.interior R).reverse) = pathLength Q + pathLength R := by
  have hQ' : IsPathFrom Gᶜ Q u v := hQ
  have hR' : IsPathFrom Gᶜ R u v := hR
  have hQl : IsPathList Gᶜ Q := hQ'.1
  have hRl : IsPathList Gᶜ R := hR'.1
  have hne : u ≠ v := by
    refine PathBasics.isPathFrom_ends_ne hQ' ?_
    rw [PathBasics.pathLength_eq]
    omega
  have hIR : IsPathFrom Gᶜ (SPGT.interior R) (R[1]'(by omega))
      (R[R.length - 2]'(by omega)) := PathGlue.isPathFrom_interior hRl hR3
  have hIRrev : IsPathFrom Gᶜ (SPGT.interior R).reverse (R[R.length - 2]'(by omega))
      (R[1]'(by omega)) := PathBasics.isPathFrom_reverse hIR
  have hdisj' : ∀ x ∈ Q, x ∉ (SPGT.interior R).reverse := by
    intro x hx hc
    exact hdisj x hx (List.mem_reverse.mp hc)
  have hcross : ∀ x ∈ Q, ∀ z ∈ (SPGT.interior R).reverse,
      (Gᶜ.Adj x z ↔ ((x = v ∧ z = (R[R.length - 2]'(by omega))) ∨
        (x = u ∧ z = (R[1]'(by omega))))) := by
    intro x hx z hz'
    have hz : z ∈ SPGT.interior R := List.mem_reverse.mp hz'
    by_cases hxu : x = u
    · rw [hxu, adj_head_interior hR' hR3 hz]
      constructor
      · intro h
        exact Or.inr ⟨rfl, h⟩
      · rintro (⟨hc, -⟩ | ⟨-, hc⟩)
        · exact absurd hc hne
        · exact hc
    · by_cases hxv : x = v
      · rw [hxv, adj_last_interior hR' hR3 hz]
        constructor
        · intro h
          exact Or.inl ⟨rfl, h⟩
        · rintro (⟨-, hc⟩ | ⟨hc, -⟩)
          · exact hc
          · exact absurd hc.symm hne
      · have hxi : x ∈ SPGT.interior Q :=
          (PathBasics.mem_interior_iff_of_pathFrom hQ').mpr ⟨hx, hxu, hxv⟩
        refine iff_of_false ?_ ?_
        · intro hadj
          exact hadj.2 (hcr x hxi z hz)
        · rintro (⟨hc, -⟩ | ⟨hc, -⟩)
          · exact hxv hc
          · exact hxu hc
  have hrevlen : (SPGT.interior R).reverse.length = R.length - 2 := by
    rw [List.length_reverse, PathBasics.interior_length]
  have hlen : 4 ≤ Q.length + (SPGT.interior R).reverse.length := by
    rw [hrevlen]; omega
  refine ⟨PathGlue.glue_hole hQ' hIRrev hdisj' hcross hlen, ?_⟩
  have e1 : holeLength (Q ++ (SPGT.interior R).reverse) = Q.length + (R.length - 2) := by
    rw [show holeLength (Q ++ (SPGT.interior R).reverse)
        = (Q ++ (SPGT.interior R).reverse).length from rfl, List.length_append, hrevlen]
  rw [e1, PathBasics.pathLength_eq, PathBasics.pathLength_eq]
  omega

/-- **Closing an antipath into an antihole through one extra vertex.**  The paper's *"`R` cannot
be completed to an antihole via `v-pₙ-u`"* and *"`S` can be completed to an antihole via
`v-p₁-u`"*: the extra vertex `w` is `G`-nonadjacent to both ends (so `Gᶜ`-adjacent to them) and
`G`-complete to the interior (so `Gᶜ`-anticomplete to it). -/
private theorem close_antipath {G : SimpleGraph V} {R : List V} {u v w : V}
    (hR : IsAntipathFrom G R u v) (hR3 : 3 ≤ R.length) (hwR : w ∉ R)
    (hwu : ¬ G.Adj w u) (hwv : ¬ G.Adj w v)
    (hwint : ∀ z ∈ SPGT.interior R, G.Adj w z) :
    IsHoleList Gᶜ (R ++ [w]) ∧ holeLength (R ++ [w]) = pathLength R + 2 := by
  have hR' : IsPathFrom Gᶜ R u v := hR
  have hRl : IsPathList Gᶜ R := hR'.1
  have humem : u ∈ R := PathBasics.head_mem hR'.2.1
  have hvmem : v ∈ R := PathBasics.getLast_mem hR'.2.2
  have hwu' : w ≠ u := fun h => hwR (h ▸ humem)
  have hwv' : w ≠ v := fun h => hwR (h ▸ hvmem)
  have hsing : IsPathFrom Gᶜ [w] w w := ⟨PathBasics.isPathList_singleton Gᶜ w, rfl, rfl⟩
  have hdisj : ∀ x ∈ R, x ∉ [w] := by
    intro x hx hc
    simp only [List.mem_singleton] at hc
    exact hwR (hc ▸ hx)
  have hcross : ∀ x ∈ R, ∀ z ∈ [w], (Gᶜ.Adj x z ↔ ((x = v ∧ z = w) ∨ (x = u ∧ z = w))) := by
    intro x hx z hz
    simp only [List.mem_singleton] at hz
    rw [hz]
    by_cases hxu : x = u
    · rw [hxu]
      exact iff_of_true ⟨fun h => hwu' h.symm, fun h => hwu h.symm⟩ (Or.inr ⟨rfl, rfl⟩)
    · by_cases hxv : x = v
      · rw [hxv]
        exact iff_of_true ⟨fun h => hwv' h.symm, fun h => hwv h.symm⟩ (Or.inl ⟨rfl, rfl⟩)
      · have hxi : x ∈ SPGT.interior R :=
          (PathBasics.mem_interior_iff_of_pathFrom hR').mpr ⟨hx, hxu, hxv⟩
        refine iff_of_false ?_ ?_
        · intro hadj
          exact hadj.2 (hwint x hxi).symm
        · rintro (⟨hc, -⟩ | ⟨hc, -⟩)
          · exact hxv hc
          · exact hxu hc
  have hslen : ([w] : List V).length = 1 := rfl
  have hlen : 4 ≤ R.length + ([w] : List V).length := by rw [hslen]; omega
  refine ⟨PathGlue.glue_hole hR' hsing hdisj hcross hlen, ?_⟩
  have e1 : holeLength (R ++ [w]) = R.length + 1 := by
    rw [show holeLength (R ++ [w]) = (R ++ [w]).length from rfl, List.length_append, hslen]
  rw [e1, PathBasics.pathLength_eq]
  omega

/-- Any element of `V ⊕ Unit` other than the new vertex comes from `V`. -/
private theorem exists_inl {x : V ⊕ Unit} (h : x ≠ (Sum.inr () : V ⊕ Unit)) :
    ∃ a : V, x = Sum.inl a := by
  rcases x with a | t
  · exact ⟨a, rfl⟩
  · exact absurd (show (Sum.inr t : V ⊕ Unit) = Sum.inr () by cases t; rfl) h

end Helpers

section Main

/-- *"Since an odd hole of length 5 is also an odd antihole, we may assume that there is an odd
antihole in `G₀`, say `D`. … But `S` can be completed to an antihole via `v-p₁-u`, a
contradiction.  This proves 2.9."* -/
theorem branch_antihole {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    {p : List V} {p₁ pn : V} (hp : IsPathList G p) (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (heven : Even (pathLength p)) (h4 : 4 ≤ pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pn))
    {D : List (V ⊕ Unit)} (hD : IsHoleList (Thm29Aux.cG0 G p X pn)ᶜ D)
    (hDodd : Odd (holeLength D)) :
    False := by
  classical
  ---------------------------------------------------------------------------
  -- Basic facts about `P`
  ---------------------------------------------------------------------------
  have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hp
  have hm5 : 5 ≤ p.length := by omega
  have hnd : p.Nodup := hp.2.1
  have hpX : ∀ w ∈ p, w ∉ X := fun w hw hc => hpXY w hw (Or.inl hc)
  have hpY : ∀ w ∈ p, w ∉ Y := fun w hw hc => hpXY w hw (Or.inr hc)
  have hXnY : ∀ x ∈ X, x ∉ Y := fun x hx hc => (Set.disjoint_left.mp hXY) hx hc
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hppos : 0 < p.length := by omega
  have hplt : p.length - 1 < p.length := by omega
  have hp0 : (p[0]'hppos) = p₁ := PathBasics.getElem_zero_of_head? hhead hppos
  have hplast : (p[p.length - 1]'hplt) = pn := PathBasics.getElem_last_of_getLast? hlast hppos
  have hpnY : VertexComplete G pn Y := (hYuniq pn hpnmem).mpr rfl
  have hp₁X : VertexComplete G p₁ X := (hXuniq p₁ hp₁mem).mpr rfl
  have hoddD : Odd D.length := hDodd
  -- the three adjacency `Iff`s of `G₀`, specialised once
  have hadjl : ∀ a b : V, (Thm29Aux.cG0 G p X pn).Adj (Sum.inl a) (Sum.inl b) ↔
      (G.Adj a b ∧ (a ∈ p ∨ a ∈ X) ∧ (b ∈ p ∨ b ∈ X)) := fun a b => Thm29Aux.cG0_adj_inl a b
  have hadjr : ∀ (a : V) (t : Unit), (Thm29Aux.cG0 G p X pn).Adj (Sum.inr t) (Sum.inl a) ↔
      (a ∈ X ∨ a = pn) := fun a t => Thm29Aux.cG0_adj_inr' a t
  have hadjr2 : ∀ (a : V) (t : Unit), (Thm29Aux.cG0 G p X pn).Adj (Sum.inl a) (Sum.inr t) ↔
      (a ∈ X ∨ a = pn) := fun a t => Thm29Aux.cG0_adj_inr a t
  ---------------------------------------------------------------------------
  -- (1)  *"Again `D` must use `y`"*
  ---------------------------------------------------------------------------
  have hy : (Sum.inr () : V ⊕ Unit) ∈ D := by
    by_contra hyD
    have hne : ∀ x ∈ D, x ≠ (Sum.inr () : V ⊕ Unit) := fun x hx hc => hyD (hc ▸ hx)
    obtain ⟨D₀, hD₀, hD₀len⟩ := AddPendantVertexTransport.exists_eq_map_inl hne
    have h1 : IsHoleList ((AddPendantVertexTransport.addPendantVertex (Thm29Aux.cG G p X)
        (Thm29Aux.cS X pn))ᶜ) (D₀.map Sum.inl) := by
      rw [← hD₀]; exact hD
    have h2 : IsHoleList (Thm29Aux.cG G p X)ᶜ D₀ :=
      (AddPendantVertexTransport.isHoleList_compl_map_inl (Thm29Aux.cG G p X)
        (Thm29Aux.cS X pn) D₀).mpr h1
    have h2' : IsHoleList (RestrictGraph.restrictTo G (Thm29Aux.cW p X))ᶜ D₀ := h2
    have h3 : IsHoleList Gᶜ D₀ := RestrictGraph.isHoleList_compl_of_restrict h2'
    have hev : Even D₀.length := hG.2 D₀ h3
    rw [Nat.even_iff] at hev
    have hod := hoddD
    rw [Nat.odd_iff] at hod
    omega
  ---------------------------------------------------------------------------
  -- (2)  every other vertex of `D` lies in `W = V(P) ∪ X`
  ---------------------------------------------------------------------------
  have hSW : ∀ z : V, (z ∈ X ∨ z = pn) → (z ∈ p ∨ z ∈ X) := by
    rintro z (hz | rfl)
    · exact Or.inr hz
    · exact Or.inl hpnmem
  have hmemW : ∀ z : V, (Sum.inl z : V ⊕ Unit) ∈ D → (z ∈ p ∨ z ∈ X) := by
    intro z hz
    by_contra hzW
    have hiso : ∀ x : V ⊕ Unit, ¬ (Thm29Aux.cG0 G p X pn).Adj (Sum.inl z) x := by
      rintro (a | t) hadj
      · exact hzW ((hadjl z a).mp hadj).2.1
      · exact hzW (hSW z ((hadjr2 z t).mp hadj))
    exact RestrictGraph.notMem_compl_hole_of_isolated hD hiso hz
  ---------------------------------------------------------------------------
  -- (3)  rotate `y` into position `0`
  ---------------------------------------------------------------------------
  obtain ⟨E, hE, hE0fun, hEmem, hE5, hEodd⟩ :
      ∃ E : List (V ⊕ Unit),
        IsHoleList ((Thm29Aux.cG0 G p X pn)ᶜ) E ∧
        (∀ h : 0 < E.length, (E[0]'h) = (Sum.inr () : V ⊕ Unit)) ∧
        (∀ z, z ∈ E → z ∈ D) ∧ 5 ≤ E.length ∧ Odd E.length := by
    obtain ⟨r, hr⟩ := HoleArithmetic.exists_rotate_head hy
    have hrot : IsHoleList ((Thm29Aux.cG0 G p X pn)ᶜ) (D.rotate r) :=
      HoleBasics.isHoleList_rotate hD r
    have hlr : (D.rotate r).length = D.length := by simp
    have hodd : Odd (D.rotate r).length := by rw [hlr]; exact hoddD
    have hge4 : 4 ≤ (D.rotate r).length := HoleBasics.hole_length_ge_four hrot
    refine ⟨D.rotate r, hrot, hr, fun z hz => List.mem_rotate.mp hz, ?_, hodd⟩
    obtain ⟨k, hk⟩ := hodd
    omega
  have hEpos : 0 < E.length := by omega
  have hone_lt : 1 < E.length := by omega
  have hlast_lt : E.length - 1 < E.length := by omega
  have hEy : (E[0]'hEpos) = (Sum.inr () : V ⊕ Unit) := hE0fun hEpos
  have hEnd : E.Nodup := HoleBasics.hole_nodup hE
  ---------------------------------------------------------------------------
  -- (4)  `D \ y` is an antipath; `y` has exactly two nonneighbours on `D`
  ---------------------------------------------------------------------------
  have htail : IsPathFrom ((Thm29Aux.cG0 G p X pn)ᶜ) E.tail (E[1]'hone_lt)
      (E[E.length - 1]'hlast_lt) := HoleMinusVertexPath.isPathFrom_tail hE hE5
  have hnotadj : ¬ ((Thm29Aux.cG0 G p X pn)ᶜ).Adj (E[1]'hone_lt) (E[E.length - 1]'hlast_lt) :=
    HoleMinusVertexPath.ends_not_adj hE hE5
  have hendsne : (E[1]'hone_lt) ≠ (E[E.length - 1]'hlast_lt) :=
    HoleMinusVertexPath.ends_ne hE hE5
  ---------------------------------------------------------------------------
  -- (5)  identify `u`, `v` and the antipath `Q`
  ---------------------------------------------------------------------------
  have hE1ne : (E[1]'hone_lt) ≠ (Sum.inr () : V ⊕ Unit) := by
    intro hcon
    have h : (E[1]'hone_lt) = (E[0]'hEpos) := hcon.trans hEy.symm
    have hk := hEnd.getElem_inj_iff.mp h
    omega
  have hEvne : (E[E.length - 1]'hlast_lt) ≠ (Sum.inr () : V ⊕ Unit) := by
    intro hcon
    have h : (E[E.length - 1]'hlast_lt) = (E[0]'hEpos) := hcon.trans hEy.symm
    have hk := hEnd.getElem_inj_iff.mp h
    omega
  obtain ⟨u, hu⟩ := exists_inl hE1ne
  obtain ⟨v, hv⟩ := exists_inl hEvne
  have huv : u ≠ v := by
    intro hc
    exact hendsne (by rw [hu, hv, hc])
  -- `u` and `v` are `G₀`-nonneighbours of `y`, hence outside `X ∪ {pₙ}`
  have hyu : ¬ (Thm29Aux.cG0 G p X pn).Adj (Sum.inr ()) (Sum.inl u) := by
    have h : ((Thm29Aux.cG0 G p X pn)ᶜ).Adj (E[0]'hEpos) (E[1]'hone_lt) :=
      (HoleMinusVertexPath.adj_head_iff hE hE5 hone_lt).mpr (Or.inl rfl)
    rw [hEy, hu] at h
    exact h.2
  have hyv : ¬ (Thm29Aux.cG0 G p X pn).Adj (Sum.inr ()) (Sum.inl v) := by
    have h : ((Thm29Aux.cG0 G p X pn)ᶜ).Adj (E[0]'hEpos) (E[E.length - 1]'hlast_lt) :=
      (HoleMinusVertexPath.adj_head_iff hE hE5 hlast_lt).mpr (Or.inr rfl)
    rw [hEy, hv] at h
    exact h.2
  have huX : u ∉ X := fun hc => hyu ((hadjr u ()).mpr (Or.inl hc))
  have hupn : u ≠ pn := fun hc => hyu ((hadjr u ()).mpr (Or.inr hc))
  have hvX : v ∉ X := fun hc => hyv ((hadjr v ()).mpr (Or.inl hc))
  have hvpn : v ≠ pn := fun hc => hyv ((hadjr v ()).mpr (Or.inr hc))
  have hu_mem_E : (Sum.inl u : V ⊕ Unit) ∈ E := by rw [← hu]; exact List.getElem_mem _
  have hv_mem_E : (Sum.inl v : V ⊕ Unit) ∈ E := by rw [← hv]; exact List.getElem_mem _
  have hup : u ∈ p := (hmemW u (hEmem _ hu_mem_E)).resolve_right huX
  have hvp : v ∈ p := (hmemW v (hEmem _ hv_mem_E)).resolve_right hvX
  -- *"between adjacent vertices of `P \ pₙ`"*
  have hadjuv : G.Adj u v := by
    have h1 : (Thm29Aux.cG0 G p X pn).Adj (Sum.inl u) (Sum.inl v) := by
      by_contra hc
      refine hnotadj ?_
      rw [hu, hv]
      exact ⟨fun he => huv (Sum.inl_injective he), hc⟩
    exact ((hadjl u v).mp h1).1
  -- the antipath `Q`
  have htailne : ∀ x ∈ E.tail, x ≠ (Sum.inr () : V ⊕ Unit) := by
    intro x hx hcon
    have h := (HoleMinusVertexPath.mem_tail_iff hE hE5 x).mp hx
    exact h.2 (hcon.trans hEy.symm)
  obtain ⟨Q, hQeq, hQlen⟩ := AddPendantVertexTransport.exists_eq_map_inl htailne
  have hQmemW : ∀ z ∈ Q, (z ∈ p ∨ z ∈ X) := by
    intro z hz
    refine hmemW z (hEmem _ ?_)
    have hmem : (Sum.inl z : V ⊕ Unit) ∈ E.tail := by
      rw [hQeq]; exact List.mem_map.mpr ⟨z, hz, rfl⟩
    exact List.mem_of_mem_tail hmem
  have hQpath : IsPathFrom ((Thm29Aux.cG0 G p X pn)ᶜ) (Q.map Sum.inl) (Sum.inl u)
      (Sum.inl v) := by
    rw [← hQeq, ← hu, ← hv]
    exact htail
  have hQ2 : IsPathFrom (Thm29Aux.cG G p X)ᶜ Q u v := by
    refine (AddPendantVertexTransport.isPathFrom_compl_map_inl (Thm29Aux.cG G p X)
      (Thm29Aux.cS X pn) Q u v).mpr ?_
    exact hQpath
  have hQ2' : IsAntipathFrom (RestrictGraph.restrictTo G (Thm29Aux.cW p X)) Q u v := hQ2
  have hQanti : IsAntipathFrom G Q u v :=
    (RestrictGraph.isAntipathFrom_iff_of_subset
      (fun z hz => Thm29Aux.mem_cW.mpr (hQmemW z hz))).mp hQ2'
  have hEtaillen : E.tail.length = E.length - 1 := by simp
  have hQlen' : Q.length = E.length - 1 := by rw [hQlen, hEtaillen]
  have hQ3 : 3 ≤ Q.length := by omega
  have hQodd : Odd (pathLength Q) := by
    rw [PathBasics.pathLength_eq, hQlen', Nat.odd_iff]
    have h := hEodd
    rw [Nat.odd_iff] at h
    omega
  -- *"and with interior in `X ∪ {pₙ}`"*
  have hQint : ∀ z ∈ SPGT.interior Q, (z ∈ X ∨ z = pn) := by
    intro z hz
    have hz1 : (Sum.inl z : V ⊕ Unit) ∈ SPGT.interior E.tail := by
      rw [hQeq, AddPendantVertexTransport.interior_map]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    obtain ⟨hzE, hz0, hzu, hzv⟩ :=
      (HoleMinusVertexPath.mem_interior_tail_iff hE hE5 (Sum.inl z)).mp hz1
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem hzE
    have hk0 : k ≠ 0 := by rintro rfl; exact hz0 hkeq.symm
    have hk1 : k ≠ 1 := by rintro rfl; exact hzu hkeq.symm
    have hkn : k ≠ E.length - 1 := by
      intro hc
      refine hzv ?_
      rw [← hkeq]
      exact hEnd.getElem_inj_iff.mpr hc
    have hnadj : ¬ ((Thm29Aux.cG0 G p X pn)ᶜ).Adj (E[0]'hEpos) (E[k]'hk) := by
      rw [HoleMinusVertexPath.adj_head_iff hE hE5 hk]
      omega
    rw [hEy, hkeq] at hnadj
    by_contra hcon
    refine hnadj ⟨(by simp : (Sum.inr () : V ⊕ Unit) ≠ Sum.inl z), ?_⟩
    intro hadj
    exact hcon ((hadjr z ()).mp hadj)
  ---------------------------------------------------------------------------
  -- (6)  *"Since `u` and `v` are not `Y`-complete, they are also joined by an antipath `R`
  --       with interior in `Y`"*
  ---------------------------------------------------------------------------
  have hnbrY : ∀ w : V, w ∈ p → w ≠ pn → ∃ y₀ ∈ Y, ¬ G.Adj w y₀ := by
    intro w hw hne
    by_contra hcon
    push Not at hcon
    exact hne ((hYuniq w hw).mp hcon)
  obtain ⟨R, hR, hRint⟩ := InducedPathExtraction.exists_antipath_interior_in hYa
    (hpY u hup) (hpY v hvp) (hnbrY u hup hupn) (hnbrY v hvp hvpn)
  have hR' : IsPathFrom Gᶜ R u v := hR
  have hRpos : 0 < R.length := PathBasics.path_length_pos hR'.1
  have hR3 : 3 ≤ R.length := by
    rcases (by omega : R.length = 1 ∨ R.length = 2 ∨ 3 ≤ R.length) with h1 | h2 | h3
    · exfalso
      obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp h1
      rw [hz] at hR'
      have e1 : z = u := by simpa using hR'.2.1
      have e2 : z = v := by simpa using hR'.2.2
      exact huv (e1.symm.trans e2)
    · exfalso
      have hpl : pathLength R = 1 := by rw [PathBasics.pathLength_eq]; omega
      exact (PathBasics.isPathFrom_ends_adj_of_length_one hR' hpl).2 hadjuv
    · exact h3
  ---------------------------------------------------------------------------
  -- (7)  *"`R` must also be odd since its union with `Q` is an antihole"*
  ---------------------------------------------------------------------------
  have hdisjQR : ∀ x ∈ Q, x ∉ SPGT.interior R := by
    intro x hx hc
    have hxY : x ∈ Y := hRint x hc
    rcases hQmemW x hx with h | h
    · exact hpY x h hxY
    · exact hXnY x h hxY
  have hcrQR : ∀ x ∈ SPGT.interior Q, ∀ z ∈ SPGT.interior R, G.Adj x z := by
    intro x hx z hz
    have hzY : z ∈ Y := hRint z hz
    rcases hQint x hx with h | h
    · exact hcompl x h z hzY
    · rw [h]; exact hpnY z hzY
  obtain ⟨hhole1, hlen1⟩ := glue_antihole hQanti hR hQ3 hR3 hdisjQR hcrQR
  have heven1 : Even (holeLength (Q ++ (SPGT.interior R).reverse)) := hG.2 _ hhole1
  rw [hlen1, Nat.even_iff] at heven1
  have hRodd : Odd (pathLength R) := by
    rw [Nat.odd_iff]
    have h := hQodd
    rw [Nat.odd_iff] at h
    omega
  have hR4 : 4 ≤ R.length := by
    have h := hRodd
    rw [PathBasics.pathLength_eq, Nat.odd_iff] at h
    omega
  ---------------------------------------------------------------------------
  -- (8)  *"Since `R` cannot be completed to an antihole via `v-pₙ-u` it follows that `pₙ` is
  --       adjacent to one of `u,v`"*
  ---------------------------------------------------------------------------
  have hpnuv : G.Adj pn u ∨ G.Adj pn v := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hnu, hnv⟩ := hcon
    have hpnR : pn ∉ R := by
      intro hc
      by_cases h1 : pn = u
      · exact hupn h1.symm
      · by_cases h2 : pn = v
        · exact hvpn h2.symm
        · exact hpY pn hpnmem
            (hRint pn ((PathBasics.mem_interior_iff_of_pathFrom hR').mpr ⟨hc, h1, h2⟩))
    have hpnint : ∀ z ∈ SPGT.interior R, G.Adj pn z := fun z hz => hpnY z (hRint z hz)
    obtain ⟨hhole2, hlen2⟩ := close_antipath hR hR3 hpnR hnu hnv hpnint
    have heven2 : Even (holeLength (R ++ [pn])) := hG.2 _ hhole2
    rw [hlen2, Nat.even_iff] at heven2
    have h := hRodd
    rw [Nat.odd_iff] at h
    omega
  ---------------------------------------------------------------------------
  -- (9)  *"and hence we may assume that `u = pₙ₋₂` and `v = pₙ₋₁`"*
  ---------------------------------------------------------------------------
  obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hup
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hvp
  have hij : i + 1 = j ∨ j + 1 = i := by
    refine (PathBasics.path_adj_iff hp hi hj).mp ?_
    rw [hieq, hjeq]; exact hadjuv
  have hine : i ≠ p.length - 1 := by
    intro hc
    refine hupn ?_
    rw [← hieq, ← hplast]
    exact hnd.getElem_inj_iff.mpr hc
  have hjne : j ≠ p.length - 1 := by
    intro hc
    refine hvpn ?_
    rw [← hjeq, ← hplast]
    exact hnd.getElem_inj_iff.mpr hc
  have hpn2 : i = p.length - 2 ∨ j = p.length - 2 := by
    rcases hpnuv with h | h
    · left
      have hadj' : G.Adj (p[p.length - 1]'hplt) (p[i]'hi) := by
        rw [hplast, hieq]; exact h
      have h2 := (PathBasics.path_adj_iff hp hplt hi).mp hadj'
      omega
    · right
      have hadj' : G.Adj (p[p.length - 1]'hplt) (p[j]'hj) := by
        rw [hplast, hjeq]; exact h
      have h2 := (PathBasics.path_adj_iff hp hplt hj).mp hadj'
      omega
  -- the paper's identification `{u,v} = {pₙ₋₂, pₙ₋₁}`, up to the symmetry between `u` and `v`
  have hkey : (i = p.length - 3 ∧ j = p.length - 2) ∨ (i = p.length - 2 ∧ j = p.length - 3) := by
    omega
  have hi2 : 2 ≤ i := by omega
  have hj2 : 2 ≤ j := by omega
  have hup₁ : u ≠ p₁ := by
    rw [← hieq, ← hp0]
    intro hc
    exact absurd (hnd.getElem_inj_iff.mp hc) (by omega)
  have hvp₁ : v ≠ p₁ := by
    rw [← hjeq, ← hp0]
    intro hc
    exact absurd (hnd.getElem_inj_iff.mp hc) (by omega)
  ---------------------------------------------------------------------------
  -- (10) *"Since `P` has length ≥ 4 it follows that `u,v` are also joined by an antipath with
  --       interior in `X`, say `S`"*
  ---------------------------------------------------------------------------
  have hnbrX : ∀ w : V, w ∈ p → w ≠ p₁ → ∃ x ∈ X, ¬ G.Adj w x := by
    intro w hw hne
    by_contra hcon
    push Not at hcon
    exact hne ((hXuniq w hw).mp hcon)
  obtain ⟨S, hS, hSint⟩ := InducedPathExtraction.exists_antipath_interior_in hXa
    (hpX u hup) (hpX v hvp) (hnbrX u hup hup₁) (hnbrX v hvp hvp₁)
  have hS' : IsPathFrom Gᶜ S u v := hS
  have hSpos : 0 < S.length := PathBasics.path_length_pos hS'.1
  have hS3 : 3 ≤ S.length := by
    rcases (by omega : S.length = 1 ∨ S.length = 2 ∨ 3 ≤ S.length) with h1 | h2 | h3
    · exfalso
      obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp h1
      rw [hz] at hS'
      have e1 : z = u := by simpa using hS'.2.1
      have e2 : z = v := by simpa using hS'.2.2
      exact huv (e1.symm.trans e2)
    · exfalso
      have hpl : pathLength S = 1 := by rw [PathBasics.pathLength_eq]; omega
      exact (PathBasics.isPathFrom_ends_adj_of_length_one hS' hpl).2 hadjuv
    · exact h3
  ---------------------------------------------------------------------------
  -- (11) *"again `S` is odd since its union with `R` is an antihole.  But `S` can be completed
  --       to an antihole via `v-p₁-u`, a contradiction."*
  ---------------------------------------------------------------------------
  have hdisjSR : ∀ x ∈ S, x ∉ SPGT.interior R := by
    intro x hx hc
    have hxY : x ∈ Y := hRint x hc
    by_cases h1 : x = u
    · exact hpY u hup (h1 ▸ hxY)
    · by_cases h2 : x = v
      · exact hpY v hvp (h2 ▸ hxY)
      · exact hXnY x
          (hSint x ((PathBasics.mem_interior_iff_of_pathFrom hS').mpr ⟨hx, h1, h2⟩)) hxY
  have hcrSR : ∀ x ∈ SPGT.interior S, ∀ z ∈ SPGT.interior R, G.Adj x z :=
    fun x hx z hz => hcompl x (hSint x hx) z (hRint z hz)
  obtain ⟨hhole3, hlen3⟩ := glue_antihole hS hR hS3 hR3 hdisjSR hcrSR
  have heven3 : Even (holeLength (S ++ (SPGT.interior R).reverse)) := hG.2 _ hhole3
  rw [hlen3, Nat.even_iff] at heven3
  have hSodd : Odd (pathLength S) := by
    rw [Nat.odd_iff]
    have h := hRodd
    rw [Nat.odd_iff] at h
    omega
  -- `p₁` closes `S` into an odd antihole
  have hnp₁u : ¬ G.Adj p₁ u := by
    rw [← hp0, ← hieq]
    intro hadj
    have h2 := (PathBasics.path_adj_iff hp hppos hi).mp hadj
    omega
  have hnp₁v : ¬ G.Adj p₁ v := by
    rw [← hp0, ← hjeq]
    intro hadj
    have h2 := (PathBasics.path_adj_iff hp hppos hj).mp hadj
    omega
  have hp₁S : p₁ ∉ S := by
    intro hc
    by_cases h1 : p₁ = u
    · exact hup₁ h1.symm
    · by_cases h2 : p₁ = v
      · exact hvp₁ h2.symm
      · exact hpX p₁ hp₁mem
          (hSint p₁ ((PathBasics.mem_interior_iff_of_pathFrom hS').mpr ⟨hc, h1, h2⟩))
  have hp₁int : ∀ z ∈ SPGT.interior S, G.Adj p₁ z := fun z hz => hp₁X z (hSint z hz)
  obtain ⟨hhole4, hlen4⟩ := close_antipath hS hS3 hp₁S hnp₁u hnp₁v hp₁int
  have heven4 : Even (holeLength (S ++ [p₁])) := hG.2 _ hhole4
  rw [hlen4, Nat.even_iff] at heven4
  have h := hSodd
  rw [Nat.odd_iff] at h
  omega

end Main

end Workspace.ProofLemmas.Thm29OddAntihole
