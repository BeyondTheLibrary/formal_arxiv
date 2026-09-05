/-  **12.4, printed claim (4) — the 2.1 application in `Ḡ` that produces the leap.**

    PAPER (printed p. 75), continuing the proof of (4) exactly where
    `Workspace.ProofLemmas.Thm124Claim4Part1` stops:

    *"… So `u` has a neighbour in `R₀*`, and similarly so does `v`.  Now `b₁-u-Q-v-a₁` is an
    odd antipath, all its internal vertices have neighbours in the connected set `R₀*`, and
    its ends do not.  By 2.1 applied in `Ḡ`, there is a leap; that is, there exist adjacent
    `a, b ∈ R₀*`, both `Q`-complete, such that `b-u-Q-v-a` is an antipath. …"*

    This module formalizes the sentence *"By 2.1 applied in `Ḡ`, there is a leap; that is,
    there exist adjacent `a, b ∈ R₀*` … such that `b-u-Q-v-a` is an antipath"*.  The printed
    clause *"both `Q`-complete"* is adjudicated in a separate module and is deliberately not
    part of any conclusion here.

    Contents:

    * `connectedSet_interior` / `anticonnectedSet_compl_interior` — *"the connected set `R₀*`"*,
      read in `G` and in `Ḡ` respectively (2.1 is applied in `Ḡ`, where the hypothesis it needs
      is anticonnectedness of `R₀*` **in `Ḡ`**, i.e. connectedness in `G`).
    * `odd_antipath_for_leap_explicit` — Part 1's `odd_antipath_for_leap` with the antipath
      `q = u-q₁-⋯-q_k-v` exposed instead of existentially hidden (a documented strengthening;
      see the theorem's own doc-comment).
    * `leap_of_odd_antipath` — the 2.1 application itself, in given-data form.
    * `leap_exists` — the two combined, which is the printed sentence.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124Claims
import Workspace.ProofLemmas.Thm124Claim4Part1
import Workspace.Statements.S02.Thm_2_1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ProofAttempts.Thm124Claim4Leap

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The interior of the banister is a connected set -/

/-- PAPER: *"all its internal vertices have neighbours in **the connected set `R₀*`**"*.

The interior of a path is a (contiguous) stretch of it, hence a chain, hence connected. -/
theorem connectedSet_interior {G : SimpleGraph V} {R₀ : List V} (h : IsPathList G R₀) :
    ConnectedSet G {z : V | z ∈ SPGT.interior R₀} := by
  have hc : List.IsChain G.Adj R₀ := InducedPathExtraction.isChain_of_isPathList h
  have hc' : List.IsChain G.Adj (SPGT.interior R₀) := by
    rw [PathBasics.interior_eq_drop_take]
    exact (hc.drop 1).take (R₀.length - 2)
  exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain hc'

/-- The same fact read in `Ḡ`: since 2.1 is applied *in the complement*, the hypothesis it
needs is that `R₀*` is **anticonnected in `Ḡ`**, which is literally connectedness in `G`. -/
theorem anticonnectedSet_compl_interior {G : SimpleGraph V} {R₀ : List V} (h : IsPathList G R₀) :
    AnticonnectedSet Gᶜ {z : V | z ∈ SPGT.interior R₀} := by
  show ConnectedSet (Gᶜ)ᶜ {z : V | z ∈ SPGT.interior R₀}
  rw [compl_compl]
  exact connectedSet_interior h

/-! ## The odd antipath `b₁-u-Q-v-a₁`, with the antipath `u-Q-v` exposed -/

/-- PAPER: *"Now `b₁-u-Q-v-a₁` is an odd antipath, all its internal vertices have neighbours in
the connected set `R₀*`, and its ends do not."*

This is `ProofAttempts.Thm124Claim4.odd_antipath_for_leap` **strengthened**: that theorem hides
the antipath `q = u-q₁-⋯-q_k-v` behind an existential and therefore loses its two ends `u`, `v`,
the fact that its interior lies in `Q`, and its length.  All three are needed downstream — the
length bound kills 2.1's third disjunct, and `u`, `v` together with the `Q`-valued interior are
the banister `v-q_k-⋯-q₁-u` of the complement staircase.  The strengthening is deliberate and
the proof is the same one, with the extra data simply not discarded: the new conjuncts
`IsAntipathFrom G q u v`, `∀ z ∈ q*, z ∈ Q` and `Odd (pathLength q)` come straight out of the
calls to `exists_antipath_through` and `antipath_odd` that the original proof already makes,
and `3 ≤ pathLength q` is `AntiholeCompletion.three_le_length_of_antipath` plus parity. -/
theorem odd_antipath_for_leap_explicit {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V}
    (huv : G.Adj u v) (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∃ (a₁ b₁ : V) (q : List V), a₁ ∈ A ∧ b₁ ∈ B ∧ G.Adj a₁ b₁ ∧
      IsAntipathFrom G q u v ∧ (∀ z ∈ SPGT.interior q, z ∈ Q) ∧
      Odd (pathLength q) ∧ 3 ≤ pathLength q ∧
      IsAntipathFrom G (b₁ :: (q ++ [a₁])) b₁ a₁ ∧
      Odd (pathLength (b₁ :: (q ++ [a₁]))) ∧
      (∀ w ∈ SPGT.interior (b₁ :: (q ++ [a₁])), ∃ z ∈ SPGT.interior R₀, G.Adj w z) ∧
      (∀ z ∈ SPGT.interior R₀, ¬ G.Adj b₁ z ∧ ¬ G.Adj a₁ z) := by
  classical
  have hCempty : C = ∅ := Thm124Claim4.claim4_C_empty h huv hu hv hunc hvnc
  have hABd : Disjoint A B := h.stepConnected.1.1
  -- the antipath `u-q₁-⋯-q_k-v` and its (odd) length
  have hunQ : ∃ x ∈ Q, ¬ G.Adj u x := by
    by_contra hno; push_neg at hno; exact hunc hno
  have hvnQ : ∃ x ∈ Q, ¬ G.Adj v x := by
    by_contra hno; push_neg at hno; exact hvnc hno
  obtain ⟨q, hq, hqint⟩ := Thm124Claim4.exists_antipath_through h.anticonnQ hunQ hvnQ
  have hqodd : Odd (pathLength q) := Thm124Claim4.antipath_odd h huv hu hv hq hqint
  -- `3 ≤ pathLength q`: the ends are `G`-adjacent, so `q` has at least three vertices, and
  -- `pathLength q` is odd
  have hq3vert : 3 ≤ q.length := AntiholeCompletion.three_le_length_of_antipath hq huv
  have hq3 : 3 ≤ pathLength q := by
    have hpl := PathBasics.pathLength_eq q
    obtain ⟨m, hm⟩ := hqodd
    omega
  -- an arbitrary rung, a single edge because `C = ∅`
  obtain ⟨aA, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨a₁, R₁, b₁, hrung, -⟩ := h.stepConnected.2.2.1 aA (Or.inl (Or.inl haA))
  have ha₁A : a₁ ∈ A := hrung.2.1
  have hb₁B : b₁ ∈ B := hrung.2.2.1
  have ha₁b₁ne : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₁B)
  have ha₁b₁ : G.Adj a₁ b₁ := (Thm124Claim4.rung_is_edge hrung hCempty ha₁b₁ne).1
  have ha₁Q : VertexComplete G a₁ Q := Thm124Claims.claim2 h a₁ (Or.inl ha₁A)
  have hb₁Q : VertexComplete G b₁ Q := Thm124Claims.claim2 h b₁ (Or.inr hb₁B)
  have huS : u ∉ A ∪ B ∪ C := hu.1
  have hvS : v ∉ A ∪ B ∪ C := hv.1
  have ha₁u : a₁ ≠ u := fun he => huS (he ▸ Or.inl (Or.inl ha₁A))
  have ha₁v : a₁ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inl ha₁A))
  have hb₁u : b₁ ≠ u := fun he => huS (he ▸ Or.inl (Or.inr hb₁B))
  have hb₁v : b₁ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inr hb₁B))
  have ha₁q : a₁ ∉ q := fun hm =>
    h.notMemQ_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
      (hqint a₁ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, ha₁u, ha₁v⟩))
  have hb₁q : b₁ ∉ q := fun hm =>
    h.notMemQ_of_memStrip b₁ (Or.inl (Or.inr hb₁B))
      (hqint b₁ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, hb₁u, hb₁v⟩))
  -- `b₁-u-q₁-⋯-q_k-v-a₁` is a path of `Gᶜ`
  have hpath : IsAntipathFrom G (b₁ :: (q ++ [a₁])) b₁ a₁ := by
    refine PathAttach.isPathFrom_cons_concat (G := Gᶜ) hq ?_ ?_ ?_ (Ne.symm ha₁b₁ne)
      hb₁q ha₁q ?_ ?_
    · exact ⟨hb₁u, fun hadj => hu.2.2 b₁ (Or.inl hb₁B) hadj.symm⟩
    · exact ⟨ha₁v, fun hadj => hv.2.2 a₁ (Or.inl ha₁A) hadj.symm⟩
    · exact fun hcadj => hcadj.2 ha₁b₁.symm
    · intro x hx hxu hcadj
      by_cases hxv : x = v
      · exact hcadj.2 (by rw [hxv]; exact (hv.2.1 b₁ hb₁B).symm)
      · exact hcadj.2 (hb₁Q x
          (hqint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hx, hxu, hxv⟩)))
    · intro x hx hxv hcadj
      by_cases hxu : x = u
      · exact hcadj.2 (by rw [hxu]; exact (hu.2.1 a₁ ha₁A).symm)
      · exact hcadj.2 (ha₁Q x
          (hqint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hx, hxu, hxv⟩)))
  -- PAPER: *"is an odd antipath"*
  have hodd : Odd (pathLength (b₁ :: (q ++ [a₁]))) := by
    have h1 := PathBasics.pathLength_eq (b₁ :: (q ++ [a₁]))
    have h2 := PathBasics.pathLength_eq q
    have h3 : (b₁ :: (q ++ [a₁])).length = q.length + 2 := by
      simp only [List.length_cons, List.length_append, List.length_nil]
    obtain ⟨m, hm⟩ := hqodd
    exact ⟨m + 1, by omega⟩
  -- PAPER: *"all its internal vertices have neighbours in the connected set `R₀*`"*
  obtain ⟨iS, iT, hiS, hiT, hiS0, hiTlast, hlt, hsQ, htQ, -, -, -, -⟩ := Thm124Setup.claim1 h
  have hsint : (R₀[iS]'hiS) ∈ SPGT.interior R₀ :=
    PathBasics.getElem_mem_interior h.pathList hiS (by omega) (by omega)
  obtain ⟨zu, hzu, hzuadj⟩ :=
    Thm124Claim4.left_star_has_neighbour_in_interior h huv hu hv hunc hvnc
  obtain ⟨zv, hzv, hzvadj⟩ :=
    Thm124Claim4.right_star_has_neighbour_in_interior h huv hu hv hunc hvnc
  refine ⟨a₁, b₁, q, ha₁A, hb₁B, ha₁b₁, hq, hqint, hqodd, hq3, hpath, hodd, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwmem, hwb₁, hwa₁⟩ := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hw
    have hwq : w ∈ q := by
      rcases List.mem_cons.mp hwmem with he | hw'
      · exact absurd he hwb₁
      · rcases List.mem_append.mp hw' with h1 | h1
        · exact h1
        · exact absurd (by simpa using h1) hwa₁
    by_cases hwu : w = u
    · exact ⟨zu, hzu, by rw [hwu]; exact hzuadj⟩
    by_cases hwv : w = v
    · exact ⟨zv, hzv, by rw [hwv]; exact hzvadj⟩
    · exact ⟨R₀[iS]'hiS, hsint,
        (hsQ w (hqint w ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr
          ⟨hwq, hwu, hwv⟩))).symm⟩
  · intro z hz
    exact ⟨fun hadj => h.interiorAnti z hz b₁ (Or.inl (Or.inr hb₁B)) hadj.symm,
      fun hadj => h.interiorAnti z hz a₁ (Or.inl (Or.inl ha₁A)) hadj.symm⟩

/-! ## *"By 2.1 applied in `Ḡ`, there is a leap"* -/

/-- PAPER: *"By 2.1 applied in `Ḡ`, there is a leap; that is, there exist adjacent
`a, b ∈ R₀*`, both `Q`-complete, such that `b-u-Q-v-a` is an antipath."*

The given-data form: the odd antipath `p = b₁-u-Q-v-a₁` of `G` (a path of `Gᶜ`), its internal
vertices all having `G`-neighbours in `R₀*` and its ends having none, is exactly the input to
2.1 in `Gᶜ` with `X = R₀*`.  Of 2.1's three outcomes the first is impossible (an internal
vertex is never `Gᶜ`-complete to `R₀*`, so an `X`-complete edge would have to be `b₁a₁`, which
is an edge of `G`) and the third is impossible (it needs `pathLength p = 3`, but
`pathLength p = |q| + 1 ≥ 5`).  What is left is the leap.

The clause *"both `Q`-complete"* of the printed sentence is adjudicated separately and is
deliberately absent here.

Note the argument order `b a` in the conclusion: `IsLeapForPath Gᶜ p b a` makes `b` the vertex
`Gᶜ`-adjacent to `p₁ = b₁`, `p₂ = u`, `pₙ = a₁`, and `a` the one `Gᶜ`-adjacent to `p₁ = b₁`,
`pₙ₋₁ = v`, `pₙ = a₁` — the paper's naming in *"`b-u-Q-v-a` is an antipath"*. -/
theorem leap_of_odd_antipath {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v a₁ b₁ : V} {q : List V}
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ B) (ha₁b₁ : G.Adj a₁ b₁)
    (hq : IsAntipathFrom G q u v) (hqlen : 3 ≤ pathLength q)
    (hpath : IsAntipathFrom G (b₁ :: (q ++ [a₁])) b₁ a₁)
    (hodd : Odd (pathLength (b₁ :: (q ++ [a₁]))))
    (hint : ∀ w ∈ SPGT.interior (b₁ :: (q ++ [a₁])), ∃ z ∈ SPGT.interior R₀, G.Adj w z)
    (hends : ∀ z ∈ SPGT.interior R₀, ¬ G.Adj b₁ z ∧ ¬ G.Adj a₁ z) :
    ∃ a b : V, a ∈ SPGT.interior R₀ ∧ b ∈ SPGT.interior R₀ ∧ G.Adj a b ∧
      IsLeapForPath Gᶜ (b₁ :: (q ++ [a₁])) b a := by
  classical
  obtain ⟨X, hXdef⟩ : ∃ X : Set V, X = {z : V | z ∈ SPGT.interior R₀} := ⟨_, rfl⟩
  have hXmem : ∀ z : V, z ∈ X ↔ z ∈ SPGT.interior R₀ := by
    intro z; rw [hXdef]; simp
  set p : List V := b₁ :: (q ++ [a₁]) with hpdef
  have hqlen' : 4 ≤ q.length := by
    have := PathBasics.pathLength_eq q
    omega
  have hplen : p.length = q.length + 2 := by
    rw [hpdef]
    simp only [List.length_cons, List.length_append, List.length_nil]
  have hpL : pathLength p = q.length + 1 := by
    rw [hpdef]
    exact PathAttach.pathLength_cons_append_singleton b₁ a₁ q
  have hintp : SPGT.interior p = q := by
    rw [hpdef]
    simp [SPGT.interior]
  have hpath' : IsPathFrom Gᶜ p b₁ a₁ := hpath
  have hpos : 0 < p.length := by omega
  have hp0 : p[0]'hpos = b₁ := PathBasics.getElem_zero_of_head? hpath'.2.1 hpos
  have hplast : p[p.length - 1]'(by omega) = a₁ :=
    PathBasics.getElem_last_of_getLast? hpath'.2.2 hpos
  -- the ends of `p` lie in `V(S)`, hence off the banister, hence outside `X`
  have hb₁R : b₁ ∉ R₀ := h.notMemR₀_of_memStrip b₁ (Or.inl (Or.inr hb₁))
  have ha₁R : a₁ ∉ R₀ := h.notMemR₀_of_memStrip a₁ (Or.inl (Or.inl ha₁))
  have hb₁X : b₁ ∉ X := fun hm => hb₁R (PathBasics.interior_subset ((hXmem b₁).mp hm))
  have ha₁X : a₁ ∉ X := fun hm => ha₁R (PathBasics.interior_subset ((hXmem a₁).mp hm))
  -- PAPER: *"and its ends do not [have neighbours in `R₀*`]"*, i.e. they are `Ḡ`-complete to it
  have hp₁ : VertexComplete Gᶜ b₁ X := by
    intro z hz
    have hz' : z ∈ SPGT.interior R₀ := (hXmem z).mp hz
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hb₁R (by rw [he]; exact PathBasics.interior_subset hz'),
      (hends z hz').1⟩
  have hpn : VertexComplete Gᶜ a₁ X := by
    intro z hz
    have hz' : z ∈ SPGT.interior R₀ := (hXmem z).mp hz
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => ha₁R (by rw [he]; exact PathBasics.interior_subset hz'),
      (hends z hz').2⟩
  -- no vertex of `p` lies in `X`
  have hpX : ∀ w ∈ p, w ∉ X := by
    intro w hw hwX
    by_cases hwb : w = b₁
    · exact hb₁X (hwb ▸ hwX)
    by_cases hwa : w = a₁
    · exact ha₁X (hwa ▸ hwX)
    have hwint : w ∈ SPGT.interior p :=
      (PathBasics.mem_interior_iff_of_pathFrom hpath').mpr ⟨hw, hwb, hwa⟩
    obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
      PathBasics.exists_getElem_of_mem_interior hpath'.1 hwint
    have hadj0 : Gᶜ.Adj (p[0]'hpos) (p[k]'hk) := by
      rw [hp0, hkw]; exact hp₁ w hwX
    have hadjn : Gᶜ.Adj (p[p.length - 1]'(show p.length - 1 < p.length by omega)) (p[k]'hk) := by
      rw [hplast, hkw]; exact hpn w hwX
    have e1 := (PathBasics.path_adj_iff hpath'.1 hpos hk).mp hadj0
    have e2 :=
      (PathBasics.path_adj_iff hpath'.1 (show p.length - 1 < p.length by omega) hk).mp hadjn
    omega
  have hBerge : Berge Gᶜ := HoleBasics.berge_compl.mpr h.berge
  have hX : AnticonnectedSet Gᶜ X := by
    rw [hXdef]
    exact anticonnectedSet_compl_interior h.pathList
  rcases Workspace.Statements.S02.SPGT.thm_2_1 Gᶜ hBerge X hX p b₁ a₁ hpath' hpX hodd hp₁ hpn with
    hd1 | hd2 | hd3
  · -- an `X`-complete edge of `p` would have to be `b₁a₁`, which is an edge of `G`
    exfalso
    obtain ⟨w₁, hw₁, w₂, hw₂, hadj, hc₁, hc₂⟩ := hd1
    have key : ∀ w ∈ p, VertexComplete Gᶜ w X → w = b₁ ∨ w = a₁ := by
      intro w hw hwc
      by_cases hwb : w = b₁
      · exact Or.inl hwb
      by_cases hwa : w = a₁
      · exact Or.inr hwa
      exfalso
      have hwint : w ∈ SPGT.interior p :=
        (PathBasics.mem_interior_iff_of_pathFrom hpath').mpr ⟨hw, hwb, hwa⟩
      obtain ⟨z, hz, hzadj⟩ := hint w hwint
      have hcz := hwc z ((hXmem z).mpr hz)
      rw [SimpleGraph.compl_adj] at hcz
      exact hcz.2 hzadj
    have hne : w₁ ≠ w₂ := hadj.ne
    have hnotadj : ¬ G.Adj a₁ b₁ := by
      rcases key w₁ hw₁ hc₁ with h1 | h1 <;> rcases key w₂ hw₂ hc₂ with h2 | h2
      · exact absurd (h1.trans h2.symm) hne
      · rw [h1, h2] at hadj
        exact fun hg => ((SimpleGraph.compl_adj G b₁ a₁).mp hadj).2 hg.symm
      · rw [h1, h2] at hadj
        exact fun hg => ((SimpleGraph.compl_adj G a₁ b₁).mp hadj).2 hg
      · exact absurd (h1.trans h2.symm) hne
    exact hnotadj ha₁b₁
  · -- the leap
    obtain ⟨h5, α, hαX, β, hβX, hlp⟩ := hd2
    refine ⟨β, α, (hXmem β).mp hβX, (hXmem α).mp hαX, ?_, hlp⟩
    have hne : α ≠ β := hlp.2.2.1
    have hnadj : ¬ Gᶜ.Adj α β := hlp.2.2.2.1
    rw [SimpleGraph.compl_adj] at hnadj
    push_neg at hnadj
    exact (hnadj hne).symm
  · -- `pathLength p = |q| + 1 ≥ 5`, so the third outcome cannot occur
    exfalso
    obtain ⟨h3, -⟩ := hd3
    rw [hpL] at h3
    omega

/-! ## The printed sentence, assembled -/

/-- PAPER: *"Now `b₁-u-Q-v-a₁` is an odd antipath, all its internal vertices have neighbours in
the connected set `R₀*`, and its ends do not.  By 2.1 applied in `Ḡ`, there is a leap; that is,
there exist adjacent `a, b ∈ R₀*` … such that `b-u-Q-v-a` is an antipath."*

(The printed clause *"both `Q`-complete"* is established elsewhere and is not part of this
conclusion.) -/
theorem leap_exists {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∃ (a b a₁ b₁ : V) (q : List V), a₁ ∈ A ∧ b₁ ∈ B ∧ G.Adj a₁ b₁ ∧
      IsAntipathFrom G q u v ∧ (∀ z ∈ SPGT.interior q, z ∈ Q) ∧ 3 ≤ pathLength q ∧
      a ∈ SPGT.interior R₀ ∧ b ∈ SPGT.interior R₀ ∧ G.Adj a b ∧
      IsLeapForPath Gᶜ (b₁ :: (q ++ [a₁])) b a := by
  obtain ⟨a₁, b₁, q, ha₁A, hb₁B, ha₁b₁, hq, hqint, hqodd, hq3, hpath, hodd, hintw, hendsw⟩ :=
    odd_antipath_for_leap_explicit h huv hu hv hunc hvnc
  obtain ⟨a, b, haint, hbint, hab, hlp⟩ :=
    leap_of_odd_antipath h ha₁A hb₁B ha₁b₁ hq hq3 hpath hodd hintw hendsw
  exact ⟨a, b, a₁, b₁, q, ha₁A, hb₁B, ha₁b₁, hq, hqint, hq3, haint, hbint, hab, hlp⟩

end ProofAttempts.Thm124Claim4Leap
