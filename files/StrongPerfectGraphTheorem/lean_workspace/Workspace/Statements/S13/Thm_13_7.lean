/-  Proof attempt 1 for statement 13.7 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 86).

    The paper's proof, verbatim:

      "Let us apply 2.9.  We may therefore assume that `P` has length ≥ 4 and there
       are nonadjacent `x₁, x₂ ∈ X` such that `x₁-p₂-⋯-pₙ-x₂` is a path `P'` say, of
       odd length ≥ 5.  But the ends of `P'` are `Y ∪ {p₁}`-complete, and its
       internal vertices are not, contrary to 13.6.  This proves 13.7."

    Reproduced step for step:

    * The printed 13.7 does not assume `V(P) ∩ (X ∪ Y) = ∅`, while 2.9 does.  It is
      a consequence: a vertex of `P` in `X` is `Y`-complete (as `X` is complete to
      `Y`), hence equals `pₙ`, so `pₙ ∈ X`; but `p₁` is `X`-complete, so `p₁pₙ` is
      an edge, contradicting that `P` is an induced path of length ≥ 2.  Dually for
      `Y`.  That is `hpX` / `hpY` below.

    * 2.9 is then applied verbatim.  Its **third** alternative is literally the
      conclusion of 13.7 and is handed straight back.  Its first alternative is the
      case the paper refutes; its second is the same case with `X` and `Y` (and the
      two ends of `P`) interchanged — the paper's silent "from the symmetry" — and
      is obtained by running the same argument on `P.reverse`.  The refutation is
      the private lemma `alt_absurd`.

    * `alt_absurd` is the printed sentence "But the ends of `P'` are `Y ∪ {p₁}`-
      complete, and its internal vertices are not, contrary to 13.6".  Concretely,
      with `X' := Y ∪ {p₁}`:
        - `P' = x₁-p₂-⋯-pₙ-x₂` has `pathLength P' = pathLength P + 1`, which is odd
          (P is even) and `≥ 5`;
        - `X'` is anticonnected, because `Y` is and `p₁` is not `Y`-complete;
        - `X'` is disjoint from `V(P')`;
        - both ends `x₁, x₂` of `P'` are `X'`-complete (`x₁, x₂ ∈ X`, `X` complete
          to `Y`, and `p₁` is `X`-complete);
      so 13.6 applies.  Its second alternative needs `pathLength P' = 3`, excluded.
      Its first alternative gives an `X'`-complete edge `uv` of `P'`; both `u` and
      `v` are then `Y`-complete and adjacent to `p₁`, and a vertex of `p₂-⋯-pₙ` with
      those two properties would have to be `pₙ` and adjacent to `p₁` — impossible.
      So `u, v ∈ {x₁, x₂}`, and `uv` being an edge contradicts `x₁ ≁ x₂`.
-/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.Statements.S02.Thm_2_9
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S13

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace SPGT

open Workspace.ProofLemmas

/-- The paper's *"But the ends of `P'` are `Y ∪ {p₁}`-complete, and its internal
vertices are not, contrary to 13.6"*: the first two alternatives of 2.9 cannot
occur under the hypotheses of 13.7.

Stated for the first alternative only; the second is obtained by applying this
  lemma to `P.reverse` with `X` and `Y` interchanged. -/
private theorem alt_absurd {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (hG : InF5 G) (X Y : Set W)
    (hcompl : Complete G X Y) (hYa : AnticonnectedSet G Y)
    (p : List W) (p₁ pn : W) (hp : IsPathList G p)
    (heven : Even (pathLength p))
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ u ∈ p, (VertexComplete G u X ↔ u = p₁))
    (hYuniq : ∀ u ∈ p, (VertexComplete G u Y ↔ u = pn))
    (hpX : ∀ w ∈ p, w ∉ X) (hpY : ∀ w ∈ p, w ∉ Y)
    (h4 : 4 ≤ pathLength p)
    (x₁ x₂ : W) (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hnadj : ¬ G.Adj x₁ x₂)
    (hP' : IsPathList G (x₁ :: (p.tail ++ [x₂]))) : False := by
  -- ### Basic data about `P`
  have hplen : pathLength p = p.length - 1 := PathBasics.pathLength_eq p
  have hlen : 5 ≤ p.length := by omega
  have h0lt : 0 < p.length := by omega
  have hnlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpe : p[p.length - 1]'hnlt = pn := PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hnotadj : ¬ G.Adj p₁ pn := by
    rw [← hp0, ← hpe]; exact PathBasics.path_ends_not_adj hp (by omega)
  have hp₁X : VertexComplete G p₁ X := (hXuniq p₁ hp₁mem).mpr rfl
  have hp₁ne : p₁ ≠ pn := by
    rw [← hp0, ← hpe]; exact PathBasics.path_ne_of_ne_index hp h0lt hnlt (by omega)
  have hp₁notY : ¬ VertexComplete G p₁ Y := fun h => hp₁ne ((hYuniq p₁ hp₁mem).mp h)
  -- `p = p₁ :: p.tail`, so `p₁` is not an internal vertex
  have hpcons : p = p₁ :: p.tail := by
    cases hpl : p with
    | nil => rw [hpl] at hhead; simp at hhead
    | cons a t =>
      rw [hpl] at hhead
      simp only [List.head?_cons, Option.some.injEq] at hhead
      rw [hhead]
      simp
  have hnd : (p₁ :: p.tail).Nodup := by rw [← hpcons]; exact PathBasics.path_nodup hp
  have hp₁tail : p₁ ∉ p.tail := (List.nodup_cons.mp hnd).1
  -- ### The path `P' = x₁-p₂-⋯-pₙ-x₂`
  have hlenP : (x₁ :: (p.tail ++ [x₂])).length = p.length + 1 := by
    simp only [List.length_cons, List.length_append, List.length_tail,
      List.length_singleton, List.length_nil]
    omega
  have hplP : pathLength (x₁ :: (p.tail ++ [x₂])) = p.length := by
    rw [PathBasics.pathLength_eq, hlenP]
    omega
  have hoddP : Odd (pathLength (x₁ :: (p.tail ++ [x₂]))) := by
    rw [hplP, Nat.odd_iff]
    have h := Nat.even_iff.mp heven
    omega
  have hheadP : (x₁ :: (p.tail ++ [x₂])).head? = some x₁ := rfl
  have hlastP : (x₁ :: (p.tail ++ [x₂])).getLast? = some x₂ := by
    show ((x₁ :: p.tail) ++ [x₂]).getLast? = some x₂
    exact List.getLast?_concat
  have hmemP : ∀ w ∈ x₁ :: (p.tail ++ [x₂]), w = x₁ ∨ w ∈ p.tail ∨ w = x₂ := by
    intro w hw
    simpa using hw
  -- ### `X' = Y ∪ {p₁}` is anticonnected and disjoint from `V(P')`
  obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y ∈ Y, ¬ G.Adj p₁ y := by
    by_contra hcon
    push Not at hcon
    exact hp₁notY hcon
  have hp₁ny : p₁ ≠ y₀ := fun h => hpY p₁ hp₁mem (h ▸ hy₀Y)
  have hX'anti : AnticonnectedSet G (Y ∪ {p₁}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hYa
      ⟨y₀, hy₀Y, ⟨hp₁ny, hy₀⟩⟩
  have hx₁notY : x₁ ∉ Y := fun h => G.irrefl (hcompl x₁ hx₁ x₁ h)
  have hx₂notY : x₂ ∉ Y := fun h => G.irrefl (hcompl x₂ hx₂ x₂ h)
  have hx₁notX' : x₁ ∉ Y ∪ {p₁} := by
    rintro (h | h)
    · exact hx₁notY h
    · exact hpX p₁ hp₁mem (h ▸ hx₁)
  have hx₂notX' : x₂ ∉ Y ∪ {p₁} := by
    rintro (h | h)
    · exact hx₂notY h
    · exact hpX p₁ hp₁mem (h ▸ hx₂)
  have htailnotX' : ∀ w ∈ p.tail, w ∉ Y ∪ {p₁} := by
    intro w hw hmem
    rcases hmem with h | h
    · exact hpY w (List.mem_of_mem_tail hw) h
    · exact hp₁tail (h ▸ hw)
  have hX'P : (Y ∪ {p₁}) ⊆ {v : W | v ∈ x₁ :: (p.tail ++ [x₂])}ᶜ := by
    intro z hz hzP
    rcases hmemP z hzP with h | h | h
    · exact hx₁notX' (h ▸ hz)
    · exact htailnotX' z h hz
    · exact hx₂notX' (h ▸ hz)
  -- ### Both ends of `P'` are `X'`-complete
  have hcx₁ : VertexComplete G x₁ (Y ∪ {p₁}) := by
    intro w hw
    rcases hw with hwY | hwp
    · exact hcompl x₁ hx₁ w hwY
    · rw [show w = p₁ from hwp]; exact (hp₁X x₁ hx₁).symm
  have hcx₂ : VertexComplete G x₂ (Y ∪ {p₁}) := by
    intro w hw
    rcases hw with hwY | hwp
    · exact hcompl x₂ hx₂ w hwY
    · rw [show w = p₁ from hwp]; exact (hp₁X x₂ hx₂).symm
  -- ### 13.6
  rcases thm_13_6 G hG (x₁ :: (p.tail ++ [x₂])) x₁ x₂ ⟨hP', hheadP, hlastP⟩ hoddP
      (Y ∪ {p₁}) hX'P hX'anti hcx₁ hcx₂ with hedge | hthree
  · -- 13.6(1): an `X'`-complete edge of `P'`
    obtain ⟨u, hu, v, hv, hadjuv, hcu, hcv⟩ := hedge
    have hin : ∀ z ∈ x₁ :: (p.tail ++ [x₂]), VertexComplete G z (Y ∪ {p₁}) →
        z = x₁ ∨ z = x₂ := by
      intro z hz hcz
      rcases hmemP z hz with h | h | h
      · exact Or.inl h
      · exfalso
        have hzp : z ∈ p := List.mem_of_mem_tail h
        have hzY : VertexComplete G z Y := fun y hy => hcz y (Or.inl hy)
        have hzn : z = pn := (hYuniq z hzp).mp hzY
        have hadjz : G.Adj z p₁ := hcz p₁ (Or.inr rfl)
        rw [hzn] at hadjz
        exact hnotadj hadjz.symm
      · exact Or.inr h
    rcases hin u hu hcu with hu' | hu' <;> rcases hin v hv hcv with hv' | hv'
    · exact hadjuv.ne (hu'.trans hv'.symm)
    · exact hnadj (by rw [← hu', ← hv']; exact hadjuv)
    · exact hnadj (by rw [← hv', ← hu']; exact hadjuv.symm)
    · exact hadjuv.ne (hu'.trans hv'.symm)
  · -- 13.6(2): `P'` would have length 3, but its length is `p.length ≥ 5`
    omega

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **13.7** (printed p. 86), introduced by *"There is an analogous strengthening of 2.9, as
follows."*

PAPER: *"Let `G ∈ F₅`, and let `X, Y` be disjoint nonempty anticonnected subsets of `V(G)`,
complete to each other.  Let `P` be a path in `G` with even length `> 0`, with vertices
`p₁, …, p_n` in order, such that `p₁` is the unique `X`-complete vertex of `P` and `p_n` is the
unique `Y`-complete vertex of `P`.  Then `P` has length 2 and there is an antipath `Q` between
`p₂` and `p₃` with interior in `X`, and an antipath `R` between `p₁` and `p₂` with interior in
`Y`, and exactly one of `Q, R` has odd length."*

Notes on the transcription.

* The printed hypothesis is *"a path in `G`"* — verified against the PDF — whereas the
  corresponding hypothesis of 2.9, which this statement strengthens, is *"a path in
  `G \ (X ∪ Y)`"*.  The literal printed hypothesis is what is formalized: no disjointness of
  `V(P)` from `X ∪ Y` is assumed here.
* *"with vertices `p₁, …, p_n` in order"* names the first and last vertices of the list, via
  `head?` and `getLast?`.
* *"`p₁` is the unique `X`-complete vertex of `P`"* is: a vertex of `P` is `X`-complete
  exactly when it is `p₁`; likewise for `p_n` and `Y`.
* Since `P` has length 2 it has exactly three vertices `p₁, p₂, p₃ = p_n`, so it is the list
  `[p₁, c, p_n]` with `c = p₂`; `Q` then joins `p₂` and `p₃`, and `R` joins `p₁` and `p₂`.
* *"exactly one of `Q, R` has odd length"* is `Xor'`. -/
theorem thm_13_7 (G : SimpleGraph V) (hG : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pn : V) (hp : IsPathList G p)
    (heven : Even (pathLength p)) (hpos : 0 < pathLength p)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pn)
    (hXuniq : ∀ u ∈ p, (VertexComplete G u X ↔ u = p₁))
    (hYuniq : ∀ u ∈ p, (VertexComplete G u Y ↔ u = pn)) :
    pathLength p = 2 ∧ ∃ c : V, p = [p₁, c, pn] ∧
      ∃ Q R : List V,
        (IsAntipathFrom G Q c pn ∧ ∀ u ∈ SPGT.interior Q, u ∈ X) ∧
        (IsAntipathFrom G R p₁ c ∧ ∀ u ∈ SPGT.interior R, u ∈ Y) ∧
        Xor' (Odd (pathLength Q)) (Odd (pathLength R)) := by
  have hBerge : Berge G := hG.1.1
  -- `P` has even length `> 0`, hence at least three vertices
  have hplen : pathLength p = p.length - 1 := PathBasics.pathLength_eq p
  have h2 : 2 ≤ pathLength p := by obtain ⟨k, hk⟩ := heven; omega
  have hlen : 3 ≤ p.length := by omega
  have h0lt : 0 < p.length := by omega
  have hnlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpe : p[p.length - 1]'hnlt = pn := PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp₁mem : p₁ ∈ p := PathBasics.head_mem hhead
  have hpnmem : pn ∈ p := PathBasics.getLast_mem hlast
  have hnotadj : ¬ G.Adj p₁ pn := by
    rw [← hp0, ← hpe]; exact PathBasics.path_ends_not_adj hp hlen
  have hp₁X : VertexComplete G p₁ X := (hXuniq p₁ hp₁mem).mpr rfl
  have hpnY : VertexComplete G pn Y := (hYuniq pn hpnmem).mpr rfl
  -- *"It follows from the hypotheses that `X`, `Y` and `V(P)` are mutually disjoint."*
  have hpX : ∀ w ∈ p, w ∉ X := by
    intro w hw hwX
    have hwY : VertexComplete G w Y := hcompl w hwX
    have hwn : w = pn := (hYuniq w hw).mp hwY
    exact hnotadj (hp₁X pn (hwn ▸ hwX))
  have hpY : ∀ w ∈ p, w ∉ Y := by
    intro w hw hwY
    have hwX : VertexComplete G w X := fun x hx => (hcompl x hx w hwY).symm
    have hw1 : w = p₁ := (hXuniq w hw).mp hwX
    exact hnotadj (hpnY p₁ (hw1 ▸ hwY)).symm
  have hpXY : ∀ w ∈ p, w ∉ X ∪ Y := by
    intro w hw hmem
    rcases hmem with h | h
    · exact hpX w hw h
    · exact hpY w hw h
  -- *"Let us apply 2.9."*
  rcases (_root_.Workspace.Statements.S02.SPGT.thm_2_9 G hBerge X Y hXY hXne hYne hXa hYa
      hcompl p p₁ pn hp hpXY heven hpos hhead hlast hXuniq hYuniq).1 with h1 | h2 | h3
  · -- 2.9(1): refuted by 13.6
    exfalso
    obtain ⟨h4, x₁, hx₁, x₂, hx₂, hnadj, hpath⟩ := h1
    exact alt_absurd G hG X Y hcompl hYa p p₁ pn hp heven hhead hlast hXuniq hYuniq
      hpX hpY h4 x₁ x₂ hx₁ hx₂ hnadj hpath
  · -- 2.9(2): the same, "from the symmetry", on `P.reverse` with `X`, `Y` interchanged
    exfalso
    obtain ⟨h4, y₁, hy₁, y₂, hy₂, hnadj, hpath⟩ := h2
    have hrev : (y₁ :: (p.dropLast ++ [y₂])).reverse = y₂ :: (p.reverse.tail ++ [y₁]) := by
      simp [List.tail_reverse]
    have hpath' : IsPathList G (y₂ :: (p.reverse.tail ++ [y₁])) := by
      rw [← hrev]; exact PathBasics.isPathList_reverse hpath
    have hrp : IsPathFrom G p.reverse pn p₁ :=
      PathBasics.isPathFrom_reverse ⟨hp, hhead, hlast⟩
    exact alt_absurd G hG Y X (fun y hy x hx => (hcompl x hx y hy).symm) hXa
      p.reverse pn p₁ hrp.1
      (by rw [PathBasics.pathLength_reverse]; exact heven)
      hrp.2.1 hrp.2.2
      (fun u hu => hYuniq u (List.mem_reverse.mp hu))
      (fun u hu => hXuniq u (List.mem_reverse.mp hu))
      (fun w hw => hpY w (List.mem_reverse.mp hw))
      (fun w hw => hpX w (List.mem_reverse.mp hw))
      (by rw [PathBasics.pathLength_reverse]; exact h4)
      y₂ y₁ hy₂ hy₁ (fun hc => hnadj hc.symm) hpath'
  · -- 2.9(3) *is* the conclusion of 13.7
    exact h3


end SPGT

end Workspace.Statements.S13
