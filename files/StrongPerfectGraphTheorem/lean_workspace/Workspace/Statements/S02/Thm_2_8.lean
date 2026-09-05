/-  Proof attempt for statement 2.8 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 10).

    PRINTED PROOF (verbatim, `paper/proofs/2_8.md`):

      "Some two of P₁, P₂, P₃ have lengths of the same parity, say P₁ and P₂.  Hence the path
       Q = b₁-P₁-a₁-a₂-P₂-b₂ (with the obvious meaning …) is odd, and its ends are X-complete,
       and none of its internal vertices are X-complete.  If Q has length 1 then the theorem
       holds, so we assume it has length ≥ 3.  By 2.2, every X-complete vertex has a neighbour
       in Q*, and since b₃ is X-complete, it follows that b₃ = a₃.  Hence we may assume both P₁
       and P₂ have length ≥ 1 for otherwise the claim holds.  Suppose that Q has length 3.  Then
       P₁ and P₂ have length 1, and the claim holds again.  So we may assume (for a contradiction)
       that Q has length ≥ 5, and from the symmetry we may assume P₁ has length ≥ 2.  Since b₃ is
       not adjacent to the end b₁ of Q or to its neighbour in Q, and yet it has at least two
       neighbours in Q* (namely a₁ and a₂), this contradicts 2.5.  This proves 2.8."

    MAP ONTO THE LEAN PROOF.

    * `core` is the printed argument for one *named* choice of the same-parity pair — it takes the
      pair to be `(P₁, P₂)` and concludes the corresponding disjunct.  The paper's "say P₁ and P₂"
      is discharged in `thm_2_8` by calling `core` three times, once per pair, after permuting the
      `SetLinkedOntoTriangle` witness (`swap12`, `swap23`).
    * `glue_path` is "the path Q = b₁-P₁-a₁-a₂-P₂-b₂": two vertex-disjoint paths whose only
      connecting edge joins the last vertex of the first to the first vertex of the second
      concatenate to a path.  `Q = P₁.reverse ++ P₂`, of length `ℓ₁ + ℓ₂ + 1`, odd by the parity
      hypothesis.
    * "its ends are X-complete, and none of its internal vertices are X-complete" is `hu₁`/`hu₂`;
      "no edge of Q is X-complete" (what 2.2 and 2.5 actually ask for) would force `b₁ = a₁` and
      `b₂ = a₂`, i.e. `ℓ₁ = ℓ₂ = 0`, which is the first alternative and is disposed of first.
    * "By 2.2 … it follows that b₃ = a₃": the neighbour of `b₃` in `Q*` lies on `P₁` or `P₂`, and
      the link's uniqueness clause then forces `b₃ = a₃`, i.e. `pathLength P₃ = 0`.
    * "So we may assume (for a contradiction) that Q has length ≥ 5, and from the symmetry we may
      assume P₁ has length ≥ 2" — `long_contra`, called with `(P₁, P₂)` or with `(P₂, P₁)`
      according to which is long; its hypotheses are stated in the flipped-friendly form so the
      second call only has to commute `G.Adj` and `∧`.
    * "this contradicts 2.5" — `no_long` applies `thm_2_5` to `Q` at `v = a₃` and refutes both
      disjuncts: `a₃` is adjacent to neither `b₁` nor `b₁`'s neighbour on `Q`, and it has the two
      distinct neighbours `a₁, a₂` in `Q*`, so the neighbour set is not a singleton.

    ONE GAP FILLED.  The paper never says the `Pᵢ` avoid `X`, yet 2.2 and 2.5 require it.  It is
    a consequence: if `w ∈ Pᵢ ∩ X` then all three `bⱼ` are adjacent to `w`, so the link's
    uniqueness clauses force `w = aᵢ` and `bⱼ = aⱼ` for the other two `j`, and `bᵢ` adjacent to
    `aᵢ` on the induced path `Pᵢ` forces `pathLength Pᵢ = 1`; the other two lengths are then `0`
    and the *first* alternative already holds.  This is handled in `thm_2_8` before `core` runs. -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_5

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Encoding infrastructure -/

section Helpers

variable {V : Type*}

/-- A list of length two is a two-element literal. -/
private theorem length_eq_two {α : Type*} {l : List α} (h : l.length = 2) :
    ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- A path of length `1` has exactly its two ends as vertices. -/
private theorem mem_of_pathLength_one {G : SimpleGraph V} {P : List V} {a b : V}
    (hP : IsPathFrom G P a b) (h1 : pathLength P = 1) : ∀ x ∈ P, x = a ∨ x = b := by
  have hlen : P.length = 2 := by
    have := PathBasics.length_eq_pathLength_add_one hP.1; omega
  obtain ⟨c, d, rfl⟩ := length_eq_two hlen
  have hc : c = a := by simpa using hP.2.1
  have hd : d = b := by simpa using hP.2.2
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · exact Or.inl (h.trans hc)
  · exact Or.inr ((by simpa using h : x = d).trans hd)

/-- **Concatenating two paths along a single edge.**  Two vertex-disjoint paths whose only
edge between them joins the last vertex of the first to the first vertex of the second
concatenate to a path — the paper's `u₀-R-u₁-w₀-S-w₁`. -/
private theorem glue_path {G : SimpleGraph V} {R S : List V} {u₀ u₁ w₀ w₁ : V}
    (hR : IsPathFrom G R u₀ u₁) (hS : IsPathFrom G S w₀ w₁)
    (hdisj : ∀ x ∈ R, x ∉ S)
    (hcross : ∀ x ∈ R, ∀ y ∈ S, (G.Adj x y ↔ (x = u₁ ∧ y = w₀))) :
    IsPathFrom G (R ++ S) u₀ w₁ := by
  obtain ⟨hRl, hRh, hRt⟩ := hR
  obtain ⟨hSl, hSh, hSt⟩ := hS
  have hm : 0 < R.length := PathBasics.path_length_pos hRl
  have hn : 0 < S.length := PathBasics.path_length_pos hSl
  have hRne : R ≠ [] := PathBasics.path_ne_nil hRl
  have hSne : S ≠ [] := PathBasics.path_ne_nil hSl
  have hRm : R[R.length - 1]'(by omega) = u₁ := PathBasics.getElem_last_of_getLast? hRt hm
  have hS0 : S[0]'hn = w₀ := PathBasics.getElem_zero_of_head? hSh hn
  have hRnd : R.Nodup := hRl.2.1
  have hSnd : S.Nodup := hSl.2.1
  have cross : ∀ (i j : ℕ) (hiR : i < R.length) (hjR : R.length ≤ j)
      (hi : i < (R ++ S).length) (hj : j < (R ++ S).length),
      (G.Adj ((R ++ S)[i]'hi) ((R ++ S)[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hiR hjR hi hj
    have hiL : i < R.length + S.length := by simpa using hi
    have hjL : j < R.length + S.length := by simpa using hj
    have hjS : j - R.length < S.length := by omega
    rw [List.getElem_append_left hiR, List.getElem_append_right hjR,
      hcross (R[i]'hiR) (List.getElem_mem hiR) (S[j - R.length]'hjS) (List.getElem_mem hjS)]
    have e1 : (R[i]'hiR = u₁) ↔ i = R.length - 1 := by
      rw [← hRm]; exact hRnd.getElem_inj_iff
    have e2 : (S[j - R.length]'hjS = w₀) ↔ j - R.length = 0 := by
      rw [← hS0]; exact hSnd.getElem_inj_iff
    rw [e1, e2]
    omega
  refine ⟨⟨by simp [hRne], ?_, ?_⟩, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hRnd, hSnd, fun a ha b hb => by rintro rfl; exact hdisj a ha hb⟩
  · intro i j hi hj
    have hiL : i < R.length + S.length := by simpa using hi
    have hjL : j < R.length + S.length := by simpa using hj
    rcases lt_or_ge i R.length with hiR | hiR
    · rcases lt_or_ge j R.length with hjR | hjR
      · rw [List.getElem_append_left hiR, List.getElem_append_left hjR,
          PathBasics.path_adj_iff hRl hiR hjR]
      · exact cross i j hiR hjR hi hj
    · rcases lt_or_ge j R.length with hjR | hjR
      · rw [SimpleGraph.adj_comm, cross j i hjR hiR hj hi]
        constructor <;> (intro h; omega)
      · have hiS : i - R.length < S.length := by omega
        have hjS : j - R.length < S.length := by omega
        rw [List.getElem_append_right hiR, List.getElem_append_right hjR,
          PathBasics.path_adj_iff hSl hiS hjS]
        omega
  · rw [List.head?_append, hRh]; rfl
  · rw [List.getLast?_append_of_ne_nil _ hSne]; exact hSt

end Helpers

/-! ### The contradiction step: "this contradicts 2.5" -/

section Core

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The final step of the printed proof, isolated.  `Q` is an odd path of length `≥ 5` in
`G \ X` whose ends `c, d` are `X`-complete and no edge of which is `X`-complete, and `z` is an
`X`-complete vertex adjacent neither to `c` nor to `c`'s neighbour on `Q`, yet having two
distinct neighbours in `Q*`.  2.5 forbids this. -/
private theorem no_long {G : SimpleGraph V} {X : Set V} (hG : Berge G)
    (hX : AnticonnectedSet G X) {Q : List V} {c d z t₁ t₂ : V}
    (hQ : IsPathFrom G Q c d) (hQX : ∀ w ∈ Q, w ∉ X)
    (hQodd : Odd (pathLength Q)) (hQ5 : 5 ≤ pathLength Q)
    (hcc : VertexComplete G c X) (hdc : VertexComplete G d X)
    (hnoedge : ¬ ∃ u ∈ Q, ∃ v ∈ Q, EdgeComplete G X u v)
    (hz : VertexComplete G z X)
    (hzc : ¬ G.Adj z c) (hzq2 : ∀ (h : 1 < Q.length), ¬ G.Adj z (Q[1]'h))
    (ht₁ : t₁ ∈ SPGT.interior Q) (ht₂ : t₂ ∈ SPGT.interior Q)
    (hzt₁ : G.Adj z t₁) (hzt₂ : G.Adj z t₂) (hne : t₁ ≠ t₂) :
    False := by
  have hQlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQ.1
  -- expose the first two vertices of `Q`, as 2.5's `p = p₁ :: p₂ :: rest` demands
  obtain ⟨q1, Q', hQ'⟩ : ∃ x l, Q = x :: l := by
    cases Q with
    | nil => exact absurd rfl (PathBasics.path_ne_nil hQ.1)
    | cons x l => exact ⟨x, l, rfl⟩
  have hQ6 : 6 ≤ Q.length := by omega
  obtain ⟨q2, Q'', hQ''⟩ : ∃ x l, Q' = x :: l := by
    cases Q' with
    | nil => exfalso; rw [hQ'] at hQ6; simp at hQ6
    | cons x l => exact ⟨x, l, rfl⟩
  have hQshape : Q = q1 :: q2 :: Q'' := by rw [hQ', hQ'']
  have hq1 : q1 = c := by
    have := hQ.2.1
    rw [hQshape] at this
    simpa using this
  have h1lt : 1 < Q.length := by omega
  have hQ1 : (Q[1]'h1lt) = q2 := by simp [hQshape]
  obtain ⟨pn1, hpn1⟩ : ∃ x, Q.dropLast.getLast? = some x := by
    have hne' : Q.dropLast ≠ [] := by
      intro h
      have : Q.dropLast.length = 0 := by rw [h]; rfl
      rw [List.length_dropLast] at this
      omega
    exact ⟨Q.dropLast.getLast hne', List.getLast?_eq_some_getLast hne'⟩
  have hshape' : Q = c :: q2 :: Q'' := by rw [hQshape, hq1]
  rcases thm_2_5 G hG X hX Q c q2 pn1 d Q'' hQ.1 hshape' hpn1 hQ.2.2 hQX hQodd hcc hdc
      hnoedge z hz with (hadj | hadj) | hsingle
  · exact hzc hadj
  · exact hzq2 h1lt (hQ1 ▸ hadj)
  · have e₁ : t₁ = pn1 := by
      have : t₁ ∈ ({pn1} : Set V) := hsingle ▸ (⟨ht₁, hzt₁⟩ : t₁ ∈ {w : V | w ∈ SPGT.interior Q ∧ G.Adj z w})
      exact this
    have e₂ : t₂ = pn1 := by
      have : t₂ ∈ ({pn1} : Set V) := hsingle ▸ (⟨ht₂, hzt₂⟩ : t₂ ∈ {w : V | w ∈ SPGT.interior Q ∧ G.Adj z w})
      exact this
    exact hne (e₁.trans e₂.symm)

/-- "So we may assume (for a contradiction) that `Q` has length `≥ 5`, and from the symmetry we
may assume `P₁` has length `≥ 2`."  Stated so that the `P₁ ↔ P₂` symmetry is a pure
argument swap at the two call sites. -/
private theorem long_contra {G : SimpleGraph V} {X : Set V} (hG : Berge G)
    (hX : AnticonnectedSet G X) {a₁ a₂ a₃ b₁ b₂ : V} {P₁ P₂ : List V}
    (he₁ : IsPathFrom G P₁ a₁ b₁) (he₂ : IsPathFrom G P₂ a₂ b₂)
    (hu₁ : ∀ w ∈ P₁, (VertexComplete G w X ↔ w = b₁))
    (hu₂ : ∀ w ∈ P₂, (VertexComplete G w X ↔ w = b₂))
    (hP₁X : ∀ w ∈ P₁, w ∉ X) (hP₂X : ∀ w ∈ P₂, w ∉ X)
    (hd12 : ∀ x ∈ P₁, x ∉ P₂)
    (hc12 : ∀ x ∈ P₁, ∀ y ∈ P₂, (G.Adj x y ↔ (x = a₁ ∧ y = a₂)))
    (hc13 : ∀ x ∈ P₁, (G.Adj x a₃ ↔ x = a₁))
    (hc23 : ∀ x ∈ P₂, (G.Adj x a₃ ↔ x = a₂))
    (ha₃c : VertexComplete G a₃ X)
    (hl₁ : 2 ≤ pathLength P₁) (hl₂ : 1 ≤ pathLength P₂)
    (hpar : pathLength P₁ % 2 = pathLength P₂ % 2) :
    False := by
  have hP₁l : IsPathList G P₁ := he₁.1
  have hP₂l : IsPathList G P₂ := he₂.1
  have hlen₁ : P₁.length = pathLength P₁ + 1 := PathBasics.length_eq_pathLength_add_one hP₁l
  have hlen₂ : P₂.length = pathLength P₂ + 1 := PathBasics.length_eq_pathLength_add_one hP₂l
  have ha₁P₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).1
  have hb₁P₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).2
  have ha₂P₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).1
  have hb₂P₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).2
  have ha₁b₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne he₁ (by omega)
  have ha₂b₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne he₂ (by omega)
  -- `Q = b₁-P₁-a₁-a₂-P₂-b₂`
  have hrev : IsPathFrom G P₁.reverse b₁ a₁ := PathBasics.isPathFrom_reverse he₁
  have hQ : IsPathFrom G (P₁.reverse ++ P₂) b₁ b₂ := by
    refine glue_path hrev he₂ (fun x hx => hd12 x (List.mem_reverse.mp hx)) ?_
    intro x hx y hy
    exact hc12 x (List.mem_reverse.mp hx) y hy
  have hmemQ : ∀ w, w ∈ P₁.reverse ++ P₂ ↔ (w ∈ P₁ ∨ w ∈ P₂) := by
    intro w; simp [List.mem_append]
  have hQlen : (P₁.reverse ++ P₂).length = P₁.length + P₂.length := by simp
  have hQpl : pathLength (P₁.reverse ++ P₂) = pathLength P₁ + pathLength P₂ + 1 := by
    simp only [pathLength, hQlen]; omega
  have hQX : ∀ w ∈ P₁.reverse ++ P₂, w ∉ X := by
    intro w hw
    rcases (hmemQ w).mp hw with h | h
    · exact hP₁X w h
    · exact hP₂X w h
  have hb₁c : VertexComplete G b₁ X := (hu₁ b₁ hb₁P₁).mpr rfl
  have hb₂c : VertexComplete G b₂ X := (hu₂ b₂ hb₂P₂).mpr rfl
  -- "no edge of `Q` is `X`-complete": an `X`-complete edge would force `b₁ = a₁`
  have hnoedge : ¬ ∃ u ∈ P₁.reverse ++ P₂, ∃ v ∈ P₁.reverse ++ P₂, EdgeComplete G X u v := by
    rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
    have hclass : ∀ w, w ∈ P₁.reverse ++ P₂ → VertexComplete G w X → w = b₁ ∨ w = b₂ := by
      intro w hw hwc
      rcases (hmemQ w).mp hw with h | h
      · exact Or.inl ((hu₁ w h).mp hwc)
      · exact Or.inr ((hu₂ w h).mp hwc)
    have hab : G.Adj b₁ b₂ := by
      rcases hclass u hu huc with hu' | hu' <;> rcases hclass v hv hvc with hv' | hv'
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
      · rw [← hu', ← hv']; exact hadj
      · rw [← hv', ← hu']; exact hadj.symm
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
    exact ha₁b₁ ((hc12 b₁ hb₁P₁ b₂ hb₂P₂).mp hab).1.symm
  -- `a₃` is adjacent neither to `b₁` nor to `b₁`'s neighbour on `Q`
  have hzc : ¬ G.Adj a₃ b₁ := by
    intro h
    exact ha₁b₁ ((hc13 b₁ hb₁P₁).mp h.symm).symm
  have hzq2 : ∀ (h : 1 < (P₁.reverse ++ P₂).length), ¬ G.Adj a₃ ((P₁.reverse ++ P₂)[1]'h) := by
    intro h hadj
    have h1r : 1 < P₁.reverse.length := by simp; omega
    have hget : (P₁.reverse ++ P₂)[1]'h = P₁.reverse[1]'h1r := List.getElem_append_left h1r
    have hget2 : P₁.reverse[1]'h1r = P₁[P₁.length - 1 - 1]'(by omega) := by
      simp only [List.getElem_reverse]
    rw [hget, hget2] at hadj
    have hmem : (P₁[P₁.length - 1 - 1]'(by omega)) ∈ P₁ := List.getElem_mem _
    have heq := (hc13 _ hmem).mp hadj.symm
    have h0 : (P₁[0]'(by omega)) = a₁ := PathBasics.getElem_zero_of_head? he₁.2.1 (by omega)
    have : (P₁[P₁.length - 1 - 1]'(by omega)) = (P₁[0]'(by omega)) := by rw [heq, h0]
    have := hP₁l.2.1.getElem_inj_iff.mp this
    omega
  -- `a₁` and `a₂` are two distinct neighbours of `a₃` in `Q*`
  have hint₁ : a₁ ∈ SPGT.interior (P₁.reverse ++ P₂) := by
    refine (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨(hmemQ a₁).mpr (Or.inl ha₁P₁), ha₁b₁, ?_⟩
    intro h
    exact hd12 a₁ ha₁P₁ (h ▸ hb₂P₂)
  have hint₂ : a₂ ∈ SPGT.interior (P₁.reverse ++ P₂) := by
    refine (PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨(hmemQ a₂).mpr (Or.inr ha₂P₂), ?_, ha₂b₂⟩
    intro h
    exact hd12 b₁ hb₁P₁ (h ▸ ha₂P₂)
  have hadj₁ : G.Adj a₃ a₁ := ((hc13 a₁ ha₁P₁).mpr rfl).symm
  have hadj₂ : G.Adj a₃ a₂ := ((hc23 a₂ ha₂P₂).mpr rfl).symm
  have hane : a₁ ≠ a₂ := fun h => hd12 a₁ ha₁P₁ (h ▸ ha₂P₂)
  refine no_long hG hX hQ hQX ?_ (by omega) hb₁c hb₂c hnoedge ha₃c hzc hzq2
    hint₁ hint₂ hadj₁ hadj₂ hane
  rw [Nat.odd_iff, hQpl]
  omega

/-- The printed argument for the named same-parity pair `(P₁, P₂)`. -/
private theorem core {G : SimpleGraph V} {X : Set V} (hG : Berge G)
    (hX : AnticonnectedSet G X) {a₁ a₂ a₃ b₁ b₂ b₃ : V} {P₁ P₂ P₃ : List V}
    (he₁ : IsPathFrom G P₁ a₁ b₁) (he₂ : IsPathFrom G P₂ a₂ b₂)
    (he₃ : IsPathFrom G P₃ a₃ b₃)
    (hu₁ : ∀ w ∈ P₁, (VertexComplete G w X ↔ w = b₁))
    (hu₂ : ∀ w ∈ P₂, (VertexComplete G w X ↔ w = b₂))
    (hu₃ : ∀ w ∈ P₃, (VertexComplete G w X ↔ w = b₃))
    (hP₁X : ∀ w ∈ P₁, w ∉ X) (hP₂X : ∀ w ∈ P₂, w ∉ X)
    (hd12 : ∀ x ∈ P₁, x ∉ P₂)
    (hc12 : ∀ x ∈ P₁, ∀ y ∈ P₂, (G.Adj x y ↔ (x = a₁ ∧ y = a₂)))
    (hc13 : ∀ x ∈ P₁, ∀ y ∈ P₃, (G.Adj x y ↔ (x = a₁ ∧ y = a₃)))
    (hc23 : ∀ x ∈ P₂, ∀ y ∈ P₃, (G.Adj x y ↔ (x = a₂ ∧ y = a₃)))
    (hpar : pathLength P₁ % 2 = pathLength P₂ % 2) :
    (pathLength P₁ = 0 ∧ pathLength P₂ = 0) ∨ (pathLength P₁ = 0 ∧ pathLength P₃ = 0) ∨
    (pathLength P₂ = 0 ∧ pathLength P₃ = 0) ∨
    (pathLength P₃ = 0 ∧ pathLength P₁ = 1 ∧ pathLength P₂ = 1 ∧
      ∀ v : V, VertexComplete G v X → G.Adj v a₁ ∨ G.Adj v a₂) := by
  by_cases hz : pathLength P₁ = 0 ∧ pathLength P₂ = 0
  · exact Or.inl hz
  have hP₁l : IsPathList G P₁ := he₁.1
  have hP₂l : IsPathList G P₂ := he₂.1
  have ha₁P₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).1
  have hb₁P₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).2
  have ha₂P₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).1
  have hb₂P₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).2
  have hb₃P₃ : b₃ ∈ P₃ := (PathBasics.isPathFrom_ends_mem he₃).2
  have hb₁c : VertexComplete G b₁ X := (hu₁ b₁ hb₁P₁).mpr rfl
  have hb₂c : VertexComplete G b₂ X := (hu₂ b₂ hb₂P₂).mpr rfl
  have hb₃c : VertexComplete G b₃ X := (hu₃ b₃ hb₃P₃).mpr rfl
  -- `Q = b₁-P₁-a₁-a₂-P₂-b₂`
  have hrev : IsPathFrom G P₁.reverse b₁ a₁ := PathBasics.isPathFrom_reverse he₁
  have hQ : IsPathFrom G (P₁.reverse ++ P₂) b₁ b₂ := by
    refine glue_path hrev he₂ (fun x hx => hd12 x (List.mem_reverse.mp hx)) ?_
    intro x hx y hy
    exact hc12 x (List.mem_reverse.mp hx) y hy
  have hmemQ : ∀ w, w ∈ P₁.reverse ++ P₂ ↔ (w ∈ P₁ ∨ w ∈ P₂) := by
    intro w; simp [List.mem_append]
  have hQpl : pathLength (P₁.reverse ++ P₂) = pathLength P₁ + pathLength P₂ + 1 := by
    have h1 : P₁.length = pathLength P₁ + 1 := PathBasics.length_eq_pathLength_add_one hP₁l
    have h2 : P₂.length = pathLength P₂ + 1 := PathBasics.length_eq_pathLength_add_one hP₂l
    simp only [pathLength, List.length_append, List.length_reverse]
    omega
  have hQodd : Odd (pathLength (P₁.reverse ++ P₂)) := by
    rw [Nat.odd_iff, hQpl]; omega
  have hQX : ∀ w ∈ P₁.reverse ++ P₂, w ∉ X := by
    intro w hw
    rcases (hmemQ w).mp hw with h | h
    · exact hP₁X w h
    · exact hP₂X w h
  have hnoedge : ¬ ∃ u ∈ P₁.reverse ++ P₂, ∃ v ∈ P₁.reverse ++ P₂, EdgeComplete G X u v := by
    rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
    have hclass : ∀ w, w ∈ P₁.reverse ++ P₂ → VertexComplete G w X → w = b₁ ∨ w = b₂ := by
      intro w hw hwc
      rcases (hmemQ w).mp hw with h | h
      · exact Or.inl ((hu₁ w h).mp hwc)
      · exact Or.inr ((hu₂ w h).mp hwc)
    have hab : G.Adj b₁ b₂ := by
      rcases hclass u hu huc with hu' | hu' <;> rcases hclass v hv hvc with hv' | hv'
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
      · rw [← hu', ← hv']; exact hadj
      · rw [← hv', ← hu']; exact hadj.symm
      · exact absurd (hu'.trans hv'.symm) (G.ne_of_adj hadj)
    obtain ⟨hba, hbb⟩ := (hc12 b₁ hb₁P₁ b₂ hb₂P₂).mp hab
    refine hz ⟨?_, ?_⟩
    · by_contra hc
      exact PathBasics.isPathFrom_ends_ne he₁ (by omega) hba.symm
    · by_contra hc
      exact PathBasics.isPathFrom_ends_ne he₂ (by omega) hbb.symm
  -- "By 2.2, every `X`-complete vertex has a neighbour in `Q*`"
  have h22 := thm_2_2 G hG X hX (P₁.reverse ++ P₂) b₁ b₂ hQ hQX hQodd hb₁c hb₂c hnoedge
  -- "since `b₃` is `X`-complete, it follows that `b₃ = a₃`"
  have hb₃a₃ : b₃ = a₃ := by
    obtain ⟨w, hwi, hwadj⟩ := h22 b₃ hb₃c
    have hwQ : w ∈ P₁.reverse ++ P₂ := PathBasics.interior_subset hwi
    rcases (hmemQ w).mp hwQ with h | h
    · exact ((hc13 w h b₃ hb₃P₃).mp hwadj.symm).2
    · exact ((hc23 w h b₃ hb₃P₃).mp hwadj.symm).2
  have hl₃ : pathLength P₃ = 0 := by
    by_contra hc
    exact PathBasics.isPathFrom_ends_ne he₃ (by omega) hb₃a₃.symm
  -- "we may assume both `P₁` and `P₂` have length ≥ 1 for otherwise the claim holds"
  by_cases hz₁ : pathLength P₁ = 0
  · exact Or.inr (Or.inl ⟨hz₁, hl₃⟩)
  by_cases hz₂ : pathLength P₂ = 0
  · exact Or.inr (Or.inr (Or.inl ⟨hz₂, hl₃⟩))
  -- "Suppose that `Q` has length 3.  Then `P₁` and `P₂` have length 1"
  by_cases h3 : pathLength P₁ = 1 ∧ pathLength P₂ = 1
  · refine Or.inr (Or.inr (Or.inr ⟨hl₃, h3.1, h3.2, ?_⟩))
    intro v hv
    obtain ⟨w, hwi, hwadj⟩ := h22 v hv
    obtain ⟨hwQ, hwb₁, hwb₂⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hwi
    rcases (hmemQ w).mp hwQ with h | h
    · rcases mem_of_pathLength_one he₁ h3.1 w h with rfl | rfl
      · exact Or.inl hwadj
      · exact absurd rfl hwb₁
    · rcases mem_of_pathLength_one he₂ h3.2 w h with rfl | rfl
      · exact Or.inr hwadj
      · exact absurd rfl hwb₂
  -- "So we may assume (for a contradiction) that `Q` has length ≥ 5"
  exfalso
  have hc13' : ∀ x ∈ P₁, (G.Adj x a₃ ↔ x = a₁) := by
    intro x hx
    have := hc13 x hx a₃ (hb₃a₃ ▸ hb₃P₃)
    rw [this]
    simp
  have hc23' : ∀ x ∈ P₂, (G.Adj x a₃ ↔ x = a₂) := by
    intro x hx
    have := hc23 x hx a₃ (hb₃a₃ ▸ hb₃P₃)
    rw [this]
    simp
  have ha₃c : VertexComplete G a₃ X := hb₃a₃ ▸ hb₃c
  -- "and from the symmetry we may assume `P₁` has length ≥ 2"
  rcases (show 2 ≤ pathLength P₁ ∨ 2 ≤ pathLength P₂ by
      by_contra hcon
      push Not at hcon
      exact h3 ⟨by omega, by omega⟩) with hlong | hlong
  · exact long_contra hG hX he₁ he₂ hu₁ hu₂ hP₁X hP₂X hd12 hc12 hc13' hc23' ha₃c hlong
      (by omega) hpar
  · refine long_contra hG hX he₂ he₁ hu₂ hu₁ hP₂X hP₁X ?_ ?_ hc23' hc13' ha₃c hlong
      (by omega) hpar.symm
    · intro x hx hx'
      exact hd12 x hx' hx
    · intro x hx y hy
      rw [SimpleGraph.adj_comm, hc12 y hy x hx]
      exact and_comm

end Core

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.8** (printed p. 10)

PAPER: *"Let `G` be Berge, let `X` be an anticonnected set, and suppose `X` can be
linked onto a triangle `{a₁,a₂,a₃}` via `P₁,P₂,P₃`.  For `i = 1,2,3` let `Pᵢ` have
ends `aᵢ` and `bᵢ`, and let `bᵢ` be the unique vertex of `Pᵢ` that is `X`-complete.
Then either at least two of `P₁,P₂,P₃` have length `0` (and hence two of
`a₁,a₂,a₃` are `X`-complete) or one of `P₁,P₂,P₃` has length `0` and the other two
have length `1` (say `P₃` has length `0`); and in this case, every `X`-complete
vertex in `G` is adjacent to one of `a₁`,`a₂`."*

"`Pᵢ` has ends `aᵢ` and `bᵢ`" is written `IsPathFrom G Pᵢ aᵢ bᵢ`: a list and its
reversal denote the same path of the paper, so orienting each list so that `aᵢ`
comes first is a relabelling, not a hypothesis.

The parenthetical "(and hence two of `a₁,a₂,a₃` are `X`-complete)" is flagged by
the paper as a consequence of the first alternative, so it is not an extra
conjunct.  The parenthetical "(say `P₃` has length `0`)" is a relabelling inside
the second alternative: it is spelled out as the three cases according to which of
the three paths is the one of length `0`, and in each case the closing clause
"every `X`-complete vertex in `G` is adjacent to one of `a₁,a₂`" names the two
`aᵢ` belonging to the two paths of length `1`. -/
theorem thm_2_8 (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (a₁ a₂ a₃ b₁ b₂ b₃ : V) (P₁ P₂ P₃ : List V)
    (hlink : SetLinkedOntoTriangle G X a₁ a₂ a₃ P₁ P₂ P₃)
    (he₁ : IsPathFrom G P₁ a₁ b₁) (he₂ : IsPathFrom G P₂ a₂ b₂)
    (he₃ : IsPathFrom G P₃ a₃ b₃)
    (hu₁ : ∀ w ∈ P₁, (VertexComplete G w X ↔ w = b₁))
    (hu₂ : ∀ w ∈ P₂, (VertexComplete G w X ↔ w = b₂))
    (hu₃ : ∀ w ∈ P₃, (VertexComplete G w X ↔ w = b₃)) :
    ((pathLength P₁ = 0 ∧ pathLength P₂ = 0) ∨
      (pathLength P₁ = 0 ∧ pathLength P₃ = 0) ∨
      (pathLength P₂ = 0 ∧ pathLength P₃ = 0)) ∨
    ((pathLength P₃ = 0 ∧ pathLength P₁ = 1 ∧ pathLength P₂ = 1 ∧
        ∀ v : V, VertexComplete G v X → G.Adj v a₁ ∨ G.Adj v a₂) ∨
      (pathLength P₂ = 0 ∧ pathLength P₁ = 1 ∧ pathLength P₃ = 1 ∧
        ∀ v : V, VertexComplete G v X → G.Adj v a₁ ∨ G.Adj v a₃) ∨
      (pathLength P₁ = 0 ∧ pathLength P₂ = 1 ∧ pathLength P₃ = 1 ∧
        ∀ v : V, VertexComplete G v X → G.Adj v a₂ ∨ G.Adj v a₃)) := by
  obtain ⟨-, ⟨hd12, hd13, hd23⟩, -, ⟨hc12, hc13, hc23⟩, -⟩ := hlink
  have ha₁P₁ : a₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).1
  have hb₁P₁ : b₁ ∈ P₁ := (PathBasics.isPathFrom_ends_mem he₁).2
  have ha₂P₂ : a₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).1
  have hb₂P₂ : b₂ ∈ P₂ := (PathBasics.isPathFrom_ends_mem he₂).2
  have ha₃P₃ : a₃ ∈ P₃ := (PathBasics.isPathFrom_ends_mem he₃).1
  have hb₃P₃ : b₃ ∈ P₃ := (PathBasics.isPathFrom_ends_mem he₃).2
  have hb₁c : VertexComplete G b₁ X := (hu₁ b₁ hb₁P₁).mpr rfl
  have hb₂c : VertexComplete G b₂ X := (hu₂ b₂ hb₂P₂).mpr rfl
  have hb₃c : VertexComplete G b₃ X := (hu₃ b₃ hb₃P₃).mpr rfl
  -- "ends equal ⟹ length 0", used repeatedly
  have hzero : ∀ (Q : List V) (a b : V), IsPathFrom G Q a b → a = b → pathLength Q = 0 := by
    intro Q a b hQ hab
    by_contra hc
    exact PathBasics.isPathFrom_ends_ne hQ (by omega) hab
  -- GAP FILLED: if some `Pᵢ` meets `X`, the first alternative already holds.
  have hmeets : ∀ (Q R S : List V) (a b a' b' a'' b'' : V),
      IsPathFrom G Q a b → IsPathFrom G R a' b' → IsPathFrom G S a'' b'' →
      VertexComplete G b X → VertexComplete G b' X → VertexComplete G b'' X →
      (∀ x ∈ Q, ∀ y ∈ R, (G.Adj x y ↔ (x = a ∧ y = a'))) →
      (∀ x ∈ Q, ∀ y ∈ S, (G.Adj x y ↔ (x = a ∧ y = a''))) →
      (∃ w ∈ Q, w ∈ X) → pathLength R = 0 ∧ pathLength S = 0 := by
    intro Q R S a b a' b' a'' b'' hQ hR hS hbc hb'c hb''c hcQR hcQS ⟨w, hwQ, hwX⟩
    have h1 := (hcQR w hwQ b' (PathBasics.isPathFrom_ends_mem hR).2).mp (hb'c w hwX).symm
    have h2 := (hcQS w hwQ b'' (PathBasics.isPathFrom_ends_mem hS).2).mp (hb''c w hwX).symm
    exact ⟨hzero R a' b' hR h1.2.symm, hzero S a'' b'' hS h2.2.symm⟩
  by_cases hm₁ : ∃ w ∈ P₁, w ∈ X
  · obtain ⟨e₂, e₃⟩ := hmeets P₁ P₂ P₃ a₁ b₁ a₂ b₂ a₃ b₃ he₁ he₂ he₃ hb₁c hb₂c hb₃c
      hc12 hc13 hm₁
    exact Or.inl (Or.inr (Or.inr ⟨e₂, e₃⟩))
  by_cases hm₂ : ∃ w ∈ P₂, w ∈ X
  · have hc21 : ∀ x ∈ P₂, ∀ y ∈ P₁, (G.Adj x y ↔ (x = a₂ ∧ y = a₁)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc12 y hy x hx]
      exact and_comm
    obtain ⟨e₁, e₃⟩ := hmeets P₂ P₁ P₃ a₂ b₂ a₁ b₁ a₃ b₃ he₂ he₁ he₃ hb₂c hb₁c hb₃c
      hc21 hc23 hm₂
    exact Or.inl (Or.inr (Or.inl ⟨e₁, e₃⟩))
  by_cases hm₃ : ∃ w ∈ P₃, w ∈ X
  · have hc31 : ∀ x ∈ P₃, ∀ y ∈ P₁, (G.Adj x y ↔ (x = a₃ ∧ y = a₁)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc13 y hy x hx]
      exact and_comm
    have hc32 : ∀ x ∈ P₃, ∀ y ∈ P₂, (G.Adj x y ↔ (x = a₃ ∧ y = a₂)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc23 y hy x hx]
      exact and_comm
    obtain ⟨e₁, e₂⟩ := hmeets P₃ P₁ P₂ a₃ b₃ a₁ b₁ a₂ b₂ he₃ he₁ he₂ hb₃c hb₁c hb₂c
      hc31 hc32 hm₃
    exact Or.inl (Or.inl ⟨e₁, e₂⟩)
  have hP₁X : ∀ w ∈ P₁, w ∉ X := by
    intro w hw hwX; exact hm₁ ⟨w, hw, hwX⟩
  have hP₂X : ∀ w ∈ P₂, w ∉ X := by
    intro w hw hwX; exact hm₂ ⟨w, hw, hwX⟩
  have hP₃X : ∀ w ∈ P₃, w ∉ X := by
    intro w hw hwX; exact hm₃ ⟨w, hw, hwX⟩
  -- "Some two of `P₁, P₂, P₃` have lengths of the same parity"
  rcases (show pathLength P₁ % 2 = pathLength P₂ % 2 ∨ pathLength P₁ % 2 = pathLength P₃ % 2 ∨
      pathLength P₂ % 2 = pathLength P₃ % 2 by omega) with hpar | hpar | hpar
  · rcases core hG hX he₁ he₂ he₃ hu₁ hu₂ hu₃ hP₁X hP₂X hd12 hc12 hc13 hc23 hpar with
      h | h | h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inr (Or.inl h)
  · -- the pair is `(P₁, P₃)`: relabel `2 ↔ 3`
    have hd13' : ∀ x ∈ P₁, x ∉ P₃ := hd13
    have hc12' : ∀ x ∈ P₁, ∀ y ∈ P₃, (G.Adj x y ↔ (x = a₁ ∧ y = a₃)) := hc13
    have hc13' : ∀ x ∈ P₁, ∀ y ∈ P₂, (G.Adj x y ↔ (x = a₁ ∧ y = a₂)) := hc12
    have hc23' : ∀ x ∈ P₃, ∀ y ∈ P₂, (G.Adj x y ↔ (x = a₃ ∧ y = a₂)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc23 y hy x hx]
      exact and_comm
    rcases core hG hX he₁ he₃ he₂ hu₁ hu₃ hu₂ hP₁X hP₃X hd13' hc12' hc13' hc23' hpar with
      h | h | h | h
    · exact Or.inl (Or.inr (Or.inl h))
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr (Or.inr ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩))
  · -- the pair is `(P₂, P₃)`: relabel to `(P₂, P₃, P₁)`
    have hd23' : ∀ x ∈ P₂, x ∉ P₃ := hd23
    have hc12' : ∀ x ∈ P₂, ∀ y ∈ P₃, (G.Adj x y ↔ (x = a₂ ∧ y = a₃)) := hc23
    have hc13' : ∀ x ∈ P₂, ∀ y ∈ P₁, (G.Adj x y ↔ (x = a₂ ∧ y = a₁)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc12 y hy x hx]
      exact and_comm
    have hc23' : ∀ x ∈ P₃, ∀ y ∈ P₁, (G.Adj x y ↔ (x = a₃ ∧ y = a₁)) := by
      intro x hx y hy
      rw [SimpleGraph.adj_comm, hc13 y hy x hx]
      exact and_comm
    rcases core hG hX he₂ he₃ he₁ hu₂ hu₃ hu₁ hP₂X hP₃X hd23' hc12' hc13' hc23' hpar with
      h | h | h | h
    · exact Or.inl (Or.inr (Or.inr h))
    · exact Or.inl (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩))


end SPGT

end Workspace.Statements.S02
