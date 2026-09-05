import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

/-!
# Gluing paths, closing cycles, and small fixed-length paths

None of the lemmas in this module has a counterpart in the paper; they are bookkeeping for the
list encoding of paths and holes, collected here because §2 alone needs them four times over.

* `glue_path` — the paper's `u₀-R-u₁-w₀-S-w₁`: two vertex-disjoint paths whose **only** edge
  between them joins the last vertex of the first to the first vertex of the second concatenate
  to a path.  This is what turns "the path `Q = b₁-P₁-a₁-a₂-P₂-b₂`" (2.8) into a Lean term.
* `glue_hole` — the same with **two** connecting edges, so the concatenation closes up into a
  hole.  Every *"two paths plus two edges form an induced cycle"* in the paper is an instance:
  2.4 (`(v :: rᵢ).reverse ++ rⱼ`), 2.6 (`p ++ [v]`), 2.7 (`P ++ (interior Q).reverse`),
  7.2 (`R₁ ++ R₂.reverse`).
* `isPathFrom_interior` — the interior of a path on `≥ 3` vertices is itself a path, from the
  second vertex to the second-from-last.  `PathBasics.isPathFrom_slice` cannot reach this
  because it demands `i < j`, which fails for the one-vertex interior of a `3`-vertex path.
* `length_eq_two`, `length_eq_four`, `length_eq_five`, `mem_of_pathLength_one`,
  `isPathList_four` — small fixed-length shape lemmas.
* `isHoleList_compl_of_length_five` — the paper's *"an odd hole of length 5 is also an odd
  antihole"* (2.9): reindexing a `5`-hole by `0,2,4,1,3` gives a hole of the complement.

`succ_mod_eq` is exported because `HoleBasics`'s copy is `private`, and every hole-index proof
needs it to eliminate `%` before calling `omega`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PathGlue

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-! ## Index bookkeeping -/

/-- The cyclic successor `(i + 1) % n` with the `%` eliminated, so that `omega` — which cannot
handle a variable modulus — can finish the arithmetic. -/
theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-! ## Fixed-length lists -/

/-- A list of length two is a two-element literal. -/
theorem length_eq_two {α : Type*} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  match l, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

/-- A list of length four is a four-element literal. -/
theorem length_eq_four {α : Type*} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

/-- A list of length five is a five-element literal. -/
theorem length_eq_five {α : Type*} {l : List α} (h : l.length = 5) :
    ∃ a b c d e, l = [a, b, c, d, e] := by
  match l, h with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- A path of length `1` has exactly its two ends as vertices. -/
theorem mem_of_pathLength_one {G : SimpleGraph V} {P : List V} {a b : V}
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

/-- A four-element list with the three consecutive edges present and the three non-consecutive
pairs absent is a path. -/
theorem isPathList_four {G : SimpleGraph V} {a b c d : V}
    (hnd : [a, b, c, d].Nodup)
    (h1 : G.Adj a b) (h2 : G.Adj b c) (h3 : G.Adj c d)
    (n1 : ¬ G.Adj a c) (n2 : ¬ G.Adj a d) (n3 : ¬ G.Adj b d) :
    IsPathList G [a, b, c, d] := by
  have key : ∀ i j : ℕ, i < 4 → j < 4 →
      ∀ (hi : i < [a, b, c, d].length) (hj : j < [a, b, c, d].length),
        (G.Adj ([a, b, c, d][i]'hi) ([a, b, c, d][j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hi4 hj4
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false G.irrefl (by first | omega | simp | tauto)
      | exact iff_of_true h1 (by first | omega | simp | tauto)
      | exact iff_of_true h2 (by first | omega | simp | tauto)
      | exact iff_of_true h3 (by first | omega | simp | tauto)
      | exact iff_of_true h1.symm (by first | omega | simp | tauto)
      | exact iff_of_true h2.symm (by first | omega | simp | tauto)
      | exact iff_of_true h3.symm (by first | omega | simp | tauto)
      | exact iff_of_false n1 (by first | omega | simp | tauto)
      | exact iff_of_false n2 (by first | omega | simp | tauto)
      | exact iff_of_false n3 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | simp | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

/-! ## The interior of a path -/

/-- The interior of a path on at least three vertices is itself a path, running from the second
vertex to the second-from-last.  (`PathBasics.isPathFrom_slice` demands `i < j`, which fails for
the one-vertex interior of a three-vertex path.) -/
theorem isPathFrom_interior {G : SimpleGraph V} {p : List V}
    (hp : IsPathList G p) (h3 : 3 ≤ p.length) :
    IsPathFrom G (SPGT.interior p) (p[1]'(by omega)) (p[p.length - 2]'(by omega)) := by
  have hd : IsPathList G (p.drop 1) := PathBasics.isPathList_drop hp (by omega)
  have ht : IsPathList G ((p.drop 1).take (p.length - 2)) :=
    PathBasics.isPathList_take hd (by omega)
  have hkey : p.length - 2 - 1 + 1 = p.length - 2 := by omega
  have hh := PathBasics.head?_slice p (i := 1) (j := p.length - 2) (by omega) (by omega)
  have hl := PathBasics.getLast?_slice p (i := 1) (j := p.length - 2) (by omega) (by omega)
  rw [hkey] at hh hl
  exact ⟨by rw [PathBasics.interior_eq_drop_take]; exact ht,
    by rw [PathBasics.interior_eq_drop_take]; exact hh,
    by rw [PathBasics.interior_eq_drop_take]; exact hl⟩

/-! ## Gluing -/

/-- **Concatenating two paths along a single edge.**  Two vertex-disjoint paths whose only edge
between them joins the last vertex of the first to the first vertex of the second concatenate to
a path — the paper's `u₀-R-u₁-w₀-S-w₁`. -/
theorem glue_path {G : SimpleGraph V} {R S : List V} {u₀ u₁ w₀ w₁ : V}
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

/-- **Closing two paths into a hole.**  Two vertex-disjoint paths whose only two connecting
edges join the last vertex of the first to the first vertex of the second, and the first vertex
of the first to the last vertex of the second, concatenate to a hole. -/
theorem glue_hole {G : SimpleGraph V} {P R : List V} {u₀ u₁ w₀ w₁ : V}
    (hP : IsPathFrom G P u₀ u₁) (hR : IsPathFrom G R w₀ w₁)
    (hdisj : ∀ x ∈ P, x ∉ R)
    (hcross : ∀ x ∈ P, ∀ y ∈ R, (G.Adj x y ↔ (x = u₁ ∧ y = w₀) ∨ (x = u₀ ∧ y = w₁)))
    (hlen : 4 ≤ P.length + R.length) :
    IsHoleList G (P ++ R) := by
  obtain ⟨hPl, hPh, hPt⟩ := hP
  obtain ⟨hRl, hRh, hRt⟩ := hR
  have hm : 0 < P.length := PathBasics.path_length_pos hPl
  have hn : 0 < R.length := PathBasics.path_length_pos hRl
  have hP0 : P[0]'hm = u₀ := PathBasics.getElem_zero_of_head? hPh hm
  have hPm : P[P.length - 1]'(by omega) = u₁ := PathBasics.getElem_last_of_getLast? hPt hm
  have hR0 : R[0]'hn = w₀ := PathBasics.getElem_zero_of_head? hRh hn
  have hRn : R[R.length - 1]'(by omega) = w₁ := PathBasics.getElem_last_of_getLast? hRt hn
  have hPnd : P.Nodup := hPl.2.1
  have hRnd : R.Nodup := hRl.2.1
  have cross : ∀ (i j : ℕ) (hiP : i < P.length) (hjP : P.length ≤ j)
      (hi : i < (P ++ R).length) (hj : j < (P ++ R).length),
      (G.Adj ((P ++ R)[i]'hi) ((P ++ R)[j]'hj) ↔
        (j = (i + 1) % (P ++ R).length ∨ i = (j + 1) % (P ++ R).length)) := by
    intro i j hiP hjP hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    have hjR : j - P.length < R.length := by omega
    rw [List.getElem_append_left hiP, List.getElem_append_right hjP,
      hcross (P[i]'hiP) (List.getElem_mem hiP) (R[j - P.length]'hjR) (List.getElem_mem hjR)]
    have e1 : (P[i]'hiP = u₁) ↔ i = P.length - 1 := by
      rw [← hPm]; exact hPnd.getElem_inj_iff
    have e2 : (P[i]'hiP = u₀) ↔ i = 0 := by
      rw [← hP0]; exact hPnd.getElem_inj_iff
    have e3 : (R[j - P.length]'hjR = w₀) ↔ j - P.length = 0 := by
      rw [← hR0]; exact hRnd.getElem_inj_iff
    have e4 : (R[j - P.length]'hjR = w₁) ↔ j - P.length = R.length - 1 := by
      rw [← hRn]; exact hRnd.getElem_inj_iff
    rw [e1, e2, e3, e4]
    simp only [List.length_append]
    rw [succ_mod_eq hiL, succ_mod_eq hjL]
    split_ifs <;> omega
  refine ⟨by simpa using hlen, ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hPnd, hRnd, fun a ha b hb => by rintro rfl; exact hdisj a ha hb⟩
  · intro i j hi hj
    have hiL : i < P.length + R.length := by simpa using hi
    have hjL : j < P.length + R.length := by simpa using hj
    rcases lt_or_ge i P.length with hiP | hiP
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [List.getElem_append_left hiP, List.getElem_append_left hjP,
          PathBasics.path_adj_iff hPl hiP hjP]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega
      · exact cross i j hiP hjP hi hj
    · rcases lt_or_ge j P.length with hjP | hjP
      · rw [SimpleGraph.adj_comm, cross j i hjP hiP hj hi]
        constructor <;> (intro h; tauto)
      · have hiR : i - P.length < R.length := by omega
        have hjR : j - P.length < R.length := by omega
        rw [List.getElem_append_right hiP, List.getElem_append_right hjP,
          PathBasics.path_adj_iff hRl hiR hjR]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega

/-! ## A hole minus one of its edges -/

/-- **A hole minus one of its edges is a path** — the paper's `C \ e`.  If the rotation
`c.rotate l` of the hole `c` runs from `v` round to `u`, then in `G \ uv` that rotation is a
path from `v` to `u`.  (2.10 feeds exactly this to 2.1, and `IsLeapForHole` is defined by it.) -/
theorem isPathFrom_hole_deleteEdges {G : SimpleGraph V} {c : List V} {u v : V} {l : ℕ}
    (hc : IsHoleList G c) (hhead : (c.rotate l).head? = some v)
    (hlast : (c.rotate l).getLast? = some u) :
    IsPathFrom (G.deleteEdges {s(u, v)}) (c.rotate l) v u := by
  obtain ⟨h4, hnd, hadj⟩ := HoleBasics.isHoleList_rotate hc l
  have hpos : 0 < (c.rotate l).length := by omega
  have h0 : ((c.rotate l)[0]'hpos) = v := PathBasics.getElem_zero_of_head? hhead hpos
  have hn : ((c.rotate l)[(c.rotate l).length - 1]'(by omega)) = u :=
    PathBasics.getElem_last_of_getLast? hlast hpos
  refine ⟨⟨?_, hnd, ?_⟩, hhead, hlast⟩
  · intro hnil
    rw [hnil] at h4
    simp at h4
  · intro i j hi hj
    rw [SimpleGraph.deleteEdges_adj, hadj i j hi hj]
    have e1 : (((c.rotate l)[i]'hi) = u) ↔ i = (c.rotate l).length - 1 := by
      rw [← hn]; exact hnd.getElem_inj_iff
    have e2 : (((c.rotate l)[i]'hi) = v) ↔ i = 0 := by
      rw [← h0]; exact hnd.getElem_inj_iff
    have e3 : (((c.rotate l)[j]'hj) = u) ↔ j = (c.rotate l).length - 1 := by
      rw [← hn]; exact hnd.getElem_inj_iff
    have e4 : (((c.rotate l)[j]'hj) = v) ↔ j = 0 := by
      rw [← h0]; exact hnd.getElem_inj_iff
    have hmem : (s(((c.rotate l)[i]'hi), ((c.rotate l)[j]'hj)) ∈ ({s(u, v)} : Set (Sym2 V)))
        ↔ ((i = (c.rotate l).length - 1 ∧ j = 0) ∨ (i = 0 ∧ j = (c.rotate l).length - 1)) := by
      rw [Set.mem_singleton_iff, Sym2.eq_iff, e1, e2, e3, e4]
    rw [hmem, succ_mod_eq hi, succ_mod_eq hj]
    split_ifs <;> omega

/-! ## A five-hole is a five-antihole -/

/-- The five-vertex case, with the vertices named.  Reindexing the cycle `v₀v₁v₂v₃v₄` by
`0,2,4,1,3` turns its five edges into the five non-edges of the new cyclic order and vice
versa, so the result is a hole of the complement. -/
private theorem isHoleList_compl_five {K : SimpleGraph V} {v0 v1 v2 v3 v4 : V}
    (hc : IsHoleList K [v0, v1, v2, v3, v4]) :
    IsHoleList Kᶜ [v0, v2, v4, v1, v3] := by
  obtain ⟨-, hnd, hadj⟩ := hc
  -- the five edges of the cycle
  have e01 : K.Adj v0 v1 := by simpa using (hadj 0 1 (by simp) (by simp)).mpr (by simp)
  have e12 : K.Adj v1 v2 := by simpa using (hadj 1 2 (by simp) (by simp)).mpr (by simp)
  have e23 : K.Adj v2 v3 := by simpa using (hadj 2 3 (by simp) (by simp)).mpr (by simp)
  have e34 : K.Adj v3 v4 := by simpa using (hadj 3 4 (by simp) (by simp)).mpr (by simp)
  have e40 : K.Adj v4 v0 := by simpa using (hadj 4 0 (by simp) (by simp)).mpr (by simp)
  -- the five non-edges
  have n02 : ¬ K.Adj v0 v2 := by
    intro h
    have h' : K.Adj ([v0, v1, v2, v3, v4][0]'(by simp)) ([v0, v1, v2, v3, v4][2]'(by simp)) := by
      simpa using h
    have := (hadj 0 2 (by simp) (by simp)).mp h'
    simp at this
  have n13 : ¬ K.Adj v1 v3 := by
    intro h
    have h' : K.Adj ([v0, v1, v2, v3, v4][1]'(by simp)) ([v0, v1, v2, v3, v4][3]'(by simp)) := by
      simpa using h
    have := (hadj 1 3 (by simp) (by simp)).mp h'
    simp at this
  have n24 : ¬ K.Adj v2 v4 := by
    intro h
    have h' : K.Adj ([v0, v1, v2, v3, v4][2]'(by simp)) ([v0, v1, v2, v3, v4][4]'(by simp)) := by
      simpa using h
    have := (hadj 2 4 (by simp) (by simp)).mp h'
    simp at this
  have n30 : ¬ K.Adj v3 v0 := by
    intro h
    have h' : K.Adj ([v0, v1, v2, v3, v4][3]'(by simp)) ([v0, v1, v2, v3, v4][0]'(by simp)) := by
      simpa using h
    have := (hadj 3 0 (by simp) (by simp)).mp h'
    simp at this
  have n41 : ¬ K.Adj v4 v1 := by
    intro h
    have h' : K.Adj ([v0, v1, v2, v3, v4][4]'(by simp)) ([v0, v1, v2, v3, v4][1]'(by simp)) := by
      simpa using h
    have := (hadj 4 1 (by simp) (by simp)).mp h'
    simp at this
  -- pairwise distinctness
  have d01 : v0 ≠ v1 := by rintro rfl; simp at hnd
  have d02 : v0 ≠ v2 := by rintro rfl; simp at hnd
  have d03 : v0 ≠ v3 := by rintro rfl; simp at hnd
  have d04 : v0 ≠ v4 := by rintro rfl; simp at hnd
  have d12 : v1 ≠ v2 := by rintro rfl; simp at hnd
  have d13 : v1 ≠ v3 := by rintro rfl; simp at hnd
  have d14 : v1 ≠ v4 := by rintro rfl; simp at hnd
  have d23 : v2 ≠ v3 := by rintro rfl; simp at hnd
  have d24 : v2 ≠ v4 := by rintro rfl; simp at hnd
  have d34 : v3 ≠ v4 := by rintro rfl; simp at hnd
  -- the five edges of the complementary cycle
  have c02 : Kᶜ.Adj v0 v2 := ⟨d02, n02⟩
  have c24 : Kᶜ.Adj v2 v4 := ⟨d24, n24⟩
  have c41 : Kᶜ.Adj v4 v1 := ⟨Ne.symm d14, n41⟩
  have c13 : Kᶜ.Adj v1 v3 := ⟨d13, n13⟩
  have c30 : Kᶜ.Adj v3 v0 := ⟨Ne.symm d03, n30⟩
  -- and its five non-edges
  have m04 : ¬ Kᶜ.Adj v0 v4 := fun h => h.2 e40.symm
  have m01 : ¬ Kᶜ.Adj v0 v1 := fun h => h.2 e01
  have m21 : ¬ Kᶜ.Adj v2 v1 := fun h => h.2 e12.symm
  have m23 : ¬ Kᶜ.Adj v2 v3 := fun h => h.2 e23
  have m43 : ¬ Kᶜ.Adj v4 v3 := fun h => h.2 e34.symm
  have key : ∀ i j : ℕ, i < 5 → j < 5 →
      ∀ (hi : i < [v0, v2, v4, v1, v3].length) (hj : j < [v0, v2, v4, v1, v3].length),
        (Kᶜ.Adj ([v0, v2, v4, v1, v3][i]'hi) ([v0, v2, v4, v1, v3][j]'hj) ↔
          (j = (i + 1) % 5 ∨ i = (j + 1) % 5)) := by
    intro i j hi5 hj5
    interval_cases i <;> interval_cases j <;> intro hi hj <;>
    simp only [List.getElem_cons_zero, List.getElem_cons_succ] <;>
    first
      | exact iff_of_false (Kᶜ).irrefl (by first | omega | simp | tauto)
      | exact iff_of_true c02 (by first | omega | simp | tauto)
      | exact iff_of_true c02.symm (by first | omega | simp | tauto)
      | exact iff_of_true c24 (by first | omega | simp | tauto)
      | exact iff_of_true c24.symm (by first | omega | simp | tauto)
      | exact iff_of_true c41 (by first | omega | simp | tauto)
      | exact iff_of_true c41.symm (by first | omega | simp | tauto)
      | exact iff_of_true c13 (by first | omega | simp | tauto)
      | exact iff_of_true c13.symm (by first | omega | simp | tauto)
      | exact iff_of_true c30 (by first | omega | simp | tauto)
      | exact iff_of_true c30.symm (by first | omega | simp | tauto)
      | exact iff_of_false m04 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => m04 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false m01 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => m01 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false m21 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => m21 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false m23 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => m23 h.symm) (by first | omega | simp | tauto)
      | exact iff_of_false m43 (by first | omega | simp | tauto)
      | exact iff_of_false (fun h => m43 h.symm) (by first | omega | simp | tauto)
  refine ⟨by simp, ?_, ?_⟩
  · simp [d02, d04, d01, d03, d24, d23, Ne.symm d12, Ne.symm d14, Ne.symm d34, d13]
  · intro i j hi hj
    have h := key i j (by simpa using hi) (by simpa using hj) hi hj
    simpa using h

/-- **"An odd hole of length 5 is also an odd antihole."**  Reindexing a five-vertex hole by
`0,2,4,1,3` produces a hole of the complement on the same vertices.

(The list binder is `c`, so every index must be written `((c)[i]'h)`: `Mathlib`'s `c[…]` cycle
notation makes a bare `c[` a single lexer atom.  See `lean_knowledge.md`.) -/
theorem isHoleList_compl_of_length_five {K : SimpleGraph V} {c : List V}
    (hc : IsHoleList K c) (h5 : c.length = 5) :
    IsHoleList Kᶜ [((c)[0]'(by omega)), ((c)[2]'(by omega)), ((c)[4]'(by omega)),
      ((c)[1]'(by omega)), ((c)[3]'(by omega))] := by
  obtain ⟨v0, v1, v2, v3, v4, rfl⟩ := length_eq_five h5
  show IsHoleList Kᶜ [v0, v2, v4, v1, v3]
  exact isHoleList_compl_five hc

/-! ## A hole cannot sit inside a path -/

/-- Greatest index below `n` satisfying `Q`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ (n : ℕ), (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- On a cycle of length `≥ 4`, every index has two *distinct* cyclic neighbours, both distinct
from it.  (This is "a hole vertex has degree exactly two", index-side.) -/
private theorem two_hole_neighbours {m i : ℕ} (h4 : 4 ≤ m) (hi : i < m) :
    ∃ j₁ j₂, j₁ < m ∧ j₂ < m ∧ j₁ ≠ j₂ ∧ j₁ ≠ i ∧ j₂ ≠ i ∧
      (j₁ = (i + 1) % m ∨ i = (j₁ + 1) % m) ∧ (j₂ = (i + 1) % m ∨ i = (j₂ + 1) % m) := by
  have hsucc : (i + 1) % m = if i + 1 = m then 0 else i + 1 := succ_mod_eq hi
  by_cases h0 : i = 0
  · subst h0
    refine ⟨1, m - 1, by omega, by omega, by omega, by omega, by omega, Or.inl ?_, Or.inr ?_⟩
    · rw [Nat.mod_eq_of_lt (show (0 : ℕ) + 1 < m by omega)]
    · rw [show m - 1 + 1 = m by omega, Nat.mod_self]
  · refine ⟨(i + 1) % m, i - 1, Nat.mod_lt _ (by omega), by omega, ?_, ?_, by omega,
      Or.inl rfl, Or.inr ?_⟩
    · rw [hsucc]; split_ifs <;> omega
    · rw [hsucc]; split_ifs <;> omega
    · rw [show i - 1 + 1 = i by omega, Nat.mod_eq_of_lt hi]

/-- **A hole cannot sit inside a path.**  Take the hole vertex occurring latest on the path: its
two distinct hole-neighbours both lie earlier on the path, so each of them must occupy the
position immediately before it — and there is only one such position. -/
theorem no_hole_in_path {H : SimpleGraph V} {D p : List V}
    (hD : IsHoleList H D) (hp : IsPathList H p) (hsub : ∀ z ∈ D, z ∈ p) : False := by
  obtain ⟨h4, hDnd, hDadj⟩ := hD
  have hex : ∃ k, k < p.length ∧ ∃ (hk : k < p.length), ((p[k]'hk) ∈ D) := by
    have hD0 : ((D)[0]'(show 0 < D.length by omega)) ∈ D :=
      List.getElem_mem (show 0 < D.length by omega)
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem (hsub _ hD0)
    exact ⟨k, hk, hk, by rw [hkeq]; exact hD0⟩
  obtain ⟨k₀, hk₀lt, ⟨hk₀, hk₀D⟩, hmax⟩ :=
    exists_greatest (Q := fun k => ∃ (hk : k < p.length), ((p[k]'hk) ∈ D)) p.length hex
  obtain ⟨i, hi, hieq⟩ := List.getElem_of_mem hk₀D
  obtain ⟨j₁, j₂, hj₁, hj₂, hj12, hj1i, hj2i, hn1, hn2⟩ := two_hole_neighbours h4 hi
  -- every hole-neighbour of `p[k₀]` sits at position `k₀ - 1` on `p`
  have step : ∀ j (hj : j < D.length), j ≠ i →
      (j = (i + 1) % D.length ∨ i = (j + 1) % D.length) →
      ∃ (k : ℕ) (hk : k < p.length), ((p[k]'hk) = ((D)[j]'hj)) ∧ k + 1 = k₀ := by
    intro j hj hji hor
    have hadjD : H.Adj ((D)[i]'hi) ((D)[j]'hj) := (hDadj i j hi hj).mpr hor
    obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem (hsub _ (List.getElem_mem hj))
    have hle : k ≤ k₀ := hmax k hk ⟨hk, by rw [hkeq]; exact List.getElem_mem hj⟩
    have hne : k ≠ k₀ := by
      intro hkk
      apply hji
      have hpp : ((p)[k₀]'hk₀) = ((p)[k]'hk) := hp.2.1.getElem_inj_iff.mpr hkk.symm
      have hdd : ((D)[i]'hi) = ((D)[j]'hj) := by rw [hieq, hpp, hkeq]
      exact (hDnd.getElem_inj_iff.mp hdd).symm
    have hadjp : H.Adj ((p)[k₀]'hk₀) ((p)[k]'hk) := by
      rw [hieq, ← hkeq] at hadjD; exact hadjD
    have hcase := (PathBasics.path_adj_iff hp hk₀ hk).mp hadjp
    exact ⟨k, hk, hkeq, by omega⟩
  obtain ⟨k₁, hk₁, hkeq₁, hs₁⟩ := step j₁ hj₁ hj1i hn1
  obtain ⟨k₂, hk₂, hkeq₂, hs₂⟩ := step j₂ hj₂ hj2i hn2
  have hkk : k₁ = k₂ := by omega
  have hpp : ((p)[k₁]'hk₁) = ((p)[k₂]'hk₂) := hp.2.1.getElem_inj_iff.mpr hkk
  have hdd : ((D)[j₁]'hj₁) = ((D)[j₂]'hj₂) := by rw [← hkeq₁, hpp, hkeq₂]
  exact hj12 (hDnd.getElem_inj_iff.mp hdd)

/-! ## Positions of a subpath along a path

The paper says *"`R*` is a subpath of the even path `P*`"* (2.9, 2.11) and reads a length off it.
The content is that each vertex of `q` has a position on `p`, that distinct vertices of `q` get
distinct positions, and that consecutive vertices of `q` — being adjacent on the *induced* path
`p` — get positions differing by exactly one.  Everything the paper does with "subpath" follows:
`|f s - f t| ≤ |s - t|` bounds `q.length` from below once two far-apart positions are known, and
injectivity of `f` into the available index range bounds it from above. -/

/-- **Positions along a subpath move one step at a time.** -/
theorem exists_pos_of_subpath {G : SimpleGraph V} {p q : List V}
    (hp : IsPathList G p) (hq : IsPathList G q) (hsub : ∀ z ∈ q, z ∈ p) :
    ∃ f : ℕ → ℕ,
      (∀ t, t < q.length → f t < p.length) ∧
      (∀ t (ht : t < q.length) (hf : f t < p.length), (p[f t]'hf) = (q[t]'ht)) ∧
      (∀ s t, s < q.length → t < q.length → f s = f t → s = t) ∧
      (∀ s t, s ≤ t → t < q.length → f t ≤ f s + (t - s) ∧ f s ≤ f t + (t - s)) := by
  classical
  have hall : ∀ t : ℕ, ∃ k : ℕ, (t < q.length → k < p.length) ∧
      ∀ (ht : t < q.length) (hk : k < p.length), (p[k]'hk) = (q[t]'ht) := by
    intro t
    by_cases ht : t < q.length
    · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem (hsub _ (List.getElem_mem ht))
      exact ⟨k, fun _ => hk, fun _ _ => hkeq⟩
    · exact ⟨0, fun h => absurd h ht, fun h => absurd h ht⟩
  choose f hf1 hf2 using hall
  have hinj : ∀ s t, s < q.length → t < q.length → f s = f t → s = t := by
    intro s t hs ht hst
    have h1 : (p[f s]'(hf1 s hs)) = (q[s]'hs) := hf2 s hs (hf1 s hs)
    have h2 : (p[f t]'(hf1 t ht)) = (q[t]'ht) := hf2 t ht (hf1 t ht)
    have hqq : (q[s]'hs) = (q[t]'ht) := by
      rw [← h1, ← h2]
      exact hp.2.1.getElem_inj_iff.mpr hst
    exact hq.2.1.getElem_inj_iff.mp hqq
  have hstep : ∀ t (ht : t + 1 < q.length), f t + 1 = f (t + 1) ∨ f (t + 1) + 1 = f t := by
    intro t ht
    have htlt : t < q.length := by omega
    have hadjq : G.Adj (q[t]'htlt) (q[t + 1]'ht) := PathBasics.path_adj_succ hq ht
    have h1 : (p[f t]'(hf1 t htlt)) = (q[t]'htlt) := hf2 t htlt (hf1 t htlt)
    have h2 : (p[f (t + 1)]'(hf1 (t + 1) ht)) = (q[t + 1]'ht) := hf2 (t + 1) ht (hf1 (t + 1) ht)
    rw [← h1, ← h2] at hadjq
    exact (PathBasics.path_adj_iff hp (hf1 t htlt) (hf1 (t + 1) ht)).mp hadjq
  refine ⟨f, hf1, hf2, hinj, ?_⟩
  intro s t
  induction t with
  | zero =>
    intro hst ht
    have hs0 : s = 0 := by omega
    subst hs0
    omega
  | succ n ih =>
    intro hst ht
    rcases Nat.lt_or_ge s (n + 1) with h | h
    · have hnlt : n < q.length := by omega
      obtain ⟨ha, hb⟩ := ih (by omega) hnlt
      rcases hstep n ht with hc | hc <;> omega
    · have hs : s = n + 1 := by omega
      subst hs
      omega

end Workspace.ProofLemmas.PathGlue
