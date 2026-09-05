/-  Proof attempt for statement 2.7 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 10).

    PRINTED PROOF (verbatim, `paper/proofs/2_7.md`):

      "The first statement follows from the second by taking complements, so it suffices
       to prove the second.  Suppose u, v ∈ A are adjacent and joined by an odd antipath P
       with interior in C.  Since B is anticonnected and u, v both have non-neighbours in
       B, they are also joined by an antipath Q with interior in B, which is even since
       (A,B) is balanced.  But then u-P-v-Q-u is an odd antihole, a contradiction.  Now
       suppose there are nonadjacent u, v ∈ C, joined by an odd path P with interior in A.
       Then P has length ≥ 5, since otherwise its vertices could be reordered to be an odd
       antipath of the kind we already handled.  The ends of P are B-complete, and no
       internal vertex is B-complete, and so B contains a leap for P by 2.1; and hence
       there is an odd path with ends in B and interior in A, which is impossible since
       (A,B) is balanced.  This proves 2.7."

    MAP ONTO THE LEAN PROOF.

    * `balanced_transfer` is the *second* printed statement, isolated so that the first can
      be obtained from it "by taking complements".
    * Its second half (`part2` inside `balanced_transfer`) is the printed first paragraph:
      `exists_antipath_interior_in` supplies `Q`, `hbal.2` makes `Q` even, and `glue_hole`
      assembles `u-P-v-Q-u` as a hole of `Gᶜ` whose length is `|P| + |Q|`, odd — contradicting
      the second clause of `Berge G`.
    * Its first half is the printed second paragraph: length `1` is excluded because the ends
      are nonadjacent; length `3` is the printed *"its vertices could be reordered to be an odd
      antipath of the kind we already handled"* — the reordering is `p₂-p₄-p₁-p₃`, an antipath
      of length 3 with ends `p₂, p₃ ∈ A` adjacent and interior `{p₄, p₁} ⊆ C`, so `part2`
      applies.  Then `2.1` is invoked at `X = B`; its first outcome is killed by *"no internal
      vertex is B-complete"*, its third by length `≥ 5`, and its second gives the leap
      `a, b ∈ B`, whence `a-p₂-⋯-p_{n-1}-b` is an odd path with ends in `B` and interior in
      `A`, contradicting the first clause of `Balanced G A B`.
    * The Lean statement omits `Disjoint A B` (the paper builds it into "balanced").  Nothing
      in the argument needs it: every vertex handed to 2.1 is shown to lie outside `B`
      directly (a vertex of the odd path lying in `B` would be complete to `C`, hence adjacent
      to both ends, which on an induced path forces length 2).

    Helper lemmas at the head of the file are pure list/graph bookkeeping and are flagged for
    lifting into `Workspace/ProofLemmas/`.  `glue_hole` and `succ_mod_eq` are copied from
    `ProofAttempts/thm_2_4/Attempt_1.lean`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Statements.S02.Thm_2_1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Encoding infrastructure -/

section Helpers

variable {V : Type*}

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- Two vertex-disjoint paths whose only two connecting edges join the last vertex of
the first to the first vertex of the second, and the first vertex of the first to the
last vertex of the second, concatenate to a hole. -/
private theorem glue_hole {G : SimpleGraph V} {P R : List V} {u₀ u₁ w₀ w₁ : V}
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

/-- The interior of a path on at least three vertices is itself a path, running from the
second vertex to the second-from-last. -/
private theorem isPathFrom_interior {G : SimpleGraph V} {p : List V}
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

/-- A four-element list with the three consecutive edges present and the three
non-consecutive pairs absent is a path. -/
private theorem isPathList_four {G : SimpleGraph V} {a b c d : V}
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
      | exact iff_of_false G.irrefl (by first | omega | tauto)
      | exact iff_of_true h1 (by first | omega | tauto)
      | exact iff_of_true h2 (by first | omega | tauto)
      | exact iff_of_true h3 (by first | omega | tauto)
      | exact iff_of_true h1.symm (by first | omega | tauto)
      | exact iff_of_true h2.symm (by first | omega | tauto)
      | exact iff_of_true h3.symm (by first | omega | tauto)
      | exact iff_of_false n1 (by first | omega | tauto)
      | exact iff_of_false n2 (by first | omega | tauto)
      | exact iff_of_false n3 (by first | omega | tauto)
      | exact iff_of_false (fun h => n1 h.symm) (by first | omega | tauto)
      | exact iff_of_false (fun h => n2 h.symm) (by first | omega | tauto)
      | exact iff_of_false (fun h => n3 h.symm) (by first | omega | tauto)
  exact ⟨by simp, hnd, fun i j hi hj => key i j (by simpa using hi) (by simpa using hj) hi hj⟩

private theorem length_eq_four {α : Type*} {l : List α} (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  match l, h with
  | [a, b, c, d], _ => exact ⟨a, b, c, d, rfl⟩

end Helpers

/-! ### The printed second statement of 2.7 -/

section Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **2.7, second item**, isolated: *"if `B` is anticonnected and no vertex in `A` is
`B`-complete, and `B` is complete to `C`, then `(A,C)` is balanced."*  The first item is
this one applied to `Gᶜ`. -/
private theorem balanced_transfer {G : SimpleGraph V} (hG : Berge G) {A B C : Set V}
    (hbal : SPGT.Balanced G A B) (hC : C ⊆ (A ∪ B)ᶜ)
    (hBanti : AnticonnectedSet G B)
    (hnc : ∀ a ∈ A, ¬ VertexComplete G a B)
    (hBC : Complete G B C) :
    SPGT.Balanced G A C := by
  have hCA : ∀ c ∈ C, c ∉ A := fun c hc hcA => (hC hc) (Or.inl hcA)
  have hCB : ∀ c ∈ C, c ∉ B := fun c hc hcB => (hC hc) (Or.inr hcB)
  -- ### The antipath clause: "Suppose u, v ∈ A are adjacent and joined by an odd antipath
  -- P with interior in C."
  have part2 : ∀ (u v : V) (p : List V), u ∈ A → v ∈ A → G.Adj u v →
      IsAntipathFrom G p u v → (∀ x ∈ SPGT.interior p, x ∈ C) → ¬ Odd (pathLength p) := by
    intro u v P huA hvA huv hP hPint hodd
    have huv' : u ≠ v := G.ne_of_adj huv
    have hPl : IsPathList Gᶜ P := hP.1
    have hpos : 0 < P.length := PathBasics.path_length_pos hPl
    have hlen1 : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hPl
    have hoddm : pathLength P % 2 = 1 := Nat.odd_iff.mp hodd
    have hne1 : pathLength P ≠ 1 := fun h1 =>
      (PathBasics.isPathFrom_ends_adj_of_length_one hP h1).2 huv
    have hP4 : 4 ≤ P.length := by omega
    -- both ends lie outside `B`, since `B` is complete to `C` while `P` avoids `G`-edges
    have hP1int : (P[1]'(by omega)) ∈ SPGT.interior P :=
      PathBasics.getElem_mem_interior hPl (by omega) (by omega) (by omega)
    have hPn2int : (P[P.length - 2]'(by omega)) ∈ SPGT.interior P :=
      PathBasics.getElem_mem_interior hPl (by omega) (by omega) (by omega)
    have hu0 : (P[0]'(by omega)) = u := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have hulast : (P[P.length - 1]'(by omega)) = v :=
      PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    have huB : u ∉ B := by
      intro huB
      have hadj : Gᶜ.Adj (P[0]'(by omega)) (P[1]'(by omega)) :=
        (PathBasics.path_adj_iff hPl (by omega) (by omega)).mpr (Or.inl rfl)
      rw [hu0] at hadj
      exact hadj.2 (hBC u huB _ (hPint _ hP1int))
    have hvB : v ∉ B := by
      intro hvB
      have hadj : Gᶜ.Adj (P[P.length - 1]'(by omega)) (P[P.length - 2]'(by omega)) :=
        (PathBasics.path_adj_iff hPl (by omega) (by omega)).mpr (Or.inr (by omega))
      rw [hulast] at hadj
      exact hadj.2 (hBC v hvB _ (hPint _ hPn2int))
    -- "Since B is anticonnected and u, v both have non-neighbours in B"
    have hunb : ∃ x ∈ B, ¬ G.Adj u x := by
      by_contra hcon
      push Not at hcon
      exact hnc u huA hcon
    have hvnb : ∃ x ∈ B, ¬ G.Adj v x := by
      by_contra hcon
      push Not at hcon
      exact hnc v hvA hcon
    obtain ⟨Q, hQ, hQint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hBanti huB hvB hunb hvnb
    -- "which is even since (A,B) is balanced"
    have hQeven : ¬ Odd (pathLength Q) := hbal.2 u v Q huA hvA huv hQ hQint
    have hQl : IsPathList Gᶜ Q := hQ.1
    have hQpos : 0 < Q.length := PathBasics.path_length_pos hQl
    have hQlen1 : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQl
    have hQ2 : 2 ≤ Q.length := by
      by_contra hcon
      obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by omega : Q.length = 1)
      have e1 : a = u := by simpa using hQ.2.1
      have e2 : a = v := by simpa using hQ.2.2
      exact huv' (e1.symm.trans e2)
    have hQ3 : 3 ≤ Q.length := by
      by_contra hcon
      have h2 : pathLength Q = 1 := by
        simp only [pathLength]; omega
      exact (PathBasics.isPathFrom_ends_adj_of_length_one hQ h2).2 huv
    have hQ0 : (Q[0]'(by omega)) = u := PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hQn : (Q[Q.length - 1]'(by omega)) = v :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
    have hQinj : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length),
        ((Q[i]'hi) = (Q[j]'hj)) ↔ i = j := fun i j hi hj => hQl.2.1.getElem_inj_iff
    -- "u-P-v-Q-u is an odd antihole"
    have hIQ : IsPathFrom Gᶜ (SPGT.interior Q) (Q[1]'(by omega)) (Q[Q.length - 2]'(by omega)) :=
      isPathFrom_interior hQl (by omega)
    have hR : IsPathFrom Gᶜ (SPGT.interior Q).reverse
        (Q[Q.length - 2]'(by omega)) (Q[1]'(by omega)) := PathBasics.isPathFrom_reverse hIQ
    have hRB : ∀ y ∈ (SPGT.interior Q).reverse, y ∈ B :=
      fun y hy => hQint y (List.mem_reverse.mp hy)
    have hPsplit : ∀ x ∈ P, x = u ∨ x = v ∨ x ∈ SPGT.interior P := by
      intro x hx
      by_cases h1 : x = u
      · exact Or.inl h1
      by_cases h2 : x = v
      · exact Or.inr (Or.inl h2)
      exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hx, h1, h2⟩))
    have hdisj : ∀ x ∈ P, x ∉ (SPGT.interior Q).reverse := by
      intro x hx hxR
      have hxB : x ∈ B := hRB x hxR
      rcases hPsplit x hx with h | h | hxi
      · exact huB (h ▸ hxB)
      · exact hvB (h ▸ hxB)
      · exact hCB x (hPint x hxi) hxB
    have hcross : ∀ x ∈ P, ∀ y ∈ (SPGT.interior Q).reverse,
        (Gᶜ.Adj x y ↔ ((x = v ∧ y = (Q[Q.length - 2]'(by omega))) ∨
          (x = u ∧ y = (Q[1]'(by omega))))) := by
      intro x hx y hy
      obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
        PathBasics.exists_getElem_of_mem_interior hQl (List.mem_reverse.mp hy)
      have hA_u : Gᶜ.Adj u (Q[k]'hk) ↔ k = 1 := by
        constructor
        · intro h
          rw [← hQ0] at h
          have := (PathBasics.path_adj_iff hQl (by omega) hk).mp h
          omega
        · rintro rfl
          rw [← hQ0]
          exact (PathBasics.path_adj_iff hQl (by omega) hk).mpr (Or.inl rfl)
      have hA_v : Gᶜ.Adj v (Q[k]'hk) ↔ k = Q.length - 2 := by
        constructor
        · intro h
          rw [← hQn] at h
          have := (PathBasics.path_adj_iff hQl (by omega) hk).mp h
          omega
        · rintro rfl
          rw [← hQn]
          exact (PathBasics.path_adj_iff hQl (by omega) hk).mpr (Or.inr (by omega))
      have hE1 : ((Q[k]'hk) = (Q[1]'(by omega : 1 < Q.length))) ↔ k = 1 :=
        hQinj k 1 hk (by omega)
      have hE2 : ((Q[k]'hk) = (Q[Q.length - 2]'(by omega : Q.length - 2 < Q.length))) ↔
          k = Q.length - 2 := hQinj k (Q.length - 2) hk (by omega)
      rcases hPsplit x hx with hxu | hxv | hxi
      · rw [hxu]
        constructor
        · intro h
          exact Or.inr ⟨rfl, hE1.mpr (hA_u.mp h)⟩
        · rintro (⟨hc, -⟩ | ⟨-, hc⟩)
          · exact absurd hc huv'
          · exact hA_u.mpr (hE1.mp hc)
      · rw [hxv]
        constructor
        · intro h
          exact Or.inl ⟨rfl, hE2.mpr (hA_v.mp h)⟩
        · rintro (⟨-, hc⟩ | ⟨hc, -⟩)
          · exact hA_v.mpr (hE2.mp hc)
          · exact absurd hc.symm huv'
      · have hxC : x ∈ C := hPint x hxi
        have hyB : (Q[k]'hk) ∈ B := hQint _ (List.mem_reverse.mp hy)
        have hGadj : G.Adj (Q[k]'hk) x := hBC _ hyB x hxC
        have hne := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hxi
        refine iff_of_false (fun hc => hc.2 hGadj.symm) ?_
        rintro (⟨hc, -⟩ | ⟨hc, -⟩)
        · exact hne.2.2 hc
        · exact hne.2.1 hc
    have hhole : IsHoleList Gᶜ (P ++ (SPGT.interior Q).reverse) :=
      glue_hole hP hR hdisj hcross (by omega)
    have heven : Even (holeLength (P ++ (SPGT.interior Q).reverse)) := hG.2 _ hhole
    have hlenQ : (SPGT.interior Q).length = Q.length - 2 := PathBasics.interior_length Q
    have hlenhole : holeLength (P ++ (SPGT.interior Q).reverse) = P.length + (Q.length - 2) := by
      simp only [holeLength, List.length_append, List.length_reverse, hlenQ]
    rw [hlenhole] at heven
    have h1 : (P.length + (Q.length - 2)) % 2 = 0 := Nat.even_iff.mp heven
    have h2 : pathLength Q % 2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hQeven)
    omega
  refine ⟨?_, part2⟩
  -- ### The path clause: "Now suppose there are nonadjacent u, v ∈ C, joined by an odd
  -- path P with interior in A."
  intro u v P huC hvC hnadj hP hPint hodd
  have hPl : IsPathList G P := hP.1
  have hpos : 0 < P.length := PathBasics.path_length_pos hPl
  have hlen1 : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hPl
  have hoddm : pathLength P % 2 = 1 := Nat.odd_iff.mp hodd
  have hne1 : pathLength P ≠ 1 := fun h1 =>
    hnadj (PathBasics.isPathFrom_ends_adj_of_length_one hP h1)
  -- "P has length ≥ 5, since otherwise its vertices could be reordered to be an odd
  -- antipath of the kind we already handled"
  have hne3 : pathLength P ≠ 3 := by
    intro h3
    have hl4 : P.length = 4 := by omega
    obtain ⟨x0, x1, x2, x3, rfl⟩ := length_eq_four hl4
    have hu0 : x0 = u := by simpa using hP.2.1
    have hv3 : x3 = v := by simpa using hP.2.2
    have hnd : [x0, x1, x2, x3].Nodup := hPl.2.1
    have e01 : G.Adj x0 x1 := by
      simpa using (PathBasics.path_adj_iff hPl (i := 0) (j := 1) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have e12 : G.Adj x1 x2 := by
      simpa using (PathBasics.path_adj_iff hPl (i := 1) (j := 2) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have e23 : G.Adj x2 x3 := by
      simpa using (PathBasics.path_adj_iff hPl (i := 2) (j := 3) (by simp) (by simp)).mpr
        (Or.inl rfl)
    have n02 : ¬ G.Adj x0 x2 := by
      intro h
      have := (PathBasics.path_adj_iff hPl (i := 0) (j := 2) (by simp) (by simp)).mp
        (by simpa using h)
      omega
    have n13 : ¬ G.Adj x1 x3 := by
      intro h
      have := (PathBasics.path_adj_iff hPl (i := 1) (j := 3) (by simp) (by simp)).mp
        (by simpa using h)
      omega
    have n03 : ¬ G.Adj x0 x3 := by rw [hu0, hv3]; exact hnadj
    have d01 : x0 ≠ x1 := by rintro rfl; simp at hnd
    have d02 : x0 ≠ x2 := by rintro rfl; simp at hnd
    have d03 : x0 ≠ x3 := by rintro rfl; simp at hnd
    have d12 : x1 ≠ x2 := by rintro rfl; simp at hnd
    have d13 : x1 ≠ x3 := by rintro rfl; simp at hnd
    have d23 : x2 ≠ x3 := by rintro rfl; simp at hnd
    -- the reordering: `p₂-p₄-p₁-p₃`
    have hnd' : [x1, x3, x0, x2].Nodup := by
      simp [d01, d02, d03, d12, d13, d23, Ne.symm d01, Ne.symm d02, Ne.symm d03,
        Ne.symm d12, Ne.symm d13, Ne.symm d23]
    have hAP : IsAntipathFrom G [x1, x3, x0, x2] x1 x2 := by
      refine ⟨isPathList_four hnd' ⟨d13, n13⟩ ⟨Ne.symm d03, fun h => n03 h.symm⟩ ⟨d02, n02⟩
        ?_ ?_ ?_, by simp, by simp⟩
      · exact fun h => h.2 e01.symm
      · exact fun h => h.2 e12
      · exact fun h => h.2 e23.symm
    have hintAP : ∀ z ∈ SPGT.interior [x1, x3, x0, x2], z ∈ C := by
      intro z hz
      have : z = x3 ∨ z = x0 := by
        simpa [SPGT.interior] using hz
      rcases this with rfl | rfl
      · rw [hv3]; exact hvC
      · rw [hu0]; exact huC
    have hx1A : x1 ∈ A :=
      hPint _ (PathBasics.getElem_mem_interior hPl (k := 1) (by simp) (by omega) (by simp))
    have hx2A : x2 ∈ A :=
      hPint _ (PathBasics.getElem_mem_interior hPl (k := 2) (by simp) (by omega) (by simp))
    refine part2 x1 x2 [x1, x3, x0, x2] (by simpa using hx1A) (by simpa using hx2A) e12 hAP
      hintAP ?_
    exact ⟨1, by simp [pathLength]⟩
  have h5 : 5 ≤ pathLength P := by omega
  have hn6 : 6 ≤ P.length := by omega
  have hu0 : (P[0]'(by omega)) = u := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hulast : (P[P.length - 1]'(by omega)) = v :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  -- "P is a path in G \ B": no vertex of P lies in B
  have hPB : ∀ w ∈ P, w ∉ B := by
    intro w hw hwB
    by_cases h1 : w = u
    · exact hCB u huC (h1 ▸ hwB)
    by_cases h2 : w = v
    · exact hCB v hvC (h2 ▸ hwB)
    have hwi : w ∈ SPGT.interior P := (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hw, h1, h2⟩
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hPl hwi
    have hau : G.Adj (P[k]'hk) u := hBC _ hwB u huC
    have hav : G.Adj (P[k]'hk) v := hBC _ hwB v hvC
    rw [← hu0] at hau
    rw [← hulast] at hav
    have c1 := (PathBasics.path_adj_iff hPl hk (by omega)).mp hau
    have c2 := (PathBasics.path_adj_iff hPl hk (by omega)).mp hav
    omega
  -- "The ends of P are B-complete"
  have hucomp : VertexComplete G u B := fun x hx => (hBC x hx u huC).symm
  have hvcomp : VertexComplete G v B := fun x hx => (hBC x hx v hvC).symm
  -- "and so B contains a leap for P by 2.1"
  rcases thm_2_1 G hG B hBanti P u v hP hPB hodd hucomp hvcomp with hc1 | hc2 | hc3
  · -- "no internal vertex is B-complete", and the two ends are nonadjacent
    obtain ⟨x, hx, y, hy, hadj, hxc, hyc⟩ := hc1
    have hxend : x = u ∨ x = v := by
      by_contra hcon
      push Not at hcon
      exact hnc x (hPint x ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨hx, hcon.1, hcon.2⟩)) hxc
    have hyend : y = u ∨ y = v := by
      by_contra hcon
      push Not at hcon
      exact hnc y (hPint y ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨hy, hcon.1, hcon.2⟩)) hyc
    rcases hxend with hxe | hxe
    · rcases hyend with hye | hye
      · exact G.ne_of_adj hadj (hxe.trans hye.symm)
      · exact hnadj (by rw [← hxe, ← hye]; exact hadj)
    · rcases hyend with hye | hye
      · exact hnadj (by rw [← hye, ← hxe]; exact hadj.symm)
      · exact G.ne_of_adj hadj (hxe.trans hye.symm)
  · -- the leap `a, b ∈ B`: `a-p₂-⋯-p_{n-1}-b` is an odd path with ends in B, interior in A
    obtain ⟨h5', a, haB, b, hbB, hleap⟩ := hc2
    obtain ⟨-, -, hab, hnab, hAd, hBd⟩ := hleap
    have hIP : IsPathFrom G (SPGT.interior P) (P[1]'(by omega)) (P[P.length - 2]'(by omega)) :=
      isPathFrom_interior hPl (by omega)
    have hsu : G.Adj a (P[1]'(by omega)) := (hAd 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    have htv : G.Adj b (P[P.length - 2]'(by omega)) :=
      (hBd (P.length - 2) (by omega)).mpr (Or.inr (Or.inl rfl))
    have haP : a ∉ SPGT.interior P := fun h => hPB a (PathBasics.interior_subset h) haB
    have hbP : b ∉ SPGT.interior P := fun h => hPB b (PathBasics.interior_subset h) hbB
    have hsother : ∀ x ∈ SPGT.interior P, x ≠ (P[1]'(by omega)) → ¬ G.Adj a x := by
      intro x hx hxne
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hPl hx
      intro hadj
      have hc := (hAd k hk).mp hadj
      have hkne : k ≠ 1 := by
        intro h; exact hxne (by subst h; rfl)
      omega
    have htother : ∀ x ∈ SPGT.interior P, x ≠ (P[P.length - 2]'(by omega)) → ¬ G.Adj b x := by
      intro x hx hxne
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hPl hx
      intro hadj
      have hc := (hBd k hk).mp hadj
      have hkne : k ≠ P.length - 2 := by
        intro h; exact hxne (by subst h; rfl)
      omega
    have hW : IsPathFrom G (a :: (SPGT.interior P ++ [b])) a b :=
      PathAttach.isPathFrom_cons_concat hIP hsu htv hnab hab haP hbP hsother htother
    have hWlen : pathLength (a :: (SPGT.interior P ++ [b])) = pathLength P := by
      rw [PathAttach.pathLength_cons_append_singleton, PathBasics.interior_length]
      simp only [pathLength]
      omega
    have hWint : ∀ x ∈ SPGT.interior (a :: (SPGT.interior P ++ [b])), x ∈ A := by
      intro x hx
      have heq : SPGT.interior (a :: (SPGT.interior P ++ [b])) = SPGT.interior P := by
        simp [SPGT.interior]
      rw [heq] at hx
      exact hPint x hx
    exact hbal.1 a b _ haB hbB hnab hW hWint (by rw [hWlen]; exact hodd)
  · exact absurd hc3.1 (by omega)

end Transfer

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.7** (printed p. 10)

PAPER: *"Let `(A,B)` be balanced in a Berge graph `G`.  Let `C ⊆ V(G) \ (A ∪ B)`.
Then :*

*1. if `A` is connected and every vertex in `B` has a neighbour in `A`, and `A` is
anticomplete to `C`, then `(C,B)` is balanced*

*2. if `B` is anticonnected and no vertex in `A` is `B`-complete, and `B` is
complete to `C`, then `(A,C)` is balanced."*

The two numbered items are the two conjuncts of the conclusion, each with its own
hypotheses.  The paper does not repeat here the disjointness of `A` and `B` that
the definition of *balanced* presupposes, and neither does this statement. -/
theorem thm_2_7 (G : SimpleGraph V) (hG : Berge G) (A B : Set V)
    (hbal : SPGT.Balanced G A B) (C : Set V) (hC : C ⊆ (A ∪ B)ᶜ) :
    (ConnectedSet G A → (∀ b ∈ B, ∃ a ∈ A, G.Adj b a) → Anticomplete G A C →
      SPGT.Balanced G C B) ∧
    (AnticonnectedSet G B → (∀ a ∈ A, ¬ VertexComplete G a B) → Complete G B C →
      SPGT.Balanced G A C) := by
  constructor
  · -- "The first statement follows from the second by taking complements"
    intro hAconn hBnbr hAC
    refine ClassLemmas.balanced_compl.mp
      (balanced_transfer (HoleBasics.berge_compl.mpr hG)
        (ClassLemmas.balanced_compl.mpr hbal) ?_ ?_ ?_ ?_)
    · intro c hc
      have h := hC hc
      simp only [Set.mem_compl_iff, Set.mem_union] at h ⊢
      tauto
    · show ConnectedSet Gᶜᶜ A
      rw [compl_compl]
      exact hAconn
    · intro b hb hcomp
      obtain ⟨a, haA, hadj⟩ := hBnbr b hb
      exact ((G.compl_adj b a).mp (hcomp a haA)).2 hadj
    · intro a ha c hc
      exact (G.compl_adj a c).mpr ⟨fun h => (hC hc) (Or.inl (h ▸ ha)), hAC a ha c hc⟩
  · intro hBanti hnc hBC
    exact balanced_transfer hG hbal hC hBanti hnc hBC


end SPGT

end Workspace.Statements.S02
