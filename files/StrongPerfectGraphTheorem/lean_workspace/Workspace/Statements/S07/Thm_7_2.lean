/-  Proof attempt 2 for statement 7.2 (`Workspace.Statements.S07.SPGT.thm_7_2`).

    THE PAPER'S PROOF.  The published paper prints NO argument for 7.2: the whole text
    after the statement (perfect.pdf printed p. 37, `paper/proofs/7_2.md`) is

        "The proof is clear."

    So there is no printed reasoning to reproduce, and per PROVING_BRIEF any correct
    proof is acceptable.  The argument below is the obvious one, and is the one the
    authors clearly have in mind: two of the three rungs of a prism, together with the
    two triangle edges joining their ends, form an induced cycle (there are no other
    edges between the two rungs, by the definition of a prism), of length
    `|R_i| + |R_j| = length(R_i) + length(R_j) + 2 ≥ 4`.  In a Berge graph that hole
    has even length, so `length(R_i) + length(R_j)` is even, i.e. the two rungs have the
    same parity.  Applying this to the pairs `(R₁,R₂)` and `(R₁,R₃)` gives the claim.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

set_option autoImplicit false

-- The frozen statement's `variable` line carries `[Fintype V] [DecidableEq V]`, which this
-- proof does not use.  The linter's suggested `omit ... in` would change the elaborated
-- signature (and be rejected by `rollback_check`), so the linter is switched off instead.
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S07

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

/-! ### Generic gluing infrastructure

`glue_hole` is a general fact about the list encoding of paths and holes: if `P` and
`R` are vertex-disjoint paths and the only edges of `G` between `V(P)` and `V(R)` are
the two joining the last vertex of `P` to the first of `R` and the first of `P` to the
last of `R`, then the concatenation `P ++ R` is a hole (as soon as it has at least four
vertices).  It has no counterpart in the paper; it is bookkeeping for the encoding, and
belongs in `Workspace/ProofLemmas/` once lifted. -/

section Glue

variable {V : Type*}

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

private theorem glue_hole {G : SimpleGraph V} {P R : List V} {u₀ u₁ w₀ w₁ : V}
    (hP : IsPathFrom G P u₀ u₁) (hR : IsPathFrom G R w₀ w₁)
    (hdisj : ∀ x ∈ P, x ∉ R)
    (hcross : ∀ x ∈ P, ∀ y ∈ R, (G.Adj x y ↔ (x = u₁ ∧ y = w₀) ∨ (x = u₀ ∧ y = w₁)))
    (hlen : 4 ≤ P.length + R.length) :
    IsHoleList G (P ++ R) := by
  obtain ⟨hPl, hPh, hPt⟩ := hP
  obtain ⟨hRl, hRh, hRt⟩ := hR
  have hm : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hPl
  have hn : 0 < R.length := Workspace.ProofLemmas.PathBasics.path_length_pos hRl
  have hP0 : P[0]'hm = u₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPh hm
  have hPm : P[P.length - 1]'(by omega) = u₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPt hm
  have hR0 : R[0]'hn = w₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hRh hn
  have hRn : R[R.length - 1]'(by omega) = w₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hRt hn
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
          Workspace.ProofLemmas.PathBasics.path_adj_iff hPl hiP hjP]
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
          Workspace.ProofLemmas.PathBasics.path_adj_iff hRl hiR hjR]
        simp only [List.length_append]
        rw [succ_mod_eq hiL, succ_mod_eq hjL]
        split_ifs <;> omega

end Glue

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **7.2** (printed p. 35)

PAPER: *"Let `R₁, R₂, R₃` form a prism in a Berge graph `G`; then `R₁, R₂, R₃` all have the
same parity."*

(The paper's entire proof reads: *"The proof is clear."*)

*"Form a prism"* is `Prisms.FormPrism G a b R₁ R₂ R₃`, with triangles `{a 0, a 1, a 2}` and
`{b 0, b 1, b 2}`; *"the same parity"* refers to the parities of the three lengths. -/
theorem thm_7_2 (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (R₁ R₂ R₃ : List V)
    (hprism : FormPrism G a b R₁ R₂ R₃) :
    (Even (pathLength R₁) ↔ Even (pathLength R₂)) ∧
      (Even (pathLength R₁) ↔ Even (pathLength R₃)) := by
  obtain ⟨htA, htB, hab, hR1, hR2, hR3, h12, h13, _h23⟩ := hprism
  -- Two ends of a path with distinct ends give at least two vertices.
  have len2 : ∀ (P : List V) (x y : V), IsPathFrom G P x y → x ≠ y → 2 ≤ P.length := by
    intro P x y hP hxy
    have h0 : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
    by_contra hcon
    have hone : P.length = 1 := by omega
    obtain ⟨c, rfl⟩ := List.length_eq_one_iff.mp hone
    have h1 : c = x := by simpa using hP.2.1
    have h2 : c = y := by simpa using hP.2.2
    exact hxy (h1.symm.trans h2)
  -- If `w` has a neighbour in `Q` but is neither end of `P`, then `w ∉ P`.
  have notmem : ∀ (P Q : List V) (x0 y0 x1 y1 w z : V),
      (∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = x0 ∧ v = x1) ∨ (u = y0 ∧ v = y1))) →
      z ∈ Q → G.Adj w z → w ≠ x0 → w ≠ y0 → w ∉ P := by
    intro P Q x0 y0 x1 y1 w z hedge hz hadj h1 h2 hw
    rcases (hedge w hw z hz).mp hadj with h | h
    · exact h1 h.1
    · exact h2 h.1
  -- Two rungs of the prism are vertex-disjoint.
  have disjOf : ∀ (P Q : List V) (x0 y0 x1 y1 : V),
      IsPathList G P → 2 ≤ P.length →
      (∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = x0 ∧ v = x1) ∨ (u = y0 ∧ v = y1))) →
      x1 ∉ P → y1 ∉ P → (∀ u ∈ P, u ∉ Q) := by
    intro P Q x0 y0 x1 y1 hPl hlP hedge hx1 hy1 u hu huQ
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hu
    rcases k with _ | k'
    · have h1 : 0 + 1 < P.length := by omega
      have hadj : G.Adj (P[0 + 1]'h1) (P[0]'hk) :=
        (Workspace.ProofLemmas.PathBasics.path_adj_succ hPl h1).symm
      rcases (hedge _ (List.getElem_mem h1) _ huQ).mp hadj with hh | hh
      · exact hx1 (by rw [← hh.2]; exact List.getElem_mem _)
      · exact hy1 (by rw [← hh.2]; exact List.getElem_mem _)
    · have hadj : G.Adj (P[k']'(by omega)) (P[k' + 1]'hk) :=
        Workspace.ProofLemmas.PathBasics.path_adj_succ hPl hk
      rcases (hedge _ (List.getElem_mem (by omega : k' < P.length)) _ huQ).mp hadj with hh | hh
      · exact hx1 (by rw [← hh.2]; exact List.getElem_mem _)
      · exact hy1 (by rw [← hh.2]; exact List.getElem_mem _)
  -- The heart: two disjoint rungs close up into a hole, whose length is even.
  have pair : ∀ (P Q : List V) (x0 y0 x1 y1 : V),
      IsPathFrom G P x0 y0 → IsPathFrom G Q x1 y1 →
      2 ≤ P.length → 2 ≤ Q.length →
      (∀ u ∈ P, u ∉ Q) →
      (∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = x0 ∧ v = x1) ∨ (u = y0 ∧ v = y1))) →
      (Even (pathLength P) ↔ Even (pathLength Q)) := by
    intro P Q x0 y0 x1 y1 hP hQ hlP hlQ hdisj hedge
    have hQr : IsPathFrom G Q.reverse y1 x1 :=
      Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hQ
    have hhole : IsHoleList G (P ++ Q.reverse) := by
      refine glue_hole hP hQr ?_ ?_ ?_
      · intro u hu hu'
        exact hdisj u hu (List.mem_reverse.mp hu')
      · intro u hu y hy
        rw [hedge u hu y (List.mem_reverse.mp hy)]
        constructor
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl h
        · rintro (h | h)
          · exact Or.inr h
          · exact Or.inl h
      · simp only [List.length_reverse]; omega
    have hev : Even ((P ++ Q.reverse).length) := hG.1 _ hhole
    simp only [List.length_append, List.length_reverse] at hev
    rw [Nat.even_iff] at hev
    simp only [Workspace.ProofLemmas.PathBasics.pathLength_eq, Nat.even_iff]
    omega
  -- Concrete data about the prism.
  have ha0 : a 0 ∈ R₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR1).1
  have hb0 : b 0 ∈ R₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR1).2
  have ha1 : a 1 ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR2).1
  have hb1 : b 1 ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR2).2
  have ha2 : a 2 ∈ R₃ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR3).1
  have hb2 : b 2 ∈ R₃ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR3).2
  have hl1 : 2 ≤ R₁.length := len2 R₁ _ _ hR1 (hab 0 0)
  have hl2 : 2 ≤ R₂.length := len2 R₂ _ _ hR2 (hab 1 1)
  have hl3 : 2 ≤ R₃.length := len2 R₃ _ _ hR3 (hab 2 2)
  have ha01 : a 0 ≠ a 1 := (htA 0 1 (by decide)).ne
  have ha02 : a 0 ≠ a 2 := (htA 0 2 (by decide)).ne
  have hb01 : b 0 ≠ b 1 := (htB 0 1 (by decide)).ne
  have hb02 : b 0 ≠ b 2 := (htB 0 2 (by decide)).ne
  constructor
  · -- the pair `R₁, R₂`, using `R₃` to see that `a 1, b 1 ∉ V(R₁)`
    have hna1 : a 1 ∉ R₁ :=
      notmem R₁ R₃ (a 0) (b 0) (a 2) (b 2) (a 1) (a 2) h13 ha2
        (htA 1 2 (by decide)) (Ne.symm ha01) (hab 1 0)
    have hnb1 : b 1 ∉ R₁ :=
      notmem R₁ R₃ (a 0) (b 0) (a 2) (b 2) (b 1) (b 2) h13 hb2
        (htB 1 2 (by decide)) (Ne.symm (hab 0 1)) (Ne.symm hb01)
    exact pair R₁ R₂ (a 0) (b 0) (a 1) (b 1) hR1 hR2 hl1 hl2
      (disjOf R₁ R₂ (a 0) (b 0) (a 1) (b 1) hR1.1 hl1 h12 hna1 hnb1) h12
  · -- the pair `R₁, R₃`, using `R₂` to see that `a 2, b 2 ∉ V(R₁)`
    have hna2 : a 2 ∉ R₁ :=
      notmem R₁ R₂ (a 0) (b 0) (a 1) (b 1) (a 2) (a 1) h12 ha1
        (htA 2 1 (by decide)) (Ne.symm ha02) (hab 2 0)
    have hnb2 : b 2 ∉ R₁ :=
      notmem R₁ R₂ (a 0) (b 0) (a 1) (b 1) (b 2) (b 1) h12 hb1
        (htB 2 1 (by decide)) (Ne.symm (hab 0 2)) (Ne.symm hb02)
    exact pair R₁ R₃ (a 0) (b 0) (a 2) (b 2) hR1 hR3 hl1 hl3
      (disjOf R₁ R₃ (a 0) (b 0) (a 2) (b 2) hR1.1 hl1 h13 hna2 hnb2) h13


end SPGT

end Workspace.Statements.S07
