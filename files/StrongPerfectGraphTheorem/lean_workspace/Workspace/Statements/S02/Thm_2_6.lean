/-  Proof attempt 2 for statement 2.6 (`Workspace.Statements.S02.SPGT.thm_2_6`).

    THE PAPER'S PROOF.  The published paper prints NO argument for 2.6: the whole text
    after the statement (perfect.pdf printed p. 11, `paper/proofs/2_6.md`) is

        "The proof is clear."

    So there is no printed reasoning to reproduce, and per PROVING_BRIEF any correct
    proof is acceptable.  The argument below is the obvious one.  `(A,B)` balanced has
    two clauses, and each is closed by `v` itself:

    * an odd path `P` between nonadjacent `u,v' ∈ B` with interior in `A` — the vertex
      `v` is adjacent to both ends of `P` (it is `B`-complete) and to no internal vertex
      of `P` (it is `A`-anticomplete), and `v ∉ V(P)` (as `v ∉ A ∪ B`), so
      `V(P) ∪ {v}` induces a cycle of length `length(P) + 2`, which is odd and at least
      `4`: an odd hole of `G`, contradicting `G` Berge;
    * an odd antipath `P` between adjacent `u,v' ∈ A` with interior in `B` — the same
      argument run in `Ḡ`, where `v` is `A`-complete and `B`-anticomplete and `u,v'` are
      nonadjacent, produces an odd hole of `Ḡ`, again contradicting `G` Berge.

    Both are the same lemma (`key` below), applied to `G` and to `Gᶜ`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics

-- The frozen statement's `variable` line carries `[Fintype V] [DecidableEq V]`, and its
-- disjointness hypothesis `hAB` is not needed by this proof.  The linters' suggested fixes
-- would change the elaborated signature (and be rejected by `rollback_check`), so the two
-- linters are switched off instead.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Workspace.Statements.S02

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace SPGT

/-! ### Generic gluing infrastructure

`glue_hole` is a general fact about the list encoding of paths and holes: if `P` and
`R` are vertex-disjoint paths and the only edges of `G` between `V(P)` and `V(R)` are
the two joining the last vertex of `P` to the first of `R` and the first of `P` to the
last of `R`, then the concatenation `P ++ R` is a hole (as soon as it has at least four
vertices).  Here `R` is the one-vertex path `[v]`.  It has no counterpart in the paper;
it is bookkeeping for the encoding, and belongs in `Workspace/ProofLemmas/` once
lifted. -/

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

/-- The single argument behind both clauses of `Balanced`: a vertex `w` outside
`A' ∪ B'`, complete to `B'` and anticomplete to `A'`, turns an odd path between
nonadjacent vertices of `B'` with interior in `A'` into an odd hole. -/
private theorem no_odd_path {H : SimpleGraph V}
    (hHberge : ∀ c : List V, IsHoleList H c → Even (holeLength c))
    (A' B' : Set V) (w : V) (hw : w ∉ A' ∪ B')
    (hwB : VertexComplete H w B') (hwA : VertexAnticomplete H w A')
    (u v : V) (p : List V) (hu : u ∈ B') (hv : v ∈ B') (hnadj : ¬ H.Adj u v)
    (hp : IsPathFrom H p u v) (hint : ∀ x ∈ Workspace.Types.Core.SPGT.interior p, x ∈ A') :
    ¬ Odd (pathLength p) := by
  intro hodd
  obtain ⟨k, hk⟩ := hodd
  -- the path has length at least 2, hence at least 3 vertices
  have hne1 : pathLength p ≠ 1 := by
    intro h
    exact hnadj (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_adj_of_length_one hp h)
  have hplen : 3 ≤ p.length := by
    have h := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hp.1
    omega
  -- `w` is not a vertex of the path
  have hwp : w ∉ p := by
    intro hmem
    by_cases h1 : w = u
    · apply hw; rw [Set.mem_union]; right; rw [h1]; exact hu
    by_cases h2 : w = v
    · apply hw; rw [Set.mem_union]; right; rw [h2]; exact hv
    · have hint' : w ∈ Workspace.Types.Core.SPGT.interior p :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hmem, h1, h2⟩
      apply hw; rw [Set.mem_union]; left; exact hint w hint'
  -- `w` is adjacent to exactly the two ends of the path
  have hadjw : ∀ x ∈ p, (H.Adj x w ↔ (x = v ∨ x = u)) := by
    intro x hx
    constructor
    · intro hxw
      by_contra hcon
      push Not at hcon
      have hint' : x ∈ Workspace.Types.Core.SPGT.interior p :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mpr
          ⟨hx, hcon.2, hcon.1⟩
      exact hwA x (hint x hint') hxw.symm
    · rintro (rfl | rfl)
      · exact (hwB _ hv).symm
      · exact (hwB _ hu).symm
  -- close the path into a hole with `w`
  have hsing : IsPathFrom H [w] w w :=
    ⟨Workspace.ProofLemmas.PathBasics.isPathList_singleton H w, by simp, by simp⟩
  have hhole : IsHoleList H (p ++ [w]) := by
    refine glue_hole hp hsing ?_ ?_ ?_
    · intro x hx hx'
      rw [List.mem_singleton] at hx'
      subst hx'
      exact hwp hx
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [hadjw x hx]
      constructor
      · rintro (h | h)
        · exact Or.inl ⟨h, rfl⟩
        · exact Or.inr ⟨h, rfl⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact Or.inl h
        · exact Or.inr h
    · simp only [List.length_singleton]; omega
  have hev : Even ((p ++ [w]).length) := hHberge _ hhole
  simp only [List.length_append, List.length_singleton] at hev
  rw [Nat.even_iff] at hev
  rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hk
  omega

end Glue

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **2.6** (printed p. 10)

PAPER: *"If `G` is Berge and `A,B ⊆ V(G)` are disjoint, and `v ∈ V(G) \ (A ∪ B)`,
and `v` is complete to `B` and anticomplete to `A`, then `(A,B)` is balanced."* -/
theorem thm_2_6 (G : SimpleGraph V) (hG : Berge G) (A B : Set V)
    (hAB : Disjoint A B) (v : V) (hv : v ∉ A ∪ B)
    (hvB : VertexComplete G v B) (hvA : VertexAnticomplete G v A) :
    SPGT.Balanced G A B := by
  constructor
  · -- no odd path between nonadjacent vertices of `B` with interior in `A`
    intro u v' p hu hv' hnadj hp hint
    exact no_odd_path hG.1 A B v hv hvB hvA u v' p hu hv' hnadj hp hint
  · -- no odd antipath between adjacent vertices of `A` with interior in `B`;
    -- this is the same statement for `Ḡ`, in which `v` is `A`-complete and
    -- `B`-anticomplete and the two ends are nonadjacent
    intro u v' p hu hv' hadj hp hint
    have hvA' : VertexComplete Gᶜ v A := by
      intro x hx
      rw [SimpleGraph.compl_adj]
      refine ⟨?_, hvA x hx⟩
      rintro rfl
      exact hv (Or.inl hx)
    have hvB' : VertexAnticomplete Gᶜ v B := by
      intro x hx hcon
      rw [SimpleGraph.compl_adj] at hcon
      exact hcon.2 (hvB x hx)
    have hvunion : v ∉ B ∪ A := by
      rw [Set.union_comm]; exact hv
    have hnadj : ¬ Gᶜ.Adj u v' := by
      intro hcon
      rw [SimpleGraph.compl_adj] at hcon
      exact hcon.2 hadj
    exact no_odd_path hG.2 B A v hvunion hvA' hvB' u v' p hu hv' hnadj
      (Workspace.ProofLemmas.PathBasics.isAntipathFrom_iff.mp hp) hint


end SPGT

end Workspace.Statements.S02
