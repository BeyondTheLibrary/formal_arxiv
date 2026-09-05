/-  Proof attempt 3 for statement 13.6 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 86).

    The paper's proof, verbatim:

      "Let `P` be `p₁-⋯-pₙ`.  By 2.1, we may assume that `P` has length ≥ 5 and `X`
       contains a leap `u, v` say; so `u-p₂-⋯-pₙ₋₁-v` is a path.  But then the three
       paths `p₁-v`, `u-pₙ`, `p₂-⋯-pₙ₋₁` form a long prism, contrary to `G ∈ F₅`.
       This proves 13.6."

    Reproduced step for step:

    * 2.1 (`thm_2_1`, the Roussel–Rubio lemma, admitted as an axiom) is applied to
      `G`, `X`, `P`.  Its **first** alternative is literally conclusion 1 of 13.6 and
      its **third** alternative is literally conclusion 2 of 13.6, so both are handed
      straight back.  Its **second** alternative — "`P` has length ≥ 5 and `X`
      contains a leap `a, b` for `P`" — is the case the paper says "we may assume",
      and it is refuted below.

    * In that case, writing `n = p.length` (so `n ≥ 6`), the leap gives the six edges
      `a p₁`, `a p₂`, `a pₙ`, `b p₁`, `b pₙ₋₁`, `b pₙ` and no others between `{a,b}`
      and `V(P)`, together with `a ≁ b`.  The paper's `u` is `a` and its `v` is `b`.
      The three paths `p₁-b = [p₁, b]`, `a-pₙ = [a, pₙ]` and `p₂-⋯-pₙ₋₁` (the slice
      `(p.drop 1).take (n-2)`) then form a prism with triangles
      `{p₁, a, p₂}` and `{b, pₙ, pₙ₋₁}`, and it is long because the third path has
      length `n - 3 ≥ 3 > 1`.  That contradicts the second clause of `G ∈ F₅`.
-/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_1
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
-- `[Fintype V]` and `[DecidableEq V]` come from the frozen statement module's `variable`
-- line and are not used by the statement or the proof; the linter would flag them.
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S13

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Assembling a long prism from its presenting data: six vertices forming the two
triangles `{a0, a1, a2}`, `{b0, b1, b2}`, the three paths `P₁, P₂, P₃` with
`Pᵢ` running from `aᵢ` to `bᵢ`, the nine disjointness conditions between the two
triangles, the three "only edges between `V(Pᵢ)` and `V(Pⱼ)`" conditions, and the
witness that one of the three paths has length `> 1`.

This is pure bookkeeping for `Workspace.Types.Prisms.SPGT.IsLongPrism`; it exists
only so that the `Fin 3`-indexed packaging does not clutter the proof of 13.6. -/
private theorem formPrism_mk {W : Type*} {G : SimpleGraph W}
    {a0 a1 a2 b0 b1 b2 : W} {P₁ P₂ P₃ : List W}
    (ha01 : G.Adj a0 a1) (ha02 : G.Adj a0 a2) (ha12 : G.Adj a1 a2)
    (hb01 : G.Adj b0 b1) (hb02 : G.Adj b0 b2) (hb12 : G.Adj b1 b2)
    (h00 : a0 ≠ b0) (h01 : a0 ≠ b1) (h02 : a0 ≠ b2)
    (h10 : a1 ≠ b0) (h11 : a1 ≠ b1) (h12 : a1 ≠ b2)
    (h20 : a2 ≠ b0) (h21 : a2 ≠ b1) (h22 : a2 ≠ b2)
    (hq1 : IsPathFrom G P₁ a0 b0) (hq2 : IsPathFrom G P₂ a1 b1)
    (hq3 : IsPathFrom G P₃ a2 b2)
    (e12 : ∀ u ∈ P₁, ∀ v ∈ P₂, (G.Adj u v ↔ (u = a0 ∧ v = a1) ∨ (u = b0 ∧ v = b1)))
    (e13 : ∀ u ∈ P₁, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a0 ∧ v = a2) ∨ (u = b0 ∧ v = b2)))
    (e23 : ∀ u ∈ P₂, ∀ v ∈ P₃, (G.Adj u v ↔ (u = a1 ∧ v = a2) ∨ (u = b1 ∧ v = b2)))
    (hlong : 1 < pathLength P₁ ∨ 1 < pathLength P₂ ∨ 1 < pathLength P₃) :
    ∃ (α β : Fin 3 → W) (Q₁ Q₂ Q₃ : List W), IsLongPrism G α β Q₁ Q₂ Q₃ := by
  refine ⟨![a0, a1, a2], ![b0, b1, b2], P₁, P₂, P₃,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hlong⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact ha01 | exact ha02 | exact ha12
        | exact ha01.symm | exact ha02.symm | exact ha12.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hb01 | exact hb02 | exact hb12
        | exact hb01.symm | exact hb02.symm | exact hb12.symm
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      assumption
  · simpa using hq1
  · simpa using hq2
  · simpa using hq3
  · simpa using e12
  · simpa using e13
  · simpa using e23


/-- **13.6** (printed p. 86), introduced by *"It turns out that for such graphs, there is a
useful strengthening of 2.1 — the second alternative of that theorem can no longer hold."*

PAPER: *"Let `G ∈ F₅`, and let `P` be a path in `G` with odd length.  Let
`X ⊆ V(G) \ V(P)` be anticonnected, such that both ends of `P` are `X`-complete.  Then
either:*

*1. some edge of `P` is `X`-complete, or*

*2. `P` has length 3 and there is an odd antipath joining the internal vertices of `P` with
interior in `X`."*

Notes on the transcription.

* This is the **published** hypothesis `X ⊆ V(G) \ V(P)`; the arXiv draft has the weaker
  `X ⊆ V(G)`.  Since `V(G)` is the whole vertex type, `X ⊆ V(G) \ V(P)` is
  `X ⊆ {v | v ∈ P}ᶜ`.
* *"some edge of `P` is `X`-complete"* is the existence of two vertices `u, v` of `P` with
  `uv` an `X`-complete edge (`EdgeComplete`, which contains `G.Adj u v`); since `P` is
  induced, its edges are exactly the adjacent pairs of its vertices.
* `P` having length 3 means it has exactly four vertices, so its interior is a two-element
  list `[c, d]`, and *"an odd antipath joining the internal vertices of `P` with interior in
  `X`"* is an antipath from `c` to `d` of odd length all of whose internal vertices lie in
  `X`.  (The two alternatives are the first and third alternatives of 2.1; the second — the
  existence of a leap in `X` — is what this strengthening removes.) -/
theorem thm_13_6 (G : SimpleGraph V) (hG : InF5 G)
    (p : List V) (p₁ pn : V) (hp : IsPathFrom G p p₁ pn) (hodd : Odd (pathLength p))
    (X : Set V) (hXP : X ⊆ {v : V | v ∈ p}ᶜ) (hX : AnticonnectedSet G X)
    (hp₁ : VertexComplete G p₁ X) (hpn : VertexComplete G pn X) :
    (∃ u ∈ p, ∃ v ∈ p, EdgeComplete G X u v) ∨
    (pathLength p = 3 ∧ ∃ c d : V, SPGT.interior p = [c, d] ∧
      ∃ q : List V, IsAntipathFrom G q c d ∧ Odd (pathLength q) ∧
        ∀ u ∈ SPGT.interior q, u ∈ X) := by
  -- `G ∈ F₅` is in particular Berge, and `X` is disjoint from `V(P)`.
  have hBerge : Berge G := hG.1.1
  have hpX : ∀ w ∈ p, w ∉ X := by
    intro w hw hwX
    exact (hXP hwX) hw
  -- "By 2.1, we may assume that `P` has length ≥ 5 and `X` contains a leap `u, v` say".
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_1 G hBerge X hX p p₁ pn hp hpX hodd
      hp₁ hpn with h1 | h2 | h3
  · -- 2.1's first alternative *is* conclusion 1 of 13.6.
    exact Or.inl h1
  · -- 2.1's second alternative: this is the case the paper refutes.
    exfalso
    obtain ⟨h5, a, haX, b, hbX, hleap⟩ := h2
    obtain ⟨hpl, -, hab, hnab, hA, hB⟩ := hleap
    -- `P` has length ≥ 5, i.e. `n ≥ 6` vertices.
    have hlen : 6 ≤ p.length := by
      have := Workspace.ProofLemmas.PathBasics.pathLength_eq p
      omega
    have h0lt : 0 < p.length := by omega
    have h1lt : 1 < p.length := by omega
    have hmlt : p.length - 2 < p.length := by omega
    have hnlt : p.length - 1 < p.length := by omega
    -- `a, b ∈ X` and `X ∩ V(P) = ∅`.
    have hap : a ∉ p := by intro h; exact (hXP haX) h
    have hbp : b ∉ p := by intro h; exact (hXP hbX) h
    have hp0 : p[0]'h0lt = p₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 h0lt
    have hpe : p[p.length - 1]'hnlt = pn :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 h0lt
    -- adjacency and distinctness along `P`
    have hadj : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
        (G.Adj (p[i]'hi) (p[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) :=
      fun i j hi hj => Workspace.ProofLemmas.PathBasics.path_adj_iff hpl hi hj
    have hinj : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length),
        ((p[i]'hi) = (p[j]'hj) ↔ i = j) := by
      intro i j hi hj
      refine ⟨fun h => ?_, ?_⟩
      · by_contra hne
        exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hpl hi hj hne h
      · rintro rfl; rfl
    have hp₁mem : p₁ ∈ p := Workspace.ProofLemmas.PathBasics.head_mem hp.2.1
    have hpnmem : pn ∈ p := Workspace.ProofLemmas.PathBasics.getLast_mem hp.2.2
    have hne_p₁_b : p₁ ≠ b := fun h => hbp (h ▸ hp₁mem)
    have hne_pn_a : pn ≠ a := fun h => hap (h ▸ hpnmem)
    have hne_x1_b : (p[1]'h1lt) ≠ b := fun h => hbp (h ▸ List.getElem_mem h1lt)
    have hne_xm_a : (p[p.length - 2]'hmlt) ≠ a := fun h => hap (h ▸ List.getElem_mem hmlt)
    have hne_p₁_pn : p₁ ≠ pn := by
      rw [← hp0, ← hpe, ne_eq, hinj 0 (p.length - 1) h0lt hnlt]; omega
    have hne_p₁_xm : p₁ ≠ (p[p.length - 2]'hmlt) := by
      rw [← hp0, ne_eq, hinj 0 (p.length - 2) h0lt hmlt]; omega
    have hne_x1_pn : (p[1]'h1lt) ≠ pn := by
      rw [← hpe, ne_eq, hinj 1 (p.length - 1) h1lt hnlt]; omega
    have hne_x1_xm : (p[1]'h1lt) ≠ (p[p.length - 2]'hmlt) := by
      rw [ne_eq, hinj 1 (p.length - 2) h1lt hmlt]; omega
    -- the six edges of the leap: `a p₁`, `a p₂`, `a pₙ`, `b p₁`, `b pₙ₋₁`, `b pₙ`
    have hA0 : G.Adj a p₁ := hp0 ▸ (hA 0 h0lt).mpr (Or.inl rfl)
    have hA1 : G.Adj a (p[1]'h1lt) := (hA 1 h1lt).mpr (Or.inr (Or.inl rfl))
    have hAn : G.Adj a pn := hpe ▸ (hA (p.length - 1) hnlt).mpr (Or.inr (Or.inr rfl))
    have hB0 : G.Adj b p₁ := hp0 ▸ (hB 0 h0lt).mpr (Or.inl rfl)
    have hBm : G.Adj b (p[p.length - 2]'hmlt) := (hB (p.length - 2) hmlt).mpr (Or.inr (Or.inl rfl))
    have hBn : G.Adj b pn := hpe ▸ (hB (p.length - 1) hnlt).mpr (Or.inr (Or.inr rfl))
    -- the first and last edge of `P`, and non-adjacency of its two ends
    have hE01 : G.Adj p₁ (p[1]'h1lt) := hp0 ▸ (hadj 0 1 h0lt h1lt).mpr (Or.inl rfl)
    have hEmn : G.Adj (p[p.length - 2]'hmlt) pn :=
      hpe ▸ (hadj (p.length - 2) (p.length - 1) hmlt hnlt).mpr (Or.inl (by omega))
    have hEends : ¬ G.Adj p₁ pn := by
      rw [← hp0, ← hpe, hadj 0 (p.length - 1) h0lt hnlt]; omega
    -- the third path of the prism: `p₂-⋯-pₙ₋₁`
    have hslice : IsPathList G (List.take (p.length - 2) (List.drop 1 p)) := by
      have h := Workspace.ProofLemmas.PathBasics.isPathList_slice hpl
        (i := 1) (j := p.length - 2) (by omega) hmlt
      have he : p.length - 2 - 1 + 1 = p.length - 2 := by omega
      rwa [he] at h
    have hQlen : (List.take (p.length - 2) (List.drop 1 p)).length = p.length - 2 := by
      simp only [List.length_take, List.length_drop]
      omega
    have hQget : ∀ (k i : ℕ) (hk : k < (List.take (p.length - 2) (List.drop 1 p)).length)
        (hi : i < p.length), i = 1 + k →
        (List.take (p.length - 2) (List.drop 1 p))[k]'hk = p[i]'hi := by
      rintro k i hk hi rfl
      simp only [List.getElem_take, List.getElem_drop]
    have hQ0lt : 0 < (List.take (p.length - 2) (List.drop 1 p)).length := by omega
    have hQLlt : (List.take (p.length - 2) (List.drop 1 p)).length - 1 <
        (List.take (p.length - 2) (List.drop 1 p)).length := by omega
    have hQhead : (List.take (p.length - 2) (List.drop 1 p)).head? = some (p[1]'h1lt) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hQ0lt,
        hQget 0 1 hQ0lt h1lt (by omega)]
    have hQlast : (List.take (p.length - 2) (List.drop 1 p)).getLast? =
        some (p[p.length - 2]'hmlt) := by
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hQLlt,
        hQget _ (p.length - 2) hQLlt hmlt (by omega)]
    have hQmem : ∀ w ∈ List.take (p.length - 2) (List.drop 1 p),
        ∃ (i : ℕ) (hi : i < p.length), 1 ≤ i ∧ i ≤ p.length - 2 ∧ w = p[i]'hi := by
      intro w hw
      obtain ⟨k, hk, hkw⟩ := List.mem_iff_getElem.mp hw
      refine ⟨1 + k, by omega, by omega, by omega, ?_⟩
      rw [← hkw]
      exact hQget k (1 + k) hk (by omega) rfl
    -- "the three paths `p₁-v`, `u-pₙ`, `p₂-⋯-pₙ₋₁` form a long prism"
    have e12 : ∀ u ∈ [p₁, b], ∀ v ∈ [a, pn],
        (G.Adj u v ↔ (u = p₁ ∧ v = a) ∨ (u = b ∧ v = pn)) := by
      intro u hu v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact iff_of_true hA0.symm (Or.inl ⟨rfl, rfl⟩)
      · refine iff_of_false hEends ?_
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact hne_pn_a h
        · exact hne_p₁_b h
      · refine iff_of_false (fun h => hnab h.symm) ?_
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hne_p₁_b h.symm
        · exact hne_pn_a h.symm
      · exact iff_of_true hBn (Or.inr ⟨rfl, rfl⟩)
    -- these four are stated *before* the case splits below: `rcases … with rfl` on a
    -- hypothesis `u = b` substitutes `b := u`, so `b` (resp. `a`, `p₁`, `pn`) is no
    -- longer a usable identifier inside the branch.
    have hb0 : ¬ ((p[0]'h0lt) = b) := by rw [hp0]; exact hne_p₁_b
    have hna : ¬ ((p[p.length - 1]'hnlt) = a) := by rw [hpe]; exact hne_pn_a
    have hbp₁ : ¬ (b = p₁) := fun h => hne_p₁_b h.symm
    have hapn : ¬ (a = pn) := fun h => hne_pn_a h.symm
    have e13 : ∀ u ∈ [p₁, b], ∀ v ∈ List.take (p.length - 2) (List.drop 1 p),
        (G.Adj u v ↔ (u = p₁ ∧ v = p[1]'h1lt) ∨ (u = b ∧ v = p[p.length - 2]'hmlt)) := by
      intro u hu v hv
      obtain ⟨i, hi, hi1, hi2, rfl⟩ := hQmem v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · rw [← hp0, hadj 0 i h0lt hi, hinj i 1 hi h1lt, hinj i (p.length - 2) hi hmlt]
        simp only [eq_self_iff_true, true_and, hb0, false_and, or_false]
        omega
      · rw [hB i hi, hinj i 1 hi h1lt, hinj i (p.length - 2) hi hmlt]
        simp only [hbp₁, false_and, false_or, eq_self_iff_true, true_and]
        omega
    have e23 : ∀ u ∈ [a, pn], ∀ v ∈ List.take (p.length - 2) (List.drop 1 p),
        (G.Adj u v ↔ (u = a ∧ v = p[1]'h1lt) ∨ (u = pn ∧ v = p[p.length - 2]'hmlt)) := by
      intro u hu v hv
      obtain ⟨i, hi, hi1, hi2, rfl⟩ := hQmem v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · rw [hA i hi, hinj i 1 hi h1lt, hinj i (p.length - 2) hi hmlt]
        simp only [eq_self_iff_true, true_and, hapn, false_and, or_false]
        omega
      · rw [← hpe, hadj (p.length - 1) i hnlt hi, hinj i 1 hi h1lt,
          hinj i (p.length - 2) hi hmlt]
        simp only [hna, false_and, false_or, eq_self_iff_true, true_and]
        omega
    have hlongQ : 1 < pathLength (List.take (p.length - 2) (List.drop 1 p)) := by
      have := Workspace.ProofLemmas.PathBasics.pathLength_eq
        (List.take (p.length - 2) (List.drop 1 p))
      omega
    -- "contrary to `G ∈ F₅`"
    exact hG.2.1 (formPrism_mk hA0.symm hE01 hA1 hBn hBm hEmn.symm
      hne_p₁_b hne_p₁_pn hne_p₁_xm hab hne_pn_a.symm hne_xm_a.symm
      hne_x1_b hne_x1_pn hne_x1_xm
      ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hB0.symm, by simp, by simp⟩
      ⟨Workspace.ProofLemmas.PathBasics.isPathList_pair hAn, by simp, by simp⟩
      ⟨hslice, hQhead, hQlast⟩ e12 e13 e23 (Or.inr (Or.inr hlongQ)))
  · -- 2.1's third alternative *is* conclusion 2 of 13.6.
    exact Or.inr h3


end SPGT

end Workspace.Statements.S13
