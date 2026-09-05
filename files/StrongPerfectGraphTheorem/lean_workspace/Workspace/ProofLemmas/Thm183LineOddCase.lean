import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Statements.S13.Thm_13_7
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.AntiholeCompletion

/-!
# 18.3, "Case B": a line one of whose ends is not `Y`-complete is odd

This module is one sentence-block of the printed proof of **18.3**
(`paper/proofs/18_3.md`, published page 110).  A *line* is a maximal subpath `P'` of `P` no
internal vertex of which is `Y`-complete.  The printed text reproduced here is:

> *"We may therefore assume that an end of `P'` is not `Y`-complete, and from the maximality of
> `P'`, any such end is either `p₁` or `pₙ`, and we may assume it is `pₙ` from the symmetry.
> The other end of `P'` is therefore not `p₁` since at least two vertices of `P` are
> `Y`-complete, and so it is `pᵢ`, where `i` is maximum with `2 ≤ i ≤ n` such that `pᵢ` is
> `Y`-complete.  Since `i > 1`, no vertex of `P'` is `X`-complete except `pₙ`.  Suppose that
> `P'` is even; then we may apply 13.7.  We deduce that `P'` has length 2, and so `i = n − 2`.
> Now the antipath joining `pₙ₋₂, pₙ₋₁` with interior in `X` is even since it can be completed
> to an antihole via `pₙ₋₁-p₁-pₙ₋₂`; and the antipath joining `pₙ₋₁, pₙ` with interior in `Y`
> is even since it can be completed to an antihole via `pₙ-p_h-pₙ₋₁`, where `p_h` is some
> `Y`-complete vertex with `1 ≤ h < i`.  But this contradicts 13.7.  Consequently `P'` is odd,
> as required."*

## Indexing

The paper's `p₁,…,pₙ` is 1-indexed; the Lean list `p` is 0-indexed, so the paper's `pₖ` is
`p[k-1]`.  The natural number `a` below is the **0-indexed** position of the paper's `pᵢ`
(so `a = i-1`); the line runs from index `a` to index `p.length - 1`, and its length is
`p.length - 1 - a`.

The paper's side conditions become hypotheses supplied by the caller:

* *"`i` is maximum with `2 ≤ i ≤ n` such that `pᵢ` is `Y`-complete"* is `hca` (`p[a]` is
  `Y`-complete) together with `hint` (nothing strictly between `a` and the last index is)
  and `hcn` (`pₙ` is not);
* *"Since `i > 1`"* is `hapos`;
* *"at least two vertices of `P` are `Y`-complete"* is `hwit`: some `p[h]` with `h < a` is
  `Y`-complete.  (Combined with `hca` these are the two.)
* `ha2 : a + 2 ≤ p.length - 1` records that the line has length `≥ 2`; lines of length `1` are
  handled by the caller (they are odd outright).

The hypothesis `hpXY` — *"`P` is a path of `G \ (X ∪ Y)`"* — is carried for faithfulness to
18.3's statement but is not consumed: 13.7 is stated without it (see the transcription note in
`Workspace/Statements/S13/Thm_13_7.lean`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm183LineOddCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **18.3, "Case B"**: *"Consequently `P'` is odd, as required."*

`P'` is the line from `p[a]` (the paper's `pᵢ`, the last `Y`-complete vertex of `P`) to the
last vertex `pₙ` of `P`, which is not `Y`-complete.  Its length `p.length - 1 - a` is odd. -/
theorem line_odd_of_last_end_not_YComplete
    (G : SimpleGraph V) (hG5 : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)))
    (a : ℕ) (hapos : 0 < a) (ha2 : a + 2 ≤ p.length - 1)
    (hint : ∀ (k : ℕ) (hk : k < p.length), a < k → k < p.length - 1 →
       ¬ VertexComplete G (p[k]'hk) Y)
    (hca : VertexComplete G (p[a]'(by omega)) Y)
    (hcn : ¬ VertexComplete G pₙ Y)
    (hwit : ∃ (h : ℕ) (hh : h < p.length), h < a ∧ VertexComplete G (p[h]'hh) Y) :
    Odd (p.length - 1 - a) := by
  -- *"Suppose that `P'` is even"* — the whole argument is a proof by contradiction.
  rcases Nat.even_or_odd (p.length - 1 - a) with hev | hodd
  · exfalso
    have hBerge : Berge G := hG5.1.1
    have h0lt : 0 < p.length := by omega
    have hnlt : p.length - 1 < p.length := by omega
    have halt : a < p.length := by omega
    have haj : a < p.length - 1 := by omega
    have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
    have hpe : p[p.length - 1]'hnlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
    -- ### Step 1 — the line `P'`, and its reversal (13.7 wants the `X`-complete end first).
    have hSlen : ((p.drop a).take (p.length - 1 - a + 1)).length = p.length - 1 - a + 1 :=
      PathBasics.length_slice p (by omega) hnlt
    have hSpath : IsPathFrom G ((p.drop a).take (p.length - 1 - a + 1))
        (p[a]'halt) (p[p.length - 1]'hnlt) := PathBasics.isPathFrom_slice hp haj hnlt
    have hRpath : IsPathFrom G ((p.drop a).take (p.length - 1 - a + 1)).reverse
        pₙ (p[a]'halt) := by
      rw [← hpe]; exact PathBasics.isPathFrom_reverse hSpath
    have hplR : pathLength ((p.drop a).take (p.length - 1 - a + 1)).reverse
        = p.length - 1 - a := by
      rw [PathBasics.pathLength_reverse, PathBasics.pathLength_eq, hSlen]
      omega
    have hmemS : ∀ x : V, x ∈ (p.drop a).take (p.length - 1 - a + 1) ↔
        ∃ (k : ℕ) (hk : k < p.length), a ≤ k ∧ k ≤ p.length - 1 ∧ p[k]'hk = x :=
      fun x => PathBasics.mem_slice_iff p (by omega) hnlt
    -- *"Since `i > 1`, no vertex of `P'` is `X`-complete except `pₙ`."*  Indeed `p₁ = p[0]`
    -- does not lie on `P'`, because every index on `P'` is `≥ a ≥ 1`.
    have hXu : ∀ u ∈ ((p.drop a).take (p.length - 1 - a + 1)).reverse,
        (VertexComplete G u X ↔ u = pₙ) := by
      intro u hu
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hmemS u).mp (List.mem_reverse.mp hu)
      constructor
      · intro hcu
        rcases (hXuniq _ (List.getElem_mem hk)).mp hcu with h | h
        · exact absurd (h.trans hp0.symm)
            (PathBasics.path_ne_of_ne_index hp hk h0lt (by omega))
        · exact h
      · intro h
        rw [h]
        exact (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
    -- *"`i` is maximum … such that `pᵢ` is `Y`-complete"*: on `P'` the only `Y`-complete
    -- vertex is `pᵢ = p[a]` — the interior by `hint`, the far end by `hcn`.
    have hYu : ∀ u ∈ ((p.drop a).take (p.length - 1 - a + 1)).reverse,
        (VertexComplete G u Y ↔ u = p[a]'halt) := by
      intro u hu
      obtain ⟨k, hk, hk1, hk2, rfl⟩ := (hmemS u).mp (List.mem_reverse.mp hu)
      constructor
      · intro hcu
        rcases Nat.lt_or_ge a k with hlt | hge
        · rcases Nat.lt_or_ge k (p.length - 1) with hlt2 | hge2
          · exact absurd hcu (hint k hk hlt hlt2)
          · exfalso
            refine hcn ?_
            have hke : p[k]'hk = pₙ := by
              have hkn : k = p.length - 1 := by omega
              subst hkn
              exact hpe
            exact hke ▸ hcu
        · have hke : k = a := by omega
          subst hke
          rfl
      · intro h
        rw [h]; exact hca
    -- ### Step 2 — *"Suppose that `P'` is even; then we may apply 13.7."*
    obtain ⟨hlen2, c, hSeq, Q, R, ⟨hQ, hQint⟩, ⟨hR, hRint⟩, hxor⟩ :=
      _root_.Workspace.Statements.S13.SPGT.thm_13_7 G hG5 X Y hXY hXne hYne hXa hYa hcompl
        ((p.drop a).take (p.length - 1 - a + 1)).reverse pₙ (p[a]'halt) hRpath.1
        (by rw [hplR]; exact hev) (by rw [hplR]; omega)
        hRpath.2.1 hRpath.2.2 hXu hYu
    -- *"We deduce that `P'` has length 2, and so `i = n − 2`."*
    have hla : p.length - 1 - a = 2 := by rw [← hplR]; exact hlen2
    have hN : p.length = a + 3 := by omega
    have ha1lt : a + 1 < p.length := by omega
    have ha2lt : a + 2 < p.length := by omega
    have ha2' : 2 ≤ a := by omega
    have hSeq' : (p.drop a).take (p.length - 1 - a + 1) = [p[a]'halt, c, pₙ] := by
      have h := congrArg List.reverse hSeq
      simpa using h
    have hSlen3 : ((p.drop a).take (p.length - 1 - a + 1)).length = 3 := by
      rw [hSlen]; omega
    have h1lt : 1 < ((p.drop a).take (p.length - 1 - a + 1)).length := by omega
    have h2lt : 2 < ((p.drop a).take (p.length - 1 - a + 1)).length := by omega
    -- `P' = pₙ₋₂-pₙ₋₁-pₙ`: its middle vertex `c` is `pₙ₋₁ = p[a+1]`, its far end is `pₙ`.
    have hc : c = p[a + 1]'ha1lt := by
      have hq : ((p.drop a).take (p.length - 1 - a + 1))[1]? = some c := by
        rw [hSeq']; simp
      rw [List.getElem?_eq_getElem h1lt,
        PathBasics.getElem_slice' p h1lt ha1lt (by omega)] at hq
      exact (Option.some_injective _ hq).symm
    have hpn2 : p[a + 2]'ha2lt = pₙ := by
      have hq : ((p.drop a).take (p.length - 1 - a + 1))[2]? = some pₙ := by
        rw [hSeq']; simp
      rw [List.getElem?_eq_getElem h2lt,
        PathBasics.getElem_slice' p h2lt ha2lt (by omega)] at hq
      exact Option.some_injective _ hq
    -- The two antipaths join consecutive vertices of `P`.
    have hadjQ : G.Adj c (p[a]'halt) := by
      rw [hc]
      exact ((PathBasics.path_adj_iff hp halt ha1lt).mpr (Or.inl rfl)).symm
    have hadjR : G.Adj pₙ c := by
      rw [hc, ← hpn2]
      exact ((PathBasics.path_adj_iff hp ha1lt ha2lt).mpr (Or.inl (by omega))).symm
    -- ### Step 3 — both antipaths are even, contradicting 13.7's `Xor'`.
    -- *"the antipath joining `pₙ₋₂, pₙ₋₁` with interior in `X` is even since it can be
    --   completed to an antihole via `pₙ₋₁-p₁-pₙ₋₂`"*.  The witness is `p₁ = p[0]`, which is
    --   `X`-complete and, since `n ≥ 5`, at index distance `≥ 2` from both `p[a]` and `p[a+1]`.
    have hz1X : VertexComplete G (p[0]'h0lt) X :=
      (hXuniq _ (List.getElem_mem h0lt)).mpr (Or.inl hp0)
    have hQeven : Even (pathLength Q) := by
      refine AntiholeCompletion.even_pathLength_of_witness hBerge hadjQ hz1X ?_ ?_ ?_ ?_ hQ hQint
      · rw [hc]; exact PathBasics.path_not_adj_of_gap hp h0lt ha1lt (by omega) (by omega)
      · exact PathBasics.path_not_adj_of_gap hp h0lt halt (by omega) (by omega)
      · rw [hc]; exact PathBasics.path_ne_of_ne_index hp h0lt ha1lt (by omega)
      · exact PathBasics.path_ne_of_ne_index hp h0lt halt (by omega)
    -- *"and the antipath joining `pₙ₋₁, pₙ` with interior in `Y` is even since it can be
    --   completed to an antihole via `pₙ-p_h-pₙ₋₁`, where `p_h` is some `Y`-complete vertex
    --   with `1 ≤ h < i`"*.  Here `h < a = n-3`, so both index distances are `≥ 2`.
    obtain ⟨w, hwlt, hwa, hwY⟩ := hwit
    have hReven : Even (pathLength R) := by
      refine AntiholeCompletion.even_pathLength_of_witness hBerge hadjR hwY ?_ ?_ ?_ ?_ hR hRint
      · rw [← hpn2]; exact PathBasics.path_not_adj_of_gap hp hwlt ha2lt (by omega) (by omega)
      · rw [hc]; exact PathBasics.path_not_adj_of_gap hp hwlt ha1lt (by omega) (by omega)
      · rw [← hpn2]; exact PathBasics.path_ne_of_ne_index hp hwlt ha2lt (by omega)
      · rw [hc]; exact PathBasics.path_ne_of_ne_index hp hwlt ha1lt (by omega)
    -- *"But this contradicts 13.7."*  13.7 says exactly one of `Q`, `R` is odd.
    have hnotodd : ∀ n : ℕ, Even n → ¬ Odd n := by
      intro n he ho
      rw [Nat.even_iff] at he
      rw [Nat.odd_iff] at ho
      omega
    rcases hxor with ⟨hq, -⟩ | ⟨hr, -⟩
    · exact hnotodd _ hQeven hq
    · exact hnotodd _ hReven hr
  -- *"Consequently `P'` is odd, as required."*
  · exact hodd

end Workspace.ProofLemmas.Thm183LineOddCase
