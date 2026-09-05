import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.AntiholeCompletion

/-!
# 18.3, "Case A": a line of length `≥ 2` whose two ends are `Y`-complete is even

This module is one sentence-block of the printed proof of **18.3**
(`paper/proofs/18_3.md`, published page 110).  A *line* is a maximal subpath `P'` of `P` no
internal vertex of which is `Y`-complete.  The printed text reproduced here is:

> *"Let us say a line is a maximal subpath `P'` of `P` such that no internal vertex of `P'` is
> `Y`-complete.  Let `P'` be a line of length `≥ 2`, and assume first that both ends of `P'`
> are `Y`-complete.  Suppose `P'` has odd length, and let its ends be `pᵢ, pⱼ` where `i < j`.
> Then 13.6 implies that `j − i = 3`, and there is an odd antipath `Q` joining `pᵢ₊₁, pᵢ₊₂`
> with interior in `Y`.  Since `n ≥ 5`, either `n > j` or `1 < i`, and from the symmetry
> between `p₁` and `pₙ` we may assume the latter.  Since `pᵢ₊₁, pᵢ₊₂` are not `X`-complete,
> they are joined by an antipath `Q'` with interior in `X`.  Since `Q ∪ Q'` is an antihole it
> follows that `Q'` is odd.  But then `p₁-pᵢ₊₁-Q'-pᵢ₊₂-p₁` is an odd antihole, a
> contradiction.  So in this case `P'` has even length."*

## Indexing

The paper's `p₁,…,pₙ` is 1-indexed; the Lean list `p` is 0-indexed, so the paper's `pₖ` is
`p[k-1]`.  The natural numbers `i < j` below are the **0-indexed** positions of the two ends of
the line, so its length is `j - i`.  The hypotheses are:

* `hij : i + 2 ≤ j` — *"a line of length `≥ 2`"*;
* `hint` — no vertex strictly between the two ends is `Y`-complete (the line has no
  `Y`-complete internal vertex);
* `hci`, `hcj` — *"both ends of `P'` are `Y`-complete"*.

Maximality of the line is **not** needed for this block: only the three facts above are used.

## The one place the printed symmetry is discharged by hand

*"Since `n ≥ 5`, either `n > j` or `1 < i`, and from the symmetry between `p₁` and `pₙ` we may
assume the latter."*  Rather than reversing `P` (which would force the whole hypothesis package
to be transported), the witness vertex needed by the closing antihole is named explicitly: it
is `p₁ = p[0]` when `1 < i`, and `pₙ = p[n-1]` when `j < n-1`.  Both are `X`-complete and both
are at index distance `≥ 2` from `pᵢ₊₁` and `pᵢ₊₂`, which is all the argument uses.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm183LineEvenCase

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The last three printed sentences of Case A, parameterised by the witness vertex `z`
(which is `p₁` or `pₙ`, per the printed symmetry):

*"Since `pᵢ₊₁, pᵢ₊₂` are not `X`-complete, they are joined by an antipath `Q'` with interior in
`X`.  Since `Q ∪ Q'` is an antihole it follows that `Q'` is odd.  But then
`p₁-pᵢ₊₁-Q'-pᵢ₊₂-p₁` is an odd antihole, a contradiction."* -/
private theorem endgame
    {G : SimpleGraph V} (hBerge : Berge G) {X Y : Set V}
    (hXY : Disjoint X Y) (hcompl : Complete G X Y)
    (hXa : AnticonnectedSet G X)
    {c d z : V} (hadjcd : G.Adj c d)
    (hcX : c ∉ X) (hdX : d ∉ X) (hcY : c ∉ Y) (hdY : d ∉ Y)
    (hcnX : ¬ VertexComplete G c X) (hdnX : ¬ VertexComplete G d X)
    (hzX : VertexComplete G z X) (hzc : ¬ G.Adj z c) (hzd : ¬ G.Adj z d)
    (hznec : z ≠ c) (hzned : z ≠ d)
    {Q : List V} (hQ : IsAntipathFrom G Q c d) (hQodd : Odd (pathLength Q))
    (hQint : ∀ w ∈ SPGT.interior Q, w ∈ Y) : False := by
  -- *"Since `pᵢ₊₁, pᵢ₊₂` are not `X`-complete, they are joined by an antipath `Q'` with
  -- interior in `X`."*
  have hcex : ∃ x ∈ X, ¬ G.Adj c x := by
    by_contra hcon
    push_neg at hcon
    exact hcnX hcon
  have hdex : ∃ x ∈ X, ¬ G.Adj d x := by
    by_contra hcon
    push_neg at hcon
    exact hdnX hcon
  obtain ⟨Q', hQ', hQ'int⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hXa hcX hdX hcex hdex
  -- *"Since `Q ∪ Q'` is an antihole it follows that `Q'` is odd."*
  have hsum : Even (pathLength Q + pathLength Q') :=
    AntiholeCompletion.even_add_pathLength_of_two_antipaths hBerge hXY hcompl hadjcd
      hcX hdX hcY hdY hQ hQint hQ' hQ'int
  -- *"But then `p₁-pᵢ₊₁-Q'-pᵢ₊₂-p₁` is an odd antihole, a contradiction."*
  have heven : Even (pathLength Q') :=
    AntiholeCompletion.even_pathLength_of_witness hBerge hadjcd hzX hzc hzd hznec hzned
      hQ' hQ'int
  rw [Nat.even_iff] at hsum heven
  rw [Nat.odd_iff] at hQodd
  omega

/-- **18.3, "Case A"**: *"So in this case `P'` has even length."*

`P'` is the stretch `pᵢ-⋯-pⱼ` of `P`, of length `j - i ≥ 2`, whose two ends are `Y`-complete
and none of whose internal vertices is. -/
theorem line_even_of_both_ends_YComplete
    (G : SimpleGraph V) (hG5 : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)))
    (i j : ℕ) (hij : i + 2 ≤ j) (hj : j < p.length)
    (hint : ∀ (k : ℕ) (hk : k < p.length), i < k → k < j →
       ¬ VertexComplete G (p[k]'hk) Y)
    (hci : VertexComplete G (p[i]'(by omega)) Y)
    (hcj : VertexComplete G (p[j]'hj) Y) :
    Even (j - i) := by
  -- *"Suppose `P'` has odd length"* — argue by contradiction.
  rcases Nat.even_or_odd (j - i) with hev | hodd
  · exact hev
  exfalso
  have hBerge : Berge G := hG5.1.1
  have hij' : i < j := by omega
  have hilt : i < p.length := by omega
  have h0lt : 0 < p.length := by omega
  have hLlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpL : p[p.length - 1]'hLlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  -- Membership bookkeeping: no vertex of `P` lies in `X` or in `Y`.
  have hnX : ∀ (m : ℕ) (hm : m < p.length), (p[m]'hm) ∉ X := fun m hm h =>
    hpXY _ (List.getElem_mem hm) (Set.mem_union_left _ h)
  have hnY : ∀ (m : ℕ) (hm : m < p.length), (p[m]'hm) ∉ Y := fun m hm h =>
    hpXY _ (List.getElem_mem hm) (Set.mem_union_right _ h)
  -- *"`p₁, pₙ` are the only `X`-complete vertices of `P`"*, in index form.
  have hnotend : ∀ (m : ℕ) (hm : m < p.length), 0 < m → m < p.length - 1 →
      ¬ VertexComplete G (p[m]'hm) X := by
    intro m hm hm0 hmL hcon
    rcases (hXuniq _ (List.getElem_mem hm)).mp hcon with h | h
    · exact PathBasics.path_ne_of_ne_index hp hm h0lt (by omega) (h.trans hp0.symm)
    · exact PathBasics.path_ne_of_ne_index hp hm hLlt (by omega) (h.trans hpL.symm)
  -- **Step 1** — the line `P'` is the stretch `pᵢ-⋯-pⱼ` of `P`.
  have hSlen : ((p.drop i).take (j - i + 1)).length = j - i + 1 :=
    PathBasics.length_slice p (by omega) hj
  have hSpath : IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'hilt) (p[j]'hj) :=
    PathBasics.isPathFrom_slice hp hij' hj
  have hSpl : pathLength ((p.drop i).take (j - i + 1)) = j - i := by
    rw [PathBasics.pathLength_eq, hSlen]; omega
  have hoddS : Odd (pathLength ((p.drop i).take (j - i + 1))) := by rw [hSpl]; exact hodd
  -- `Y` is disjoint from `V(P')`: 13.6's hypothesis `Y ⊆ V(G) \ V(P')`.
  have hYS : Y ⊆ {v : V | v ∈ (p.drop i).take (j - i + 1)}ᶜ := by
    intro y hy hyS
    obtain ⟨m, hm, -, -, rfl⟩ := (PathBasics.mem_slice_iff p (by omega) hj).mp hyS
    exact hnY m hm hy
  -- **Step 2** — *"Then 13.6 implies that `j − i = 3`, and there is an odd antipath `Q`
  -- joining `pᵢ₊₁, pᵢ₊₂` with interior in `Y`."*
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG5 _ _ _ hSpath hoddS
      Y hYS hYa hci hcj with hedge | hthree
  · -- 13.6(1): a `Y`-complete edge of `P'`.  Both its ends are `Y`-complete, so by `hint`
    -- each sits at position `i` or `j`; but those two positions differ by `≥ 2`, so the two
    -- vertices are not adjacent on the induced path `P`.
    obtain ⟨u, hu, v, hv, hadjuv, hcu, hcv⟩ := hedge
    obtain ⟨a, ha, hai, haj, rfl⟩ := (PathBasics.mem_slice_iff p (by omega) hj).mp hu
    obtain ⟨b, hb, hbi, hbj, rfl⟩ := (PathBasics.mem_slice_iff p (by omega) hj).mp hv
    have hEa : a = i ∨ a = j := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      exact hint a ha (by omega) (by omega) hcu
    have hEb : b = i ∨ b = j := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨h1, h2⟩ := hcon
      exact hint b hb (by omega) (by omega) hcv
    have hidx := (PathBasics.path_adj_iff hp ha hb).mp hadjuv
    omega
  · -- 13.6(2): `P'` has length `3` and its two internal vertices are joined by an odd
    -- antipath with interior in `Y`.
    obtain ⟨h3, c, d, hIeq, q, hq, hqodd, hqint⟩ := hthree
    have hji : j = i + 3 := by rw [hSpl] at h3; omega
    -- `c ≠ d`, since the interior of a path has no repeated vertex.
    have hSnd : ((p.drop i).take (j - i + 1)).Nodup := PathBasics.path_nodup hSpath.1
    have hInd : (SPGT.interior ((p.drop i).take (j - i + 1))).Nodup := by
      rw [PathBasics.interior_eq]
      exact List.Nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _)) hSnd
    have hcd : c ≠ d := by rw [hIeq] at hInd; simpa using hInd
    have hcmem : c ∈ SPGT.interior ((p.drop i).take (j - i + 1)) := by rw [hIeq]; simp
    have hdmem : d ∈ SPGT.interior ((p.drop i).take (j - i + 1)) := by rw [hIeq]; simp
    -- The interior vertices of `P'` are `pᵢ₊₁` and `pᵢ₊₂`, in some order.
    obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
      (PathBasics.mem_interior_slice_iff hp hij' hj).mp hcmem
    obtain ⟨k', hk', hk'1, hk'2, rfl⟩ :=
      (PathBasics.mem_interior_slice_iff hp hij' hj).mp hdmem
    have hkne : k ≠ k' := by rintro rfl; exact hcd rfl
    -- `pᵢ₊₁ pᵢ₊₂` is an edge of `P`.
    have hadjcd : G.Adj (p[k]'hk) (p[k']'hk') :=
      (PathBasics.path_adj_iff hp hk hk').mpr (by omega)
    -- Neither internal vertex is `X`-complete.
    have hcnX : ¬ VertexComplete G (p[k]'hk) X := hnotend k hk (by omega) (by omega)
    have hdnX : ¬ VertexComplete G (p[k']'hk') X := hnotend k' hk' (by omega) (by omega)
    -- **Step 3** — *"Since `n ≥ 5`, either `n > j` or `1 < i`, and from the symmetry between
    -- `p₁` and `pₙ` we may assume the latter."*  Instead of reversing `P`, the witness vertex
    -- `z` is named explicitly: `p₁` in the first case, `pₙ` in the second.
    have hsym : 0 < i ∨ j < p.length - 1 := by omega
    rcases hsym with hlo | hhi
    · -- `z = p₁ = p[0]`.
      refine endgame (z := p[0]'h0lt) hBerge hXY hcompl hXa hadjcd (hnX k hk) (hnX k' hk')
        (hnY k hk) (hnY k' hk') hcnX hdnX ?_ ?_ ?_ ?_ ?_ hq hqodd hqint
      · exact (hXuniq _ (List.getElem_mem h0lt)).mpr (Or.inl hp0)
      · rw [PathBasics.path_adj_iff hp h0lt hk]; omega
      · rw [PathBasics.path_adj_iff hp h0lt hk']; omega
      · exact PathBasics.path_ne_of_ne_index hp h0lt hk (by omega)
      · exact PathBasics.path_ne_of_ne_index hp h0lt hk' (by omega)
    · -- `z = pₙ = p[n-1]`.
      refine endgame (z := p[p.length - 1]'hLlt) hBerge hXY hcompl hXa hadjcd (hnX k hk)
        (hnX k' hk') (hnY k hk) (hnY k' hk') hcnX hdnX ?_ ?_ ?_ ?_ ?_ hq hqodd hqint
      · exact (hXuniq _ (List.getElem_mem hLlt)).mpr (Or.inr hpL)
      · rw [PathBasics.path_adj_iff hp hLlt hk]; omega
      · rw [PathBasics.path_adj_iff hp hLlt hk']; omega
      · exact PathBasics.path_ne_of_ne_index hp hLlt hk (by omega)
      · exact PathBasics.path_ne_of_ne_index hp hLlt hk' (by omega)

end Workspace.ProofLemmas.Thm183LineEvenCase
