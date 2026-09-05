import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# Splicing induced paths at a shared end, and first-hitting extraction

(See `Workspace/ProofLemmas/PathGlueInduced.lean` for the full module docstring.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.PathGlueInduced

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}

/-! ### Private bookkeeping -/

/-- Two entries of a list at equal indices are equal. -/
private theorem getElem_eq_of_eq {l : List V} {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- The `k`-th entry of `l.tail` is the `(k+1)`-st entry of `l`. -/
private theorem tail_getElem : ∀ {l : List V} {k : ℕ} (hk : k < l.tail.length)
    (hk' : k + 1 < l.length), l.tail[k]'hk = l[k + 1]'hk'
  | [], k, hk, _ => absurd hk (by simp)
  | _ :: t, k, hk, hk' => rfl

/-! ### The two exported lemmas -/

/-- **Splicing two induced paths that meet at one shared end.**  If `p` is an induced path
from `a` to `c`, `q` an induced path from `c` to `b`, the two share `c` and nothing else, and
there is no edge between `V(p) \ {c}` and `V(q) \ {c}`, then `p ++ q.tail` is an induced path
from `a` to `b`.

The anticompleteness hypothesis is exactly necessary: any edge between `V(p) \ {c}` and
`V(q) \ {c}` is a chord of the concatenation, so it cannot be weakened (in particular it
already covers the one pair — the neighbour of `c` on `p` and the neighbour of `c` on `q` —
that a careless statement would forget).

Degenerate cases are allowed and behave correctly: if `p = [c]` (so `a = c`) the result is
`q`, and if `q = [c]` (so `b = c`) the result is `p`.

Call sites: 22.4, *"Since `y, u₁, …, u_{n-1}` have no neighbours in `A_t` it follows that
`z-y-u₁-⋯-u_n-P-p` is a path, `Q` say"* (before claim (2)); 22.4 claim (5), *"the path
`z-x_{t+1}-R-r`"*; 22.4 claim (7), *"The path `s-S-x_{t+1}-R-r`"*. -/
theorem isPathList_append_at_end {G : SimpleGraph V} {p q : List V} {a b c : V}
    (hp : IsPathFrom G p a c) (hq : IsPathFrom G q c b)
    (hmeet : ∀ x, x ∈ p → x ∈ q → x = c)
    (hanti : ∀ x ∈ p, x ≠ c → ∀ y ∈ q, y ≠ c → ¬ G.Adj x y) :
    IsPathFrom G (p ++ q.tail) a b := by
  obtain ⟨hpl, hph, hpt⟩ := hp
  obtain ⟨hql, hqh, hqt⟩ := hq
  have hnp : 0 < p.length := PathBasics.path_length_pos hpl
  have hnq : 0 < q.length := PathBasics.path_length_pos hql
  have hpnd : p.Nodup := hpl.2.1
  have hqnd : q.Nodup := hql.2.1
  have hpc : p[p.length - 1]'(by omega) = c := PathBasics.getElem_last_of_getLast? hpt hnp
  have hq0 : q[0]'hnq = c := PathBasics.getElem_zero_of_head? hqh hnq
  have hqb : q[q.length - 1]'(by omega) = b := PathBasics.getElem_last_of_getLast? hqt hnq
  have htlen : q.tail.length = q.length - 1 := List.length_tail
  have hget : ∀ (k : ℕ) (hk : k < q.tail.length),
      q.tail[k]'hk = q[k + 1]'(by omega) := fun k hk => tail_getElem hk (by omega)
  have hmemt : ∀ x ∈ q.tail, x ∈ q := fun x hx => List.mem_of_mem_tail hx
  have hcnt : c ∉ q.tail := by
    intro hc
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.mp hc
    rw [hget k hk] at hkc
    have := hqnd.getElem_inj_iff.mp (hkc.trans hq0.symm)
    omega
  have hdisj : ∀ x ∈ p, x ∉ q.tail := by
    intro x hx hxt
    have : x = c := hmeet x hx (hmemt x hxt)
    exact hcnt (this ▸ hxt)
  have htnd : q.tail.Nodup := (List.tail_sublist q).nodup hqnd
  -- The key case: one index in `p`, the other in `q.tail`.
  have cross : ∀ (i j : ℕ) (hip : i < p.length) (hjp : p.length ≤ j)
      (hi : i < (p ++ q.tail).length) (hj : j < (p ++ q.tail).length),
      (G.Adj ((p ++ q.tail)[i]'hi) ((p ++ q.tail)[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i j hip hjp hi hj
    have hjL : j < p.length + q.tail.length := by simpa using hj
    have hjt : j - p.length < q.tail.length := by omega
    have hkq : j - p.length + 1 < q.length := by omega
    rw [List.getElem_append_left hip, List.getElem_append_right hjp, hget _ hjt]
    have hne : q[j - p.length + 1]'hkq ≠ c := by
      intro h
      have := hqnd.getElem_inj_iff.mp (h.trans hq0.symm)
      omega
    by_cases hilast : i = p.length - 1
    · -- `p[i] = c = q[0]`; the adjacency is the first edge of `q`
      have hpi : p[i]'hip = c := by
        rw [getElem_eq_of_eq hip (by omega) hilast]; exact hpc
      rw [hpi, ← hq0, PathBasics.path_adj_iff hql hnq hkq]
      constructor
      · rintro (h | h) <;> omega
      · intro h; left; omega
    · -- `p[i] ≠ c`, so anticompleteness forbids the edge, and the indices are far apart
      have hpi : p[i]'hip ≠ c := by
        intro h
        exact hilast (hpnd.getElem_inj_iff.mp (h.trans hpc.symm))
      constructor
      · intro hadj
        exact absurd hadj (hanti _ (List.getElem_mem hip) hpi _ (List.getElem_mem hkq) hne)
      · intro h; omega
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro h
    have hz : (p ++ q.tail).length = 0 := by rw [h]; rfl
    simp only [List.length_append] at hz
    omega
  · rw [List.nodup_append]
    exact ⟨hpnd, htnd, fun x hx y hy => by rintro rfl; exact hdisj x hx hy⟩
  · intro i j hi hj
    have hiL : i < p.length + q.tail.length := by simpa using hi
    have hjL : j < p.length + q.tail.length := by simpa using hj
    rcases lt_or_ge i p.length with hip | hip
    · rcases lt_or_ge j p.length with hjp | hjp
      · rw [List.getElem_append_left hip, List.getElem_append_left hjp,
          PathBasics.path_adj_iff hpl hip hjp]
      · exact cross i j hip hjp hi hj
    · rcases lt_or_ge j p.length with hjp | hjp
      · rw [SimpleGraph.adj_comm, cross j i hjp hip hj hi]
        constructor <;> (intro h; omega)
      · have hit : i - p.length < q.tail.length := by omega
        have hjt : j - p.length < q.tail.length := by omega
        rw [List.getElem_append_right hip, List.getElem_append_right hjp, hget _ hit,
          hget _ hjt, PathBasics.path_adj_iff hql (by omega) (by omega)]
        omega
  · rw [List.head?_append, hph]; rfl
  · rcases eq_or_ne q.tail [] with hte | hte
    · -- `q = [c]`, so `b = c` and the concatenation is just `p`
      have htz : q.tail.length = 0 := by rw [hte]; rfl
      have hq1 : q.length = 1 := by omega
      have hbc : b = c := by
        rw [← hqb, ← hq0]; exact getElem_eq_of_eq (by omega) (by omega) (by omega)
      rw [hte, List.append_nil, hpt, hbc]
    · rw [List.getLast?_append_of_ne_nil _ hte]
      have hlt : 0 < q.tail.length := by
        cases hqt' : q.tail with
        | nil => exact absurd hqt' hte
        | cons x t => simp [hqt']
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show q.tail.length - 1 < q.tail.length by omega),
        hget _ (show q.tail.length - 1 < q.tail.length by omega)]
      refine congrArg some ?_
      rw [← hqb]
      exact getElem_eq_of_eq (by omega) (by omega) (by omega)

/-- **First-hitting extraction.**  Let `S` be a connected set, let `v ∉ S` have a neighbour in
`S`, and let a predicate `P` hold somewhere in `S` but not at `v`.  Then there is an induced
path of `G` from `v` to some `p ∈ S` with `P p`, all of whose vertices lie in `S ∪ {v}`, and
whose **only** vertex satisfying `P` is its far end `p`.

The hypothesis `¬ P v` is load-bearing, not cosmetic: with `P v` no path can have `p` as its
unique `P`-vertex, so the conclusion would be false.  Every call site supplies it — in 22.4
before claim (1) it is *"since `T` is a tail it follows that none of `u₁, …, u_n` are
`Y`-complete"*, and in claim (5) it is claim (4) itself (*"`x_{t+1}` is not `Y`-complete"*).

The length conclusion `1 ≤ pathLength q` is the paper's *"For `P` has length `≥ 1` …"* and
*"For certainly `R` has length `≥ 1`"*; it is free here because `p ∈ S` and `v ∉ S`.

Contrast `PathInteriorIn.exists_path_interior_in`, which prescribes **both** endpoints and
only controls the interior; that is not the shape 22.4 needs.

Call sites: 22.4, *"Let `P` be a path with vertex set in `A_t ∪ {u_n}`, from `u_n` to some
`Y`-complete vertex `p` say, such that no vertex of `P \ p` is `Y`-complete"* (before claim
(1)); 22.4 claim (5), *"there is a path `R` from `x_{t+1}` to some `Y`-complete vertex `r` in
`A_t` with `V(R \ x_{t+1}) ⊆ A_t` such that no vertex of `R \ r` is `Y`-complete"*; 22.4
claim (7), the path `S` from `x_{t+1}` to an `X_t`-complete vertex `s`. -/
theorem exists_path_to_first {G : SimpleGraph V} {S : Set V} (hS : ConnectedSet G S)
    {v : V} (hvS : v ∉ S) (hvadj : ∃ s ∈ S, G.Adj v s)
    (P : V → Prop) (hPv : ¬ P v) (hPS : ∃ s ∈ S, P s) :
    ∃ (q : List V) (p : V), IsPathFrom G q v p ∧ p ∈ S ∧ P p ∧
      1 ≤ pathLength q ∧
      (∀ x ∈ q, x = v ∨ x ∈ S) ∧
      (∀ x ∈ q, P x → x = p) := by
  classical
  obtain ⟨s₀, hs₀S, hPs₀⟩ := hPS
  -- `S ∪ {v}` is connected, so there is an induced path inside it from `v` to `s₀`.
  have hSv : ConnectedSet G (S ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hS hvadj
  obtain ⟨r, hr, hrsub⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hSv
      (Set.mem_union_right _ (Set.mem_singleton v)) (Set.mem_union_left _ hs₀S)
  have hrpos : 0 < r.length := PathBasics.path_length_pos hr.1
  have hrnd : r.Nodup := hr.1.2.1
  have hr0 : r[0]'hrpos = v := PathBasics.getElem_zero_of_head? hr.2.1 hrpos
  have hrl : r[r.length - 1]'(by omega) = s₀ := PathBasics.getElem_last_of_getLast? hr.2.2 hrpos
  -- Take the FIRST position along `r` at which `P` holds.
  have hex : ∃ i, ∃ (h : i < r.length), P (r[i]'h) :=
    ⟨r.length - 1, by omega, by rw [hrl]; exact hPs₀⟩
  obtain ⟨i, ⟨hi, hPi⟩, hmin⟩ : ∃ i, (∃ (h : i < r.length), P (r[i]'h)) ∧
      ∀ j, j < i → ¬ ∃ (h : j < r.length), P (r[j]'h) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hipos : 0 < i := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · exfalso
      apply hPv
      have : r[i]'hi = v := by rw [getElem_eq_of_eq hi hrpos h0]; exact hr0
      exact this ▸ hPi
    · exact h0
  -- The initial stretch `r[0] … r[i]` is the required path.
  refine ⟨(r.drop 0).take (i - 0 + 1), r[i]'hi, ?_, ?_, hPi, ?_, ?_, ?_⟩
  · rw [← hr0]; exact PathBasics.isPathFrom_slice hr.1 hipos hi
  · rcases hrsub _ (List.getElem_mem hi) with h | h
    · exact h
    · exfalso
      have hv : r[i]'hi = v := h
      have := hrnd.getElem_inj_iff.mp (hv.trans hr0.symm)
      omega
  · have hlen := PathBasics.length_slice r (show 0 ≤ i by omega) hi
    simp only [pathLength, hlen]
    omega
  · intro x hx
    obtain ⟨k, hk, _, _, hkx⟩ := (PathBasics.mem_slice_iff r (show 0 ≤ i by omega) hi).mp hx
    rcases hrsub _ (hkx ▸ List.getElem_mem hk) with h | h
    · exact Or.inr h
    · exact Or.inl h
  · intro x hx hPx
    obtain ⟨k, hk, _, hki, hkx⟩ := (PathBasics.mem_slice_iff r (show 0 ≤ i by omega) hi).mp hx
    rcases lt_or_eq_of_le hki with hlt | heq
    · exact absurd ⟨hk, hkx ▸ hPx⟩ (hmin k hlt)
    · rw [← hkx]; exact getElem_eq_of_eq hk hi heq

end Workspace.ProofLemmas.PathGlueInduced
