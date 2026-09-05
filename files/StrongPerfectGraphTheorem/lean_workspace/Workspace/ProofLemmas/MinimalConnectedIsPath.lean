import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# A connected set between two attachments is the interior of a path

Section 18 says, four times inside the proof of 18.6 alone,

> From the minimality of `F`, `F` is the interior of a path `p_a`-`f₁`-`⋯`-`f_k`-`p_c`.

and

> From the minimality of `F`, there is a path `p_a`-`f₁`-`⋯`-`f_k` such that `F = {f₁,…,f_k}`.

The graph-theoretic content of those sentences — the part that does *not* mention minimality —
is that a **connected** `F` with an attachment at each of two non-adjacent vertices `u, v ∉ F`
carries an induced path from `u` to `v` whose interior lies in `F`.  That is
`exists_path_interior_in` below: the `G`-side twin of
`InducedPathExtraction.exists_antipath_interior_in`, which existed only for antipaths.

The minimality half is then a *counting* step at the call site, and what it needs is that the
interior is itself an admissible replacement for `F`: connected, contained in `F`, and still
attached to both `u` and `v`.  `exists_path_interior_attached` returns exactly that package, so
a caller with a `Set.ncard`-minimal `F` closes with
`Set.eq_of_subset_of_ncard_le` (or with `Set.ncard_lt_ncard` against its minimality
hypothesis) and gets `F = V(P*)` — the printed sentence.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.MinimalConnectedIsPath

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- **The `G`-side twin of `exists_antipath_interior_in`.**  The paper's *"let `Q` be a path
between `u` and `v` with interior in `F`"*: `F` is connected, `u` and `v` lie outside `F` and
each has a neighbour in `F`. -/
theorem exists_path_interior_in {F : Set V} (hF : ConnectedSet G F) {u v : V}
    (huF : u ∉ F) (hvF : v ∉ F)
    (hu : ∃ f ∈ F, G.Adj u f) (hv : ∃ f ∈ F, G.Adj v f) :
    ∃ p : List V, IsPathFrom G p u v ∧ ∀ z ∈ SPGT.interior p, z ∈ F := by
  obtain ⟨a, haF, hua⟩ := hu
  obtain ⟨b, hbF, hvb⟩ := hv
  have h1 : ConnectedSet G (F ∪ {u}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hF ⟨a, haF, hua⟩
  have h2 : ConnectedSet G ((F ∪ {u}) ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton h1 ⟨b, Or.inl hbF, hvb⟩
  have humem : u ∈ (F ∪ {u}) ∪ {v} := Or.inl (Or.inr rfl)
  have hvmem : v ∈ (F ∪ {u}) ∪ {v} := Or.inr rfl
  obtain ⟨p, hp, hpmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected h2 humem hvmem
  refine ⟨p, hp, ?_⟩
  intro z hz
  rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hz
  obtain ⟨hzp, hzu, hzv⟩ := hz
  rcases hpmem z hzp with h | h
  · rcases h with h | h
    · exact h
    · exact absurd h hzu
  · exact absurd h hzv

/-- A path whose two ends are distinct and non-adjacent has at least three vertices. -/
theorem three_le_length_of_not_adj {p : List V} {u v : V} (hp : IsPathFrom G p u v)
    (huv : u ≠ v) (hnadj : ¬ G.Adj u v) : 3 ≤ p.length := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  rcases (show p.length = 1 ∨ p.length = 2 ∨ 3 ≤ p.length by omega) with h | h | h
  · refine absurd ?_ huv
    rw [← h0, ← hl]
    exact gidx p (show (0 : ℕ) = p.length - 1 by omega) hpos (by omega)
  · refine absurd ?_ hnadj
    have hadj := PathBasics.path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
    rw [h0] at hadj
    have he : p[0 + 1]'(show 0 + 1 < p.length by omega) = v := by
      rw [← hl]
      exact gidx p (show 0 + 1 = p.length - 1 by omega) (by omega) (by omega)
    rw [he] at hadj
    exact hadj
  · exact h

/-- The vertex set of the interior of a path is connected (it is empty, or a path in its own
right). -/
theorem connectedSet_interior {p : List V} {u v : V} (hp : IsPathFrom G p u v) :
    ConnectedSet G {z : V | z ∈ SPGT.interior p} := by
  by_cases h3 : 3 ≤ p.length
  · exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathGlue.isPathFrom_interior hp.1 h3).1
  · intro a b
    exfalso
    have hmem : (a : V) ∈ SPGT.interior p := a.2
    have h1 : 0 < (SPGT.interior p).length := List.length_pos_of_mem hmem
    have h2 : (SPGT.interior p).length = p.length - 2 := PathBasics.interior_length p
    omega

/-- **The package a minimality argument consumes.**  `F` connected, attached at the
non-adjacent vertices `u, v ∉ F`: there is an induced path `u`-`P*`-`v` whose interior `P*` is
a **connected subset of `F` attached to both `u` and `v`**.  A caller whose `F` is minimal
among such sets concludes `F = V(P*)`, which is the paper's *"`F` is the interior of a path
`p_a`-`f₁`-`⋯`-`f_k`-`p_c`"*. -/
theorem exists_path_interior_attached {F : Set V} (hF : ConnectedSet G F) {u v : V}
    (huv : u ≠ v) (hnadj : ¬ G.Adj u v) (huF : u ∉ F) (hvF : v ∉ F)
    (hu : ∃ f ∈ F, G.Adj u f) (hv : ∃ f ∈ F, G.Adj v f) :
    ∃ p : List V, IsPathFrom G p u v ∧ 3 ≤ p.length ∧
      (∀ z ∈ SPGT.interior p, z ∈ F) ∧
      ConnectedSet G {z : V | z ∈ SPGT.interior p} ∧
      (∃ d ∈ SPGT.interior p, G.Adj u d) ∧ (∃ d ∈ SPGT.interior p, G.Adj v d) := by
  obtain ⟨p, hp, hint⟩ := exists_path_interior_in hF huF hvF hu hv
  have h3 : 3 ≤ p.length := three_le_length_of_not_adj hp huv hnadj
  have hpos : 0 < p.length := by omega
  have h0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = v :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hnd : p.Nodup := PathBasics.path_nodup hp.1
  refine ⟨p, hp, h3, hint, connectedSet_interior hp, ⟨p[1]'(by omega), ?_, ?_⟩,
    ⟨p[p.length - 2]'(by omega), ?_, ?_⟩⟩
  · rw [PathBasics.mem_interior_iff_of_pathFrom hp]
    refine ⟨List.getElem_mem _, ?_, ?_⟩
    · rw [← h0]
      exact PathBasics.path_ne_of_ne_index hp.1 (by omega) (by omega) (by omega)
    · rw [← hl]
      exact PathBasics.path_ne_of_ne_index hp.1 (by omega) (by omega) (by omega)
  · have hadj := PathBasics.path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
    rw [h0] at hadj
    exact hadj
  · rw [PathBasics.mem_interior_iff_of_pathFrom hp]
    refine ⟨List.getElem_mem _, ?_, ?_⟩
    · rw [← h0]
      exact PathBasics.path_ne_of_ne_index hp.1 (by omega) (by omega) (by omega)
    · rw [← hl]
      exact PathBasics.path_ne_of_ne_index hp.1 (by omega) (by omega) (by omega)
  · have hadj := PathBasics.path_adj_succ hp.1
      (show (p.length - 2) + 1 < p.length by omega)
    have he : p[(p.length - 2) + 1]'(show (p.length - 2) + 1 < p.length by omega) = v := by
      rw [← hl]
      exact gidx p (show (p.length - 2) + 1 = p.length - 1 by omega) (by omega) (by omega)
    rw [he] at hadj
    exact hadj.symm

end Workspace.ProofLemmas.MinimalConnectedIsPath
