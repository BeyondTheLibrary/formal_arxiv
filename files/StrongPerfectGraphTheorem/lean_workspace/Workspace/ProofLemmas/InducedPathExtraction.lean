import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach

/-!
# Extracting an induced path from a connected set

The paper says, over and over and without comment, *"let `P` be a path of `F` between `f`
and `f'`"* or *"let `Q` be an antipath between `p₁, p₂` with interior in `X`"*.  Since the
paper's *path* is an **induced** subgraph, that move is genuinely a small theorem: from
connectivity one only gets a *walk*, and a walk has to be shortened before it is induced.
Mathlib has no notion of induced path at all, so the whole extraction is done here.

The route is the obvious one.  A **chain** from `u` to `v` inside `S` is a list of vertices
of `S` starting at `u`, ending at `v`, with consecutive entries adjacent — i.e. exactly the
support list of a walk of `G|S`.  A chain of *minimum length* is automatically an induced
path: a repeated vertex or a chord would let us splice out a nonempty middle block and get
a shorter chain.

Contents:

* `exists_isPathFrom_of_connected` — the headline lemma: a connected set contains an induced
  path of `G` between any two of its vertices, with all vertices inside the set.
* `exists_isAntipathFrom_of_anticonnected` — the same statement for `Gᶜ`, i.e. *antipaths*
  inside an anticonnected set (this is the form §§2, 15, 17, 23, 24 use).
* `exists_antipath_interior_in` — the paper's *"an antipath between `u` and `v` with interior
  in `X`"*: `X` anticonnected and `u, v` each with a nonneighbour in `X`.
* `connectedSet_setOf_mem_of_isPathList` — the converse bookkeeping fact, that the vertex set
  of a path is connected (needed whenever a proof replaces a connected set by a path inside it).

None of these has a counterpart in the paper; they are infrastructure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.InducedPathExtraction

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-! ### Chains -/

/-- A **chain** from `u` to `v` inside `S`: a list of vertices of `S` beginning at `u`,
ending at `v`, whose consecutive entries are adjacent.  Unlike a path it may repeat
vertices and may have chords. -/
private def IsChainFrom (G : SimpleGraph V) (S : Set V) (p : List V) (u v : V) : Prop :=
  p.head? = some u ∧ p.getLast? = some v ∧ (∀ z ∈ p, z ∈ S) ∧ List.IsChain G.Adj p

private theorem chain_length_pos {S : Set V} {p : List V} {u v : V}
    (h : IsChainFrom G S p u v) : 0 < p.length := by
  rcases p with _ | ⟨a, l⟩
  · simp [IsChainFrom] at h
  · simp

private theorem chain_getElem_last {S : Set V} {p : List V} {u v : V}
    (h : IsChainFrom G S p u v) : p[p.length - 1]'(by have := chain_length_pos h; omega) = v := by
  have h2 := h.2.1
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (by have := chain_length_pos h; omega)] at h2
  exact Option.some_inj.mp h2

/-- The support list of a walk of `G|S` is a chain of `G` inside `S`. -/
private theorem exists_chain_of_connected {S : Set V} (hS : ConnectedSet G S) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) : ∃ p : List V, IsChainFrom G S p u v := by
  obtain ⟨w⟩ := hS ⟨u, hu⟩ ⟨v, hv⟩
  have hh : w.support.head? = some (⟨u, hu⟩ : ↥S) := by
    rw [List.head?_eq_some_head w.support_ne_nil]
    congr 1
    exact w.head_support
  have hl : w.support.getLast? = some (⟨v, hv⟩ : ↥S) := by
    rw [List.getLast?_eq_some_getLast w.support_ne_nil]
    congr 1
    exact w.getLast_support
  refine ⟨w.support.map Subtype.val, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_map, hh]; rfl
  · rw [List.getLast?_map, hl]; rfl
  · intro z hz
    obtain ⟨a, -, rfl⟩ := List.mem_map.mp hz
    exact a.2
  · exact (List.isChain_map _).2 w.isChain_adj_support

/-- Truncating a chain at a position that already carries the last vertex. -/
private theorem chain_take {S : Set V} {p : List V} {u v : V} (h : IsChainFrom G S p u v)
    {i : ℕ} (hi : i < p.length) (hiv : (p[i]'hi) = v) :
    IsChainFrom G S (p.take (i + 1)) u v ∧ (p.take (i + 1)).length = i + 1 := by
  refine ⟨⟨?_, ?_, ?_, h.2.2.2.take _⟩, by rw [List.length_take]; omega⟩
  · rw [List.head?_take, if_neg (by omega)]
    exact h.1
  · rw [List.getLast?_take, if_neg (by omega)]
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, hiv, Option.some_or]
  · exact fun z hz => h.2.2.1 z (List.take_subset _ _ hz)

/-- Splicing a chain: if positions `i` and `k` with `i + 1 < k` carry adjacent vertices,
the block strictly between them can be cut out, giving a strictly shorter chain. -/
private theorem chain_splice {S : Set V} {p : List V} {u v : V} (h : IsChainFrom G S p u v)
    {i k : ℕ} (hik : i + 1 < k) (hk : k < p.length)
    (hadj : G.Adj (p[i]'(by omega)) (p[k]'hk)) :
    IsChainFrom G S (p.take (i + 1) ++ p.drop k) u v ∧
      (p.take (i + 1) ++ p.drop k).length < p.length := by
  have hip : i < p.length := by omega
  have hqlen : (p.take (i + 1) ++ p.drop k).length = (i + 1) + (p.length - k) := by
    rw [List.length_append, List.length_take, List.length_drop]
    omega
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by omega⟩
  · rw [List.head?_append, List.head?_take, if_neg (by omega), h.1]
    rfl
  · rw [List.getLast?_append, List.getLast?_drop, if_neg (by omega), h.2.1]
    rfl
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact h.2.2.1 z (List.take_subset _ _ hz)
    · exact h.2.2.1 z (List.drop_subset _ _ hz)
  · refine List.IsChain.append (h.2.2.2.take _) (h.2.2.2.drop _) ?_
    intro x hx y hy
    rw [List.getLast?_take, if_neg (by omega)] at hx
    simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hip, Option.some_or,
      Option.mem_some_iff] at hx
    rw [List.head?_drop, List.getElem?_eq_getElem hk, Option.mem_some_iff] at hy
    rw [← hx, ← hy]
    exact hadj

/-! ### The extraction theorem -/

/-- **Extraction of an induced path.**  If `S` is connected and `u, v ∈ S`, there is a path
of `G` (in the paper's sense: an induced subgraph) from `u` to `v` all of whose vertices lie
in `S`.

This is the content of every *"let `P` be a path of `F` between `f` and `f'`"* in the paper. -/
theorem exists_isPathFrom_of_connected {S : Set V} (hS : ConnectedSet G S) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) :
    ∃ p : List V, IsPathFrom G p u v ∧ ∀ z ∈ p, z ∈ S := by
  classical
  have hex : ∃ n : ℕ, ∃ p : List V, IsChainFrom G S p u v ∧ p.length = n := by
    obtain ⟨p, hp⟩ := exists_chain_of_connected hS hu hv
    exact ⟨p.length, p, hp, rfl⟩
  obtain ⟨p, hp, hplen⟩ := Nat.find_spec hex
  have hmin : ∀ q : List V, IsChainFrom G S q u v → p.length ≤ q.length := by
    intro q hq
    rw [hplen]
    exact Nat.find_min' hex ⟨q, hq, rfl⟩
  have hpos : 0 < p.length := chain_length_pos hp
  have hlastv : p[p.length - 1]'(by omega) = v := chain_getElem_last hp
  -- no chord: positions at distance `≥ 2` carry nonadjacent vertices
  have hchord : ∀ (i j : ℕ) (hi : i < p.length) (hj : j < p.length), i + 1 < j →
      ¬ G.Adj (p[i]'hi) (p[j]'hj) := by
    intro i j hi hj hij hadj
    obtain ⟨hsp, hlt⟩ := chain_splice hp hij hj hadj
    exact absurd (hmin _ hsp) (by omega)
  -- no repetition
  have hnodup : p.Nodup := by
    refine List.pairwise_iff_getElem.mpr ?_
    intro i j hi hj hij heq
    by_cases hjl : j + 1 = p.length
    · have hiv : (p[i]'hi) = v := by
        rw [heq]
        have hjj : j = p.length - 1 := by omega
        subst hjj
        exact hlastv
      obtain ⟨hct, hctlen⟩ := chain_take hp hi hiv
      have := hmin _ hct
      omega
    · have hj1 : j + 1 < p.length := by omega
      have hadj : G.Adj (p[i]'hi) (p[j + 1]'hj1) := by
        rw [heq]
        exact hp.2.2.2.getElem j hj1
      obtain ⟨hsp, hlt⟩ := chain_splice hp (by omega : i + 1 < j + 1) hj1 hadj
      exact absurd (hmin _ hsp) (by omega)
  refine ⟨p, ⟨⟨?_, hnodup, ?_⟩, hp.1, hp.2.1⟩, hp.2.2.1⟩
  · intro hnil
    rw [hnil] at hpos
    simp at hpos
  · intro i j hi hj
    constructor
    · intro hadj
      by_contra hcon
      push Not at hcon
      obtain ⟨h1, h2⟩ := hcon
      rcases lt_trichotomy i j with hlt | heq | hgt
      · exact hchord i j hi hj (by omega) hadj
      · subst heq
        exact G.irrefl hadj
      · exact hchord j i hj hi (by omega) hadj.symm
    · rintro (rfl | rfl)
      · exact hp.2.2.2.getElem i hj
      · exact (hp.2.2.2.getElem j hi).symm

/-! ### The `Gᶜ` forms -/

/-- **Extraction of an antipath.**  The `Gᶜ` instance of `exists_isPathFrom_of_connected`:
an anticonnected set contains an antipath between any two of its vertices. -/
theorem exists_isAntipathFrom_of_anticonnected {S : Set V} (hS : AnticonnectedSet G S) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) :
    ∃ p : List V, IsAntipathFrom G p u v ∧ ∀ z ∈ p, z ∈ S :=
  exists_isPathFrom_of_connected (G := Gᶜ) hS hu hv

/-- The paper's *"let `Q` be an antipath between `u` and `v` with interior in `X`"*: `X` is
anticonnected, `u` and `v` lie outside `X` and each has a nonneighbour in `X`. -/
theorem exists_antipath_interior_in {X : Set V} (hX : AnticonnectedSet G X) {u v : V}
    (huX : u ∉ X) (hvX : v ∉ X)
    (hu : ∃ x ∈ X, ¬ G.Adj u x) (hv : ∃ x ∈ X, ¬ G.Adj v x) :
    ∃ q : List V, IsAntipathFrom G q u v ∧ ∀ z ∈ SPGT.interior q, z ∈ X := by
  obtain ⟨a, haX, hua⟩ := hu
  obtain ⟨b, hbX, hvb⟩ := hv
  have h1 : ConnectedSet Gᶜ (X ∪ {u}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hX
      ⟨a, haX, ⟨fun h => huX (h ▸ haX), hua⟩⟩
  have h2 : ConnectedSet Gᶜ ((X ∪ {u}) ∪ {v}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton h1
      ⟨b, Or.inl hbX, ⟨fun h => hvX (h ▸ hbX), hvb⟩⟩
  have humem : u ∈ (X ∪ {u}) ∪ {v} := Or.inl (Or.inr rfl)
  have hvmem : v ∈ (X ∪ {u}) ∪ {v} := Or.inr rfl
  obtain ⟨q, hq, hqmem⟩ := exists_isPathFrom_of_connected (G := Gᶜ) h2 humem hvmem
  refine ⟨q, hq, ?_⟩
  intro z hz
  rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hz
  obtain ⟨hzq, hzu, hzv⟩ := hz
  rcases hqmem z hzq with h | h
  · rcases h with h | h
    · exact h
    · exact absurd h hzu
  · exact absurd h hzv

/-! ### The converse bookkeeping: the vertex set of a path is connected -/

/-- A path's consecutive entries are adjacent. -/
theorem isChain_of_isPathList {p : List V} (h : IsPathList G p) : List.IsChain G.Adj p := by
  refine List.isChain_iff_getElem.mpr ?_
  intro i hi
  exact (h.2.2 i (i + 1) (by omega) hi).mpr (Or.inl rfl)

/-- The vertex set of any list with adjacent consecutive entries is connected. -/
theorem connectedSet_setOf_mem_of_isChain {p : List V} (h : List.IsChain G.Adj p) :
    ConnectedSet G {z : V | z ∈ p} := by
  intro a b
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem a.2
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem b.2
  have hpos : 0 < p.length := by omega
  have key : ∀ (k : ℕ) (hk : k < p.length),
      (G.induce {z : V | z ∈ p}).Reachable
        ⟨p[0]'hpos, List.getElem_mem hpos⟩ ⟨p[k]'hk, List.getElem_mem hk⟩ := by
    intro k
    induction k with
    | zero => intro hk; exact SimpleGraph.Reachable.refl _
    | succ m ih =>
        intro hk
        have hm : m < p.length := by omega
        exact (ih hm).trans (SimpleGraph.Adj.reachable (h.getElem m hk))
  have ha : a = ⟨p[i]'hi, List.getElem_mem hi⟩ := Subtype.ext hia.symm
  have hb : b = ⟨p[j]'hj, List.getElem_mem hj⟩ := Subtype.ext hjb.symm
  rw [ha, hb]
  exact (key i hi).symm.trans (key j hj)

/-- The vertex set of a path is connected. -/
theorem connectedSet_setOf_mem_of_isPathList {p : List V} (h : IsPathList G p) :
    ConnectedSet G {z : V | z ∈ p} :=
  connectedSet_setOf_mem_of_isChain (isChain_of_isPathList h)

/-- The vertex set of an antipath is anticonnected. -/
theorem anticonnectedSet_setOf_mem_of_isAntipathList {p : List V} (h : IsAntipathList G p) :
    AnticonnectedSet G {z : V | z ∈ p} :=
  connectedSet_setOf_mem_of_isPathList (G := Gᶜ) h

end Workspace.ProofLemmas.InducedPathExtraction
