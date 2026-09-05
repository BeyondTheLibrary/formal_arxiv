import Mathlib
import Workspace.Types.Core

/-!
# Path basics

Infrastructure lemmas about the list encoding of paths (`IsPathList`, `IsPathFrom`)
and antipaths (`IsAntipathList`, `IsAntipathFrom`) fixed in `Workspace.Types.Core`.

None of these corresponds to a numbered result of the paper; they are the routine
list-manipulation facts that every section proof silently uses.

Indexing convention (see `paper/spec/CONVENTIONS.md`): the paper's `p₁,…,p_m` is the
list `p` with `p.length = m`, so the paper's `p_i` is `p[i-1]`.
-/

namespace Workspace.ProofLemmas.PathBasics

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*}
variable {G : SimpleGraph V} {p : List V} {u v : V}

/-! ### Basic projections and adjacency -/

/-- A path is a non-empty list. -/
theorem path_ne_nil (h : IsPathList G p) : p ≠ [] := h.1

/-- A path has no repeated vertex. -/
theorem path_nodup (h : IsPathList G p) : p.Nodup := h.2.1

/-- A path has at least one vertex. -/
theorem path_length_pos (h : IsPathList G p) : 0 < p.length :=
  List.length_pos_of_ne_nil (path_ne_nil h)

/-- Two vertices of a path are adjacent exactly when their positions differ by one. -/
theorem path_adj_iff (h : IsPathList G p) {i j : ℕ} (hi : i < p.length) (hj : j < p.length) :
    G.Adj (p[i]'hi) (p[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i) :=
  h.2.2 i j hi hj

/-- Consecutive vertices of a path are adjacent. -/
theorem path_adj_succ (h : IsPathList G p) {i : ℕ} (hi : i + 1 < p.length) :
    G.Adj (p[i]'(Nat.lt_of_succ_lt hi)) (p[i + 1]'hi) :=
  (path_adj_iff h (Nat.lt_of_succ_lt hi) hi).mpr (Or.inl rfl)

/-- Non-consecutive vertices of a path are non-adjacent (this is what makes the
subgraph induced). -/
theorem path_not_adj_of_gap (h : IsPathList G p) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) (h1 : i + 1 ≠ j) (h2 : j + 1 ≠ i) :
    ¬ G.Adj (p[i]'hi) (p[j]'hj) := by
  intro hadj
  rcases (path_adj_iff h hi hj).mp hadj with h' | h'
  · exact h1 h'
  · exact h2 h'

/-- The two ends of a path with at least three vertices (i.e. of length `≥ 2`) are
non-adjacent: a path is never a cycle. -/
theorem path_ends_not_adj (h : IsPathList G p) (hlen : 3 ≤ p.length) :
    ¬ G.Adj (p[0]'(by omega)) (p[p.length - 1]'(by omega)) :=
  path_not_adj_of_gap h (by omega) (by omega) (by omega) (by omega)

/-- Distinct positions of a path carry distinct vertices. -/
theorem path_ne_of_ne_index (h : IsPathList G p) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) (hij : i ≠ j) : (p[i]'hi) ≠ (p[j]'hj) := fun he =>
  hij ((List.Nodup.getElem_inj_iff (path_nodup h)).mp he)

/-! ### Small paths -/

/-- A single vertex is a path (of length `0`); the paper explicitly recognises these. -/
theorem isPathList_singleton (G : SimpleGraph V) (a : V) : IsPathList G [a] := by
  refine ⟨by simp, by simp, ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i
  interval_cases j
  simp

/-- An edge is a path (of length `1`). -/
theorem isPathList_pair {a b : V} (h : G.Adj a b) : IsPathList G [a, b] := by
  refine ⟨by simp, by simp [h.ne], ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;> simp [h, h.symm]

/-! ### Length -/

theorem pathLength_eq (p : List V) : pathLength p = p.length - 1 := rfl

theorem pathLength_singleton (a : V) : pathLength [a] = 0 := rfl

theorem pathLength_pair (a b : V) : pathLength [a, b] = 1 := rfl

/-- `pathLength` of a cons is the length of the tail.  (No hypothesis is needed:
`(a :: q).length - 1 = q.length` holds also for `q = []`.) -/
theorem pathLength_cons (a : V) (q : List V) : pathLength (a :: q) = q.length := by
  simp [pathLength]

/-- For an actual path (which is non-empty) the natural subtraction in `pathLength`
can be undone. -/
theorem length_eq_pathLength_add_one (h : IsPathList G p) : p.length = pathLength p + 1 := by
  have := path_length_pos h
  simp only [pathLength]
  omega

/-! ### Reversal -/

/-- The reverse of a path is a path. -/
theorem isPathList_reverse (h : IsPathList G p) : IsPathList G p.reverse := by
  obtain ⟨hne, hnd, hadj⟩ := h
  refine ⟨by simpa using hne, by simpa using hnd, ?_⟩
  intro i j hi hj
  have hi' : i < p.length := by simpa using hi
  have hj' : j < p.length := by simpa using hj
  simp only [List.getElem_reverse]
  refine (hadj (p.length - 1 - i) (p.length - 1 - j) (by omega) (by omega)).trans ?_
  omega

theorem pathLength_reverse (p : List V) : pathLength p.reverse = pathLength p := by
  simp [pathLength]

/-- Reversing a path from `u` to `v` gives a path from `v` to `u`.  This is the
formal content of the paper's frequent "from the symmetry we may assume". -/
theorem isPathFrom_reverse (h : IsPathFrom G p u v) : IsPathFrom G p.reverse v u :=
  ⟨isPathList_reverse h.1, by rw [List.head?_reverse]; exact h.2.2,
    by rw [List.getLast?_reverse]; exact h.2.1⟩

/-! ### Sub-paths

The paper writes `p_i-⋯-p_j` for a stretch of a path.  In the 0-based list encoding
that stretch is `(p.drop i).take (j - i + 1)`. -/

/-- Any non-empty initial segment of a path is a path. -/
theorem isPathList_take (h : IsPathList G p) {k : ℕ} (hk : 0 < k) :
    IsPathList G (p.take k) := by
  obtain ⟨hne, hnd, hadj⟩ := h
  refine ⟨?_, List.Nodup.sublist (List.take_sublist k p) hnd, ?_⟩
  · rw [Ne, List.take_eq_nil_iff, not_or]
    exact ⟨by omega, hne⟩
  · intro i j hi hj
    have hle : (p.take k).length ≤ p.length := by simp only [List.length_take]; omega
    have hik : i < p.length := lt_of_lt_of_le hi hle
    have hjk : j < p.length := lt_of_lt_of_le hj hle
    simp only [List.getElem_take]
    exact hadj i j hik hjk

/-- Any non-empty final segment of a path is a path. -/
theorem isPathList_drop (h : IsPathList G p) {k : ℕ} (hk : k < p.length) :
    IsPathList G (p.drop k) := by
  obtain ⟨hne, hnd, hadj⟩ := h
  have hlen : (p.drop k).length = p.length - k := List.length_drop
  refine ⟨?_, List.Nodup.sublist (List.drop_sublist k p) hnd, ?_⟩
  · intro hc
    have h0 : (p.drop k).length = 0 := by rw [hc]; rfl
    omega
  · intro i j hi hj
    have hik : k + i < p.length := by omega
    have hjk : k + j < p.length := by omega
    simp only [List.getElem_drop]
    refine (hadj (k + i) (k + j) hik hjk).trans ?_
    omega

/-- The stretch of a path running from position `i` to position `j` (0-based,
inclusive at both ends — the paper's `p_{i+1}-⋯-p_{j+1}`) is itself a path. -/
theorem isPathList_slice (h : IsPathList G p) {i j : ℕ} (hij : i < j) (hj : j < p.length) :
    IsPathList G ((p.drop i).take (j - i + 1)) :=
  isPathList_take (isPathList_drop h (by omega)) (by omega)

theorem length_slice (p : List V) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    ((p.drop i).take (j - i + 1)).length = j - i + 1 := by
  simp only [List.length_take, List.length_drop]
  omega

theorem getElem_slice (p : List V) {i j k : ℕ}
    (h : k < ((p.drop i).take (j - i + 1)).length) :
    ((p.drop i).take (j - i + 1))[k] =
      p[i + k]'(by simp only [List.length_take, List.length_drop] at h; omega) := by
  simp only [List.getElem_take, List.getElem_drop]

/-- Index transfer for a slice with the *target* index supplied as a separate
variable `m`.  Stating it this way (rather than as `slice[k] = p[i + k]`) is what
avoids all `i + k` normalisation pain at call sites: one passes `m` in whatever
form the ambient goal already has it, and discharges `m = i + k` by `omega`. -/
theorem getElem_slice' (p : List V) {i j k m : ℕ}
    (hk : k < ((p.drop i).take (j - i + 1)).length) (hm : m < p.length) (h : m = i + k) :
    ((p.drop i).take (j - i + 1))[k]'hk = p[m]'hm := by
  subst h
  simp only [List.getElem_take, List.getElem_drop]

/-- The first vertex of the stretch from position `i` to position `j` is `p_i`. -/
theorem head?_slice (p : List V) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    ((p.drop i).take (j - i + 1)).head? = some (p[i]'(by omega)) := by
  have hlen := length_slice p hij hj
  have h0 : 0 < ((p.drop i).take (j - i + 1)).length := by omega
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem h0]
  exact congrArg some (getElem_slice' p h0 (by omega) (by omega))

/-- The last vertex of the stretch from position `i` to position `j` is `p_j`. -/
theorem getLast?_slice (p : List V) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    ((p.drop i).take (j - i + 1)).getLast? = some (p[j]'hj) := by
  have hlen := length_slice p hij hj
  have h0 : ((p.drop i).take (j - i + 1)).length - 1 <
      ((p.drop i).take (j - i + 1)).length := by omega
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem h0]
  exact congrArg some (getElem_slice' p h0 hj (by omega))

/-- The stretch of a path running from position `i` to position `j` is a path
**with named ends** — the paper's `p_{i+1}-P-p_{j+1}`.  This is
`isPathList_slice` together with `head?_slice` and `getLast?_slice`. -/
theorem isPathFrom_slice (h : IsPathList G p) {i j : ℕ} (hij : i < j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) :=
  ⟨isPathList_slice h hij hj, head?_slice p (le_of_lt hij) hj,
    getLast?_slice p (le_of_lt hij) hj⟩

/-- Membership decoder for a stretch: its vertices are exactly the `p_k` with
`i ≤ k ≤ j`.  No path hypothesis is needed — this is pure list surgery. -/
theorem mem_slice_iff (p : List V) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) {x : V} :
    x ∈ (p.drop i).take (j - i + 1) ↔
      ∃ (k : ℕ) (hk : k < p.length), i ≤ k ∧ k ≤ j ∧ p[k]'hk = x := by
  have hlen := length_slice p hij hj
  constructor
  · intro hx
    obtain ⟨n, hn, hnx⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i + n, by omega, by omega, by omega, ?_⟩
    rw [← hnx]
    exact (getElem_slice' p hn (by omega) rfl).symm
  · rintro ⟨k, hk, h1, h2, rfl⟩
    exact List.mem_iff_getElem.mpr
      ⟨k - i, by omega, getElem_slice' p (by omega) hk (by omega)⟩

/-- Interior decoder for a stretch: the interior of `p_{i+1}-P-p_{j+1}` consists
of the `p_k` with `i < k < j`. -/
theorem interior_eq (p : List V) : SPGT.interior p = p.tail.dropLast := rfl

theorem interior_eq_drop_take (p : List V) :
    SPGT.interior p = (p.drop 1).take (p.length - 2) := by
  rw [interior_eq, List.drop_one, List.dropLast_eq_take, List.length_tail]
  congr 1

/-- Membership in `dropLast`, for lists without repetition. -/
theorem mem_dropLast_iff {l : List V} (hnd : l.Nodup) (hne : l ≠ []) {x : V} :
    x ∈ l.dropLast ↔ x ∈ l ∧ x ≠ l.getLast hne := by
  have hsplit := List.dropLast_append_getLast hne
  have hnd' : (l.dropLast ++ [l.getLast hne]).Nodup := by rw [hsplit]; exact hnd
  rw [List.nodup_append] at hnd'
  constructor
  · intro hx
    refine ⟨by rw [← hsplit]; simp [hx], ?_⟩
    rintro rfl
    exact hnd'.2.2 _ hx _ (List.mem_singleton_self _) rfl
  · rintro ⟨hx, hne'⟩
    rw [← hsplit] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    tauto

/-- The interior of a repetition-free list consists of its members that are neither
the first nor the last one.  Stated with `head?`/`getLast?`, so no non-emptiness
side condition is needed; `Nodup` **is** needed (for `[a,b,a,c]` the vertex `a` lies
in `p.tail.dropLast` yet is also the head). -/
theorem mem_interior_iff (hnd : p.Nodup) {x : V} :
    x ∈ SPGT.interior p ↔ (x ∈ p ∧ p.head? ≠ some x ∧ p.getLast? ≠ some x) := by
  rcases p with _ | ⟨a, t⟩
  · simp [interior_eq]
  · rcases eq_or_ne t [] with rfl | ht
    · refine ⟨fun hx => absurd hx (by simp [interior_eq]), ?_⟩
      rintro ⟨hx, hha, -⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hha
      exact absurd hx.symm hha
    · rw [interior_eq]
      simp only [List.tail_cons]
      rw [mem_dropLast_iff hnd.of_cons ht, List.head?_cons,
        List.getLast?_cons_of_ne_nil ht, List.getLast?_eq_some_getLast ht]
      have hat : a ∉ t := (List.nodup_cons.mp hnd).1
      simp only [ne_eq, Option.some.injEq]
      constructor
      · rintro ⟨hx, hxl⟩
        refine ⟨List.mem_cons_of_mem _ hx, ?_, fun hc => hxl hc.symm⟩
        rintro rfl
        exact hat hx
      · rintro ⟨hx, hha, hgl⟩
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact absurd rfl hha
        · exact ⟨hx', fun hc => hgl hc.symm⟩

/-- Interior membership for a path with named ends. -/
theorem mem_interior_iff_of_pathFrom (h : IsPathFrom G p u v) {x : V} :
    x ∈ SPGT.interior p ↔ (x ∈ p ∧ x ≠ u ∧ x ≠ v) := by
  rw [mem_interior_iff (path_nodup h.1), h.2.1, h.2.2]
  simp only [ne_eq, Option.some.injEq]
  constructor
  · rintro ⟨ha, hb, hc⟩; exact ⟨ha, fun e => hb e.symm, fun e => hc e.symm⟩
  · rintro ⟨ha, hb, hc⟩; exact ⟨ha, fun e => hb e.symm, fun e => hc e.symm⟩

theorem interior_subset {x : V} (h : x ∈ SPGT.interior p) : x ∈ p :=
  (List.tail_sublist p).subset ((List.dropLast_sublist p.tail).subset h)

theorem interior_length (p : List V) : (SPGT.interior p).length = p.length - 2 := by
  rw [interior_eq, List.length_dropLast, List.length_tail]
  omega

/-- The interior is reversal-symmetric — the paper uses this silently whenever it
says "from the symmetry we may assume". -/
theorem interior_reverse (p : List V) :
    SPGT.interior p.reverse = (SPGT.interior p).reverse := by
  rw [interior_eq, interior_eq, List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

/-- Consequently membership in the interior is reversal-invariant. -/
theorem mem_interior_reverse {x : V} : x ∈ SPGT.interior p.reverse ↔ x ∈ SPGT.interior p := by
  rw [interior_reverse, List.mem_reverse]

/-- The vertex of a path at a position strictly between the two extreme positions
is an interior vertex.  (Section proofs re-derive this by hand constantly; the
index side conditions are `1 ≤ k` and `k ≤ p.length - 2`, stated without natural
subtraction.) -/
theorem getElem_mem_interior (h : IsPathList G p) {k : ℕ} (hk : k < p.length)
    (h1 : 1 ≤ k) (h2 : k + 2 ≤ p.length) : (p[k]'hk) ∈ SPGT.interior p := by
  have hpos : 0 < p.length := path_length_pos h
  rw [mem_interior_iff (path_nodup h)]
  refine ⟨List.getElem_mem hk, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
    simp only [ne_eq, Option.some.injEq]
    exact path_ne_of_ne_index h hpos hk (by omega)
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show p.length - 1 < p.length by omega)]
    simp only [ne_eq, Option.some.injEq]
    exact path_ne_of_ne_index h (by omega) hk (by omega)

/-- Conversely, every interior vertex of a path sits at a position strictly
between the two extreme positions.  Together with `getElem_mem_interior` this is
the index-level decoder for `P*`. -/
theorem exists_getElem_of_mem_interior (h : IsPathList G p) {x : V}
    (hx : x ∈ SPGT.interior p) :
    ∃ (k : ℕ) (hk : k < p.length), 1 ≤ k ∧ k + 2 ≤ p.length ∧ (p[k]'hk) = x := by
  have hpos : 0 < p.length := path_length_pos h
  rw [mem_interior_iff (path_nodup h)] at hx
  obtain ⟨hxp, hhd, hlt⟩ := hx
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hxp
  refine ⟨k, hk, ?_, ?_, hkx⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk0
    · exact absurd (by rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos, hkx]) hhd
    · exact hk0
  · by_contra hcon
    have hke : k = p.length - 1 := by omega
    subst hke
    refine hlt ?_
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show p.length - 1 < p.length by omega)]
    exact congrArg some hkx

/-- A path with at least three vertices really does have an interior vertex,
namely the one at position `1`. -/
theorem interior_ne_nil (h : IsPathList G p) (hlen : 3 ≤ p.length) :
    SPGT.interior p ≠ [] := fun hnil => by
  have := getElem_mem_interior h (k := 1) (by omega) le_rfl (by omega)
  rw [hnil] at this
  exact absurd this (List.not_mem_nil)

/-! ### Antipaths -/

theorem isAntipathList_iff : IsAntipathList G p ↔ IsPathList Gᶜ p := Iff.rfl

theorem isAntipathFrom_iff : IsAntipathFrom G p u v ↔ IsPathFrom Gᶜ p u v := Iff.rfl

/-- An antipath of `Gᶜ` is exactly a path of `G`. -/
theorem isAntipathList_compl : IsAntipathList Gᶜ p ↔ IsPathList G p := by
  rw [isAntipathList_iff, compl_compl]

theorem isAntipathFrom_compl : IsAntipathFrom Gᶜ p u v ↔ IsPathFrom G p u v := by
  rw [isAntipathFrom_iff, compl_compl]

theorem isAntipathList_reverse (h : IsAntipathList G p) : IsAntipathList G p.reverse :=
  isPathList_reverse h

theorem isAntipathFrom_reverse (h : IsAntipathFrom G p u v) : IsAntipathFrom G p.reverse v u :=
  isPathFrom_reverse h

theorem antipath_nodup (h : IsAntipathList G p) : p.Nodup := path_nodup h

theorem antipath_ne_nil (h : IsAntipathList G p) : p ≠ [] := path_ne_nil h

/-! ### Ends -/

theorem head_mem (h : p.head? = some u) : u ∈ p := List.mem_of_mem_head? h

theorem getLast_mem (h : p.getLast? = some v) : v ∈ p := List.mem_of_mem_getLast? h

theorem isPathFrom_ends_mem (h : IsPathFrom G p u v) : u ∈ p ∧ v ∈ p :=
  ⟨head_mem h.2.1, getLast_mem h.2.2⟩

theorem getElem_zero_of_head? (h : p.head? = some u) (hlen : 0 < p.length) :
    p[0]'hlen = u := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h
  exact Option.some_injective _ h

theorem getElem_last_of_getLast? (h : p.getLast? = some v) (hlen : 0 < p.length) :
    p[p.length - 1]'(by omega) = v := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (show p.length - 1 < p.length by omega)]
    at h
  exact Option.some_injective _ h

/-- The ends of a path of length `1` are adjacent. -/
theorem isPathFrom_ends_adj_of_length_one (h : IsPathFrom G p u v) (hl : pathLength p = 1) :
    G.Adj u v := by
  obtain ⟨hp, hu, hv⟩ := h
  have hpos : 0 < p.length := path_length_pos hp
  rw [pathLength_eq] at hl
  have h0 : p[0]'hpos = u := getElem_zero_of_head? hu hpos
  have h1 : p[p.length - 1]'(by omega) = v := getElem_last_of_getLast? hv hpos
  rw [← h0, ← h1]
  exact (path_adj_iff hp hpos (by omega)).mpr (by omega)

/-- The ends of a path of length `≥ 1` are distinct. -/
theorem isPathFrom_ends_ne (h : IsPathFrom G p u v) (hl : 1 ≤ pathLength p) : u ≠ v := by
  obtain ⟨hp, hu, hv⟩ := h
  have hpos : 0 < p.length := path_length_pos hp
  rw [pathLength_eq] at hl
  have h0 : p[0]'hpos = u := getElem_zero_of_head? hu hpos
  have h1 : p[p.length - 1]'(by omega) = v := getElem_last_of_getLast? hv hpos
  rw [← h0, ← h1]
  exact path_ne_of_ne_index hp hpos (by omega) (by omega)

theorem mem_interior_slice_iff (h : IsPathList G p) {i j : ℕ} (hij : i < j)
    (hj : j < p.length) {x : V} :
    x ∈ SPGT.interior ((p.drop i).take (j - i + 1)) ↔
      ∃ (k : ℕ) (hk : k < p.length), i < k ∧ k < j ∧ p[k]'hk = x := by
  rw [mem_interior_iff_of_pathFrom (isPathFrom_slice h hij hj),
    mem_slice_iff p (le_of_lt hij) hj]
  constructor
  · rintro ⟨⟨k, hk, h1, h2, rfl⟩, hne1, hne2⟩
    refine ⟨k, hk, ?_, ?_, rfl⟩
    · by_contra hcon
      have hki : k = i := by omega
      subst hki
      exact hne1 rfl
    · by_contra hcon
      have hkj : k = j := by omega
      subst hkj
      exact hne2 rfl
  · rintro ⟨k, hk, h1, h2, rfl⟩
    exact ⟨⟨k, hk, le_of_lt h1, le_of_lt h2, rfl⟩,
      path_ne_of_ne_index h hk (by omega) (by omega),
      path_ne_of_ne_index h hk hj (by omega)⟩

/-! ### Interior -/


end Workspace.ProofLemmas.PathBasics
