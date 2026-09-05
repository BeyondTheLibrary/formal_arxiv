import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Sub-tracks

Step 2 of 5.3 slices tracks constantly.  The second `K₄`-subdivision

> *"The subgraph `H'` formed by the edges `E(P) ∪ E(Q) ∪ E(R) ∪ {p₁q_n, p_mq₁, p_mq_n}` … is a
> subdivision of `K₄`"*

has, as four of its six tracks, the sub-tracks `p_i-⋯-p_m`, `p_i-⋯-p₁`, `q_j-⋯-q₁` and
`q_j-⋯-q_n` of `P` and `Q`; and the normalisation

> *"We may assume that … none of `r₂, …, r_{t−1}` belong to `V(P) ∪ V(Q)`"*

replaces `R` by one of its sub-tracks.

`Workspace.ProofLemmas.PathBasics` has the analogous slicing lemmas for the paper's *paths*, but
they are unusable here: a path is **induced**, a track is not, so `IsPathList` carries an "only
if" direction that `IsTrackList` lacks and the two predicates are independent.  Slicing a track
is strictly easier — `Nodup` passes to sublists and the adjacency clause is a reindexing — so
this module redoes it for `IsTrackList`.

Everything is stated for the concrete slice `slice R i j = (R.drop i).take (j - i + 1)`, the
sub-track running from position `i` to position `j` inclusive.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.TrackSlice

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting

variable {W : Type*}

/-- The sub-track of `R` running from position `i` to position `j` inclusive. -/
def slice (R : List W) (i j : ℕ) : List W := (R.drop i).take (j - i + 1)

theorem length_slice (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) :
    (slice R i j).length = j - i + 1 := by
  simp only [slice, List.length_take, List.length_drop]
  omega

theorem getElem_slice (R : List W) {i j k : ℕ} (hk : k < (slice R i j).length)
    (hk' : i + k < R.length) : (slice R i j)[k]'hk = R[i + k]'hk' := by
  simp only [slice, List.getElem_take, List.getElem_drop]

theorem slice_sublist (R : List W) (i j : ℕ) : List.Sublist (slice R i j) R :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

theorem mem_of_mem_slice {R : List W} {i j : ℕ} {x : W} (h : x ∈ slice R i j) : x ∈ R :=
  (slice_sublist R i j).subset h

/-- A slice of a track is a track. -/
theorem isTrackList_slice {H : SimpleGraph W} {R : List W} (hR : IsTrackList H R)
    {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) : IsTrackList H (slice R i j) := by
  have hlen := length_slice R hj hij
  refine ⟨?_, List.Nodup.sublist (slice_sublist R i j) hR.2.1, ?_⟩
  · intro hc
    rw [hc] at hlen
    simp at hlen
  · intro k hk
    have hkb : k + 1 < j - i + 1 := by rw [hlen] at hk; exact hk
    have h1 : i + k < R.length := by omega
    have h2 : i + (k + 1) < R.length := by omega
    rw [getElem_slice R (by omega) h1, getElem_slice R hk h2]
    exact hR.2.2 (i + k) (by omega)

/-- A slice of a track, with its two ends named. -/
theorem isTrackFrom_slice {H : SimpleGraph W} {R : List W} (hR : IsTrackList H R)
    {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) :
    IsTrackFrom H (slice R i j) (R[i]'(by omega)) (R[j]'hj) := by
  have hlen := length_slice R hj hij
  refine ⟨isTrackList_slice hR hj hij, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    exact congrArg some (getElem_slice R (by omega) (by omega))
  · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    refine congrArg some ?_
    rw [getElem_slice R (by omega) (show i + ((slice R i j).length - 1) < R.length by omega)]
    exact getElem_eq_of_index_eq R (by omega) _ _

/-- Membership in a slice, by index. -/
theorem mem_slice_iff {R : List W} {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) {x : W} :
    x ∈ slice R i j ↔ ∃ (k : ℕ) (h : k < R.length), i ≤ k ∧ k ≤ j ∧ R[k]'h = x := by
  have hlen := length_slice R hj hij
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    exact ⟨i + k, by omega, by omega, by omega, (getElem_slice R hk (by omega)).symm⟩
  · rintro ⟨k, hk, hik, hkj, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨k - i, by omega, ?_⟩
    rw [getElem_slice R (by omega) (show i + (k - i) < R.length by omega)]
    exact getElem_eq_of_index_eq R (by omega) _ _

/-- The internal vertices of a slice, by index: they are the strictly-between positions. -/
theorem mem_trackInterior_slice_iff {R : List W} {i j : ℕ} (hj : j < R.length) (hij : i ≤ j)
    {x : W} :
    x ∈ trackInterior (slice R i j) ↔ ∃ (k : ℕ) (h : k < R.length), i < k ∧ k < j ∧ R[k]'h = x := by
  have hlen := length_slice R hj hij
  rw [mem_trackInterior_iff]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨i + (m + 1), by omega, by omega, by omega,
      (getElem_slice R (by omega) (by omega)).symm⟩
  · rintro ⟨k, hk, hik, hkj, rfl⟩
    refine ⟨k - i - 1, by omega, ?_⟩
    rw [getElem_slice R (by omega) (show i + (k - i - 1 + 1) < R.length by omega)]
    exact getElem_eq_of_index_eq R (by omega) _ _

/-- **Choosing such a track minimal.**

5.3's *"We may assume that `r₁ ∈ {p₁, …, p_{m−1}}`, `r_t ∈ {q₁, …, q_{n−1}}`, and **none of
`r₂, …, r_{t−1}` belong to `V(P) ∪ V(Q)`**"* — and every other *"choose such a path/track
minimal"* in the paper.

Given a position of `R` in `A` strictly before a position in `B`, there is a sub-interval
`[i, j]` of `[i₀, j₀]` whose ends still lie in `A` and `B` and whose **interior positions avoid
both**.  Stated on indices so that no list surgery is needed here; feed `i` and `j` to
`isTrackFrom_slice` and `mem_trackInterior_slice_iff` to get the sub-track itself.

Note `A` and `B` need not be disjoint and need not be anything in particular. -/
theorem exists_clean_indices {R : List W} {A B : Set W} :
    ∀ (d i₀ j₀ : ℕ) (_hd : j₀ - i₀ ≤ d) (hj₀ : j₀ < R.length) (hlt : i₀ < j₀)
      (_hA : R[i₀]'(by omega) ∈ A) (_hB : R[j₀]'hj₀ ∈ B),
      ∃ i j, i₀ ≤ i ∧ i < j ∧ j ≤ j₀ ∧ ∃ (hi : i < R.length) (hj : j < R.length),
        R[i]'hi ∈ A ∧ R[j]'hj ∈ B ∧
        ∀ (k : ℕ) (hk : k < R.length), i < k → k < j → R[k]'hk ∉ A ∧ R[k]'hk ∉ B := by
  classical
  intro d
  induction d with
  | zero => intro i₀ j₀ hd hj₀ hlt _ _; exact absurd hlt (by omega)
  | succ n ih =>
      intro i₀ j₀ hd hj₀ hlt hA hB
      by_cases hbad : ∃ (k : ℕ) (hk : k < R.length),
          i₀ < k ∧ k < j₀ ∧ (R[k]'hk ∈ A ∨ R[k]'hk ∈ B)
      · obtain ⟨k, hk, hik, hkj, hor⟩ := hbad
        rcases hor with hkA | hkB
        · obtain ⟨i, j, h1, h2, h3, hi, hj, h4, h5, h6⟩ :=
            ih k j₀ (by omega) hj₀ (by omega) hkA hB
          exact ⟨i, j, by omega, h2, h3, hi, hj, h4, h5, h6⟩
        · obtain ⟨i, j, h1, h2, h3, hi, hj, h4, h5, h6⟩ :=
            ih i₀ k (by omega) hk hik hA hkB
          exact ⟨i, j, h1, h2, by omega, hi, hj, h4, h5, h6⟩
      · refine ⟨i₀, j₀, le_refl _, hlt, le_refl _, by omega, hj₀, hA, hB, ?_⟩
        intro k hk hik hkj
        exact ⟨fun hc => hbad ⟨k, hk, hik, hkj, Or.inl hc⟩,
          fun hc => hbad ⟨k, hk, hik, hkj, Or.inr hc⟩⟩

/-- **The minimal cross-track, as a track.**

`exists_clean_indices` packaged with `isTrackFrom_slice`: a track meeting `A` strictly before it
meets `B` contains a sub-track whose ends lie in `A` and `B` and whose **interior avoids both**.
This is 5.3's *"So we may assume that there is a track `R` of `H` … from `V(P)` to `V(Q)` … and
none of `r₂, …, r_{t−1}` belong to `V(P) ∪ V(Q)`"*. -/
theorem exists_clean_subtrack {H : SimpleGraph W} {R : List W} (hR : IsTrackList H R)
    {A B : Set W} {i₀ j₀ : ℕ} (hj₀ : j₀ < R.length) (hlt : i₀ < j₀)
    (hA : R[i₀]'(by omega) ∈ A) (hB : R[j₀]'hj₀ ∈ B) :
    ∃ (R' : List W) (a b : W), IsTrackFrom H R' a b ∧ a ∈ A ∧ b ∈ B ∧
      2 ≤ R'.length ∧
      (∀ w ∈ trackInterior R', w ∉ A ∧ w ∉ B) ∧
      (∀ w ∈ R', w ∈ R) := by
  obtain ⟨i, j, h1, h2, h3, hi, hj, hiA, hjB, hclean⟩ :=
    exists_clean_indices (R := R) (A := A) (B := B) (j₀ - i₀) i₀ j₀ le_rfl hj₀ hlt hA hB
  refine ⟨slice R i j, R[i]'hi, R[j]'hj, isTrackFrom_slice hR hj (by omega), hiA, hjB, ?_, ?_,
    fun w hw => mem_of_mem_slice hw⟩
  · rw [length_slice R hj (by omega)]
    omega
  · intro w hw
    obtain ⟨k, hk, hik, hkj, rfl⟩ := (mem_trackInterior_slice_iff hj (by omega)).mp hw
    exact hclean k hk hik hkj

/-! ### Reversing a track, and hanging one more vertex on the end

The six tracks of 5.3's second subdivision `H'` are built from `slice` by exactly two further
operations: reversal (`r₁→q_n` runs *down* `P`) and appending a single vertex across one of the
three retained cross edges.  These are the constructors and the matching interior decoders. -/

theorem isTrackList_reverse {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q) :
    IsTrackList H q.reverse := by
  refine ⟨by simp [hq.1], by simpa using hq.2.1, ?_⟩
  intro i hi
  have hi' : i + 1 < q.length := by simpa using hi
  have hadj := hq.2.2 (q.length - 2 - i) (by omega)
  simp only [List.getElem_reverse]
  rw [getElem_eq_of_index_eq q (show q.length - 1 - i = q.length - 2 - i + 1 by omega)
      (by omega) (by omega),
    getElem_eq_of_index_eq q (show q.length - 1 - (i + 1) = q.length - 2 - i by omega)
      (by omega) (by omega)]
  exact hadj.symm

theorem isTrackFrom_reverse {H : SimpleGraph W} {q : List W} {a b : W}
    (hq : IsTrackFrom H q a b) : IsTrackFrom H q.reverse b a := by
  refine ⟨isTrackList_reverse hq.1, ?_, ?_⟩
  · rw [List.head?_reverse]; exact hq.2.2
  · rw [List.getLast?_reverse]; exact hq.2.1

theorem trackInterior_reverse (q : List W) :
    trackInterior q.reverse = (trackInterior q).reverse := by
  simp only [trackInterior, List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

theorem mem_trackInterior_reverse {q : List W} {w : W} :
    w ∈ trackInterior q.reverse ↔ w ∈ trackInterior q := by
  rw [trackInterior_reverse, List.mem_reverse]

/-- Hanging one further vertex on the far end of a track. -/
theorem isTrackList_concat {H : SimpleGraph W} {q : List W} {b x : W}
    (hq : IsTrackList H q) (hlast : q.getLast? = some b) (hadj : H.Adj b x) (hx : x ∉ q) :
    IsTrackList H (q ++ [x]) := by
  have hqne : 0 < q.length := by
    cases q with
    | nil => exact absurd rfl hq.1
    | cons _ _ => simp
  have hb : q[q.length - 1]'(by omega) = b := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some_injective _ hlast
  refine ⟨by simp, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨hq.2.1, List.nodup_singleton x, ?_⟩
    intro a ha c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact fun hcon => hx (hcon ▸ ha)
  · intro i hi
    have hlen : (q ++ [x]).length = q.length + 1 := by simp
    by_cases hc : i + 1 < q.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left hc]
      exact hq.2.2 i hc
    · have hieq : i = q.length - 1 := by omega
      rw [List.getElem_append_left (by omega), List.getElem_append_right (by omega)]
      rw [getElem_eq_of_index_eq q hieq (by omega) (by omega), hb]
      have : ([x] : List W)[i + 1 - q.length]'(by simp; omega) = x := by
        rw [getElem_eq_of_index_eq [x] (show i + 1 - q.length = 0 by omega) (by simp; omega)
          (by simp)]
        rfl
      rw [this]
      exact hadj

theorem isTrackFrom_concat {H : SimpleGraph W} {q : List W} {a b x : W}
    (hq : IsTrackFrom H q a b) (hadj : H.Adj b x) (hx : x ∉ q) :
    IsTrackFrom H (q ++ [x]) a x := by
  refine ⟨isTrackList_concat hq.1 hq.2.2 hadj hx, ?_, by simp⟩
  rw [List.head?_append, hq.2.1]
  rfl

/-- The interior of `q ++ [x]` is `q` minus its head: the vertex `x` is new, and the old last
vertex of `q` has become internal. -/
theorem trackInterior_concat {q : List W} (hq : q ≠ []) (x : W) :
    trackInterior (q ++ [x]) = q.tail := by
  cases q with
  | nil => exact absurd rfl hq
  | cons a t => simp [trackInterior]

/-! ### `tail` and `dropLast` of a slice are slices

This is what makes the six tracks of 5.3's `H'` tractable: every one of them is a slice, a
reversed slice, or a reversed slice with one pendant vertex, and `trackInterior` of each of those
is again (the reverse of) a **slice**.  So every membership question reduces to `mem_slice_iff`
and there is no bespoke list surgery anywhere. -/

theorem tail_slice (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i < j) :
    (slice R i j).tail = slice R (i + 1) j := by
  have h1 := length_slice R hj (le_of_lt hij)
  have h2 := length_slice R hj (show i + 1 ≤ j by omega)
  refine List.ext_getElem ?_ ?_
  · rw [List.length_tail, h1, h2]
    omega
  · intro k hk1 hk2
    have hb1 : k + 1 < (slice R i j).length := by
      rw [List.length_tail, h1] at hk1; rw [h1]; omega
    have e1 : (slice R i j).tail[k]'hk1 = R[i + (k + 1)]'(by rw [h1] at hb1; omega) := by
      rw [List.getElem_tail]
      exact getElem_slice R hb1 _
    have e2 : (slice R (i + 1) j)[k]'hk2 = R[i + 1 + k]'(by rw [h2] at hk2; omega) :=
      getElem_slice R hk2 _
    rw [e1, e2]
    exact getElem_eq_of_index_eq R (by omega) _ _

theorem dropLast_slice (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i < j) :
    (slice R i j).dropLast = slice R i (j - 1) := by
  have h1 := length_slice R hj (le_of_lt hij)
  have h2 := length_slice R (show j - 1 < R.length by omega) (show i ≤ j - 1 by omega)
  refine List.ext_getElem ?_ ?_
  · rw [List.length_dropLast, h1, h2]
    omega
  · intro k hk1 hk2
    have hb1 : k < (slice R i j).length := by
      rw [List.length_dropLast, h1] at hk1; rw [h1]; omega
    have e1 : (slice R i j).dropLast[k]'hk1 = R[i + k]'(by rw [h1] at hb1; omega) := by
      rw [List.getElem_dropLast]
      exact getElem_slice R hb1 _
    have e2 : (slice R i (j - 1))[k]'hk2 = R[i + k]'(by rw [h2] at hk2; omega) :=
      getElem_slice R hk2 _
    rw [e1, e2]

/-- The interior of a slice is a slice. -/
theorem trackInterior_slice (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i + 1 < j) :
    trackInterior (slice R i j) = slice R (i + 1) (j - 1) := by
  rw [trackInterior, tail_slice R hj (by omega), dropLast_slice R hj (by omega)]

/-- The interior of a **reversed slice with one pendant vertex** — the shape of the two tracks
`r₁→q_n` and `r_t→p_m` of `H'` — is the reverse of a slice.  Membership is then `mem_slice_iff`. -/
theorem trackInterior_reverse_slice_concat (R : List W) {i j : ℕ} (hj : j < R.length)
    (hij : i < j) (y : W) :
    trackInterior ((slice R i j).reverse ++ [y]) = (slice R i (j - 1)).reverse := by
  have hlen := length_slice R hj (le_of_lt hij)
  have hne : (slice R i j).reverse ≠ [] := by
    intro hc
    rw [← List.length_eq_zero_iff, List.length_reverse, hlen] at hc
    omega
  rw [trackInterior_concat hne, List.tail_reverse, dropLast_slice R hj hij]

/-! ### Unconditional membership decoders

`trackInterior_slice` and `trackInterior_reverse_slice_concat` are *equalities*, and so carry the
side condition `i + 1 < j` resp. `i < j`.  In 5.3's `H'` the degenerate cases genuinely occur —
`i = 0` (the track `r₁→q_n` is the single edge `p₁q_n`) and `i = m-2` (the track `r₁→p_m` is the
single edge) are both possible *a priori*, and are only excluded afterwards.  These membership
decoders hold with no such side condition. -/

theorem mem_dropLast_slice_iff (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) {x : W} :
    x ∈ (slice R i j).dropLast ↔ ∃ (k : ℕ) (h : k < R.length), i ≤ k ∧ k < j ∧ R[k]'h = x := by
  have hlen := length_slice R hj hij
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
    have hk' : k < (slice R i j).length := by
      rw [List.length_dropLast, hlen] at hk; rw [hlen]; omega
    have hkb : k < j - i := by rw [List.length_dropLast, hlen] at hk; omega
    refine ⟨i + k, by omega, by omega, by omega, ?_⟩
    rw [← hkx, List.getElem_dropLast]
    exact (getElem_slice R hk' (by omega)).symm
  · rintro ⟨k, hk, hik, hkj, rfl⟩
    have hk' : k - i < (slice R i j).length := by rw [hlen]; omega
    refine List.mem_iff_getElem.mpr ⟨k - i, by rw [List.length_dropLast, hlen]; omega, ?_⟩
    rw [List.getElem_dropLast,
      getElem_slice R hk' (show i + (k - i) < R.length by omega)]
    exact getElem_eq_of_index_eq R (by omega) _ _

/-- The interior of `(slice R i j).reverse ++ [y]` — the shape of `H'`'s tracks `r₁→q_n` and
`r_t→p_m` — is exactly the positions strictly below `j`.  No side condition beyond `i ≤ j`. -/
theorem mem_trackInterior_reverse_concat_iff (R : List W) {i j : ℕ} (hj : j < R.length)
    (hij : i ≤ j) (y : W) {x : W} :
    x ∈ trackInterior ((slice R i j).reverse ++ [y]) ↔
      ∃ (k : ℕ) (h : k < R.length), i ≤ k ∧ k < j ∧ R[k]'h = x := by
  have hlen := length_slice R hj hij
  have hne : (slice R i j).reverse ≠ [] := by
    intro hc
    rw [← List.length_eq_zero_iff, List.length_reverse, hlen] at hc
    omega
  rw [trackInterior_concat hne, List.tail_reverse, List.mem_reverse,
    mem_dropLast_slice_iff R hj hij]

/-- Membership in `(slice R i j).reverse ++ [y]`. -/
theorem mem_reverse_slice_concat_iff (R : List W) {i j : ℕ} (hj : j < R.length)
    (hij : i ≤ j) (y : W) {x : W} :
    x ∈ (slice R i j).reverse ++ [y] ↔
      (∃ (k : ℕ) (h : k < R.length), i ≤ k ∧ k ≤ j ∧ R[k]'h = x) ∨ x = y := by
  rw [List.mem_append, List.mem_reverse, mem_slice_iff hj hij, List.mem_singleton]

end Workspace.ProofLemmas.TrackSlice
