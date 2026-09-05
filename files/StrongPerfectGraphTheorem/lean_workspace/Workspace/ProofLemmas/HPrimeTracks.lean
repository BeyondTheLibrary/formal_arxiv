import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.TrackSlice

/-!
# The five extra tracks of 5.3's second subdivision `H'`

Step 2 of 5.3, cross-track branch:

> *"The subgraph `H'` formed by the edges `E(P) ∪ E(Q) ∪ E(R) ∪ {p₁q_n, p_mq₁, p_mq_n}` (and the
> vertices of `H` incident with them) is a subdivision of `K₄`."*

Its four branch-vertices are `r₁ = P[i]`, `r_t = Q[j]`, `p_m = P[m-1]`, `q_n = Q[n-1]`
(`0`-based; `m = P.length`, `n = Q.length`), and its six tracks are `R` together with the five
built here:

| track | list | length (vertices) |
|---|---|---|
| `r₁ → p_m` | `slice P i (m-1)` | `m - i` |
| `r₁ → q_n` | `(slice P 0 i).reverse ++ [Q[n-1]]` | `i + 2` |
| `r_t → p_m` | `(slice Q 0 j).reverse ++ [P[m-1]]` | `j + 2` |
| `r_t → q_n` | `slice Q j (n-1)` | `n - j` |
| `p_m → q_n` | `[P[m-1], Q[n-1]]` | `2` |

so the *edge* counts are `m-1-i`, `i+1`, `j+1`, `n-1-j`, `1`, which with `R`'s `t-1` are the six
numbers `CrossTrackEndgame.cross_track_indices` consumes.

Besides the tracks themselves this returns, for each, a **membership decoder** and an
**interior decoder** phrased in `P`/`Q` indices.  Those are what make the pairwise
interior-disjointness clause of `SubdivisionDatum.IsK4Datum` a set of index comparisons rather
than list surgery.

Both degenerate cases are permitted and are *not* excluded here: `i = 0` (the track `r₁→q_n`
degenerates to the single edge `p₁q_n`) and `i = m-2` (the track `r₁→p_m` degenerates to a single
edge) are possible a priori and are ruled out only later, by the arithmetic core.  This is why
the decoders used are the unconditional ones.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.HPrimeTracks

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*}

/-- A single edge is a track. -/
theorem isTrackFrom_pair {H : SimpleGraph W} {a b : W} (hab : H.Adj a b) :
    IsTrackFrom H [a, b] a b := by
  refine ⟨⟨by simp, by simp [hab.ne], ?_⟩, rfl, rfl⟩
  intro k hk
  have hk2 : k + 1 < 2 := hk
  have hk0 : k = 0 := by omega
  subst hk0
  exact hab

theorem trackInterior_pair (a b : W) : trackInterior [a, b] = [] := rfl

/-- **The five extra tracks of `H'`**, with endpoints, lengths, and membership and interior
decoders. -/
theorem exists_hprime_tracks {H : SimpleGraph W} {P Q : List W} {i j : ℕ}
    (hP : IsTrackList H P) (hQ : IsTrackList H Q)
    (hm : 3 ≤ P.length) (hn : 3 ≤ Q.length)
    (hi : i ≤ P.length - 2) (hj : j ≤ Q.length - 2)
    (hPQ : ∀ x ∈ P, x ∉ Q)
    (e1n : H.Adj (P[0]'(by omega)) (Q[Q.length - 1]'(by omega)))
    (em1 : H.Adj (P[P.length - 1]'(by omega)) (Q[0]'(by omega)))
    (emn : H.Adj (P[P.length - 1]'(by omega)) (Q[Q.length - 1]'(by omega))) :
    ∃ A02 A03 A12 A13 A23 : List W,
      IsTrackFrom H A02 (P[i]'(by omega)) (P[P.length - 1]'(by omega)) ∧
      IsTrackFrom H A03 (P[i]'(by omega)) (Q[Q.length - 1]'(by omega)) ∧
      IsTrackFrom H A12 (Q[j]'(by omega)) (P[P.length - 1]'(by omega)) ∧
      IsTrackFrom H A13 (Q[j]'(by omega)) (Q[Q.length - 1]'(by omega)) ∧
      IsTrackFrom H A23 (P[P.length - 1]'(by omega)) (Q[Q.length - 1]'(by omega)) ∧
      A02.length = P.length - i ∧ A03.length = i + 2 ∧
      A12.length = j + 2 ∧ A13.length = Q.length - j ∧ A23.length = 2 ∧
      (∀ x, x ∈ A02 ↔ ∃ (k : ℕ) (h : k < P.length), i ≤ k ∧ P[k]'h = x) ∧
      (∀ x, x ∈ A03 ↔ (∃ (k : ℕ) (h : k < P.length), k ≤ i ∧ P[k]'h = x) ∨
        x = Q[Q.length - 1]'(by omega)) ∧
      (∀ x, x ∈ A12 ↔ (∃ (k : ℕ) (h : k < Q.length), k ≤ j ∧ Q[k]'h = x) ∨
        x = P[P.length - 1]'(by omega)) ∧
      (∀ x, x ∈ A13 ↔ ∃ (k : ℕ) (h : k < Q.length), j ≤ k ∧ Q[k]'h = x) ∧
      (∀ x, x ∈ A23 ↔ x = P[P.length - 1]'(by omega) ∨ x = Q[Q.length - 1]'(by omega)) ∧
      (∀ x, x ∈ trackInterior A02 ↔
        ∃ (k : ℕ) (h : k < P.length), i < k ∧ k < P.length - 1 ∧ P[k]'h = x) ∧
      (∀ x, x ∈ trackInterior A03 ↔ ∃ (k : ℕ) (h : k < P.length), k < i ∧ P[k]'h = x) ∧
      (∀ x, x ∈ trackInterior A12 ↔ ∃ (k : ℕ) (h : k < Q.length), k < j ∧ Q[k]'h = x) ∧
      (∀ x, x ∈ trackInterior A13 ↔
        ∃ (k : ℕ) (h : k < Q.length), j < k ∧ k < Q.length - 1 ∧ Q[k]'h = x) ∧
      trackInterior A23 = [] := by
  have hPlen : P.length - 1 < P.length := by omega
  have hQlen : Q.length - 1 < Q.length := by omega
  have hiP : i < P.length := by omega
  have hjQ : j < Q.length := by omega
  -- `Q[n-1]` is not on `P`, and `P[m-1]` is not on `Q`
  have hqnP : (Q[Q.length - 1]'hQlen) ∉ (slice P 0 i).reverse := by
    intro hc
    rw [List.mem_reverse] at hc
    exact hPQ _ (mem_of_mem_slice hc) (List.getElem_mem hQlen)
  have hpmQ : (P[P.length - 1]'hPlen) ∉ (slice Q 0 j).reverse := by
    intro hc
    rw [List.mem_reverse] at hc
    exact hPQ _ (List.getElem_mem hPlen) (mem_of_mem_slice hc)
  refine ⟨slice P i (P.length - 1), (slice P 0 i).reverse ++ [Q[Q.length - 1]'hQlen],
    (slice Q 0 j).reverse ++ [P[P.length - 1]'hPlen], slice Q j (Q.length - 1),
    [P[P.length - 1]'hPlen, Q[Q.length - 1]'hQlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- endpoints
  · exact isTrackFrom_slice hP hPlen (by omega)
  · exact isTrackFrom_concat (isTrackFrom_reverse (isTrackFrom_slice hP hiP (by omega))) e1n hqnP
  · exact isTrackFrom_concat (isTrackFrom_reverse (isTrackFrom_slice hQ hjQ (by omega)))
      em1.symm hpmQ
  · exact isTrackFrom_slice hQ hQlen (by omega)
  · exact isTrackFrom_pair emn
  -- lengths
  · rw [length_slice P hPlen (by omega)]; omega
  · rw [List.length_append, List.length_reverse, length_slice P hiP (by omega)]; simp
  · rw [List.length_append, List.length_reverse, length_slice Q hjQ (by omega)]; simp
  · rw [length_slice Q hQlen (by omega)]; omega
  · simp
  -- membership decoders
  · intro x
    rw [mem_slice_iff hPlen (show i ≤ P.length - 1 by omega)]
    constructor
    · rintro ⟨k, hk, h1, -, h2⟩; exact ⟨k, hk, h1, h2⟩
    · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, h1, by omega, h2⟩
  · intro x
    rw [mem_reverse_slice_concat_iff P hiP (by omega)]
    constructor
    · rintro (⟨k, hk, -, h1, h2⟩ | h)
      · exact Or.inl ⟨k, hk, h1, h2⟩
      · exact Or.inr h
    · rintro (⟨k, hk, h1, h2⟩ | h)
      · exact Or.inl ⟨k, hk, by omega, h1, h2⟩
      · exact Or.inr h
  · intro x
    rw [mem_reverse_slice_concat_iff Q hjQ (by omega)]
    constructor
    · rintro (⟨k, hk, -, h1, h2⟩ | h)
      · exact Or.inl ⟨k, hk, h1, h2⟩
      · exact Or.inr h
    · rintro (⟨k, hk, h1, h2⟩ | h)
      · exact Or.inl ⟨k, hk, by omega, h1, h2⟩
      · exact Or.inr h
  · intro x
    rw [mem_slice_iff hQlen (show j ≤ Q.length - 1 by omega)]
    constructor
    · rintro ⟨k, hk, h1, -, h2⟩; exact ⟨k, hk, h1, h2⟩
    · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, h1, by omega, h2⟩
  · intro x; simp
  -- interior decoders
  · intro x
    rw [mem_trackInterior_slice_iff hPlen (show i ≤ P.length - 1 by omega)]
  · intro x
    rw [mem_trackInterior_reverse_concat_iff P hiP (by omega)]
    constructor
    · rintro ⟨k, hk, -, h1, h2⟩; exact ⟨k, hk, h1, h2⟩
    · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, by omega, h1, h2⟩
  · intro x
    rw [mem_trackInterior_reverse_concat_iff Q hjQ (by omega)]
    constructor
    · rintro ⟨k, hk, -, h1, h2⟩; exact ⟨k, hk, h1, h2⟩
    · rintro ⟨k, hk, h1, h2⟩; exact ⟨k, hk, by omega, h1, h2⟩
  · intro x
    rw [mem_trackInterior_slice_iff hQlen (show j ≤ Q.length - 1 by omega)]
  · exact trackInterior_pair _ _

end Workspace.ProofLemmas.HPrimeTracks
