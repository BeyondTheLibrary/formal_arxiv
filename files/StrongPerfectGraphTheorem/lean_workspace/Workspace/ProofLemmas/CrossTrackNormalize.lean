import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# Normalising the cross track of 5.3

The cross-track branch of Step 2 opens with

> *"So we may assume that there is a track `R` of `H`, say `r₁-⋯-r_t`, from `V(P)` to `V(Q)`, not
> using any of `p₁q₁, p₁q_n, p_mq₁, p_mq_n`.  We may assume that `r₁ ∈ {p₁, …, p_{m−1}}`,
> `r_t ∈ {q₁, …, q_{n−1}}`, and **none of `r₂, …, r_{t−1}` belong to `V(P) ∪ V(Q)`**."*

This module does the last part — replacing `R` by a sub-track meeting `V(P)` and `V(Q)` only at
its two ends — and delivers the ends as *indices* `i`, `j` into `P` and `Q`, which is the form
`HPrimeDatum.exists_hprime_datum` consumes.

Crucially it also records `trackEdges R' ⊆ trackEdges R`, so the hypothesis *"not using any of
the four cross edges"* survives the shortening.  Without that the arithmetic core could not
exclude its first candidate four-cycle, which is exactly the one saying `R` **is** the edge
`p₁q₁`.

The remaining *"we may assume `r₁ ∈ {p₁, …, p_{m−1}}`"* is a reversal of `P` (resp. `Q`) and is
handled where it is needed, since reversing `P` permutes the four cross edges among themselves
and so changes nothing else.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.CrossTrackNormalize

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.TrackSlice

variable {W : Type*}

/-- A sub-track uses only edges of the original track. -/
theorem trackEdges_slice_subset (R : List W) {i j : ℕ} (hj : j < R.length) (hij : i ≤ j) :
    trackEdges (slice R i j) ⊆ trackEdges R := by
  rintro e ⟨k, hk, rfl⟩
  have hlen := length_slice R hj hij
  have hk' : k < (slice R i j).length := by omega
  refine ⟨i + k, by omega, ?_⟩
  rw [getElem_slice R hk' (show i + k < R.length by omega),
    getElem_slice R hk (show i + (k + 1) < R.length by omega),
    getElem_eq_of_index_eq R (show i + (k + 1) = i + k + 1 from by omega)
      (show i + (k + 1) < R.length by omega) (show i + k + 1 < R.length by omega)]

/-- **The normalised cross track.**  A track from a vertex of `P` to a vertex of `Q` contains a
sub-track whose ends are `P[i]` and `Q[j]` and whose interior misses `V(P) ∪ V(Q)` entirely,
using only edges of the original. -/
theorem exists_normalized_cross_track {H : SimpleGraph W} {P Q R : List W} {a b : W}
    (hR : IsTrackFrom H R a b) (haP : a ∈ P) (hbQ : b ∈ Q)
    (hPQ : ∀ x ∈ P, x ∉ Q) :
    ∃ (R' : List W) (i j : ℕ) (hiP : i < P.length) (hjQ : j < Q.length),
      IsTrackFrom H R' (P[i]'hiP) (Q[j]'hjQ) ∧ 2 ≤ R'.length ∧
      (∀ w ∈ trackInterior R', w ∉ P ∧ w ∉ Q) ∧
      trackEdges R' ⊆ trackEdges R := by
  classical
  have hRne : R ≠ [] := hR.1.1
  have hR0 : 0 < R.length := by
    cases R with
    | nil => exact absurd rfl hRne
    | cons _ _ => simp
  have hab : a ≠ b := fun h => hPQ a haP (h ▸ hbQ)
  have ha : (R[0]'hR0) = a := track_head hR hR0
  have hb : (R[R.length - 1]'(by omega)) = b := DegenerateK4Tracks.track_getLast hR hR0
  have hR2 : 2 ≤ R.length := by
    by_contra hc
    exact hab (by rw [← ha, ← hb]; exact getElem_eq_of_index_eq R (by omega) hR0 (by omega))
  obtain ⟨i', j', -, hlt, hle, hi', hj', hiP', hjQ', hclean⟩ :=
    exists_clean_indices (R := R) (A := {x : W | x ∈ P}) (B := {x : W | x ∈ Q})
      (R.length - 1) 0 (R.length - 1) (by omega) (by omega) (by omega)
      (show (R[0]'(by omega)) ∈ {x : W | x ∈ P} by rw [ha]; exact haP)
      (show (R[R.length - 1]'(by omega)) ∈ {x : W | x ∈ Q} by rw [hb]; exact hbQ)
  obtain ⟨ip, hip, hipe⟩ := List.mem_iff_getElem.mp hiP'
  obtain ⟨jq, hjq, hjqe⟩ := List.mem_iff_getElem.mp hjQ'
  refine ⟨slice R i' j', ip, jq, hip, hjq, ?_, ?_, ?_,
    trackEdges_slice_subset R hj' (by omega)⟩
  · rw [hipe, hjqe]
    exact isTrackFrom_slice hR.1 hj' (by omega)
  · rw [length_slice R hj' (by omega)]
    omega
  · intro w hw
    obtain ⟨k, hk, hik, hkj, rfl⟩ := (mem_trackInterior_slice_iff hj' (by omega)).mp hw
    exact hclean k hk hik hkj

end Workspace.ProofLemmas.CrossTrackNormalize
