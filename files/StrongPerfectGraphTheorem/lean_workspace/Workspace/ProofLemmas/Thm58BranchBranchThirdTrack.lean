import Workspace.ProofLemmas.Connectivity58Concat
import Workspace.ProofLemmas.TrackToRungPath

/-!
# The third track of 5.8 (7)

PAPER (5.8 (7), printed p. 28): *"… and there is a third path `R` say from `p₁` to `N_{u₂}` via
`F` and a subpath of `R_{u₂v₂}`."*

Read from the cycle end, that path leaves the cycle at a vertex `w`, runs to the branch
`R_{u₂v₂}` and then along that branch until it first meets an attachment of `p₂`; there it stops,
so that `p₂` sees the rung of the track exactly once, at its far end.  This file builds that
track: a track `S` from the cycle to the branch is prolonged along the branch and then cut at
the first edge which `p₂` sees.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58BranchBranchThirdTrack

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.SubdivisionCounting

variable {V W : Type*} [DecidableEq W] {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}

/-- **The third track.**  `S` runs from the cycle (which it meets only at its first vertex `w`)
to the vertex `q[r]` of the branch `q` (which it meets only there); some edge of `q` at or after
`r` is seen by `p₂`.  The track below leaves the cycle at `w`, follows `S`, then runs along `q`
and stops at the first edge seen by `p₂`. -/
theorem exists_third_track (φ : H.lineGraph ≃g G.induce K) {p₂ : V}
    {q : List W} (hq : IsTrackList H q)
    {cy S : List W} {w y : W} (hS : IsTrackFrom H S w y)
    (hSc : ∀ z ∈ S, z ∈ cy → z = w)
    (hSq : ∀ z ∈ S, z ∈ q → z = y)
    (hcut : ∀ z ∈ q, z ∈ cy → z ∈ S)
    {r : ℕ} (hr : r < q.length) (hry : q[r]'hr = y)
    (hex : ∃ (l : ℕ) (hl : l + 1 < q.length), r ≤ l ∧
      G.Adj p₂ (↑(φ ⟨s(q[l]'(by omega), q[l + 1]'hl), trackEdge_mem_edgeSet hq l hl⟩) : V)) :
    ∃ (T : List W) (hT : IsTrackList H T), 2 ≤ T.length ∧ T.head? = some w ∧
      (∀ z ∈ T, z ∈ cy → z = w) ∧
      ∃ zl, (trackRung φ T hT).getLast? = some zl ∧
        ∀ z ∈ trackRung φ T hT, (G.Adj p₂ z ↔ z = zl) := by
  classical
  obtain ⟨l, hl, hrl, hladj⟩ := hex
  have hSpos : 0 < S.length := List.length_pos_of_ne_nil hS.1.1
  -- the tail of the branch beyond `q[r]`
  set T₂ : List W := TrackSlice.slice q r (q.length - 1) with hT₂def
  have hT₂len : T₂.length = q.length - r := by
    rw [hT₂def, TrackSlice.length_slice q (by omega) (by omega)]; omega
  have hT₂get : ∀ (k : ℕ) (hk : k < T₂.length), T₂[k]'hk = q[r + k]'(by rw [hT₂len] at hk; omega) :=
    fun k hk => TrackSlice.getElem_slice q hk (by rw [hT₂len] at hk; omega)
  have hT₂from : IsTrackFrom H T₂ y (q[q.length - 1]'(by omega)) := by
    have := TrackSlice.isTrackFrom_slice hq (show q.length - 1 < q.length by omega)
      (show r ≤ q.length - 1 by omega)
    rwa [hry] at this
  have hT₂q : ∀ z ∈ T₂, z ∈ q := fun z hz => TrackSlice.mem_of_mem_slice hz
  have hT₂nd : T₂.Nodup := hT₂from.1.2.1
  have hT₂0 : T₂[0]'(by rw [hT₂len]; omega) = y := by
    rw [hT₂get 0 (by rw [hT₂len]; omega),
      getElem_eq_of_index_eq q (show r + 0 = r by omega) (by omega) hr]
    exact hry
  have hynotail : y ∉ T₂.tail := by
    intro hmem
    obtain ⟨i, hi, hie⟩ := List.mem_iff_getElem.mp hmem
    rw [List.length_tail] at hi
    rw [List.getElem_tail] at hie
    have := hT₂nd.getElem_inj_iff (hi := (by omega : i + 1 < T₂.length))
      (hj := (by rw [hT₂len]; omega : 0 < T₂.length)) |>.mp (hie.trans hT₂0.symm)
    omega
  -- the full track: `S` prolonged along the branch
  have hdisjST : ∀ z ∈ S, z ∈ T₂ → z = y := fun z hz hz' => hSq z hz (hT₂q z hz')
  have hTffrom : IsTrackFrom H (S ++ T₂.tail) w (q[q.length - 1]'(by omega)) :=
    Connectivity58Concat.isTrackFrom_append hS hT₂from hdisjST
  have hTflen : (S ++ T₂.tail).length = S.length + (T₂.length - 1) :=
    Connectivity58Concat.length_append S T₂
  have hTfleft : ∀ (i : ℕ) (hi : i < S.length),
      (S ++ T₂.tail)[i]'(by rw [hTflen]; omega) = S[i]'hi :=
    fun i hi => Connectivity58Concat.append_getElem_left S T₂ i hi _
  have hTfright : ∀ (k : ℕ) (hk : k < T₂.length),
      (S ++ T₂.tail)[S.length - 1 + k]'(by rw [hTflen]; omega) = q[r + k]'(by
        rw [hT₂len] at hk; omega) := by
    intro k hk
    rw [Connectivity58Concat.append_getElem_right hS hT₂from k hk (by rw [hTflen]; omega),
      hT₂get k hk]
  have hTf0 : (S ++ T₂.tail)[0]'(by rw [hTflen]; omega) = w := by
    rw [hTfleft 0 hSpos]
    have h' := hS.2.1
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hSpos] at h'
    exact Option.some_injective _ h'
  have hTfcy : ∀ z ∈ S ++ T₂.tail, z ∈ cy → z = w := by
    intro z hz hzcy
    rcases List.mem_append.mp hz with hz' | hz'
    · exact hSc z hz' hzcy
    · exfalso
      have hzq : z ∈ q := hT₂q z (List.mem_of_mem_tail hz')
      exact hynotail (hSq z (hcut z hzq hzcy) hzq ▸ hz')
  -- cut at the first edge that `p₂` sees
  set Q : ℕ → Prop := fun i => ∃ hi : i + 1 < (S ++ T₂.tail).length,
    G.Adj p₂ (↑(φ ⟨s((S ++ T₂.tail)[i]'(by omega), (S ++ T₂.tail)[i + 1]'hi),
      trackEdge_mem_edgeSet hTffrom.1 i hi⟩) : V) with hQdef
  have hiw : S.length - 1 + (l - r) + 1 < (S ++ T₂.tail).length := by
    rw [hTflen, hT₂len]; omega
  have hQw : Q (S.length - 1 + (l - r)) := by
    refine ⟨hiw, ?_⟩
    have e1 : (S ++ T₂.tail)[S.length - 1 + (l - r)]'(by omega) = q[l]'(by omega) := by
      rw [hTfright (l - r) (by rw [hT₂len]; omega),
        getElem_eq_of_index_eq q (show r + (l - r) = l by omega) (by omega) (by omega)]
    have e2 : (S ++ T₂.tail)[S.length - 1 + (l - r) + 1]'hiw = q[l + 1]'hl := by
      rw [getElem_eq_of_index_eq (S ++ T₂.tail)
        (show S.length - 1 + (l - r) + 1 = S.length - 1 + (l - r + 1) by omega) hiw
        (by rw [hTflen, hT₂len]; omega),
        hTfright (l - r + 1) (by rw [hT₂len]; omega),
        getElem_eq_of_index_eq q (show r + (l - r + 1) = l + 1 by omega) (by omega) hl]
    have hedge : s((S ++ T₂.tail)[S.length - 1 + (l - r)]'(by omega),
        (S ++ T₂.tail)[S.length - 1 + (l - r) + 1]'hiw)
        = s(q[l]'(by omega), q[l + 1]'hl) := by rw [e1, e2]
    have := congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hedge :
      (⟨_, trackEdge_mem_edgeSet hTffrom.1 (S.length - 1 + (l - r)) hiw⟩ : H.edgeSet)
        = ⟨_, trackEdge_mem_edgeSet hq l hl⟩)
    simpa only [this] using hladj
  have hQex : ∃ i, Q i := ⟨_, hQw⟩
  obtain ⟨hi₀, hi₀adj⟩ : Q (Nat.find hQex) := Nat.find_spec hQex
  set i₀ : ℕ := Nat.find hQex with hi₀def
  have hmin : ∀ i, i < i₀ → ¬ Q i := fun i hi => Nat.find_min hQex hi
  set T : List W := TrackSlice.slice (S ++ T₂.tail) 0 (i₀ + 1) with hTdef
  have hTlist : IsTrackList H T := TrackSlice.isTrackList_slice hTffrom.1 hi₀ (by omega)
  have hTlen : T.length = i₀ + 2 := by
    rw [hTdef, TrackSlice.length_slice _ hi₀ (by omega)]; omega
  have hTget : ∀ (k : ℕ) (hk : k < T.length),
      T[k]'hk = (S ++ T₂.tail)[k]'(by rw [hTlen] at hk; omega) := by
    intro k hk
    have h1 : T[k]'hk = (S ++ T₂.tail)[0 + k]'(by rw [hTlen] at hk; omega) :=
      TrackSlice.getElem_slice (S ++ T₂.tail) hk (by rw [hTlen] at hk; omega)
    rw [h1]
    exact getElem_eq_of_index_eq _ (by omega) _ _
  refine ⟨T, hTlist, by omega, ?_, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega : 0 < T.length),
      hTget 0 (by omega), hTf0]
  · intro z hz hzcy
    exact hTfcy z (TrackSlice.mem_of_mem_slice hz) hzcy
  · -- the rung of the cut track
    have hRlen : (trackRung φ T hTlist).length = i₀ + 1 := by
      rw [trackRung_length]; simp only [trackLength]; omega
    have hRget : ∀ (k : ℕ) (hk : k + 1 < (S ++ T₂.tail).length) (hki : k ≤ i₀),
        (trackRung φ T hTlist)[k]'(by rw [hRlen]; omega)
          = (↑(φ ⟨s((S ++ T₂.tail)[k]'(by omega), (S ++ T₂.tail)[k + 1]'hk),
              trackEdge_mem_edgeSet hTffrom.1 k hk⟩) : V) := by
      intro k hk hki
      rw [trackRung_getElem φ T hTlist k (by rw [hRlen]; omega) (by rw [hTlen]; omega)
        (trackEdge_mem_edgeSet hTlist k (by rw [hTlen]; omega))]
      have e1 : T[k]'(by rw [hTlen]; omega) = (S ++ T₂.tail)[k]'(by omega) :=
        hTget k (by rw [hTlen]; omega)
      have e2 : T[k + 1]'(by rw [hTlen]; omega) = (S ++ T₂.tail)[k + 1]'hk :=
        hTget (k + 1) (by rw [hTlen]; omega)
      have hedge : s(T[k]'(by rw [hTlen]; omega), T[k + 1]'(by rw [hTlen]; omega))
          = s((S ++ T₂.tail)[k]'(by omega), (S ++ T₂.tail)[k + 1]'hk) := by rw [e1, e2]
      exact congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hedge)
    refine ⟨(↑(φ ⟨s((S ++ T₂.tail)[i₀]'(by omega), (S ++ T₂.tail)[i₀ + 1]'hi₀),
        trackEdge_mem_edgeSet hTffrom.1 i₀ hi₀⟩) : V), ?_, ?_⟩
    · rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by rw [hRlen]; omega : (trackRung φ T hTlist).length - 1 <
          (trackRung φ T hTlist).length)]
      congr 1
      rw [getElem_eq_of_index_eq (trackRung φ T hTlist)
        (show (trackRung φ T hTlist).length - 1 = i₀ by rw [hRlen]; omega) (by rw [hRlen]; omega)
        (by rw [hRlen]; omega)]
      exact hRget i₀ hi₀ (le_refl _)
    · intro z hz
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hz
      rw [hRlen] at hk
      have hk' : k + 1 < (S ++ T₂.tail).length := by rw [hTflen] at hi₀ ⊢; omega
      rw [hRget k hk' (by omega)]
      constructor
      · intro hadj
        have : ¬ (k < i₀) := fun hlt => hmin k hlt ⟨hk', hadj⟩
        have hkk : k = i₀ := by omega
        subst hkk
        rfl
      · intro heq
        rw [heq]
        exact hi₀adj

/-- **The third track, either way along the branch.**  The attachment of `p₂` may lie on either
side of the point where `S` meets the branch; running along the branch in the right direction is
the same statement for the reversed branch. -/
theorem exists_third_track_any (φ : H.lineGraph ≃g G.induce K) {p₂ : V}
    {q : List W} (hq : IsTrackList H q)
    {cy S : List W} {w y : W} (hS : IsTrackFrom H S w y)
    (hSc : ∀ z ∈ S, z ∈ cy → z = w)
    (hSq : ∀ z ∈ S, z ∈ q → z = y)
    (hcut : ∀ z ∈ q, z ∈ cy → z ∈ S)
    (hyq : y ∈ q)
    (hex : ∃ (l : ℕ) (hl : l + 1 < q.length),
      G.Adj p₂ (↑(φ ⟨s(q[l]'(by omega), q[l + 1]'hl), trackEdge_mem_edgeSet hq l hl⟩) : V)) :
    ∃ (T : List W) (hT : IsTrackList H T), 2 ≤ T.length ∧ T.head? = some w ∧
      (∀ z ∈ T, z ∈ cy → z = w) ∧
      ∃ zl, (trackRung φ T hT).getLast? = some zl ∧
        ∀ z ∈ trackRung φ T hT, (G.Adj p₂ z ↔ z = zl) := by
  classical
  obtain ⟨l, hl, hladj⟩ := hex
  obtain ⟨r, hr, hry⟩ := List.mem_iff_getElem.mp hyq
  by_cases hrl : r ≤ l
  · exact exists_third_track φ hq hS hSc hSq hcut hr hry ⟨l, hl, hrl, hladj⟩
  · -- run the other way, that is, along the reversed branch
    have hrev : IsTrackList H q.reverse := TrackSlice.isTrackList_reverse hq
    have hrevlen : q.reverse.length = q.length := List.length_reverse
    have hrevget : ∀ (k : ℕ) (hk : k < q.reverse.length),
        q.reverse[k]'hk = q[q.length - 1 - k]'(by rw [hrevlen] at hk; omega) := by
      intro k hk
      rw [List.getElem_reverse]
    have hry' : q.reverse[q.length - 1 - r]'(by rw [hrevlen]; omega) = y := by
      rw [hrevget _ (by rw [hrevlen]; omega),
        getElem_eq_of_index_eq q (show q.length - 1 - (q.length - 1 - r) = r by omega)
          (by omega) hr]
      exact hry
    have hl' : q.length - 2 - l + 1 < q.reverse.length := by rw [hrevlen]; omega
    have he1 : q.reverse[q.length - 2 - l]'(by omega) = q[l + 1]'hl := by
      rw [hrevget _ (by omega),
        getElem_eq_of_index_eq q (show q.length - 1 - (q.length - 2 - l) = l + 1 by omega)
          (by omega) hl]
    have he2 : q.reverse[q.length - 2 - l + 1]'hl' = q[l]'(by omega) := by
      rw [hrevget _ hl',
        getElem_eq_of_index_eq q (show q.length - 1 - (q.length - 2 - l + 1) = l by omega)
          (by omega) (by omega)]
    have hedge : s(q.reverse[q.length - 2 - l]'(by omega), q.reverse[q.length - 2 - l + 1]'hl')
        = s(q[l]'(by omega), q[l + 1]'hl) := by
      rw [he1, he2]; exact Sym2.eq_swap
    have hladj' : G.Adj p₂ (↑(φ ⟨s(q.reverse[q.length - 2 - l]'(by omega),
        q.reverse[q.length - 2 - l + 1]'hl'),
        trackEdge_mem_edgeSet hrev (q.length - 2 - l) hl'⟩) : V) := by
      have := congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hedge :
        (⟨_, trackEdge_mem_edgeSet hrev (q.length - 2 - l) hl'⟩ : H.edgeSet)
          = ⟨_, trackEdge_mem_edgeSet hq l hl⟩)
      simpa only [this] using hladj
    exact exists_third_track φ hrev hS hSc
      (fun z hz hz' => hSq z hz (List.mem_reverse.mp hz'))
      (fun z hz hz' => hcut z (List.mem_reverse.mp hz) hz')
      (by rw [hrevlen]; omega) hry' ⟨q.length - 2 - l, hl', by omega, hladj'⟩

end Workspace.ProofLemmas.Thm58BranchBranchThirdTrack
