import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.OddWheelParityFacts

/-!
# The rim of a wheel as an index function: shared toolkit for the claims of 16.2

Every claim of the `|F| ≥ 2` line of 16.2 numbers the rim *"`p₁, …, p_n` in order"* and then
argues about arcs of it.  This module is that vocabulary, shared by
`OddWheelAttachmentClaim2`, `OddWheelAttachmentClaim4` and `OddWheelAttachmentEndgame`:
`exists_reorient` (re-present the rim so that a named edge sits at positions `0, 1`), `cyc`
(the rim as a function `ℕ → V`), `arc` (a cyclically consecutive block as a list, with
`arc_isPathFrom`), and `parity_telescope` (the number of `Y`-complete edges along a chain of
rim vertices has the parity of `π` of its two ends).

Original context (retained for reference):

> **(3) If `X₁` has members of opposite wheel-parity then the theorem holds.**

Its printed proof derives a contradiction, so the Lean form
(`OddWheelAttachmentMain.Claim3`) is the negation `¬ HasOpp G C Y X₁`.

This module contains the geometric toolkit the printed argument needs — a re-orientation of the
rim so that the printed numbering `p₁, p₂, …, p_n` is available as an index function, arcs of
the rim as explicit lists, and the parity bookkeeping for `Y`-complete edges along an arc — and
then the proof of claim (3) itself.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.OddWheelAttachmentArcs

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### Re-orienting the rim

The printed proof numbers the rim `p₁, …, p_n` *in order*, starting at `p₁` and running towards
`p₂`.  Since wheel-parity is only ever used here through the two-valued function `π` and the
membership predicate `· ∈ C`, and both are insensitive to how the cyclic list is presented, we
may replace `C` by any rotation of `C` or of `C.reverse`. -/

theorem exists_reorient {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    {u v : V} (hu : u ∈ C) (hv : v ∈ C) (hadj : G.Adj u v) :
    ∃ D : List V, IsHoleList G D ∧ D.length = C.length ∧ (∀ w : V, w ∈ D ↔ w ∈ C) ∧
      ∃ (h0 : 0 < D.length) (h1 : 1 < D.length), D[0]'h0 = u ∧ D[1]'h1 = v := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hnpos : 0 < C.length := by omega
  have hnd : C.Nodup := hC.2.1
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  have hadjij : G.Adj (C[i]'hi) (C[j]'hj) := by rw [hiu, hjv]; exact hadj
  have hfb : j % C.length = (i + 1) % C.length ∨ i % C.length = (j + 1) % C.length := by
    rcases WheelParity.hole_adj_index hC hi hj hadjij with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      rw [Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt (show i + 1 < C.length by omega)]
      omega
    · right
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (show j + 1 < C.length by omega)]
      omega
    · right
      rw [Nat.mod_eq_of_lt hi, h1, h2, show C.length - 1 + 1 = C.length by omega, Nat.mod_self]
    · left
      rw [Nat.mod_eq_of_lt hj, h1, h2, show C.length - 1 + 1 = C.length by omega, Nat.mod_self]
  rcases hfb with hfwd | hbwd
  · -- `v` follows `u`: rotate `C` so that `u` comes first.
    have hlen : (C.rotate i).length = C.length := List.length_rotate C i
    refine ⟨C.rotate i, HoleBasics.isHoleList_rotate hC i, hlen, fun w => List.mem_rotate,
      by omega, by omega, ?_, ?_⟩
    · rw [WheelParity.getElem_rotate_eq (C := C) hnpos (by omega),
        HoleArithmetic.getElem_congr_idx C (Nat.mod_lt _ hnpos) hi
          (by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hi)]
      exact hiu
    · rw [WheelParity.getElem_rotate_eq (C := C) hnpos (by omega),
        HoleArithmetic.getElem_congr_idx C (Nat.mod_lt _ hnpos) hj
          (by rw [show 1 + i = i + 1 by omega, ← hfwd, Nat.mod_eq_of_lt hj])]
      exact hjv
  · -- `u` follows `v`: reverse `C` and rotate.
    have hrlen : C.reverse.length = C.length := List.length_reverse
    have hRhole : IsHoleList G C.reverse := HoleBasics.isHoleList_reverse hC
    have hlen : (C.reverse.rotate (C.length - 1 - i)).length = C.length := by
      rw [List.length_rotate, hrlen]
    have hidx0 : (0 + (C.length - 1 - i)) % C.reverse.length = C.length - 1 - i := by
      rw [hrlen, Nat.zero_add, Nat.mod_eq_of_lt (by omega)]
    have hidx1 : C.length - 1 - ((1 + (C.length - 1 - i)) % C.reverse.length) = j := by
      rw [hrlen]
      by_cases h0 : i = 0
      · have hjn : j = C.length - 1 := by
          rw [h0] at hbwd
          rw [Nat.mod_eq_of_lt (show (0 : ℕ) < C.length by omega)] at hbwd
          by_cases hjl : j + 1 < C.length
          · rw [Nat.mod_eq_of_lt hjl] at hbwd; omega
          · omega
        rw [h0, show 1 + (C.length - 1 - 0) = C.length by omega, Nat.mod_self]
        omega
      · have hji : j + 1 = i := by
          rw [Nat.mod_eq_of_lt hi] at hbwd
          by_cases hjl : j + 1 < C.length
          · rw [Nat.mod_eq_of_lt hjl] at hbwd; omega
          · rw [show j + 1 = C.length by omega, Nat.mod_self] at hbwd; omega
        rw [show 1 + (C.length - 1 - i) = C.length - i by omega,
          Nat.mod_eq_of_lt (show C.length - i < C.length by omega)]
        omega
    refine ⟨C.reverse.rotate (C.length - 1 - i), HoleBasics.isHoleList_rotate hRhole _, hlen,
      fun w => by rw [List.mem_rotate, List.mem_reverse], by omega, by omega, ?_, ?_⟩
    · rw [WheelParity.getElem_rotate_eq (C := C.reverse) (by omega) (by omega),
        HoleArithmetic.getElem_congr_idx C.reverse (Nat.mod_lt _ (by omega))
          (show C.length - 1 - i < C.reverse.length by omega) hidx0,
        List.getElem_reverse,
        HoleArithmetic.getElem_congr_idx C (by omega) hi (by omega)]
      exact hiu
    · rw [WheelParity.getElem_rotate_eq (C := C.reverse) (by omega) (by omega),
        List.getElem_reverse,
        HoleArithmetic.getElem_congr_idx C (by omega) hj (by rw [hrlen] at hidx1 ⊢; omega)]
      exact hjv

/-! ### The rim as an index function -/

/-- `cyc D t` is the paper's `p_{t+1}`: the `t`-th vertex of the re-oriented rim `D`, read
cyclically. -/
noncomputable def cyc (D : List V) (hpos : 0 < D.length) (t : ℕ) : V :=
  D[t % D.length]'(Nat.mod_lt _ hpos)

theorem cyc_eq {D : List V} (hpos : 0 < D.length) {t : ℕ} (ht : t < D.length) :
    cyc D hpos t = D[t]'ht := by
  simp only [cyc]
  exact HoleArithmetic.getElem_congr_idx D _ ht (Nat.mod_eq_of_lt ht)

theorem cyc_mem {D : List V} (hpos : 0 < D.length) (t : ℕ) : cyc D hpos t ∈ D :=
  List.getElem_mem _

theorem cyc_congr {D : List V} (hpos : 0 < D.length) {s t : ℕ} (h : s % D.length = t % D.length) :
    cyc D hpos s = cyc D hpos t := by
  simp only [cyc]
  exact HoleArithmetic.getElem_congr_idx D _ _ h

theorem cyc_inj {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length)
    {s t : ℕ} (h : cyc D hpos s = cyc D hpos t) : s % D.length = t % D.length :=
  (List.Nodup.getElem_inj_iff hD.2.1).mp h

theorem cyc_adj {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length)
    (s t : ℕ) :
    G.Adj (cyc D hpos s) (cyc D hpos t) ↔
      (t % D.length = (s + 1) % D.length ∨ s % D.length = (t + 1) % D.length) := by
  simp only [cyc]
  rw [HoleBasics.hole_adj_iff hD (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos),
    Nat.mod_add_mod, Nat.mod_add_mod]

theorem cyc_surj {D : List V} (hpos : 0 < D.length) {x : V} (hx : x ∈ D) :
    ∃ t, t < D.length ∧ cyc D hpos t = x := by
  obtain ⟨t, ht, hte⟩ := List.getElem_of_mem hx
  exact ⟨t, ht, by rw [cyc_eq hpos ht]; exact hte⟩

/-! ### Arcs of the rim -/

/-- The arc `p_{a+1}-p_{a+2}-⋯-p_{a+L}` of the rim, as a list. -/
noncomputable def arc (D : List V) (hpos : 0 < D.length) (a L : ℕ) : List V :=
  (List.range L).map (fun t => cyc D hpos (a + t))

theorem arc_length {D : List V} (hpos : 0 < D.length) (a L : ℕ) :
    (arc D hpos a L).length = L := by simp [arc]

theorem arc_getElem {D : List V} (hpos : 0 < D.length) {a L t : ℕ}
    (ht : t < (arc D hpos a L).length) :
    (arc D hpos a L)[t]'ht = cyc D hpos (a + t) := by
  simp only [arc, List.getElem_map, List.getElem_range]

theorem mem_arc {D : List V} (hpos : 0 < D.length) {a L : ℕ} {x : V} :
    x ∈ arc D hpos a L ↔ ∃ t, t < L ∧ cyc D hpos (a + t) = x := by
  simp only [arc, List.mem_map, List.mem_range]

theorem arc_isPathList {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D)
    (hpos : 0 < D.length) {a L : ℕ} (hL1 : 1 ≤ L) (hL2 : L + 1 ≤ D.length) :
    IsPathList G (arc D hpos a L) := by
  have hlen : (arc D hpos a L).length = L := arc_length hpos a L
  have hkey : ∀ s t : ℕ, s < L → t < L → (a + s) % D.length = (a + t) % D.length → s = t := by
    intro s t hs ht h
    have h' : s % D.length = t % D.length :=
      Nat.ModEq.add_left_cancel' a (h : (a + s) ≡ (a + t) [MOD D.length])
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    exact h'
  refine ⟨?_, ?_, ?_⟩
  · intro hnil
    rw [hnil] at hlen
    simp at hlen
    omega
  · refine List.Nodup.map_on ?_ List.nodup_range
    intro s hs t ht hst
    rw [List.mem_range] at hs ht
    exact hkey s t hs ht (cyc_inj hD hpos hst)
  · intro s t hs ht
    rw [hlen] at hs ht
    rw [arc_getElem, arc_getElem, cyc_adj hD hpos]
    constructor
    · rintro (h | h)
      · left
        have h' : t % D.length = (s + 1) % D.length :=
          Nat.ModEq.add_left_cancel' a
            (by rw [show a + (s + 1) = a + s + 1 by omega]; exact h)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (show s + 1 < D.length by omega)] at h'
        omega
      · right
        have h' : s % D.length = (t + 1) % D.length :=
          Nat.ModEq.add_left_cancel' a
            (by rw [show a + (t + 1) = a + t + 1 by omega]; exact h)
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (show t + 1 < D.length by omega)] at h'
        omega
    · rintro (h | h)
      · left; rw [show a + t = a + s + 1 by omega]
      · right; rw [show a + s = a + t + 1 by omega]

theorem arc_isPathFrom {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D)
    (hpos : 0 < D.length) {a L : ℕ} (hL1 : 1 ≤ L) (hL2 : L + 1 ≤ D.length) :
    IsPathFrom G (arc D hpos a L) (cyc D hpos a) (cyc D hpos (a + L - 1)) := by
  have hlen : (arc D hpos a L).length = L := arc_length hpos a L
  refine ⟨arc_isPathList hD hpos hL1 hL2, ?_, ?_⟩
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < (arc D hpos a L).length by omega)]
    rw [arc_getElem]
    simp
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (arc D hpos a L).length - 1 < (arc D hpos a L).length by omega)]
    rw [arc_getElem]
    congr 2
    omega

/-! ### Parity of the number of `Y`-complete edges along a chain of rim vertices -/

/-- Along a chain of consecutive rim vertices the number of `Y`-complete edges has the parity of
`π` of the two ends: an edge of the rim is `Y`-complete exactly when its ends have opposite
wheel-parity. -/
theorem parity_telescope {G : SimpleGraph V} {C : List V} {Y : Set V} {π : V → ℕ}
    (hπ2 : ∀ x : V, π x < 2)
    (hstep : ∀ x y : V, x ∈ C → y ∈ C → G.Adj x y → (π x ≠ π y ↔ EdgeComplete G Y x y))
    (f : ℕ → V) (r : ℕ) :
    ∀ s : ℕ, r ≤ s → (∀ t, r ≤ t → t ≤ s → f t ∈ C) →
      (∀ t, r ≤ t → t < s → G.Adj (f t) (f (t + 1))) →
      (((Finset.Ico r s).filter (fun t => EdgeComplete G Y (f t) (f (t + 1)))).card
        + π (f r) + π (f s)) % 2 = 0 := by
  intro s
  induction s with
  | zero =>
      intro hrs _ _
      have hr0 : r = 0 := by omega
      subst hr0
      have h1 := hπ2 (f 0)
      simp only [Finset.Ico_self, Finset.filter_empty, Finset.card_empty, Nat.zero_add]
      omega
  | succ s ih =>
      intro hrs hmem hadj
      rcases Nat.lt_or_ge r (s + 1) with hlt | hge
      · have hrs' : r ≤ s := by omega
        have hprev := ih hrs' (fun t h1 h2 => hmem t h1 (by omega))
          (fun t h1 h2 => hadj t h1 (by omega))
        have hIco : Finset.Ico r (s + 1) = insert s (Finset.Ico r s) := by
          ext u
          simp only [Finset.mem_Ico, Finset.mem_insert]
          omega
        have hnotmem : s ∉ Finset.Ico r s := by simp
        have hcard :
            ((Finset.Ico r (s + 1)).filter (fun t => EdgeComplete G Y (f t) (f (t + 1)))).card
              = ((Finset.Ico r s).filter (fun t => EdgeComplete G Y (f t) (f (t + 1)))).card
                + (if EdgeComplete G Y (f s) (f (s + 1)) then 1 else 0) := by
          rw [hIco, Finset.filter_insert]
          by_cases hE : EdgeComplete G Y (f s) (f (s + 1))
          · rw [if_pos hE, if_pos hE, Finset.card_insert_of_notMem
              (fun hc => hnotmem (Finset.mem_of_mem_filter _ hc))]
          · rw [if_neg hE, if_neg hE, Nat.add_zero]
        have hms : f s ∈ C := hmem s (by omega) (by omega)
        have hms1 : f (s + 1) ∈ C := hmem (s + 1) (by omega) (by omega)
        have hstep' := hstep (f s) (f (s + 1)) hms hms1 (hadj s (by omega) (by omega))
        have h1 := hπ2 (f r)
        have h2 := hπ2 (f s)
        have h3 := hπ2 (f (s + 1))
        rw [hcard]
        by_cases hE : EdgeComplete G Y (f s) (f (s + 1))
        · rw [if_pos hE]
          have : π (f s) ≠ π (f (s + 1)) := hstep'.mpr hE
          omega
        · rw [if_neg hE]
          have : π (f s) = π (f (s + 1)) := by
            by_contra hc
            exact hE (hstep'.mp hc)
          omega
      · have hre : r = s + 1 := by omega
        subst hre
        have h1 := hπ2 (f (s + 1))
        simp only [Finset.Ico_self, Finset.filter_empty, Finset.card_empty, Nat.zero_add]
        omega

/-! ### `%`-free hole adjacency, and the absence of triangles -/

/-- The `%`-free reading of hole adjacency, in `cyc` terms.  Per the standing recipe, the `%`
is eliminated inside `WheelParity.hole_adj_index` *before* the disjunction is split, so every
downstream use is a single `omega`. -/
theorem cyc_adj_index {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D)
    (hpos : 0 < D.length) {s t : ℕ} (hs : s < D.length) (ht : t < D.length)
    (h : G.Adj (cyc D hpos s) (cyc D hpos t)) :
    t = s + 1 ∨ s = t + 1 ∨ (s = 0 ∧ t = D.length - 1) ∨ (t = 0 ∧ s = D.length - 1) := by
  rw [cyc_eq hpos hs, cyc_eq hpos ht] at h
  exact WheelParity.hole_adj_index hD hs ht h

/-- Distinct cyclic positions carry distinct vertices. -/
theorem cyc_ne {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length)
    {s t : ℕ} (hs : s < D.length) (ht : t < D.length) (hst : s ≠ t) :
    cyc D hpos s ≠ cyc D hpos t := by
  intro he
  have hmod := cyc_inj hD hpos he
  rw [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt ht] at hmod
  exact hst hmod

/-- **A hole has no triangle.**  Three pairwise-adjacent positions of a cycle of length `≥ 4`
are impossible; feeding `omega` one `cyc_adj_index` disjunction per edge decides it. -/
theorem no_triangle {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D) (hpos : 0 < D.length)
    {s t r : ℕ} (hs : s < D.length) (ht : t < D.length) (hr : r < D.length)
    (hst : s ≠ t) (hsr : s ≠ r) (htr : t ≠ r)
    (h1 : G.Adj (cyc D hpos s) (cyc D hpos t)) (h2 : G.Adj (cyc D hpos s) (cyc D hpos r))
    (h3 : G.Adj (cyc D hpos t) (cyc D hpos r)) : False := by
  have hn4 : 4 ≤ D.length := hD.1
  have e1 := cyc_adj_index hD hpos hs ht h1
  have e2 := cyc_adj_index hD hpos hs hr h2
  have e3 := cyc_adj_index hD hpos ht hr h3
  omega

end Workspace.ProofLemmas.OddWheelAttachmentArcs
