import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics

/-!
# A hole with two "crossing" chord-pairs contains `L(H)` for a bipartite subdivision `H` of `K₄`

Let `C` be a hole of `G` of length `n`, and let `a, b ∉ V(C)` be two non-adjacent vertices, each
having exactly four neighbours on `C`, forming two cyclically consecutive pairs, and arranged so
that the four "gaps" `c₁, c₂, c₃, c₄` (the distances between consecutive attachments around the
rim) satisfy `c₁ + c₂` and `c₁ + c₄` both odd.

Then `V(C) ∪ {a, b}` induces `L(H)`, where `H` is the `n`-cycle `w₀ ⋯ w_{n-1}` together with the
two chords `w₀ w_{c₁+c₂}` and `w_{c₁} w_{c₁+c₂+c₃}`: the rim vertex `C[t]` corresponds to the
cycle edge `w_t w_{t+1}`, `a` to the first chord and `b` to the second.  `H` is a subdivision of
`K₄` (branch vertices `w₀, w_{c₁}, w_{c₁+c₂}, w_{c₁+c₂+c₃}`) and the parity hypotheses make it
bipartite.  Since `G ∈ F₃` forbids exactly this, we obtain a contradiction.

The main export is `not_inF3_of_two_chord_config`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.LineGraphK4Chords

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-! ## The host graph: an `n`-cycle with two chords -/

/-- The `n`-cycle `w₀ - w₁ - ⋯ - w_{n-1} - w₀` together with the two chords `w₀ w_P` and
`w_R w_Q`. -/
def Hg (n P R Q : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((j.val = (i.val + 1) % n ∨ i.val = (j.val + 1) % n) ∨
      (((i.val = 0 ∧ j.val = P) ∨ (j.val = 0 ∧ i.val = P)) ∨
       ((i.val = R ∧ j.val = Q) ∨ (j.val = R ∧ i.val = Q))))
  symm := by
    intro i j h
    exact ⟨h.1.symm, by tauto⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem Hg_adj {n P R Q : ℕ} {i j : Fin n} :
    (Hg n P R Q).Adj i j ↔ i ≠ j ∧ ((j.val = (i.val + 1) % n ∨ i.val = (j.val + 1) % n) ∨
      (((i.val = 0 ∧ j.val = P) ∨ (j.val = 0 ∧ i.val = P)) ∨
       ((i.val = R ∧ j.val = Q) ∨ (j.val = R ∧ i.val = Q)))) := Iff.rfl

/-! ## Cyclic indexing -/

/-- The vertex `w_{m mod n}` of the cycle. -/
def cyc (n : ℕ) [NeZero n] (m : ℕ) : Fin n :=
  ⟨m % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n))⟩

@[simp] theorem cyc_val (n : ℕ) [NeZero n] (m : ℕ) : (cyc n m).val = m % n := rfl

theorem cyc_eq_iff (n : ℕ) [NeZero n] (j k : ℕ) : cyc n j = cyc n k ↔ j % n = k % n :=
  ⟨fun h => congrArg Fin.val h, fun h => Fin.val_injective h⟩

theorem cyc_of_lt (n : ℕ) [NeZero n] {m : ℕ} (h : m < n) : (cyc n m).val = m :=
  Nat.mod_eq_of_lt h

theorem cyc_self (n : ℕ) [NeZero n] (x : Fin n) : cyc n x.val = x :=
  Fin.val_injective (Nat.mod_eq_of_lt x.isLt)

theorem cyc_inj_of_lt (n : ℕ) [NeZero n] {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : cyc n a = cyc n b) : a = b := by
  have := congrArg Fin.val h
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- Successive cycle vertices are adjacent in `Hg`. -/
theorem cyc_adj_succ {n P R Q : ℕ} [NeZero n] (hn : 2 ≤ n) (m : ℕ) :
    (Hg n P R Q).Adj (cyc n m) (cyc n (m + 1)) := by
  have hmod : (m + 1) % n = (m % n + 1) % n := (Nat.mod_add_mod m n 1).symm
  have hlt : m % n < n := Nat.mod_lt _ (by omega)
  refine ⟨?_, Or.inl (Or.inl ?_)⟩
  · intro hc
    have h3 : m % n = (m + 1) % n := (cyc_eq_iff n m (m + 1)).mp hc
    rw [hmod] at h3
    by_cases hc2 : m % n + 1 = n
    · rw [hc2, Nat.mod_self] at h3; omega
    · have h4 : (m % n + 1) % n = m % n + 1 := Nat.mod_eq_of_lt (by omega)
      rw [h4] at h3; omega
  · simp only [cyc_val]
    exact hmod

/-! ## Arcs of the cycle -/

/-- The arc `[w_s, w_{s+1}, …, w_{s+len}]`, a list of `len + 1` vertices. -/
def arc (n : ℕ) [NeZero n] (s len : ℕ) : List (Fin n) :=
  (List.range (len + 1)).map (fun t => cyc n (s + t))

@[simp] theorem arc_length (n : ℕ) [NeZero n] (s len : ℕ) :
    (arc n s len).length = len + 1 := by simp [arc]

theorem arc_getElem (n : ℕ) [NeZero n] (s len : ℕ) {i : ℕ} (h : i < (arc n s len).length) :
    (arc n s len)[i] = cyc n (s + i) := by
  simp only [arc, List.getElem_map, List.getElem_range]

theorem arc_ne_nil (n : ℕ) [NeZero n] (s len : ℕ) : arc n s len ≠ [] := by
  intro h
  have := arc_length n s len
  rw [h] at this
  simp at this

theorem arc_mem_iff (n : ℕ) [NeZero n] (s len : ℕ) (x : Fin n) :
    x ∈ arc n s len ↔ ∃ t, t ≤ len ∧ x = cyc n (s + t) := by
  simp only [arc, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩
  · rintro ⟨t, ht, rfl⟩; exact ⟨t, by omega, rfl⟩

theorem arc_nodup (n : ℕ) [NeZero n] (s len : ℕ) (h : len < n) : (arc n s len).Nodup := by
  refine List.Nodup.map_on ?_ List.nodup_range
  intro x hx y hy hxy
  rw [List.mem_range] at hx hy
  have h1 : (s + x) % n = (s + y) % n := congrArg Fin.val hxy
  have h2 : x % n = y % n := Nat.ModEq.add_left_cancel' s h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  exact h2

theorem arc_head (n : ℕ) [NeZero n] (s len : ℕ) :
    (arc n s len).head? = some (cyc n s) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by rw [arc_length]; omega),
    arc_getElem]
  rfl

theorem arc_last (n : ℕ) [NeZero n] (s len : ℕ) :
    (arc n s len).getLast? = some (cyc n (s + len)) := by
  have hl : (arc n s len).length - 1 = len := by simp
  rw [List.getLast?_eq_getElem?, hl, List.getElem?_eq_getElem (by rw [arc_length]; omega),
    arc_getElem]

theorem arc_interior_mem_iff (n : ℕ) [NeZero n] (s len : ℕ) (x : Fin n) :
    x ∈ trackInterior (arc n s len) ↔ ∃ t, 1 ≤ t ∧ t < len ∧ x = cyc n (s + t) := by
  have hlen : (trackInterior (arc n s len)).length = len - 1 := by
    simp [trackInterior]
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hi2 : i < len - 1 := hlen ▸ hi
    refine ⟨i + 1, by omega, by omega, ?_⟩
    rw [← hix]
    simp only [trackInterior, List.getElem_dropLast, List.getElem_tail, arc_getElem]
  · rintro ⟨t, ht1, ht2, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨t - 1, by rw [hlen]; omega, ?_⟩
    simp only [trackInterior, List.getElem_dropLast, List.getElem_tail, arc_getElem]
    congr 1
    omega

theorem arc_chain {n P R Q : ℕ} [NeZero n] (hn : 2 ≤ n) (s len : ℕ) :
    List.IsChain (Hg n P R Q).Adj (arc n s len) := by
  refine List.isChain_iff_getElem.mpr ?_
  intro i hi
  rw [arc_getElem, arc_getElem]
  exact cyc_adj_succ hn (s + i)

/-! ## Reversal of tracks -/

theorem trackInterior_reverse {W : Type*} (q : List W) :
    trackInterior q.reverse = (trackInterior q).reverse := by
  simp only [trackInterior]
  rw [List.tail_reverse, List.dropLast_reverse, List.tail_dropLast]

theorem isTrackList_reverse {W : Type*} {D : SimpleGraph W} {q : List W}
    (h : IsTrackList D q) : IsTrackList D q.reverse := by
  obtain ⟨hne, hnd, hadj⟩ := h
  refine ⟨?_, List.nodup_reverse.mpr hnd, ?_⟩
  · intro hc
    apply hne
    have : q.reverse.length = 0 := by rw [hc]; rfl
    simpa using this
  · intro i hi
    have hlen : q.reverse.length = q.length := List.length_reverse
    have hi' : i + 1 < q.length := by rw [← hlen]; exact hi
    have gidx : ∀ (a b : ℕ) (ha : a < q.length) (hb : b < q.length), a = b →
        q[a]'ha = q[b]'hb := by rintro a b ha hb rfl; rfl
    have e1 : q.reverse[i]'(by omega) = q[q.length - 1 - i]'(by omega) :=
      List.getElem_reverse _
    have e2 : q.reverse[i + 1]'hi = q[q.length - 1 - (i + 1)]'(by omega) :=
      List.getElem_reverse _
    rw [e1, e2, gidx (q.length - 1 - i) ((q.length - 1 - (i + 1)) + 1) (by omega) (by omega)
      (by omega)]
    exact (hadj (q.length - 1 - (i + 1)) (by omega)).symm

theorem isTrackFrom_reverse {W : Type*} {D : SimpleGraph W} {q : List W} {x y : W}
    (h : IsTrackFrom D q x y) : IsTrackFrom D q.reverse y x := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨isTrackList_reverse h1, ?_, ?_⟩
  · rw [List.head?_reverse]; exact h3
  · rw [List.getLast?_reverse]; exact h2

/-! ## The four branch vertices, the six tracks -/

section Tracks

variable {n P R Q : ℕ} [NeZero n]

/-- The cyclic positions of the four branch vertices: `0 < R < P < Q < n`. -/
def bp (P R Q : ℕ) (u : Fin 4) : ℕ :=
  if u = 0 then 0 else if u = 1 then R else if u = 2 then P else Q

@[simp] theorem bp_zero (P R Q : ℕ) : bp P R Q 0 = 0 := rfl
@[simp] theorem bp_one (P R Q : ℕ) : bp P R Q 1 = R := rfl
@[simp] theorem bp_two (P R Q : ℕ) : bp P R Q 2 = P := rfl
@[simp] theorem bp_three (P R Q : ℕ) : bp P R Q 3 = Q := rfl

theorem fin4_cases : ∀ u : Fin 4, u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by decide

theorem bp_lt (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n) (u : Fin 4) :
    bp P R Q u < n := by
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    simp only [bp_zero, bp_one, bp_two, bp_three] <;> omega

/-- The branch-vertex embedding `V(K₄) → V(H)`. -/
def iot (n P R Q : ℕ) [NeZero n] (u : Fin 4) : Fin n := cyc n (bp P R Q u)

@[simp] theorem iot_zero : iot n P R Q 0 = cyc n 0 := rfl
@[simp] theorem iot_one : iot n P R Q 1 = cyc n R := rfl
@[simp] theorem iot_two : iot n P R Q 2 = cyc n P := rfl
@[simp] theorem iot_three : iot n P R Q 3 = cyc n Q := rfl

/-- The six tracks of the subdivision, in both orientations. -/
def Tr (n P R Q : ℕ) [NeZero n] (u v : Fin 4) : List (Fin n) :=
  if u = 0 ∧ v = 1 then arc n 0 R
  else if u = 1 ∧ v = 0 then (arc n 0 R).reverse
  else if u = 1 ∧ v = 2 then arc n R (P - R)
  else if u = 2 ∧ v = 1 then (arc n R (P - R)).reverse
  else if u = 2 ∧ v = 3 then arc n P (Q - P)
  else if u = 3 ∧ v = 2 then (arc n P (Q - P)).reverse
  else if u = 3 ∧ v = 0 then arc n Q (n - Q)
  else if u = 0 ∧ v = 3 then (arc n Q (n - Q)).reverse
  else if u = 0 ∧ v = 2 then [cyc n 0, cyc n P]
  else if u = 2 ∧ v = 0 then [cyc n P, cyc n 0]
  else if u = 1 ∧ v = 3 then [cyc n R, cyc n Q]
  else if u = 3 ∧ v = 1 then [cyc n Q, cyc n R]
  else []

@[simp] theorem Tr_01 : Tr n P R Q 0 1 = arc n 0 R := rfl
@[simp] theorem Tr_10 : Tr n P R Q 1 0 = (arc n 0 R).reverse := rfl
@[simp] theorem Tr_12 : Tr n P R Q 1 2 = arc n R (P - R) := rfl
@[simp] theorem Tr_21 : Tr n P R Q 2 1 = (arc n R (P - R)).reverse := rfl
@[simp] theorem Tr_23 : Tr n P R Q 2 3 = arc n P (Q - P) := rfl
@[simp] theorem Tr_32 : Tr n P R Q 3 2 = (arc n P (Q - P)).reverse := rfl
@[simp] theorem Tr_30 : Tr n P R Q 3 0 = arc n Q (n - Q) := rfl
@[simp] theorem Tr_03 : Tr n P R Q 0 3 = (arc n Q (n - Q)).reverse := rfl
@[simp] theorem Tr_02 : Tr n P R Q 0 2 = [cyc n 0, cyc n P] := rfl
@[simp] theorem Tr_20 : Tr n P R Q 2 0 = [cyc n P, cyc n 0] := rfl
@[simp] theorem Tr_13 : Tr n P R Q 1 3 = [cyc n R, cyc n Q] := rfl
@[simp] theorem Tr_31 : Tr n P R Q 3 1 = [cyc n Q, cyc n R] := rfl

/-- The four open arcs of cyclic positions strictly between consecutive branch vertices. -/
def IntV (n P R Q : ℕ) (u v : Fin 4) (k : ℕ) : Prop :=
  (((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)) ∧ 0 < k ∧ k < R) ∨
  (((u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)) ∧ R < k ∧ k < P) ∨
  (((u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2)) ∧ P < k ∧ k < Q) ∨
  (((u = 3 ∧ v = 0) ∨ (u = 0 ∧ v = 3)) ∧ Q < k ∧ k < n)

theorem IntV_symm {u v : Fin 4} {k : ℕ} (h : IntV n P R Q u v k) : IntV n P R Q v u k := by
  unfold IntV at h ⊢; tauto

/-- The `K₄`-edge whose track carries the cyclic position `k`. -/
def whichE (P R Q : ℕ) (k : ℕ) : Sym2 (Fin 4) :=
  if k < R then s(0, 1) else if k < P then s(1, 2) else if k < Q then s(2, 3) else s(3, 0)

theorem IntV_which (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)
    {u v : Fin 4} {k : ℕ} (h : IntV n P R Q u v k) : s(u, v) = whichE P R Q k := by
  unfold IntV at h
  unfold whichE
  rcases h with ⟨hp, hk⟩ | ⟨hp, hk⟩ | ⟨hp, hk⟩ | ⟨hp, hk⟩
  · rw [if_pos (by omega : k < R)]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  · rw [if_neg (by omega : ¬ k < R), if_pos (by omega : k < P)]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  · rw [if_neg (by omega : ¬ k < R), if_neg (by omega : ¬ k < P), if_pos (by omega : k < Q)]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap
  · rw [if_neg (by omega : ¬ k < R), if_neg (by omega : ¬ k < P), if_neg (by omega : ¬ k < Q)]
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact Sym2.eq_swap

theorem IntV_avoid (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)
    {u v : Fin 4} {k : ℕ} (h : IntV n P R Q u v k) :
    k ≠ 0 ∧ k ≠ R ∧ k ≠ P ∧ k ≠ Q := by
  unfold IntV at h
  rcases h with ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩ | ⟨-, hk⟩ <;> omega

theorem IntV_ne_bp (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)
    {u v : Fin 4} {k : ℕ} (h : IntV n P R Q u v k) (x : Fin 4) : k ≠ bp P R Q x := by
  obtain ⟨e0, e1, e2, e3⟩ := IntV_avoid h0R hRP hPQ hQn h
  rcases fin4_cases x with rfl | rfl | rfl | rfl <;>
    simp only [bp_zero, bp_one, bp_two, bp_three] <;> assumption

/-! ### The enumeration of ordered pairs of distinct `K₄`-vertices -/

theorem fin4_pairs (u v : Fin 4) (huv : u ≠ v) :
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) ∨
    (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) ∨ (u = 3 ∧ v = 0) ∨ (u = 0 ∧ v = 3) ∨
    (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) ∨ (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) := by
  revert huv
  revert u v
  decide

end Tracks

/-! ## Per-pair verification of the track axioms -/

section TrackFacts

variable {n P R Q : ℕ} [NeZero n]

theorem isTrackFrom_arc (hn2 : 2 ≤ n) (s len e : ℕ) (hlen : len < n)
    (he : e % n = (s + len) % n) :
    IsTrackFrom (Hg n P R Q) (arc n s len) (cyc n s) (cyc n e) := by
  refine ⟨⟨arc_ne_nil n s len, arc_nodup n s len hlen, ?_⟩, arc_head n s len, ?_⟩
  · intro i hi
    rw [arc_getElem, arc_getElem]
    exact cyc_adj_succ hn2 (s + i)
  · rw [arc_last]
    exact congrArg some ((cyc_eq_iff n (s + len) e).mpr he.symm)

theorem isTrackFrom_pair {a b : ℕ} (hab : (Hg n P R Q).Adj (cyc n a) (cyc n b)) :
    IsTrackFrom (Hg n P R Q) [cyc n a, cyc n b] (cyc n a) (cyc n b) := by
  refine ⟨⟨by simp, by simp [hab.ne], ?_⟩, rfl, by simp⟩
  intro i hi
  have hlen : ([cyc n a, cyc n b] : List (Fin n)).length = 2 := rfl
  have hi0 : i = 0 := by omega
  subst hi0
  exact hab

theorem arc_val_mem (s len e : ℕ) (hs : s < n) (hsl : s + len ≤ n) (he : e = (s + len) % n)
    {w : Fin n} (hw : w ∈ arc n s len) :
    w.val = s ∨ w.val = e ∨ (s < w.val ∧ w.val < s + len) := by
  rw [arc_mem_iff] at hw
  obtain ⟨t, ht, rfl⟩ := hw
  simp only [cyc_val]
  rcases (by omega : t = 0 ∨ t = len ∨ (0 < t ∧ t < len)) with h | h | ⟨h1, h2⟩
  · left; rw [h, Nat.add_zero]; exact Nat.mod_eq_of_lt hs
  · right; left; rw [h, he]
  · right; right
    have hm : (s + t) % n = s + t := Nat.mod_eq_of_lt (by omega)
    rw [hm]; omega

/-! ### Small facts about interiors of `Nodup` lists -/

theorem mem_of_mem_trackInterior {W : Type*} {l : List W} {w : W} (h : w ∈ trackInterior l) :
    w ∈ l := List.tail_subset _ (List.dropLast_subset _ h)

theorem ne_head_of_mem_trackInterior {W : Type*} {l : List W} {u w : W} (hnd : l.Nodup)
    (hh : l.head? = some u) (hw : w ∈ trackInterior l) : w ≠ u := by
  intro hwu
  have hcons : u :: l.tail = l := List.cons_head?_tail hh
  have hnd' : (u :: l.tail).Nodup := by rw [hcons]; exact hnd
  refine (List.nodup_cons.mp hnd').1 ?_
  rw [← hwu]
  exact List.dropLast_subset _ hw

theorem ne_getLast_of_mem_trackInterior {W : Type*} {l : List W} {v w : W} (hnd : l.Nodup)
    (hl : l.getLast? = some v) (hw : w ∈ trackInterior l) : w ≠ v := by
  intro hwv
  have hcons : l.dropLast ++ [v] = l := List.dropLast_append_getLast? v hl
  have hnd' : (l.dropLast ++ [v]).Nodup := by rw [hcons]; exact hnd
  refine (List.nodup_append.mp hnd').2.2 v ?_ v (List.mem_singleton_self v) rfl
  rw [← hwv]
  have hw' : w ∈ l.dropLast.tail := by
    rw [List.tail_dropLast]
    exact hw
  exact List.tail_subset _ hw'

/-! ### The twelve tracks -/

variable (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)

include h0R hRP hPQ hQn

theorem chord_one_adj : (Hg n P R Q).Adj (cyc n 0) (cyc n P) := by
  refine ⟨?_, Or.inr (Or.inl (Or.inl ⟨?_, ?_⟩))⟩
  · intro hc
    have := cyc_inj_of_lt n (show 0 < n by omega) (show P < n by omega) hc
    omega
  · rw [cyc_val, Nat.zero_mod]
  · rw [cyc_val, Nat.mod_eq_of_lt (show P < n by omega)]

theorem chord_two_adj : (Hg n P R Q).Adj (cyc n R) (cyc n Q) := by
  refine ⟨?_, Or.inr (Or.inr (Or.inl ⟨?_, ?_⟩))⟩
  · intro hc
    have := cyc_inj_of_lt n (show R < n by omega) (show Q < n by omega) hc
    omega
  · rw [cyc_val, Nat.mod_eq_of_lt (show R < n by omega)]
  · rw [cyc_val, Nat.mod_eq_of_lt (show Q < n by omega)]

theorem Tr_isTrackFrom (u v : Fin 4) (huv : u ≠ v) :
    IsTrackFrom (Hg n P R Q) (Tr n P R Q u v) (iot n P R Q u) (iot n P R Q v) := by
  have hn2 : 2 ≤ n := by omega
  have hA1 : IsTrackFrom (Hg n P R Q) (arc n 0 R) (cyc n 0) (cyc n R) :=
    isTrackFrom_arc hn2 0 R R (by omega) (by rw [Nat.zero_add])
  have hA2 : IsTrackFrom (Hg n P R Q) (arc n R (P - R)) (cyc n R) (cyc n P) :=
    isTrackFrom_arc hn2 R (P - R) P (by omega) (by rw [show R + (P - R) = P from by omega])
  have hA3 : IsTrackFrom (Hg n P R Q) (arc n P (Q - P)) (cyc n P) (cyc n Q) :=
    isTrackFrom_arc hn2 P (Q - P) Q (by omega) (by rw [show P + (Q - P) = Q from by omega])
  have hA4 : IsTrackFrom (Hg n P R Q) (arc n Q (n - Q)) (cyc n Q) (cyc n 0) :=
    isTrackFrom_arc hn2 Q (n - Q) 0
      (by omega) (by rw [show Q + (n - Q) = n from by omega, Nat.mod_self, Nat.zero_mod])
  rcases fin4_pairs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hA1
  · exact isTrackFrom_reverse hA1
  · exact hA2
  · exact isTrackFrom_reverse hA2
  · exact hA3
  · exact isTrackFrom_reverse hA3
  · exact hA4
  · exact isTrackFrom_reverse hA4
  · exact isTrackFrom_pair (chord_one_adj h0R hRP hPQ hQn)
  · exact isTrackFrom_pair (chord_one_adj h0R hRP hPQ hQn).symm
  · exact isTrackFrom_pair (chord_two_adj h0R hRP hPQ hQn)
  · exact isTrackFrom_pair (chord_two_adj h0R hRP hPQ hQn).symm

theorem Tr_len2 (u v : Fin 4) (huv : u ≠ v) : 2 ≤ (Tr n P R Q u v).length := by
  rcases fin4_pairs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp <;> omega

theorem Tr_rev (u v : Fin 4) (huv : u ≠ v) : Tr n P R Q v u = (Tr n P R Q u v).reverse := by
  rcases fin4_pairs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem Tr_loc (u v : Fin 4) (huv : u ≠ v) (w : Fin n) (hw : w ∈ Tr n P R Q u v) :
    w.val = bp P R Q u ∨ w.val = bp P R Q v ∨ IntV n P R Q u v w.val := by
  have e1 : R = (0 + R) % n := by rw [Nat.zero_add, Nat.mod_eq_of_lt (show R < n by omega)]
  have e2 : P = (R + (P - R)) % n := by
    rw [show R + (P - R) = P from by omega, Nat.mod_eq_of_lt (show P < n by omega)]
  have e3 : Q = (P + (Q - P)) % n := by
    rw [show P + (Q - P) = Q from by omega, Nat.mod_eq_of_lt (show Q < n by omega)]
  have e4 : 0 = (Q + (n - Q)) % n := by
    rw [show Q + (n - Q) = n from by omega, Nat.mod_self]
  rcases fin4_pairs u v huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [Tr_01, Tr_10, Tr_12, Tr_21, Tr_23, Tr_32, Tr_30, Tr_03, Tr_02, Tr_20, Tr_13,
      Tr_31, List.mem_reverse, bp_zero, bp_one, bp_two, bp_three] at hw ⊢
  · rcases arc_val_mem 0 R R (by omega) (by omega) e1 hw with h | h | ⟨ha, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩, by omega, by omega⟩))
  · rcases arc_val_mem 0 R R (by omega) (by omega) e1 hw with h | h | ⟨ha, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩))
  · rcases arc_val_mem R (P - R) P (by omega) (by omega) e2 hw with h | h | ⟨ha, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩, by omega, by omega⟩)))
  · rcases arc_val_mem R (P - R) P (by omega) (by omega) e2 hw with h | h | ⟨ha, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩)))
  · rcases arc_val_mem P (Q - P) Q (by omega) (by omega) e3 hw with h | h | ⟨ha, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, rfl⟩, by omega, by omega⟩))))
  · rcases arc_val_mem P (Q - P) Q (by omega) (by omega) e3 hw with h | h | ⟨ha, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩))))
  · rcases arc_val_mem Q (n - Q) 0 (by omega) (by omega) e4 hw with h | h | ⟨ha, hb⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨rfl, rfl⟩, by omega, by omega⟩))))
  · rcases arc_val_mem Q (n - Q) 0 (by omega) (by omega) e4 hw with h | h | ⟨ha, hb⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩))))
  · rcases List.mem_cons.mp hw with rfl | hw2
    · exact Or.inl (by rw [cyc_val, Nat.zero_mod])
    · rw [List.mem_singleton] at hw2
      subst hw2
      exact Or.inr (Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show P < n by omega)]))
  · rcases List.mem_cons.mp hw with rfl | hw2
    · exact Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show P < n by omega)])
    · rw [List.mem_singleton] at hw2
      subst hw2
      exact Or.inr (Or.inl (by rw [cyc_val, Nat.zero_mod]))
  · rcases List.mem_cons.mp hw with rfl | hw2
    · exact Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show R < n by omega)])
    · rw [List.mem_singleton] at hw2
      subst hw2
      exact Or.inr (Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show Q < n by omega)]))
  · rcases List.mem_cons.mp hw with rfl | hw2
    · exact Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show Q < n by omega)])
    · rw [List.mem_singleton] at hw2
      subst hw2
      exact Or.inr (Or.inl (by rw [cyc_val, Nat.mod_eq_of_lt (show R < n by omega)]))

theorem iot_val (u : Fin 4) : (iot n P R Q u).val = bp P R Q u := by
  simp only [iot, cyc_val]
  exact Nat.mod_eq_of_lt (bp_lt h0R hRP hPQ hQn u)

theorem Tr_int (u v : Fin 4) (huv : u ≠ v) (w : Fin n)
    (hw : w ∈ trackInterior (Tr n P R Q u v)) : IntV n P R Q u v w.val := by
  obtain ⟨⟨-, hnd, -⟩, hh, hl⟩ := Tr_isTrackFrom h0R hRP hPQ hQn u v huv
  have hwu : w ≠ iot n P R Q u := ne_head_of_mem_trackInterior hnd hh hw
  have hwv : w ≠ iot n P R Q v := ne_getLast_of_mem_trackInterior hnd hl hw
  rcases Tr_loc h0R hRP hPQ hQn u v huv w (mem_of_mem_trackInterior hw) with h | h | h
  · exact absurd (Fin.val_injective (h.trans (iot_val h0R hRP hPQ hQn u).symm)) hwu
  · exact absurd (Fin.val_injective (h.trans (iot_val h0R hRP hPQ hQn v).symm)) hwv
  · exact h

end TrackFacts

end Workspace.ProofLemmas.LineGraphK4Chords
