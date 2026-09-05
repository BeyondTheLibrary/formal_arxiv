import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics

/-!
# Wheel-parity, made arithmetic

Section 16 of Chudnovsky–Robertson–Seymour–Thomas uses *wheel-parity* (printed p. 96) as if it
were a two-valued invariant of the vertices of the rim: vertices are constantly said to have
"the same" or "opposite" wheel-parity, and the paper freely composes those relations.  The
definition, `Workspace.Types.Wheels.SPGT.SameWheelParity`, is an existential over the arcs of the
rim, so nothing of the sort is available out of the box.

This module supplies the arithmetic reading.  For a hole `C` of length `n` write the *cyclic
edges* of `C` as `e₀, …, e_{n-1}`, where `e_m` joins `C[m mod n]` to `C[(m+1) mod n]`
(`CycEdge`), and let `cycCount k` be the number of `Y`-complete ones among `e₀, …, e_{k-1}`.
Then, **as soon as the total number of `Y`-complete edges of `C` is even** — which is the case
for the rim of a wheel, by 2.3 — two distinct vertices `C[i]`, `C[j]` have the same wheel-parity
exactly when `cycCount i ≡ cycCount j (mod 2)` (`sameWheelParity_iff`).  Everything §16 does with
wheel-parity is then an `omega` away.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.WheelParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### The cyclic edges of a hole, and the running count of `Y`-complete ones -/

/-- The `m`-th cyclic edge of the list `C` joins `C[m mod n]` to `C[(m+1) mod n]`; `CycEdge`
says that this edge is `Y`-complete.  Phrased with `getElem?` so that it is total in `m`. -/
def CycEdge (G : SimpleGraph V) (Y : Set V) (C : List V) (m : ℕ) : Prop :=
  ∃ u v : V, C[m % C.length]? = some u ∧ C[(m + 1) % C.length]? = some v ∧
    EdgeComplete G Y u v

/-- The number of `Y`-complete edges among the cyclic edges `e₀, …, e_{k-1}` of `C`. -/
noncomputable def cycCount (G : SimpleGraph V) (Y : Set V) (C : List V) (k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun m => CycEdge G Y C m)).card

theorem cycCount_eq_sum (k : ℕ) :
    cycCount G Y C k = ∑ m ∈ Finset.range k, (if CycEdge G Y C m then 1 else 0) := by
  simp only [cycCount, Finset.card_filter]

theorem cycCount_zero : cycCount G Y C 0 = 0 := by simp [cycCount]

theorem cycCount_succ (k : ℕ) :
    cycCount G Y C (k + 1) = cycCount G Y C k + (if CycEdge G Y C k then 1 else 0) := by
  simp only [cycCount_eq_sum, Finset.sum_range_succ]

theorem cycCount_mono {a b : ℕ} (h : a ≤ b) : cycCount G Y C a ≤ cycCount G Y C b := by
  simp only [cycCount]
  refine Finset.card_le_card (Finset.filter_subset_filter _ ?_)
  intro x hx
  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) h)

/-- The running count is the partial sum of the indicator, shifted. -/
theorem cycCount_add (k j : ℕ) :
    cycCount G Y C (k + j) =
      cycCount G Y C k + ∑ t ∈ Finset.range j, (if CycEdge G Y C (k + t) then 1 else 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [← Nat.add_assoc, cycCount_succ, ih, Finset.sum_range_succ]
      ring

theorem cycEdge_periodic (m : ℕ) : CycEdge G Y C (m + C.length) ↔ CycEdge G Y C m := by
  have h1 : (m + C.length) % C.length = m % C.length := Nat.add_mod_right m C.length
  have h2 : (m + C.length + 1) % C.length = (m + 1) % C.length := by
    rw [show m + C.length + 1 = m + 1 + C.length by ring, Nat.add_mod_right]
  simp only [CycEdge, h1, h2]

theorem cycCount_add_length (k : ℕ) :
    cycCount G Y C (k + C.length) = cycCount G Y C k + cycCount G Y C C.length := by
  induction k with
  | zero => simp [cycCount_zero]
  | succ k ih =>
      have e : k + 1 + C.length = (k + C.length) + 1 := by ring
      rw [e, cycCount_succ, ih, cycCount_succ]
      by_cases hc : CycEdge G Y C k
      · rw [if_pos hc, if_pos ((cycEdge_periodic k).mpr hc)]; ring
      · rw [if_neg hc, if_neg (fun h => hc ((cycEdge_periodic k).mp h))]; ring

theorem cycCount_add_mul_length (k q : ℕ) :
    cycCount G Y C (k + q * C.length) = cycCount G Y C k + q * cycCount G Y C C.length := by
  induction q with
  | zero => simp
  | succ q ih =>
      have e : k + (q + 1) * C.length = (k + q * C.length) + C.length := by ring
      rw [e, cycCount_add_length, ih]
      ring

/-- Once the total is even, the running count only matters modulo the length of the cycle. -/
theorem cycCount_mod_two (heven : Even (cycCount G Y C C.length)) (k : ℕ) :
    cycCount G Y C k % 2 = cycCount G Y C (k % C.length) % 2 := by
  rcases Nat.eq_zero_or_pos C.length with h0 | hpos
  · rw [h0]; simp
  have e : k = k % C.length + (k / C.length) * C.length := by
    rw [Nat.mul_comm]
    exact (Nat.mod_add_div k C.length).symm
  conv_lhs => rw [e]
  rw [cycCount_add_mul_length]
  obtain ⟨r, hr⟩ := heven
  rw [hr, show (k / C.length) * (r + r) = 2 * ((k / C.length) * r) by ring,
    Nat.add_mul_mod_self_left]

/-! ### Reading `CycEdge` off the list -/

theorem cycEdge_iff_getElem (hn : 0 < C.length) (m : ℕ) :
    CycEdge G Y C m ↔
      EdgeComplete G Y (C[m % C.length]'(Nat.mod_lt _ hn))
        (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  constructor
  · rintro ⟨u, v, hu, hv, hE⟩
    rw [List.getElem?_eq_getElem (Nat.mod_lt m hn)] at hu
    rw [List.getElem?_eq_getElem (Nat.mod_lt (m + 1) hn)] at hv
    rw [Option.some_injective _ hu, Option.some_injective _ hv]
    exact hE
  · intro h
    exact ⟨_, _, List.getElem?_eq_getElem (Nat.mod_lt m hn),
      List.getElem?_eq_getElem (Nat.mod_lt (m + 1) hn), h⟩

theorem edgeComplete_symm {u v : V} (h : EdgeComplete G Y u v) : EdgeComplete G Y v u :=
  ⟨h.1.symm, h.2.2, h.2.1⟩

/-- Index reading of hole-adjacency, with the modular arithmetic already discharged. -/
theorem hole_adj_index (hC : IsHoleList G C) {i j : ℕ} (hi : i < C.length) (hj : j < C.length)
    (h : G.Adj (C[i]'hi) (C[j]'hj)) :
    j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = C.length - 1) ∨ (j = 0 ∧ i = C.length - 1) := by
  have hres := (HoleBasics.hole_adj_iff hC hi hj).mp h
  have e1 : (i + 1) % C.length = if i + 1 = C.length then 0 else i + 1 := by
    by_cases h' : i + 1 = C.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  have e2 : (j + 1) % C.length = if j + 1 = C.length then 0 else j + 1 := by
    by_cases h' : j + 1 = C.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at hres
  split_ifs at hres <;> omega

/-! ### Arcs of the hole -/

/-- A proper cyclic arc of a hole is a path. -/
theorem isPathList_rotate_take (hC : IsHoleList G C) {k L : ℕ}
    (h1 : 1 ≤ L) (h2 : L + 1 ≤ C.length) : IsPathList G ((C.rotate k).take L) := by
  have hCr : IsHoleList G (C.rotate k) := HoleBasics.isHoleList_rotate hC k
  have hlenr : (C.rotate k).length = C.length := by simp
  obtain ⟨hlen, hnd, hadj⟩ := hCr
  have hlt : ((C.rotate k).take L).length = L := by
    simp only [List.length_take, hlenr]; omega
  refine ⟨?_, List.Nodup.sublist (List.take_sublist L _) hnd, ?_⟩
  · intro hnil
    rw [hnil] at hlt
    simp at hlt
    omega
  · intro i j hi hj
    rw [hlt] at hi hj
    have hi' : i < (C.rotate k).length := by omega
    have hj' : j < (C.rotate k).length := by omega
    have ei : ((C.rotate k).take L)[i]'(by omega) = ((C.rotate k)[i]'hi') := by
      simp only [List.getElem_take]
    have ej : ((C.rotate k).take L)[j]'(by omega) = ((C.rotate k)[j]'hj') := by
      simp only [List.getElem_take]
    rw [ei, ej, hadj i j hi' hj']
    have m1 : (i + 1) % (C.rotate k).length = i + 1 := Nat.mod_eq_of_lt (by omega)
    have m2 : (j + 1) % (C.rotate k).length = j + 1 := Nat.mod_eq_of_lt (by omega)
    rw [m1, m2]
    omega

theorem getElem_rotate_eq (hn : 0 < C.length) {k i : ℕ} (hi : i < (C.rotate k).length) :
    (C.rotate k)[i]'hi = C[(i + k) % C.length]'(Nat.mod_lt _ hn) := by
  simp only [List.getElem_rotate]

/-- The two ends of a proper cyclic arc of a hole. -/
theorem arc_isPathFrom (hC : IsHoleList G C) {k L p q : ℕ}
    (hp : p < C.length) (hq : q < C.length) (h1 : 2 ≤ L) (h2 : L + 1 ≤ C.length)
    (hkp : k % C.length = p) (hkq : (k + L - 1) % C.length = q) :
    IsPathFrom G ((C.rotate k).take L) (C[p]'hp) (C[q]'hq) := by
  have hn : 0 < C.length := by omega
  have hlenr : (C.rotate k).length = C.length := by simp
  have hlt : ((C.rotate k).take L).length = L := by
    simp only [List.length_take, hlenr]; omega
  refine ⟨isPathList_rotate_take hC (by omega) h2, ?_, ?_⟩
  · rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < ((C.rotate k).take L).length by omega)]
    congr 1
    have e : ((C.rotate k).take L)[0]'(by omega) = ((C.rotate k)[0]'(by omega)) := by
      simp only [List.getElem_take]
    rw [e, getElem_rotate_eq hn]
    simp only [Nat.zero_add, hkp]
  · rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show ((C.rotate k).take L).length - 1 <
        ((C.rotate k).take L).length by omega)]
    congr 1
    have e : ((C.rotate k).take L)[((C.rotate k).take L).length - 1]'(by omega)
        = ((C.rotate k)[L - 1]'(by omega)) := by
      simp only [List.getElem_take, hlt]
    rw [e, getElem_rotate_eq hn]
    simp only [show L - 1 + k = k + L - 1 by omega, hkq]

/-- The `Y`-complete edges of a cyclic arc `Q` of `C` starting at cyclic position `k` are the
cyclic edges `e_k, …, e_{k+|Q|-2}` of `C`. -/
theorem arc_count (hC : IsHoleList G C) {k L : ℕ} {Q : List V}
    (hpre : Q <+: C.rotate k) (hQL : Q.length = L) (h2 : 2 ≤ L) (hL : L + 1 ≤ C.length) :
    cycCount G Y C k +
        {i : ℕ | ∃ h : i + 1 < Q.length, EdgeComplete G Y Q[i] Q[i + 1]}.ncard
      = cycCount G Y C (k + (L - 1)) := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hple := hpre.length_le
  have hstep : ∀ (i : ℕ) (hi : i + 1 < Q.length),
      (EdgeComplete G Y (Q[i]'(by omega)) (Q[i + 1]'hi) ↔ CycEdge G Y C (k + i)) := by
    intro i hi
    have ha : i < (C.rotate k).length := by omega
    have hb : i + 1 < (C.rotate k).length := by omega
    have ea : (Q[i]'(by omega)) = ((C.rotate k)[i]'ha) := hpre.getElem (by omega)
    have eb : (Q[i + 1]'hi) = ((C.rotate k)[i + 1]'hb) := hpre.getElem hi
    rw [ea, eb, getElem_rotate_eq hn ha, getElem_rotate_eq hn hb, cycEdge_iff_getElem hn (k + i)]
    simp only [show i + k = k + i by omega, show i + 1 + k = k + i + 1 by omega]
  have hsetimg : {i : ℕ | ∃ h : i + 1 < Q.length, EdgeComplete G Y Q[i] Q[i + 1]}
      = ↑((Finset.range (L - 1)).filter (fun t => CycEdge G Y C (k + t))) := by
    ext t
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨h, hE⟩
      exact ⟨by omega, (hstep t h).mp hE⟩
    · rintro ⟨hlt, hce⟩
      exact ⟨by omega, (hstep t (by omega)).mpr hce⟩
  rw [hsetimg, Set.ncard_coe_finset, Finset.card_filter, cycCount_add]

/-! ### The total number of `Y`-complete edges of the rim -/

theorem ncard_yEdges_eq_cycCount (hC : IsHoleList G C) :
    {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard
      = cycCount G Y C C.length := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hn4 : 4 ≤ C.length := hC.1
  have hnd : C.Nodup := hC.2.1
  have key : {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u, v) ∧ EdgeComplete G Y u v}
      = ↑(((Finset.range C.length).filter (fun m => CycEdge G Y C m)).image
          (fun m => s(C[m % C.length]'(Nat.mod_lt _ hn),
            C[(m + 1) % C.length]'(Nat.mod_lt _ hn)))) := by
    ext e
    simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range]
    constructor
    · rintro ⟨u, huC, v, hvC, rfl, hE⟩
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem huC
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hvC
      have hcase := hole_adj_index hC ha hb hE.1
      have ma : a % C.length = a := Nat.mod_eq_of_lt ha
      have mb : b % C.length = b := Nat.mod_eq_of_lt hb
      rcases hcase with h | h | ⟨h, h'⟩ | ⟨h, h'⟩
      · have e2 : (a + 1) % C.length = b := by
          rw [Nat.mod_eq_of_lt (by omega)]; exact h.symm
        refine ⟨a, ⟨ha, ?_⟩, ?_⟩
        · rw [cycEdge_iff_getElem hn]
          simp only [ma, e2]
          exact hE
        · simp only [ma, e2]
      · have e2 : (b + 1) % C.length = a := by
          rw [Nat.mod_eq_of_lt (by omega)]; exact h.symm
        refine ⟨b, ⟨hb, ?_⟩, ?_⟩
        · rw [cycEdge_iff_getElem hn]
          simp only [mb, e2]
          exact edgeComplete_symm hE
        · simp only [mb, e2]
          exact Sym2.eq_swap
      · have e1 : (C.length - 1) % C.length = b := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have e2 : (C.length - 1 + 1) % C.length = a := by
          rw [show C.length - 1 + 1 = C.length by omega, Nat.mod_self]; omega
        refine ⟨C.length - 1, ⟨by omega, ?_⟩, ?_⟩
        · rw [cycEdge_iff_getElem hn]
          simp only [e1, e2]
          exact edgeComplete_symm hE
        · simp only [e1, e2]
          exact Sym2.eq_swap
      · have e1 : (C.length - 1) % C.length = a := by
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        have e2 : (C.length - 1 + 1) % C.length = b := by
          rw [show C.length - 1 + 1 = C.length by omega, Nat.mod_self]; omega
        refine ⟨C.length - 1, ⟨by omega, ?_⟩, ?_⟩
        · rw [cycEdge_iff_getElem hn]
          simp only [e1, e2]
          exact hE
        · simp only [e1, e2]
    · rintro ⟨m, ⟨hm, hce⟩, rfl⟩
      rw [cycEdge_iff_getElem hn] at hce
      exact ⟨_, List.getElem_mem _, _, List.getElem_mem _, rfl, hce⟩
  have hinj : Set.InjOn
      (fun m => s(C[m % C.length]'(Nat.mod_lt _ hn), C[(m + 1) % C.length]'(Nat.mod_lt _ hn)))
      ↑((Finset.range C.length).filter (fun m => CycEdge G Y C m)) := by
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
    have ha' : a < C.length := ha.1
    have hb' : b < C.length := hb.1
    have ma : a % C.length = a := Nat.mod_eq_of_lt ha'
    have mb : b % C.length = b := Nat.mod_eq_of_lt hb'
    have ma1 : (a + 1) % C.length = if a + 1 = C.length then 0 else a + 1 := by
      by_cases h' : a + 1 = C.length
      · simp [h']
      · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
    have mb1 : (b + 1) % C.length = if b + 1 = C.length then 0 else b + 1 := by
      by_cases h' : b + 1 = C.length
      · simp [h']
      · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
    simp only at hab
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have i1 := (List.Nodup.getElem_inj_iff hnd).mp h1
      rw [ma, mb] at i1
      exact i1
    · have i1 := (List.Nodup.getElem_inj_iff hnd).mp h1
      have i2 := (List.Nodup.getElem_inj_iff hnd).mp h2
      rw [ma, mb1] at i1
      rw [ma1, mb] at i2
      split_ifs at i1 i2 <;> omega
  rw [key, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]
  rfl

/-! ### The main equivalence -/

theorem sameWheelParity_symm {u v : V} (h : SameWheelParity G C Y u v) :
    SameWheelParity G C Y v u := by
  obtain ⟨h1, h2, h3, P, hends, hpre, hev⟩ := h
  exact ⟨h1.symm, h3, h2, P, hends.symm, hpre, hev⟩

/-- **Wheel-parity is `cycCount` mod 2.**  For a hole `C` whose `Y`-complete edges are even in
number, two distinct vertices of `C` have the same wheel-parity exactly when their running
counts of `Y`-complete edges agree mod `2`. -/
theorem sameWheelParity_iff (hC : IsHoleList G C)
    (heven : Even (cycCount G Y C C.length))
    {i j : ℕ} (hi : i < C.length) (hj : j < C.length) (hij : i ≠ j) :
    SameWheelParity G C Y (C[i]'hi) (C[j]'hj) ↔
      cycCount G Y C i % 2 = cycCount G Y C j % 2 := by
  have hn : 0 < C.length := by omega
  have hn4 : 4 ≤ C.length := hC.1
  have hnd : C.Nodup := hC.2.1
  have hne : (C[i]'hi) ≠ (C[j]'hj) := fun he => hij ((List.Nodup.getElem_inj_iff hnd).mp he)
  constructor
  · -- an arc with an even number of `Y`-complete edges pins down the parity
    rintro ⟨-, -, -, P, hends, ⟨k, hpre⟩, heven'⟩
    have hpath : IsPathList G P := by rcases hends with h | h <;> exact h.1
    have hpos : 0 < P.length := PathBasics.path_length_pos hpath
    have hlenr : (C.rotate k).length = C.length := by simp
    have hPle : P.length ≤ C.length := by have := hpre.length_le; omega
    have hPub : P.length + 1 ≤ C.length := by
      rcases Nat.lt_or_ge P.length C.length with h | h
      · omega
      exfalso
      have hPeq : P.length = C.length := by omega
      have h1 : P.length - 1 < P.length := by omega
      have hCr : IsHoleList G (C.rotate k) := HoleBasics.isHoleList_rotate hC k
      have i0 : (0 : ℕ) < (C.rotate k).length := by omega
      have i1 : P.length - 1 < (C.rotate k).length := by omega
      have hadjC : G.Adj ((C.rotate k)[0]'i0) ((C.rotate k)[P.length - 1]'i1) :=
        (HoleBasics.hole_adj_iff hCr i0 i1).mpr (Or.inr (by
          rw [show P.length - 1 + 1 = (C.rotate k).length by omega, Nat.mod_self]))
      have hadj : G.Adj (P[0]'hpos) (P[P.length - 1]'h1) := by
        rw [hpre.getElem hpos, hpre.getElem h1]
        exact hadjC
      have := (PathBasics.path_adj_iff hpath hpos h1).mp hadj
      omega
    have hPlen : 2 ≤ P.length := by
      by_contra hcon
      have h1 : P.length = 1 := by omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h1
      rcases hends with h | h
      · have e1 : x = (C[i]'hi) := by have := h.2.1; rw [hx] at this; simpa using this
        have e2 : x = (C[j]'hj) := by have := h.2.2; rw [hx] at this; simpa using this
        exact hne (e1.symm.trans e2)
      · have e1 : x = (C[j]'hj) := by have := h.2.1; rw [hx] at this; simpa using this
        have e2 : x = (C[i]'hi) := by have := h.2.2; rw [hx] at this; simpa using this
        exact hne (e2.symm.trans e1)
    have hhead : P.head? = some (C[k % C.length]'(Nat.mod_lt _ hn)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
      congr 1
      rw [hpre.getElem hpos, getElem_rotate_eq hn]
      simp
    have hlast : P.getLast? = some (C[(k + P.length - 1) % C.length]'(Nat.mod_lt _ hn)) := by
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (show P.length - 1 < P.length by omega)]
      congr 1
      rw [hpre.getElem (show P.length - 1 < P.length by omega), getElem_rotate_eq hn]
      simp only [show P.length - 1 + k = k + P.length - 1 by omega]
    have hkey : ((C[i]'hi) = (C[k % C.length]'(Nat.mod_lt _ hn)) ∧
          (C[j]'hj) = (C[(k + P.length - 1) % C.length]'(Nat.mod_lt _ hn))) ∨
        ((C[j]'hj) = (C[k % C.length]'(Nat.mod_lt _ hn)) ∧
          (C[i]'hi) = (C[(k + P.length - 1) % C.length]'(Nat.mod_lt _ hn))) := by
      rcases hends with h | h
      · exact Or.inl ⟨Option.some_injective _ (h.2.1.symm.trans hhead),
          Option.some_injective _ (h.2.2.symm.trans hlast)⟩
      · exact Or.inr ⟨Option.some_injective _ (h.2.1.symm.trans hhead),
          Option.some_injective _ (h.2.2.symm.trans hlast)⟩
    have hcount := arc_count (Y := Y) hC hpre rfl hPlen hPub
    have hpar : cycCount G Y C k % 2 = cycCount G Y C (k + (P.length - 1)) % 2 := by
      obtain ⟨r, hr⟩ := heven'
      omega
    have hmod1 : cycCount G Y C (k % C.length) % 2 = cycCount G Y C k % 2 :=
      (cycCount_mod_two heven k).symm
    have hmod2 : cycCount G Y C ((k + P.length - 1) % C.length) % 2
        = cycCount G Y C (k + P.length - 1) % 2 := (cycCount_mod_two heven _).symm
    have hkl : k + P.length - 1 = k + (P.length - 1) := by omega
    rcases hkey with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rw [(List.Nodup.getElem_inj_iff hnd).mp e1, (List.Nodup.getElem_inj_iff hnd).mp e2,
        hmod1, hmod2, hkl]
      exact hpar
    · rw [(List.Nodup.getElem_inj_iff hnd).mp e1, (List.Nodup.getElem_inj_iff hnd).mp e2,
        hmod1, hmod2, hkl]
      exact hpar.symm
  · -- conversely, one of the two arcs joining them has an even number of `Y`-complete edges
    intro hpar
    have arcSame : ∀ (k L p q : ℕ) (hp : p < C.length) (hq : q < C.length), p ≠ q →
        2 ≤ L → L + 1 ≤ C.length → k % C.length = p → (k + L - 1) % C.length = q →
        cycCount G Y C k % 2 = cycCount G Y C (k + (L - 1)) % 2 →
        SameWheelParity G C Y (C[p]'hp) (C[q]'hq) := by
      intro k L p q hp hq hpq h2 hL hkp hkq hcnt
      have hlt : ((C.rotate k).take L).length = L := by
        simp only [List.length_take, List.length_rotate]; omega
      refine ⟨fun he => hpq ((List.Nodup.getElem_inj_iff hnd).mp he),
        List.getElem_mem _, List.getElem_mem _, (C.rotate k).take L,
        Or.inl (arc_isPathFrom hC hp hq h2 hL hkp hkq), ⟨k, List.take_prefix _ _⟩, ?_⟩
      have hcount := arc_count (Y := Y) hC (List.take_prefix L (C.rotate k)) hlt h2 hL
      rw [Nat.even_iff]
      omega
    have main : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length), a < b →
        cycCount G Y C a % 2 = cycCount G Y C b % 2 →
        SameWheelParity G C Y (C[a]'ha) (C[b]'hb) := by
      intro a b ha hb hab hpar'
      rcases Nat.lt_or_ge (b - a) (C.length - 1) with hcase | hcase
      · refine arcSame a (b - a + 1) a b ha hb (by omega) (by omega) (by omega)
          (Nat.mod_eq_of_lt ha) ?_ ?_
        · rw [show a + (b - a + 1) - 1 = b by omega]
          exact Nat.mod_eq_of_lt hb
        · rw [show a + (b - a + 1 - 1) = b by omega]
          exact hpar'
      · -- the forward arc would be the whole cycle: use the other one
        have hae : a = 0 := by omega
        have hbe : b = C.length - 1 := by omega
        refine sameWheelParity_symm (arcSame b 2 b a hb ha (by omega) (by omega) (by omega)
          (Nat.mod_eq_of_lt hb) ?_ ?_)
        · rw [show b + 2 - 1 = C.length by omega, Nat.mod_self]
          omega
        · rw [show b + (2 - 1) = C.length by omega]
          rw [hae, cycCount_zero] at hpar'
          obtain ⟨r, hr⟩ := heven
          omega
    rcases Nat.lt_or_ge i j with h | h
    · exact main i j hi hj h hpar
    · exact sameWheelParity_symm (main j i hj hi (by omega) hpar.symm)

/-- Two consecutive vertices of the rim have the same wheel-parity exactly when the edge
joining them is **not** `Y`-complete.  (This is the form §16 uses constantly: *"since `p, q`
have opposite wheel-parity and are not `Y`-complete, they are not adjacent"*.) -/
theorem sameWheelParity_succ_iff (hC : IsHoleList G C)
    (heven : Even (cycCount G Y C C.length)) {i : ℕ} (hi : i + 1 < C.length) :
    SameWheelParity G C Y (C[i]'(by omega)) (C[i + 1]'hi) ↔
      ¬ EdgeComplete G Y (C[i]'(by omega)) (C[i + 1]'hi) := by
  have hn : 0 < C.length := by omega
  rw [sameWheelParity_iff hC heven (show i < C.length by omega) hi (by omega), cycCount_succ]
  have hce : CycEdge G Y C i ↔ EdgeComplete G Y (C[i]'(by omega)) (C[i + 1]'hi) := by
    rw [cycEdge_iff_getElem hn]
    simp only [Nat.mod_eq_of_lt (show i < C.length by omega), Nat.mod_eq_of_lt hi]
  by_cases hE : EdgeComplete G Y (C[i]'(by omega)) (C[i + 1]'hi)
  · rw [if_pos (hce.mpr hE)]
    exact iff_of_false (by omega) (not_not_intro hE)
  · rw [if_neg (fun h => hE (hce.mp h))]
    exact iff_of_true (by omega) hE

/-- The wrap-around case of `sameWheelParity_succ_iff`. -/
theorem sameWheelParity_wrap_iff (hC : IsHoleList G C)
    (heven : Even (cycCount G Y C C.length)) :
    SameWheelParity G C Y (C[C.length - 1]'(by have := hC.1; omega))
        (C[0]'(by have := hC.1; omega)) ↔
      ¬ EdgeComplete G Y (C[C.length - 1]'(by have := hC.1; omega))
        (C[0]'(by have := hC.1; omega)) := by
  have hn4 : 4 ≤ C.length := hC.1
  rw [sameWheelParity_iff hC heven (by omega) (by omega) (by omega), cycCount_zero]
  have hce : CycEdge G Y C (C.length - 1) ↔
      EdgeComplete G Y (C[C.length - 1]'(by omega)) (C[0]'(by omega)) := by
    rw [cycEdge_iff_getElem (show 0 < C.length by omega)]
    simp only [Nat.mod_eq_of_lt (show C.length - 1 < C.length by omega),
      show C.length - 1 + 1 = C.length by omega, Nat.mod_self]
  have hsum : cycCount G Y C C.length
      = cycCount G Y C (C.length - 1) + (if CycEdge G Y C (C.length - 1) then 1 else 0) := by
    rw [← cycCount_succ]
    congr 1
    omega
  obtain ⟨r, hr⟩ := heven
  by_cases hE : EdgeComplete G Y (C[C.length - 1]'(by omega)) (C[0]'(by omega))
  · rw [if_pos (hce.mpr hE)] at hsum
    exact iff_of_false (by omega) (not_not_intro hE)
  · rw [if_neg (fun h => hE (hce.mp h))] at hsum
    exact iff_of_true (by omega) hE

end Workspace.ProofLemmas.WheelParity
