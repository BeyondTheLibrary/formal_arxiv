/-  Proof attempt for statement 23.5 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.  The theorem statement below is
    byte-identical to `Workspace/Statements/S23/Thm_23_5.lean`.

    The printed proof (paper/proofs/23_5.md) is followed step for step:

    * *"By 2.3, and since `G ∈ F₁₀`, every vertex in `B` has at most `½(a+w)`
      neighbours in `C`"* -- `indep_or_two` (2.3's second assertion applied to
      `X = {v}`, plus the `F₉` no-wheel clause and the `F₁₀` no-three-consecutive
      clause) and `two_card_le` (an independent set of a cycle of length `m` has
      at most `m/2` vertices, because it is disjoint from its own shift).
    * *"Also, every vertex in `W` has at most two neighbours in `A ∪ W`"* --
      `nbrCount_hole_eq_two`.
    * The two displayed inequalities are `hb1` and `hb2`; the identity
      *"`p+p'+q+q'+r+r'+2s+2s' = ab+aw+bw+w(w-1)`"* is `hid`
      (`E + F + w = m*n`, with `m = a+w` and `n = b+w`).
    * *"so `w(a + b + 2w - 10) ≤ 0`.  Since `a + w, b + w ≥ 6`, it follows that
      `w = 0`"* -- `arith`.
    * *"Moreover, equality holds throughout this calculation, so every vertex in
      `D` is adjacent to exactly half the vertices of `C` and vice versa"* --
      `heq1`, `heq2`, `hexactC`, `hexactD`.
    * *"By 2.3, and since `G ∈ F₁₀`, it follows that for each `v ∈ D`, its
      neighbours in `C` are pairwise nonadjacent ... its set of neighbours in
      `V(C)` is either the set of all `cᵢ` with `i` even, or the set with `i`
      odd"* -- `hP1`, `hP2` (the alternation), from the independence together
      with the covering `shift_cover` forced by the equality.
    * *"We may assume that `c₁` is adjacent to `d₁`.  Hence the edges between
      `{c₁,c₂,c₄,c₅}` and `{d₁,d₂,d₄,d₅}` are ... and so the subgraph induced on
      these eight vertices is a double diamond, contrary to `G ∈ F₁₀`"* --
      `final_config` (the rotation realising *"we may assume"*) and
      `final_config0` (the explicit eight vertices).  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.LongOddPrism
-- extra imports needed by the proof only
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S02.Thm_2_3

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-! ## Helper lemmas (private to this attempt) -/

namespace Thm235Helpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A singleton is anticonnected. -/
theorem anticonn_singleton (G : SimpleGraph V) (v : V) :
    AnticonnectedSet G ({v} : Set V) := by
  intro p q
  exact (Subtype.ext (p.2.trans q.2.symm) ▸ SimpleGraph.Reachable.refl p)

theorem prefix_three {α : Type*} (l : List α) (h : 3 ≤ l.length) :
    [l[0]'(by omega), l[1]'(by omega), l[2]'(by omega)] <+: l := by
  match l, h with
  | a :: b :: c :: t, _ => exact ⟨t, rfl⟩

/-- The mod-free reading of hole adjacency. -/
theorem hole_adj_index {G : SimpleGraph V} {cl : List V} (hc : IsHoleList G cl)
    {i j : ℕ} (hi : i < cl.length) (hj : j < cl.length)
    (h : G.Adj ((cl)[i]'hi) ((cl)[j]'hj)) :
    j = i + 1 ∨ i = j + 1 ∨ (i = 0 ∧ j = cl.length - 1) ∨ (j = 0 ∧ i = cl.length - 1) := by
  have hres := (HoleBasics.hole_adj_iff hc hi hj).mp h
  have e1 : (i + 1) % cl.length = if i + 1 = cl.length then 0 else i + 1 := by
    by_cases h' : i + 1 = cl.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  have e2 : (j + 1) % cl.length = if j + 1 = cl.length then 0 else j + 1 := by
    by_cases h' : j + 1 = cl.length
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at hres
  split_ifs at hres <;> omega

/-- `F₁₀`'s clause, in index form: no vertex has three cyclically consecutive
neighbours on a hole of length `≥ 6`. -/
theorem no_three {G : SimpleGraph V}
    (hG10 : ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
        ¬ ∃ v x y z : V, (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
          G.Adj v x ∧ G.Adj v y ∧ G.Adj v z)
    {C : List V} (hC : IsHoleList G C) (hm : 6 ≤ C.length) (v : V) (p : ℕ) (hp : p < C.length)
    (h0 : G.Adj v (C[p]'hp))
    (h1 : G.Adj v (C[(p + 1) % C.length]'(Nat.mod_lt _ (by omega))))
    (h2 : G.Adj v (C[(p + 2) % C.length]'(Nat.mod_lt _ (by omega)))) : False := by
  have hlr : (C.rotate p).length = C.length := by simp
  have h3 : 3 ≤ (C.rotate p).length := by rw [hlr]; omega
  have hpre := prefix_three (C.rotate p) h3
  have e0 : (C.rotate p)[0]'(by omega) = C[p]'hp := by
    simp only [List.getElem_rotate, Nat.zero_add, Nat.mod_eq_of_lt hp]
  have e1 : (C.rotate p)[1]'(by omega) = C[(p + 1) % C.length]'(Nat.mod_lt _ (by omega)) := by
    simp only [List.getElem_rotate]
    congr 1
    rw [Nat.add_comm]
  have e2 : (C.rotate p)[2]'(by omega) = C[(p + 2) % C.length]'(Nat.mod_lt _ (by omega)) := by
    simp only [List.getElem_rotate]
    congr 1
    rw [Nat.add_comm]
  rw [e0, e1, e2] at hpre
  exact hG10 C hC hm ⟨v, _, _, _, ⟨p, hpre⟩, h0, h1, h2⟩

/-- The vertex form: no path `x-y-z` inside the hole has all three vertices adjacent to `v`. -/
theorem no_three_v {G : SimpleGraph V}
    (hG10 : ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
        ¬ ∃ v x y z : V, (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
          G.Adj v x ∧ G.Adj v y ∧ G.Adj v z)
    {C : List V} (hC : IsHoleList G C) (hm : 6 ≤ C.length) {v x y z : V}
    (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : x ≠ z)
    (hvx : G.Adj v x) (hvy : G.Adj v y) (hvz : G.Adj v z) : False := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hz
  set m := C.length with hmdef
  have h4 : 4 ≤ m := hC.1
  have r1 := hole_adj_index hC hi hj hxy
  have r2 := hole_adj_index hC hj hk hyz
  have hik : i ≠ k := by rintro rfl; exact hxz rfl
  -- `prev j` and `next j`
  set pj : ℕ := if j = 0 then m - 1 else j - 1 with hpj
  have hpjlt : pj < m := by rw [hpj]; split_ifs <;> omega
  have hstep1 : (pj + 1) % m = j := by
    rw [hpj]
    split_ifs with h
    · subst h; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    · rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hj]
  have hstep2 : (pj + 2) % m = if j + 1 = m then 0 else j + 1 := by
    rw [hpj]
    split_ifs with h1 h2 h2
    · omega
    · subst h1
      rw [show m - 1 + 2 = m + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    · rw [show j - 1 + 2 = j + 1 by omega, h2, Nat.mod_self]
    · rw [show j - 1 + 2 = j + 1 by omega, Nat.mod_eq_of_lt (by omega)]
  -- either (i,k) = (pj, next j) or (i,k) = (next j, pj)
  have key : (i = pj ∧ k = (if j + 1 = m then 0 else j + 1)) ∨
      (k = pj ∧ i = (if j + 1 = m then 0 else j + 1)) := by
    rw [hpj]
    split_ifs <;> omega
  have hstep2' : (pj + 2) % m < m := by rw [hstep2]; split_ifs <;> omega
  rcases key with ⟨rfl, hk2⟩ | ⟨rfl, hi2⟩
  · refine no_three hG10 hC hm v pj hpjlt hvx ?_ ?_
    · have : (pj + 1) % m = j := hstep1
      simp only [← hmdef]
      rw [show ((C[(pj+1) % m]'(Nat.mod_lt _ (by omega))) = C[j]'hj) from by congr 1]
      exact hvy
    · simp only [← hmdef]
      rw [show ((C[(pj+2) % m]'(Nat.mod_lt _ (by omega))) = C[k]'hk) from by
        congr 1; rw [hstep2, hk2]]
      exact hvz
  · refine no_three hG10 hC hm v pj hpjlt hvz ?_ ?_
    · simp only [← hmdef]
      rw [show ((C[(pj+1) % m]'(Nat.mod_lt _ (by omega))) = C[j]'hj) from by congr 1]
      exact hvy
    · simp only [← hmdef]
      rw [show ((C[(pj+2) % m]'(Nat.mod_lt _ (by omega))) = C[i]'hi) from by
        congr 1; rw [hstep2, hi2]]
      exact hvx

/-- PAPER (2.3 + `G ∈ F₁₀`): for a vertex `v` off a hole `C` of length `≥ 6`, either no two
neighbours of `v` on `C` are adjacent, or `v` has exactly two neighbours on `C` and they are
adjacent. -/
theorem indep_or_two {G : SimpleGraph V} (hberge : Berge G)
    (hnowheel : ¬ ∃ (C : List V) (Y : Set V), IsWheel G C Y)
    (hG10 : ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
        ¬ ∃ v x y z : V, (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
          G.Adj v x ∧ G.Adj v y ∧ G.Adj v z)
    {C : List V} (hC : IsHoleList G C) (hm : 6 ≤ C.length) {v : V} (hv : v ∉ C) :
    (∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y)
      ∨ (∃ a b : V, {w : V | w ∈ C ∧ G.Adj v w} = {a, b} ∧ a ≠ b ∧ G.Adj a b) := by
  have hvc : ∀ w ∈ C, w ∉ ({v} : Set V) := by
    intro w hw hwv
    rw [Set.mem_singleton_iff] at hwv
    exact hv (hwv ▸ hw)
  have hVC : ∀ w : V, VertexComplete G w ({v} : Set V) ↔ G.Adj w v := by
    intro w
    constructor
    · intro h; exact h v rfl
    · intro h x hx; rw [Set.mem_singleton_iff] at hx; exact hx ▸ h
  have key := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hberge ({v} : Set V)
      (anticonn_singleton G v) C (Or.inr hC) hvc).2 hC
  rcases key with heven | ⟨a, b, hset, hab, hadjab⟩
  · -- even number of `{v}`-complete edges; we show there are none at all
    left
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, y, hy, hvx, hvy, hxy⟩ := hcon
    set Xed : Set (Sym2 V) :=
      {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧ EdgeComplete G ({v} : Set V) u w} with hXed
    have hmemxy : s(x, y) ∈ Xed :=
      ⟨x, hx, y, hy, rfl, hxy, (hVC x).mpr hvx.symm, (hVC y).mpr hvy.symm⟩
    have hpos : 0 < Xed.ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      exact ⟨_, hmemxy⟩
    have h1lt : 1 < Xed.ncard := by
      rcases heven with ⟨t, ht⟩
      omega
    obtain ⟨e₁, he₁, e₂, he₂, hne⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp h1lt
    obtain ⟨a, ha, b, hb, rfl, hEab⟩ := he₁
    obtain ⟨c, hc, d, hd, rfl, hEcd⟩ := he₂
    have hva : G.Adj v a := ((hVC a).mp hEab.2.1).symm
    have hvb : G.Adj v b := ((hVC b).mp hEab.2.2).symm
    have hvc' : G.Adj v c := ((hVC c).mp hEcd.2.1).symm
    have hvd : G.Adj v d := ((hVC d).mp hEcd.2.2).symm
    have hac : a ≠ c := by
      rintro rfl
      have hbd : b ≠ d := by rintro rfl; exact hne rfl
      exact no_three_v hG10 hC hm hb ha hd hEab.1.symm hEcd.1 hbd hvb hva hvd
    have had : a ≠ d := by
      rintro rfl
      have hbc : b ≠ c := by rintro rfl; exact hne (Sym2.eq_swap)
      exact no_three_v hG10 hC hm hb ha hc hEab.1.symm hEcd.1.symm hbc hvb hva hvc'
    have hbc : b ≠ c := by
      rintro rfl
      have had' : a ≠ d := by rintro rfl; exact hne (Sym2.eq_swap)
      exact no_three_v hG10 hC hm ha hb hd hEab.1 hEcd.1 had' hva hvb hvd
    have hbd : b ≠ d := by
      rintro rfl
      have hac' : a ≠ c := by rintro rfl; exact hne rfl
      exact no_three_v hG10 hC hm ha hb hc hEab.1 hEcd.1.symm hac' hva hvb hvc'
    exact hnowheel ⟨C, ({v} : Set V),
      ⟨hC, hm⟩, ⟨⟨v, rfl⟩, anticonn_singleton G v, hvc⟩,
      ⟨a, b, c, d, ha, hb, hc, hd, hEab, hEcd, hac, had, hbc, hbd⟩⟩
  · right
    refine ⟨a, b, ?_, hab, hadjab⟩
    rw [← hset]
    ext w
    simp only [Set.mem_setOf_eq, and_congr_right_iff]
    intro _
    rw [hVC w]
    exact ⟨fun h => h.symm, fun h => h.symm⟩

/-! ## Counting -/

/-- The set of positions of `C` occupied by a neighbour of `v`. -/
noncomputable def nbrIdx (G : SimpleGraph V) (v : V) (C : List V) : Finset ℕ :=
  @Finset.filter ℕ (fun i => ∃ h : i < C.length, G.Adj v (C[i]'h)) (Classical.decPred _)
    (Finset.range C.length)

theorem mem_nbrIdx {G : SimpleGraph V} {v : V} {C : List V} {i : ℕ} :
    i ∈ nbrIdx G v C ↔ ∃ h : i < C.length, G.Adj v (C[i]'h) := by
  simp only [nbrIdx, Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

theorem nbrIdx_subset {G : SimpleGraph V} {v : V} {C : List V} :
    nbrIdx G v C ⊆ Finset.range C.length := by
  intro i hi
  exact Finset.mem_range.mpr (mem_nbrIdx.mp hi).1

/-- The number of neighbours of `v` inside a `Finset` of vertices. -/
noncomputable def nbrCount (G : SimpleGraph V) (v : V) (X : Finset V) : ℕ :=
  (@Finset.filter V (fun y => G.Adj v y) (Classical.decPred _) X).card

theorem mem_nbrFilter {G : SimpleGraph V} {v : V} {X : Finset V} {y : V} :
    y ∈ (@Finset.filter V (fun y => G.Adj v y) (Classical.decPred _) X) ↔ y ∈ X ∧ G.Adj v y := by
  simp only [Finset.mem_filter]

theorem nbrCount_eq_card_nbrIdx (G : SimpleGraph V) (v : V) {C : List V} (hnd : C.Nodup) :
    nbrCount G v C.toFinset = (nbrIdx G v C).card := by
  unfold nbrCount
  refine (Finset.card_bij (fun (i : ℕ) (hi : i ∈ nbrIdx G v C) => C[i]'((mem_nbrIdx.mp hi).1))
    ?_ ?_ ?_).symm
  · intro a ha
    exact mem_nbrFilter.mpr ⟨List.mem_toFinset.mpr (List.getElem_mem _), (mem_nbrIdx.mp ha).2⟩
  · intro a ha b hb hab
    exact (List.Nodup.getElem_inj_iff hnd).mp hab
  · intro b hb
    obtain ⟨hbC, hadj⟩ := mem_nbrFilter.mp hb
    obtain ⟨k, hk, hkb⟩ := List.getElem_of_mem (List.mem_toFinset.mp hbC)
    exact ⟨k, mem_nbrIdx.mpr ⟨hk, by rw [hkb]; exact hadj⟩, hkb⟩

/-- The successor map on positions of a cycle of length `m`. -/
private def shiftm (m i : ℕ) : ℕ := (i + 1) % m

private theorem shiftm_lt {m : ℕ} (hm : 0 < m) (i : ℕ) : shiftm m i < m :=
  Nat.mod_lt _ hm

private theorem shiftm_inj {m : ℕ} {i j : ℕ} (hi : i < m) (hj : j < m)
    (h : shiftm m i = shiftm m j) : i = j := by
  unfold shiftm at h
  have e1 : (i + 1) % m = if i + 1 = m then 0 else i + 1 := by
    by_cases h' : i + 1 = m
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  have e2 : (j + 1) % m = if j + 1 = m then 0 else j + 1 := by
    by_cases h' : j + 1 = m
    · simp [h']
    · rw [if_neg h', Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h
  split_ifs at h <;> omega

/-- If no two neighbours of `v` on the hole `C` are adjacent, the neighbour positions and
their shifts are disjoint. -/
private theorem shift_disjoint {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) {v : V}
    (hindep : ∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y) :
    Disjoint (nbrIdx G v C) ((nbrIdx G v C).image (shiftm C.length)) := by
  have h4 : 4 ≤ C.length := hC.1
  rw [Finset.disjoint_left]
  intro j hj hj'
  obtain ⟨i, hi, hij⟩ := Finset.mem_image.mp hj'
  obtain ⟨hilt, hvi⟩ := mem_nbrIdx.mp hi
  obtain ⟨hjlt, hvj⟩ := mem_nbrIdx.mp hj
  refine hindep _ (List.getElem_mem hilt) _ (List.getElem_mem hjlt) hvi hvj ?_
  exact (HoleBasics.hole_adj_iff hC hilt hjlt).mpr (Or.inl hij.symm)

private theorem two_card_le {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) {v : V}
    (hindep : ∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y) :
    2 * (nbrIdx G v C).card ≤ C.length := by
  have h4 : 4 ≤ C.length := hC.1
  have himg : ((nbrIdx G v C).image (shiftm C.length)).card = (nbrIdx G v C).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    exact shiftm_inj (mem_nbrIdx.mp ha).1 (mem_nbrIdx.mp hb).1 hab
  have hsub : nbrIdx G v C ∪ (nbrIdx G v C).image (shiftm C.length) ⊆ Finset.range C.length := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact nbrIdx_subset h
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_range.mpr (shiftm_lt (by omega) k)
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (shift_disjoint hC hindep), himg,
    Finset.card_range] at hcard
  omega

/-- In the equality case, the neighbour positions and their shifts cover every position. -/
private theorem shift_cover {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) {v : V}
    (hindep : ∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y)
    (heq : 2 * (nbrIdx G v C).card = C.length) :
    nbrIdx G v C ∪ (nbrIdx G v C).image (shiftm C.length) = Finset.range C.length := by
  have h4 : 4 ≤ C.length := hC.1
  have himg : ((nbrIdx G v C).image (shiftm C.length)).card = (nbrIdx G v C).card := by
    refine Finset.card_image_of_injOn ?_
    intro a ha b hb hab
    exact shiftm_inj (mem_nbrIdx.mp ha).1 (mem_nbrIdx.mp hb).1 hab
  have hsub : nbrIdx G v C ∪ (nbrIdx G v C).image (shiftm C.length) ⊆ Finset.range C.length := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact nbrIdx_subset h
    · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_range.mpr (shiftm_lt (by omega) k)
  refine Finset.eq_of_subset_of_card_le hsub ?_
  rw [Finset.card_union_of_disjoint (shift_disjoint hC hindep), himg, Finset.card_range]
  omega

/-- The covering statement in vertex form: in the equality case, of two adjacent vertices of
`C` at least one is a neighbour of `v`. -/
private theorem cover_of_eq {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) {v : V}
    (hindep : ∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y)
    (heq : 2 * (nbrIdx G v C).card = C.length)
    {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hxy : G.Adj x y) :
    G.Adj v x ∨ G.Adj v y := by
  have h4 : 4 ≤ C.length := hC.1
  have hcov := shift_cover hC hindep heq
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
  have hrel := (HoleBasics.hole_adj_iff hC hi hj).mp hxy
  -- reduce to the case `j = (i+1) % m`
  have main : ∀ (p q : ℕ) (hp : p < C.length) (hq : q < C.length), q = (p + 1) % C.length →
      G.Adj v (C[p]'hp) ∨ G.Adj v (C[q]'hq) := by
    intro p q hp hq hpq
    have hqmem : q ∈ Finset.range C.length := Finset.mem_range.mpr hq
    rw [← hcov] at hqmem
    rcases Finset.mem_union.mp hqmem with h | h
    · exact Or.inr (mem_nbrIdx.mp h).2
    · obtain ⟨k, hk, hkq⟩ := Finset.mem_image.mp h
      have hkp : k = p := shiftm_inj (mem_nbrIdx.mp hk).1 hp (by rw [hkq, hpq]; rfl)
      subst hkp
      exact Or.inl (mem_nbrIdx.mp hk).2
  rcases hrel with h | h
  · exact main i j hi hj h
  · exact (main j i hj hi h).symm

/-! ## Double counting -/

theorem nbrCount_symm (G : SimpleGraph V) (X Y : Finset V) :
    ∑ x ∈ X, nbrCount G x Y = ∑ y ∈ Y, nbrCount G y X := by
  simp only [nbrCount, Finset.card_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  by_cases h : G.Adj x y
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh : G.Adj y x => h hh.symm)]

theorem nbrCount_add_compl (G : SimpleGraph V) (v : V) (Y : Finset V) :
    nbrCount G v Y + nbrCount Gᶜ v Y + (if v ∈ Y then 1 else 0) = Y.card := by
  have hlast : (if v ∈ Y then (1 : ℕ) else 0) = ∑ y ∈ Y, (if y = v then (1 : ℕ) else 0) :=
    (Finset.sum_ite_eq' Y v (fun _ => (1 : ℕ))).symm
  simp only [nbrCount, Finset.card_eq_sum_ones, Finset.sum_filter, hlast,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y = v
  · subst hy
    simp [SimpleGraph.irrefl]
  · by_cases hadj : G.Adj v y
    · have : ¬ Gᶜ.Adj v y := fun h => h.2 hadj
      simp [hadj, this, hy]
    · have : Gᶜ.Adj v y := ⟨fun h => hy h.symm, hadj⟩
      simp [hadj, this, hy]

/-- Every vertex of a hole has exactly two neighbours on it. -/
theorem nbrIdx_hole_card {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    {i : ℕ} (hi : i < C.length) : (nbrIdx G (C[i]'hi) C).card = 2 := by
  have h4 : 4 ≤ C.length := hC.1
  set m := C.length with hmdef
  set nx : ℕ := if i + 1 = m then 0 else i + 1 with hnx
  set pv : ℕ := if i = 0 then m - 1 else i - 1 with hpv
  have hnxlt : nx < m := by rw [hnx]; split_ifs <;> omega
  have hpvlt : pv < m := by rw [hpv]; split_ifs <;> omega
  have hne : nx ≠ pv := by rw [hnx, hpv]; split_ifs <;> omega
  have enx : (i + 1) % m = nx := by
    rw [hnx]; split_ifs with h
    · rw [h, Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
  have epv : (pv + 1) % m = i := by
    rw [hpv]; split_ifs with h
    · subst h; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    · rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hi]
  have hset : nbrIdx G (C[i]'hi) C = ({nx, pv} : Finset ℕ) := by
    ext j
    simp only [Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hj
      obtain ⟨hjlt, hadj⟩ := mem_nbrIdx.mp hj
      have hres := hole_adj_index hC hi hjlt hadj
      rw [hnx, hpv]
      split_ifs <;> omega
    · intro hj
      rcases hj with rfl | rfl
      · exact mem_nbrIdx.mpr ⟨hnxlt, (HoleBasics.hole_adj_iff hC hi hnxlt).mpr
          (Or.inl (by rw [← hmdef, enx]))⟩
      · exact mem_nbrIdx.mpr ⟨hpvlt, (HoleBasics.hole_adj_iff hC hi hpvlt).mpr
          (Or.inr (by rw [← hmdef, epv]))⟩
  rw [hset, Finset.card_pair hne]

theorem nbrCount_hole_eq_two {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    {x : V} (hx : x ∈ C) : nbrCount G x C.toFinset = 2 := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [nbrCount_eq_card_nbrIdx G _ hC.2.1, nbrIdx_hole_card hC hi]

/-! ## The final configuration -/

theorem final_config0 {G : SimpleGraph V} {C D : List V}
    (hC : IsHoleList G C) (hD : IsHoleList Gᶜ D)
    (hm : 6 ≤ C.length) (hn : 6 ≤ D.length)
    (hdisj : ∀ x ∈ C, x ∉ D)
    (hP1 : ∀ y ∈ D, ∀ x ∈ C, ∀ x' ∈ C, G.Adj x x' → (G.Adj y x ↔ ¬ G.Adj y x'))
    (hP2 : ∀ x ∈ C, ∀ y ∈ D, ∀ y' ∈ D, Gᶜ.Adj y y' → (G.Adj x y ↔ ¬ G.Adj x y'))
    (h00 : G.Adj (C[0]'(by omega)) (D[0]'(by omega))) :
    ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ := by
  obtain ⟨cc, hcceq⟩ : ∃ f : ℕ → V, ∀ i (h : i < C.length), f i = C[i]'h :=
    ⟨fun i => C.getD i (C[0]'(by omega)), fun i h => List.getD_eq_getElem _ _ h⟩
  obtain ⟨dd, hddeq⟩ : ∃ f : ℕ → V, ∀ j (h : j < D.length), f j = D[j]'h :=
    ⟨fun j => D.getD j (D[0]'(by omega)), fun j h => List.getD_eq_getElem _ _ h⟩
  have hccmem : ∀ i, i < C.length → cc i ∈ C := by
    intro i h; rw [hcceq i h]; exact List.getElem_mem h
  have hddmem : ∀ j, j < D.length → dd j ∈ D := by
    intro j h; rw [hddeq j h]; exact List.getElem_mem h
  have hccne : ∀ i j, i < C.length → j < C.length → i ≠ j → cc i ≠ cc j := by
    intro i j hi hj hij
    rw [hcceq i hi, hcceq j hj]
    exact HoleBasics.hole_ne_of_ne_index hC hi hj hij
  have hddne : ∀ i j, i < D.length → j < D.length → i ≠ j → dd i ≠ dd j := by
    intro i j hi hj hij
    rw [hddeq i hi, hddeq j hj]
    exact HoleBasics.hole_ne_of_ne_index hD hi hj hij
  have hcross : ∀ i j, i < C.length → j < D.length → cc i ≠ dd j := by
    intro i j hi hj he
    exact hdisj (cc i) (hccmem i hi) (he ▸ hddmem j hj)
  have hCedge : ∀ i, i + 1 < C.length → G.Adj (cc i) (cc (i + 1)) := by
    intro i hi
    rw [hcceq i (by omega), hcceq (i + 1) hi]
    exact HoleBasics.hole_adj_succ hC hi
  have hDedge : ∀ j, j + 1 < D.length → Gᶜ.Adj (dd j) (dd (j + 1)) := by
    intro j hj
    rw [hddeq j (by omega), hddeq (j + 1) hj]
    exact HoleBasics.hole_adj_succ hD hj
  have hCnon : ∀ i j, i < 5 → j < 5 → j ≠ i + 1 → i ≠ j + 1 → ¬ G.Adj (cc i) (cc j) := by
    intro i j hi hj h1 h2
    rw [hcceq i (by omega), hcceq j (by omega)]
    refine HoleBasics.hole_not_adj_of_gap' hC (by omega) (by omega) ?_ ?_
    · rw [Nat.mod_eq_of_lt (by omega)]; exact h1
    · rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  have hDnon : ∀ i j, i < 5 → j < 5 → j ≠ i + 1 → i ≠ j + 1 → ¬ Gᶜ.Adj (dd i) (dd j) := by
    intro i j hi hj h1 h2
    rw [hddeq i (by omega), hddeq j (by omega)]
    refine HoleBasics.hole_not_adj_of_gap' hD (by omega) (by omega) ?_ ?_
    · rw [Nat.mod_eq_of_lt (by omega)]; exact h1
    · rw [Nat.mod_eq_of_lt (by omega)]; exact h2
  have hGof : ∀ u v : V, u ≠ v → ¬ Gᶜ.Adj u v → G.Adj u v := by
    intro u v hne h
    by_contra hg
    exact h ⟨hne, hg⟩
  -- the base adjacency
  have hb0 : G.Adj (dd 0) (cc 0) := by
    rw [hcceq 0 (by omega), hddeq 0 (by omega)]
    exact h00.symm
  -- walk along `C` keeping `dd 0` fixed
  have hstepC : ∀ i, i + 1 < C.length → (G.Adj (dd 0) (cc i) ↔ ¬ G.Adj (dd 0) (cc (i + 1))) :=
    fun i hi => hP1 (dd 0) (hddmem 0 (by omega)) (cc i) (hccmem i (by omega))
      (cc (i + 1)) (hccmem (i + 1) hi) (hCedge i hi)
  have hb1 : ¬ G.Adj (dd 0) (cc 1) := (hstepC 0 (by omega)).mp hb0
  have hb2 : G.Adj (dd 0) (cc 2) := by
    by_contra h; exact hb1 ((hstepC 1 (by omega)).mpr h)
  have hb3 : ¬ G.Adj (dd 0) (cc 3) := (hstepC 2 (by omega)).mp hb2
  have hb4 : G.Adj (dd 0) (cc 4) := by
    by_contra h; exact hb3 ((hstepC 3 (by omega)).mpr h)
  -- walk along `D` keeping `cc i` fixed
  have hstepD : ∀ i j, i < C.length → j + 1 < D.length →
      (G.Adj (cc i) (dd j) ↔ ¬ G.Adj (cc i) (dd (j + 1))) :=
    fun i j hi hj => hP2 (cc i) (hccmem i hi) (dd j) (hddmem j (by omega))
      (dd (j + 1)) (hddmem (j + 1) hj) (hDedge j hj)
  have chain : ∀ i, i < C.length → G.Adj (cc i) (dd 0) →
      ¬ G.Adj (cc i) (dd 1) ∧ G.Adj (cc i) (dd 2) ∧ ¬ G.Adj (cc i) (dd 3) ∧
        G.Adj (cc i) (dd 4) := by
    intro i hi h0
    have h1 : ¬ G.Adj (cc i) (dd 1) := (hstepD i 0 hi (by omega)).mp h0
    have h2 : G.Adj (cc i) (dd 2) := by
      by_contra h; exact h1 ((hstepD i 1 hi (by omega)).mpr h)
    have h3 : ¬ G.Adj (cc i) (dd 3) := (hstepD i 2 hi (by omega)).mp h2
    have h4 : G.Adj (cc i) (dd 4) := by
      by_contra h; exact h3 ((hstepD i 3 hi (by omega)).mpr h)
    exact ⟨h1, h2, h3, h4⟩
  have chain' : ∀ i, i < C.length → ¬ G.Adj (cc i) (dd 0) →
      G.Adj (cc i) (dd 1) ∧ ¬ G.Adj (cc i) (dd 2) ∧ G.Adj (cc i) (dd 3) ∧
        ¬ G.Adj (cc i) (dd 4) := by
    intro i hi h0
    have h1 : G.Adj (cc i) (dd 1) := by
      by_contra h; exact h0 ((hstepD i 0 hi (by omega)).mpr h)
    have h2 : ¬ G.Adj (cc i) (dd 2) := (hstepD i 1 hi (by omega)).mp h1
    have h3 : G.Adj (cc i) (dd 3) := by
      by_contra h; exact h2 ((hstepD i 2 hi (by omega)).mpr h)
    have h4 : ¬ G.Adj (cc i) (dd 4) := (hstepD i 3 hi (by omega)).mp h3
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨r01, r02, r03, r04⟩ := chain 0 (by omega) hb0.symm
  obtain ⟨r11, r12, r13, r14⟩ := chain' 1 (by omega) (fun h => hb1 h.symm)
  obtain ⟨r31, r32, r33, r34⟩ := chain' 3 (by omega) (fun h => hb3 h.symm)
  obtain ⟨r41, r42, r43, r44⟩ := chain 4 (by omega) hb4.symm
  -- distinctness of the eight vertices
  have e1 : dd 0 ≠ dd 4 := hddne 0 4 (by omega) (by omega) (by omega)
  have e2 : dd 0 ≠ cc 0 := fun h => hcross 0 0 (by omega) (by omega) h.symm
  have e3 : dd 0 ≠ cc 4 := fun h => hcross 4 0 (by omega) (by omega) h.symm
  have e4 : dd 0 ≠ dd 3 := hddne 0 3 (by omega) (by omega) (by omega)
  have e5 : dd 0 ≠ dd 1 := hddne 0 1 (by omega) (by omega) (by omega)
  have e6 : dd 0 ≠ cc 1 := fun h => hcross 1 0 (by omega) (by omega) h.symm
  have e7 : dd 0 ≠ cc 3 := fun h => hcross 3 0 (by omega) (by omega) h.symm
  have e8 : dd 4 ≠ cc 0 := fun h => hcross 0 4 (by omega) (by omega) h.symm
  have e9 : dd 4 ≠ cc 4 := fun h => hcross 4 4 (by omega) (by omega) h.symm
  have e10 : dd 4 ≠ dd 3 := hddne 4 3 (by omega) (by omega) (by omega)
  have e11 : dd 4 ≠ dd 1 := hddne 4 1 (by omega) (by omega) (by omega)
  have e12 : dd 4 ≠ cc 1 := fun h => hcross 1 4 (by omega) (by omega) h.symm
  have e13 : dd 4 ≠ cc 3 := fun h => hcross 3 4 (by omega) (by omega) h.symm
  have e14 : cc 0 ≠ cc 4 := hccne 0 4 (by omega) (by omega) (by omega)
  have e15 : cc 0 ≠ dd 3 := hcross 0 3 (by omega) (by omega)
  have e16 : cc 0 ≠ dd 1 := hcross 0 1 (by omega) (by omega)
  have e17 : cc 0 ≠ cc 1 := hccne 0 1 (by omega) (by omega) (by omega)
  have e18 : cc 0 ≠ cc 3 := hccne 0 3 (by omega) (by omega) (by omega)
  have e19 : cc 4 ≠ dd 3 := hcross 4 3 (by omega) (by omega)
  have e20 : cc 4 ≠ dd 1 := hcross 4 1 (by omega) (by omega)
  have e21 : cc 4 ≠ cc 1 := hccne 4 1 (by omega) (by omega) (by omega)
  have e22 : cc 4 ≠ cc 3 := hccne 4 3 (by omega) (by omega) (by omega)
  have e23 : dd 3 ≠ dd 1 := hddne 3 1 (by omega) (by omega) (by omega)
  have e24 : dd 3 ≠ cc 1 := fun h => hcross 1 3 (by omega) (by omega) h.symm
  have e25 : dd 3 ≠ cc 3 := fun h => hcross 3 3 (by omega) (by omega) h.symm
  have e26 : dd 1 ≠ cc 1 := fun h => hcross 1 1 (by omega) (by omega) h.symm
  have e27 : dd 1 ≠ cc 3 := fun h => hcross 3 1 (by omega) (by omega) h.symm
  have e28 : cc 1 ≠ cc 3 := hccne 1 3 (by omega) (by omega) (by omega)
  refine ⟨dd 0, dd 4, cc 0, cc 4, dd 3, dd 1, cc 1, cc 3, ?_, ?_, ?_, ?_, ?_⟩
  · simp [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18,
      e19, e20, e21, e22, e23, e24, e25, e26, e27, e28]
  · exact ⟨hGof _ _ e1 (hDnon 0 4 (by omega) (by omega) (by omega) (by omega)),
      hb0, hb4, r04.symm, r44.symm, hCnon 0 4 (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨hGof _ _ e23 (hDnon 3 1 (by omega) (by omega) (by omega) (by omega)),
      r13.symm, r33.symm, r11.symm, r31.symm,
      hCnon 1 3 (by omega) (by omega) (by omega) (by omega)⟩
  · exact ⟨hGof _ _ e4 (hDnon 0 3 (by omega) (by omega) (by omega) (by omega)),
      hGof _ _ e11 (hDnon 4 1 (by omega) (by omega) (by omega) (by omega)),
      hCedge 0 (by omega), (hCedge 3 (by omega)).symm⟩
  · refine ⟨(hDedge 0 (by omega)).2, hb1, hb3, ?_, fun h => r14 h.symm, fun h => r34 h.symm,
      r03, r01, hCnon 0 3 (by omega) (by omega) (by omega) (by omega),
      r43, r41, hCnon 4 1 (by omega) (by omega) (by omega) (by omega)⟩
    exact fun h => (hDedge 3 (by omega)).2 h.symm

theorem final_config {G : SimpleGraph V} {C D : List V}
    (hC : IsHoleList G C) (hD : IsHoleList Gᶜ D)
    (hm : 6 ≤ C.length) (hn : 6 ≤ D.length)
    (hdisj : ∀ x ∈ C, x ∉ D)
    (hP1 : ∀ y ∈ D, ∀ x ∈ C, ∀ x' ∈ C, G.Adj x x' → (G.Adj y x ↔ ¬ G.Adj y x'))
    (hP2 : ∀ x ∈ C, ∀ y ∈ D, ∀ y' ∈ D, Gᶜ.Adj y y' → (G.Adj x y ↔ ¬ G.Adj x y'))
    (hex : ∃ x ∈ C, ∃ y ∈ D, G.Adj x y) :
    ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hex
  obtain ⟨i0, hi0, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem hy
  have hlenC : (C.rotate i0).length = C.length := by simp
  have hlenD : (D.rotate j0).length = D.length := by simp
  refine final_config0 (HoleBasics.isHoleList_rotate hC i0) (HoleBasics.isHoleList_rotate hD j0)
    (by rw [hlenC]; exact hm) (by rw [hlenD]; exact hn)
    (fun z hz hz' => hdisj z (List.mem_rotate.mp hz) (List.mem_rotate.mp hz'))
    (fun yy hyy xx hxx xx' hxx' hadj => hP1 yy (List.mem_rotate.mp hyy) xx
      (List.mem_rotate.mp hxx) xx' (List.mem_rotate.mp hxx') hadj)
    (fun xx hxx yy hyy yy' hyy' hadj => hP2 xx (List.mem_rotate.mp hxx) yy
      (List.mem_rotate.mp hyy) yy' (List.mem_rotate.mp hyy') hadj) ?_
  have e1 : (C.rotate i0)[0]'(by rw [hlenC]; omega) = C[i0]'hi0 := by
    simp only [List.getElem_rotate, Nat.zero_add, Nat.mod_eq_of_lt hi0]
  have e2 : (D.rotate j0)[0]'(by rw [hlenD]; omega) = D[j0]'hj0 := by
    simp only [List.getElem_rotate, Nat.zero_add, Nat.mod_eq_of_lt hj0]
  rw [e1, e2]
  exact hxy

/-! ## The per-vertex half bound -/

theorem half_facts {G : SimpleGraph V} (hberge : Berge G)
    (hnw : ¬ ∃ (C : List V) (Y : Set V), IsWheel G C Y)
    (hf10 : ∀ C : List V, IsHoleList G C → 6 ≤ holeLength C →
        ¬ ∃ v x y z : V, (∃ k : ℕ, [x, y, z] <+: C.rotate k) ∧
          G.Adj v x ∧ G.Adj v y ∧ G.Adj v z)
    {C : List V} (hC : IsHoleList G C) (hm : 6 ≤ C.length) {v : V} (hv : v ∉ C) :
    2 * nbrCount G v C.toFinset ≤ C.length ∧
      (2 * nbrCount G v C.toFinset = C.length →
        (∀ x ∈ C, ∀ y ∈ C, G.Adj v x → G.Adj v y → ¬ G.Adj x y) ∧
        (∀ x ∈ C, ∀ y ∈ C, G.Adj x y → (G.Adj v x ∨ G.Adj v y))) := by
  have hnd : C.Nodup := hC.2.1
  rcases indep_or_two hberge hnw hf10 hC hm hv with hindep | ⟨a, b, hset, hab, hadjab⟩
  · rw [nbrCount_eq_card_nbrIdx G v hnd]
    exact ⟨two_card_le hC hindep, fun heq =>
      ⟨hindep, fun x hx y hy hxy => cover_of_eq hC hindep heq hx hy hxy⟩⟩
  · have hfe : (@Finset.filter V (fun y => G.Adj v y) (Classical.decPred _) C.toFinset)
        = ({a, b} : Finset V) := by
      ext u
      rw [mem_nbrFilter, List.mem_toFinset, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hu
        have h1 : u ∈ ({a, b} : Set V) := hset ▸ hu
        simpa using h1
      · intro hu
        have h1 : u ∈ ({a, b} : Set V) := by rcases hu with rfl | rfl <;> simp
        rw [← hset] at h1
        exact h1
    have hcard : nbrCount G v C.toFinset = 2 := by
      unfold nbrCount
      rw [hfe, Finset.card_pair hab]
    rw [hcard]
    exact ⟨by omega, fun heq => absurd heq (by omega)⟩

/-! ## The arithmetic of the printed calculation -/

theorem arith (m n aa bb w E F : ℕ)
    (hmaa : m = aa + w) (hnbb : n = bb + w) (hm6 : 6 ≤ m) (hn6 : 6 ≤ n)
    (hid : E + F + w = m * n)
    (h1 : 2 * E ≤ bb * m + w * 4) (h2 : 2 * F ≤ aa * n + w * 4) :
    w = 0 ∧ 2 * E = m * n ∧ 2 * F = m * n := by
  have hw : w = 0 := by
    by_contra hne
    have hw1 : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr hne
    have hkey : 2 * (m * n) ≤ bb * m + aa * n + 10 * w := by omega
    rw [hmaa, hnbb] at hkey
    have hexp : (aa + bb + 2 * w) * w ≤ 10 * w := by nlinarith [hkey]
    have h12 : 12 ≤ aa + bb + 2 * w := by omega
    have hfin : 12 * w ≤ (aa + bb + 2 * w) * w := Nat.mul_le_mul_right w h12
    omega
  subst hw
  rw [Nat.add_zero] at hmaa hnbb
  subst hmaa
  subst hnbb
  have hc : n * m = m * n := Nat.mul_comm n m
  refine ⟨rfl, ?_, ?_⟩ <;> omega

/-! ## The theorem -/

theorem thm_23_5_main (G : SimpleGraph V) (hG : InF10 G) :
    ¬ ((∃ C : List V, IsHoleList G C ∧ 6 ≤ holeLength C) ∧
        (∃ D : List V, IsAntiholeList G D ∧ 6 ≤ holeLength D)) := by
  rintro ⟨⟨C, hC, hm⟩, ⟨D, hD, hn⟩⟩
  have hberge : Berge G := hG.1.1.1.1.1.1.1
  have hbergec : Berge Gᶜ := HoleBasics.berge_compl.mpr hberge
  have hnw : ¬ ∃ (c : List V) (Y : Set V), IsWheel G c Y := hG.1.2.1
  have hnwc : ¬ ∃ (c : List V) (Y : Set V), IsWheel Gᶜ c Y := hG.1.2.2
  have hf10 := hG.2.1
  have hf10c := hG.2.2
  have hndd : ¬ ∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ :=
    hG.1.1.1.1.2
  have hD' : IsHoleList Gᶜ D := hD
  have hmC : 6 ≤ C.length := hm
  have hnD : 6 ≤ D.length := hn
  have hCnd : C.Nodup := hC.2.1
  have hDnd : D.Nodup := hD'.2.1
  have hCcard : C.toFinset.card = C.length := List.toFinset_card_of_nodup hCnd
  have hDcard : D.toFinset.card = D.length := List.toFinset_card_of_nodup hDnd
  -- the two per-vertex facts, for `G, C` and for `Ḡ, D`
  have HC : ∀ v : V, v ∉ C → _ := fun v hv => half_facts hberge hnw hf10 hC hmC hv
  have HD : ∀ v : V, v ∉ D → _ := fun v hv => half_facts hbergec hnwc hf10c hD' hnD hv
  -- the two sums, and the identity `E + F + w = m n`
  have hwsum : ∑ u ∈ C.toFinset, (if u ∈ D.toFinset then (1 : ℕ) else 0)
      = (C.toFinset ∩ D.toFinset).card := by
    rw [Finset.sum_ite_mem, Finset.sum_const, smul_eq_mul, mul_one]
  have hid : (∑ u ∈ C.toFinset, nbrCount G u D.toFinset)
      + (∑ u ∈ C.toFinset, nbrCount Gᶜ u D.toFinset)
      + (C.toFinset ∩ D.toFinset).card = C.length * D.length := by
    rw [← hwsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun u _ => nbrCount_add_compl G u D.toFinset),
      Finset.sum_const, smul_eq_mul, hCcard, hDcard]
  -- the first printed inequality
  have hb1 : 2 * (∑ u ∈ C.toFinset, nbrCount G u D.toFinset)
      ≤ (D.toFinset \ C.toFinset).card * C.length + (C.toFinset ∩ D.toFinset).card * 4 := by
    rw [nbrCount_symm G C.toFinset D.toFinset, Finset.mul_sum]
    have hdisj : Disjoint (D.toFinset \ C.toFinset) (D.toFinset ∩ C.toFinset) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hx').2
    have hsplit : ∑ v ∈ D.toFinset, 2 * nbrCount G v C.toFinset
        = ∑ v ∈ D.toFinset \ C.toFinset, 2 * nbrCount G v C.toFinset
          + ∑ v ∈ D.toFinset ∩ C.toFinset, 2 * nbrCount G v C.toFinset := by
      rw [← Finset.sum_union hdisj, Finset.sdiff_union_inter]
    rw [hsplit]
    have hpart1 : ∑ v ∈ D.toFinset \ C.toFinset, 2 * nbrCount G v C.toFinset
        ≤ (D.toFinset \ C.toFinset).card * C.length := by
      refine le_trans (Finset.sum_le_sum ?_) (by rw [Finset.sum_const, smul_eq_mul])
      intro v hv
      exact (HC v (fun hvC => (Finset.mem_sdiff.mp hv).2 (List.mem_toFinset.mpr hvC))).1
    have hpart2 : ∑ v ∈ D.toFinset ∩ C.toFinset, 2 * nbrCount G v C.toFinset
        = (C.toFinset ∩ D.toFinset).card * 4 := by
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [nbrCount_hole_eq_two hC (List.mem_toFinset.mp (Finset.mem_inter.mp hv).2)]),
        Finset.sum_const, smul_eq_mul, Finset.inter_comm]
    omega
  -- the same argument in the complement
  have hb2 : 2 * (∑ u ∈ C.toFinset, nbrCount Gᶜ u D.toFinset)
      ≤ (C.toFinset \ D.toFinset).card * D.length + (C.toFinset ∩ D.toFinset).card * 4 := by
    rw [Finset.mul_sum]
    have hdisj : Disjoint (C.toFinset \ D.toFinset) (C.toFinset ∩ D.toFinset) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hx').2
    have hsplit : ∑ v ∈ C.toFinset, 2 * nbrCount Gᶜ v D.toFinset
        = ∑ v ∈ C.toFinset \ D.toFinset, 2 * nbrCount Gᶜ v D.toFinset
          + ∑ v ∈ C.toFinset ∩ D.toFinset, 2 * nbrCount Gᶜ v D.toFinset := by
      rw [← Finset.sum_union hdisj, Finset.sdiff_union_inter]
    rw [hsplit]
    have hpart1 : ∑ v ∈ C.toFinset \ D.toFinset, 2 * nbrCount Gᶜ v D.toFinset
        ≤ (C.toFinset \ D.toFinset).card * D.length := by
      refine le_trans (Finset.sum_le_sum ?_) (by rw [Finset.sum_const, smul_eq_mul])
      intro v hv
      exact (HD v (fun hvD => (Finset.mem_sdiff.mp hv).2 (List.mem_toFinset.mpr hvD))).1
    have hpart2 : ∑ v ∈ C.toFinset ∩ D.toFinset, 2 * nbrCount Gᶜ v D.toFinset
        = (C.toFinset ∩ D.toFinset).card * 4 := by
      rw [Finset.sum_congr rfl (fun v hv => by
        rw [nbrCount_hole_eq_two hD' (List.mem_toFinset.mp (Finset.mem_inter.mp hv).2)]),
        Finset.sum_const, smul_eq_mul]
    omega
  -- `w(a + b + 2w − 10) ≤ 0`, hence `w = 0` and equality throughout
  obtain ⟨hw0, heq1, heq2⟩ := arith C.length D.length (C.toFinset \ D.toFinset).card
    (D.toFinset \ C.toFinset).card (C.toFinset ∩ D.toFinset).card
    (∑ u ∈ C.toFinset, nbrCount G u D.toFinset)
    (∑ u ∈ C.toFinset, nbrCount Gᶜ u D.toFinset)
    (by rw [← hCcard]; exact (Finset.card_sdiff_add_card_inter C.toFinset D.toFinset).symm)
    (by rw [← hDcard, Finset.inter_comm C.toFinset D.toFinset]
        exact (Finset.card_sdiff_add_card_inter D.toFinset C.toFinset).symm)
    hmC hnD hid hb1 hb2
  -- `C` and `D` are disjoint
  have hdisjCD : ∀ x ∈ C, x ∉ D := by
    intro x hx hxD
    have : x ∈ C.toFinset ∩ D.toFinset :=
      Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hx, List.mem_toFinset.mpr hxD⟩
    rw [Finset.card_eq_zero.mp hw0] at this
    simp at this
  -- every vertex of `D` is adjacent to exactly half the vertices of `C`, and conversely
  have hexactC : ∀ v ∈ D.toFinset, 2 * nbrCount G v C.toFinset = C.length := by
    have hle : ∀ v ∈ D.toFinset, 2 * nbrCount G v C.toFinset ≤ C.length := by
      intro v hv
      exact (HC v (fun hvC => hdisjCD v hvC (List.mem_toFinset.mp hv))).1
    refine (Finset.sum_eq_sum_iff_of_le hle).mp ?_
    rw [Finset.sum_const, smul_eq_mul, hDcard, ← Finset.mul_sum,
      ← nbrCount_symm G C.toFinset D.toFinset, heq1, Nat.mul_comm]
  have hexactD : ∀ v ∈ C.toFinset, 2 * nbrCount Gᶜ v D.toFinset = D.length := by
    have hle : ∀ v ∈ C.toFinset, 2 * nbrCount Gᶜ v D.toFinset ≤ D.length := by
      intro v hv
      exact (HD v (fun hvD => hdisjCD v (List.mem_toFinset.mp hv) hvD)).1
    refine (Finset.sum_eq_sum_iff_of_le hle).mp ?_
    rw [Finset.sum_const, smul_eq_mul, hCcard, ← Finset.mul_sum, heq2]
  -- the alternation of the neighbours, in `G` along `C` and in `Ḡ` along `D`
  have hP1 : ∀ y ∈ D, ∀ x ∈ C, ∀ x' ∈ C, G.Adj x x' → (G.Adj y x ↔ ¬ G.Adj y x') := by
    intro y hy x hx x' hx' hxx'
    obtain ⟨hindep, hcov⟩ :=
      (HC y (fun hyC => hdisjCD y hyC hy)).2 (hexactC y (List.mem_toFinset.mpr hy))
    constructor
    · intro h h'
      exact hindep x hx x' hx' h h' hxx'
    · intro h
      rcases hcov x hx x' hx' hxx' with h' | h'
      · exact h'
      · exact absurd h' h
  have hP2 : ∀ x ∈ C, ∀ y ∈ D, ∀ y' ∈ D, Gᶜ.Adj y y' → (G.Adj x y ↔ ¬ G.Adj x y') := by
    intro x hx y hy y' hy' hyy'
    obtain ⟨hindep, hcov⟩ :=
      (HD x (fun hxD => hdisjCD x hx hxD)).2 (hexactD x (List.mem_toFinset.mpr hx))
    have hcompl : ∀ z ∈ D, (Gᶜ.Adj x z ↔ ¬ G.Adj x z) := by
      intro z hz
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨fun he => hdisjCD x hx (he ▸ hz), h⟩
    constructor
    · intro h h'
      rcases hcov y hy y' hy' hyy' with hc | hc
      · exact (hcompl y hy).mp hc h
      · exact (hcompl y' hy').mp hc h'
    · intro h
      by_contra hg
      exact hindep y hy y' hy' ((hcompl y hy).mpr hg) ((hcompl y' hy').mpr h) hyy'
  -- some vertex of `C` has a neighbour in `D`
  have hex : ∃ x ∈ C, ∃ y ∈ D, G.Adj x y := by
    have hDne : D ≠ [] := by intro h; rw [h] at hnD; simp at hnD
    obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil D hDne
    have hyc := hexactC y (List.mem_toFinset.mpr hy)
    have hpos : 0 < nbrCount G y C.toFinset := by omega
    unfold nbrCount at hpos
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, List.mem_toFinset.mp (mem_nbrFilter.mp hx).1, y, hy,
      (mem_nbrFilter.mp hx).2.symm⟩
  exact hndd (final_config hC hD' hmC hnD hdisjCD hP1 hP2 hex)
end Thm235Helpers

/-! ## The statement, in its frozen context -/

namespace Workspace.Statements.S23

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **23.5** -- one of the twelve main steps: this is statement **1.8.11** (printed
p. 143), introduced by *"This has the following useful corollary, which is
1.8.11."*

PAPER: *"Let `G ∈ F₁₀`; then `G` does not contain both a hole of length `≥ 6` and
an antihole of length `≥ 6`.  In particular, for every recalcitrant graph `G`, one
of `G, Ḡ` belongs to `F₁₁`."* -/
theorem thm_23_5 (G : SimpleGraph V) (hG : InF10 G) :
    ¬ ((∃ C : List V, IsHoleList G C ∧ 6 ≤ holeLength C) ∧
        (∃ D : List V, IsAntiholeList G D ∧ 6 ≤ holeLength D)) :=
  Thm235Helpers.thm_23_5_main G hG


end SPGT

end Workspace.Statements.S23
