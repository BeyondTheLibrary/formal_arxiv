import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.ProofLemmas.AnticomponentOfSkewSideBasics

/-!
# Claim (1), case 1: no odd hole of `G'` through the new vertex

§3.1 of the proof of 1.5, verbatim:

> *"Suppose first that there is an odd hole, `C` say.  Then the neighbours of `z` in
> `C` (say `x, y`) belong to `B₁`, and no other vertex of `B₁` is in `C`.  No vertex
> of `B \ B₁` is in `C` since it would be adjacent to `x, y` and `C` would have
> length 4; so `C \ z` is an odd path of `G`, with ends in `B₁` and with interior in
> `A`, contradicting that `(A, B)` is balanced."*

Assume `k := holeLength c` is odd, so `k ≥ 5`; rotate `z` to position `0`; its two
neighbours `x = c[1]`, `y = c[k−1]` lie in `Sum.inl '' B₁`; no third vertex of `B₁`
and — by `AnticomponentOfSkewSideBasics.complete_sdiff` — no vertex of `B \ B₁` can
lie on `c`, since either would force `k = 4`; so `c.tail` pulls back along `Sum.inl`
to an odd path of `G` between the nonadjacent `x₀, y₀ ∈ B₁ ⊆ B` with interior in `A`,
which clause (S4a) of `SPGT.Balanced` forbids.

Note that `Berge G` is **not** a hypothesis: this case never uses it (it is needed
only for the branch of claim (1) where the hole avoids `z`).  This is the only place
where clause (S4a) of balancedness is used in the whole proof.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoOddHoleThroughAddedVertex

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport

/-- The cyclic successor `(i + 1) % n` of an index `i < n`, with the `%` eliminated. -/
private theorem succ_mod {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- Rewriting the index of a `getElem`. -/
private theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-- Every hole of `G' = G +ᵥ B₁` that passes through the new vertex `z = Sum.inr ()`
has even length. -/
theorem even_holeLength_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B B₁ : Set V}
    (hAB : A ∪ B = Set.univ) (hbal : SPGT.Balanced G A B)
    (hB₁ : IsAnticomponent G B B₁)
    {c : List (V ⊕ Unit)} (hc : IsHoleList (addPendantVertex G B₁) c)
    (hz : (Sum.inr () : V ⊕ Unit) ∈ c) :
    Even (holeLength c) := by
  classical
  by_contra hnoteven
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hnoteven
  -- `k ≥ 4` and `k` is odd, so `k ≥ 5`
  have hc4 : 4 ≤ c.length := hc.1
  have hlen5 : 5 ≤ c.length := by
    have : holeLength c = c.length := rfl
    omega
  -- rotate `z` into position `0`
  obtain ⟨d, hd, hdlen, hd0, hdmem⟩ :
      ∃ d : List (V ⊕ Unit), IsHoleList (addPendantVertex G B₁) d ∧ d.length = c.length ∧
        (∀ h : 0 < d.length, (d[0]'h) = Sum.inr ()) ∧ (∀ u, u ∈ d ↔ u ∈ c) := by
    obtain ⟨m, hm, hmz⟩ := List.getElem_of_mem hz
    refine ⟨c.rotate m, HoleBasics.isHoleList_rotate hc m, List.length_rotate .., ?_,
      fun u => List.mem_rotate⟩
    intro h
    simp only [List.getElem_rotate]
    exact (getElem_congr_idx c _ hm
      (by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hm)).trans hmz
  have hlen : 5 ≤ d.length := by omega
  -- 1. the neighbours of `z` on the hole are exactly `d[1]` and `d[k-1]`
  have hzx : (addPendantVertex G B₁).Adj (d[0]'(by omega)) (d[1]'(by omega)) :=
    (HoleMinusVertexPath.adj_head_iff hd hlen (by omega)).mpr (Or.inl rfl)
  have hzy : (addPendantVertex G B₁).Adj (d[0]'(by omega)) (d[d.length - 1]'(by omega)) :=
    (HoleMinusVertexPath.adj_head_iff hd hlen (by omega)).mpr (Or.inr rfl)
  rw [hd0 (by omega)] at hzx hzy
  -- 2. "the neighbours of `z` in `C` (say `x, y`) belong to `B₁`"
  have hinl : ∀ t : V ⊕ Unit, (addPendantVertex G B₁).Adj (Sum.inr ()) t →
      ∃ w : V, t = Sum.inl w ∧ w ∈ B₁ := by
    rintro (a | u) h
    · exact ⟨a, rfl, h⟩
    · exact absurd h (not_adj_inr_inr G B₁ () u)
  obtain ⟨x₀, hx0, hx0B₁⟩ := hinl _ hzx
  obtain ⟨y₀, hy0, hy0B₁⟩ := hinl _ hzy
  have hcompl : Complete G B₁ (B \ B₁) :=
    AnticomponentOfSkewSideBasics.complete_sdiff G hB₁
  -- 3. "and no other vertex of `B₁` is in `C`"; 4. "no vertex of `B \ B₁` is in `C`
  -- since it would be adjacent to `x, y` and `C` would have length 4"
  have hkey : ∀ (w : V) (j : ℕ) (hj : j < d.length), (d[j]'hj) = Sum.inl w → w ∈ B →
      ((d[j]'hj) = (d[1]'(by omega)) ∨ (d[j]'hj) = (d[d.length - 1]'(by omega))) := by
    intro w j hj hjw hwB
    by_cases hwB₁ : w ∈ B₁
    · -- a third vertex of `B₁` would be a third neighbour of `z`
      have hadj : (addPendantVertex G B₁).Adj (d[0]'(by omega)) (d[j]'hj) := by
        rw [hd0 (by omega), hjw]
        exact hwB₁
      rcases (HoleMinusVertexPath.adj_head_iff hd hlen hj).mp hadj with h1 | h1
      · exact Or.inl (getElem_congr_idx d hj (by omega) h1)
      · exact Or.inr (getElem_congr_idx d hj (by omega) h1)
    · -- a vertex of `B \ B₁` is complete to `B₁` (P3), so adjacent to both `x` and `y`;
      -- the two index conditions force `2 = k - 2`, i.e. `k = 4`
      exfalso
      have hj0 : j ≠ 0 := by
        rintro rfl
        rw [hd0 (by omega)] at hjw
        exact absurd hjw (by simp)
      have hax : (addPendantVertex G B₁).Adj (d[1]'(by omega)) (d[j]'hj) := by
        rw [hx0, hjw]
        exact hcompl x₀ hx0B₁ w ⟨hwB, hwB₁⟩
      have hay : (addPendantVertex G B₁).Adj (d[d.length - 1]'(by omega)) (d[j]'hj) := by
        rw [hy0, hjw]
        exact hcompl y₀ hy0B₁ w ⟨hwB, hwB₁⟩
      have e1 := (HoleBasics.hole_adj_iff hd (show 1 < d.length by omega) hj).mp hax
      have e2 := (HoleBasics.hole_adj_iff hd (show d.length - 1 < d.length by omega) hj).mp hay
      have m1 : (1 + 1) % d.length = 2 := Nat.mod_eq_of_lt (by omega)
      have m2 : (d.length - 1 + 1) % d.length = 0 := by
        rw [show d.length - 1 + 1 = d.length from by omega, Nat.mod_self]
      have m3 : (j + 1) % d.length = if j + 1 = d.length then 0 else j + 1 := succ_mod hj
      rw [m1, m3] at e1
      rw [m2, m3] at e2
      by_cases hjn : j + 1 = d.length
      · rw [if_pos hjn] at e1 e2
        omega
      · rw [if_neg hjn] at e1 e2
        omega
  -- 5. "so `C \ z` is an odd path of `G`, with ends in `B₁` and with interior in `A`"
  have hpath : IsPathFrom (addPendantVertex G B₁) d.tail
      (d[1]'(by omega)) (d[d.length - 1]'(by omega)) :=
    HoleMinusVertexPath.isPathFrom_tail hd hlen
  have hqz : ∀ u ∈ d.tail, u ≠ (Sum.inr () : V ⊕ Unit) := by
    intro u hu
    rw [HoleMinusVertexPath.mem_tail_iff hd hlen u] at hu
    rw [← hd0 (by omega)]
    exact hu.2
  obtain ⟨q₀, hq₀, hq₀len⟩ := exists_eq_map_inl hqz
  have hpath0 : IsPathFrom G q₀ x₀ y₀ := by
    rw [isPathFrom_map_inl G B₁ q₀ x₀ y₀, ← hq₀, ← hx0, ← hy0]
    exact hpath
  have hnadj : ¬ G.Adj x₀ y₀ := by
    have h := HoleMinusVertexPath.ends_not_adj hd hlen
    rw [hx0, hy0, adj_inl_inl] at h
    exact h
  have hint : ∀ u ∈ SPGT.interior q₀, u ∈ A := by
    intro u hu
    have hmapu : (Sum.inl u : V ⊕ Unit) ∈ SPGT.interior d.tail := by
      rw [hq₀, interior_map]
      exact List.mem_map_of_mem hu
    rw [HoleMinusVertexPath.mem_interior_tail_iff hd hlen _] at hmapu
    obtain ⟨humem, -, hune1, hune2⟩ := hmapu
    have huB : u ∉ B := by
      intro hB
      obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem humem
      rcases hkey u j hj hjeq hB with h1 | h1
      · exact hune1 (hjeq.symm.trans h1)
      · exact hune2 (hjeq.symm.trans h1)
    rcases (hAB ▸ Set.mem_univ u : u ∈ A ∪ B) with h | h
    · exact h
    · exact absurd h huB
  have hodd : Odd (pathLength q₀) := by
    have hpl : pathLength (q₀.map (Sum.inl : V → V ⊕ Unit)) = pathLength q₀ :=
      pathLength_map Sum.inl q₀
    rw [← hpl, ← hq₀, HoleMinusVertexPath.pathLength_tail hd hlen, Nat.odd_iff]
    have : holeLength c = c.length := rfl
    omega
  -- 6. "contradicting that `(A, B)` is balanced" — clause (S4a)
  exact hbal.1 x₀ y₀ q₀ (hB₁.1 hx0B₁) (hB₁.1 hy0B₁) hnadj hpath0 hint hodd

end Workspace.ProofLemmas.NoOddHoleThroughAddedVertex
