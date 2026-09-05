import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.AddPendantVertexTransport
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.ProofLemmas.AnticomponentOfSkewSideBasics

/-!
# Claim (1), case 2: no odd antihole of `G'` through the new vertex

§3.2 of the proof of 1.5, verbatim:

> *"Now assume there is an odd antihole `D` in `G'`, again using `z`.  Then exactly
> two vertices of `D \ z` are nonadjacent to `z`, so all the others belong to `B₁`.
> Hence in `G` there is an odd antipath `Q` of length `≥ 3`, with ends `x, y ∉ B₁`
> and with interior in `B₁`.  Since both `x` and `y` have nonneighbours in the
> interior of `Q` it follows that `x, y ∉ B`; and so `x, y ∈ A`, again contradicting
> that `(A, B)` is balanced.  This proves (1)."*

Assume `k := holeLength c` is odd, so `k ≥ 5`; rotate `z` to position `0` in the hole
`c` of `(G')ᶜ`.  Exactly two vertices `x = c[1]`, `y = c[k−1]` of `c \ z` are
nonadjacent to `z` in `G'`, so all the others lie in `Sum.inl '' B₁` and
`x, y ∉ Sum.inl '' B₁`.  Then `c.tail` pulls back to an odd antipath `Q₀` of `G` of
length `≥ 3` with interior in `B₁` and adjacent ends `x₀, y₀`; because the length is
`≥ 3`, the entries next to the ends are interior vertices, so each end has a
nonneighbour in `B₁`, whence by `AnticomponentOfSkewSideBasics.complete_sdiff`
neither end lies in `B`, so both lie in `A` — which clause (S4b) of `SPGT.Balanced`
forbids.

An antihole of `G'` is a hole of `(G')ᶜ` (`HoleBasics.isAntiholeList_iff`).  This is
the only place where clause (S4b) of balancedness is used in the whole proof, and
like case 1 it does not need `Berge G`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoOddAntiholeThroughAddedVertex

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.AddPendantVertexTransport

/-- Rewriting the index of a `getElem`. -/
private theorem getElem_congr_idx {α : Type*} (l : List α) {a b : ℕ} (ha : a < l.length)
    (hb : b < l.length) (h : a = b) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-- Every antihole of `G' = G +ᵥ B₁` — that is, every hole of `(G')ᶜ` — that passes
through the new vertex `z = Sum.inr ()` has even length. -/
theorem even_holeLength_of_mem {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B B₁ : Set V}
    (hAB : A ∪ B = Set.univ) (hbal : SPGT.Balanced G A B)
    (hB₁ : IsAnticomponent G B B₁)
    {c : List (V ⊕ Unit)} (hc : IsHoleList ((addPendantVertex G B₁)ᶜ) c)
    (hz : (Sum.inr () : V ⊕ Unit) ∈ c) :
    Even (holeLength c) := by
  classical
  by_contra hnoteven
  rw [Nat.not_even_iff_odd, Nat.odd_iff] at hnoteven
  have hc4 : 4 ≤ c.length := hc.1
  have hlen5 : 5 ≤ c.length := by
    have : holeLength c = c.length := rfl
    omega
  -- rotate `z` into position `0` of the hole `D` of `(G')ᶜ`
  obtain ⟨d, hd, hdlen, hd0, hdmem⟩ :
      ∃ d : List (V ⊕ Unit), IsHoleList ((addPendantVertex G B₁)ᶜ) d ∧ d.length = c.length ∧
        (∀ h : 0 < d.length, (d[0]'h) = Sum.inr ()) ∧ (∀ u, u ∈ d ↔ u ∈ c) := by
    obtain ⟨m, hm, hmz⟩ := List.getElem_of_mem hz
    refine ⟨c.rotate m, HoleBasics.isHoleList_rotate hc m, List.length_rotate .., ?_,
      fun u => List.mem_rotate⟩
    intro h
    simp only [List.getElem_rotate]
    exact (getElem_congr_idx c _ hm
      (by rw [Nat.zero_add]; exact Nat.mod_eq_of_lt hm)).trans hmz
  have hlen : 5 ≤ d.length := by omega
  have hcompl : Complete G B₁ (B \ B₁) :=
    AnticomponentOfSkewSideBasics.complete_sdiff G hB₁
  have hinl : ∀ t : V ⊕ Unit, (addPendantVertex G B₁).Adj (Sum.inr ()) t →
      ∃ w : V, t = Sum.inl w ∧ w ∈ B₁ := by
    rintro (a | u) h
    · exact ⟨a, rfl, h⟩
    · exact absurd h (not_adj_inr_inr G B₁ () u)
  have hnotz : ∀ t : V ⊕ Unit, t ≠ Sum.inr () → ∃ w : V, t = Sum.inl w := by
    rintro (a | u) h
    · exact ⟨a, rfl⟩
    · exact absurd (by cases u; rfl) h
  -- 1. "exactly two vertices of `D \ z` are nonadjacent to `z`" — `d[1]` and `d[k-1]`
  have hzx : ((addPendantVertex G B₁)ᶜ).Adj (d[0]'(by omega)) (d[1]'(by omega)) :=
    (HoleMinusVertexPath.adj_head_iff hd hlen (by omega)).mpr (Or.inl rfl)
  have hzy : ((addPendantVertex G B₁)ᶜ).Adj (d[0]'(by omega)) (d[d.length - 1]'(by omega)) :=
    (HoleMinusVertexPath.adj_head_iff hd hlen (by omega)).mpr (Or.inr rfl)
  rw [hd0 (by omega)] at hzx hzy
  obtain ⟨x₀, hx0⟩ := hnotz _ (fun h => hzx.1 h.symm)
  obtain ⟨y₀, hy0⟩ := hnotz _ (fun h => hzy.1 h.symm)
  have hx0nB₁ : x₀ ∉ B₁ := fun hmem => hzx.2 (by rw [hx0]; exact hmem)
  have hy0nB₁ : y₀ ∉ B₁ := fun hmem => hzy.2 (by rw [hy0]; exact hmem)
  -- 2. "so all the others belong to `B₁`"
  have hother : ∀ (j : ℕ) (hj : j < d.length), j ≠ 1 → j ≠ d.length - 1 →
      (d[j]'hj) ≠ (Sum.inr () : V ⊕ Unit) → ∃ w : V, (d[j]'hj) = Sum.inl w ∧ w ∈ B₁ := by
    intro j hj hj1 hjn hjz
    have hne : (d[0]'(by omega)) ≠ (d[j]'hj) := by
      rw [hd0 (by omega)]
      exact fun h => hjz h.symm
    have hadjG' : (addPendantVertex G B₁).Adj (d[0]'(by omega)) (d[j]'hj) := by
      by_contra hcon
      rcases (HoleMinusVertexPath.adj_head_iff hd hlen hj).mp ⟨hne, hcon⟩ with h | h
      · exact hj1 h
      · exact hjn h
    rw [hd0 (by omega)] at hadjG'
    exact hinl _ hadjG'
  -- 3. "hence in `G` there is an odd antipath `Q` of length `≥ 3`, with ends `x, y ∉ B₁`
  --    and with interior in `B₁`"
  have hpath : IsPathFrom ((addPendantVertex G B₁)ᶜ) d.tail
      (d[1]'(by omega)) (d[d.length - 1]'(by omega)) :=
    HoleMinusVertexPath.isPathFrom_tail hd hlen
  have hqz : ∀ u ∈ d.tail, u ≠ (Sum.inr () : V ⊕ Unit) := by
    intro u hu
    rw [HoleMinusVertexPath.mem_tail_iff hd hlen u] at hu
    rw [← hd0 (by omega)]
    exact hu.2
  obtain ⟨q₀, hq₀, hq₀len⟩ := exists_eq_map_inl hqz
  have hpath0 : IsPathFrom Gᶜ q₀ x₀ y₀ := by
    rw [isPathFrom_compl_map_inl G B₁ q₀ x₀ y₀, ← hq₀, ← hx0, ← hy0]
    exact hpath
  have hq₀lenval : q₀.length = d.length - 1 := by
    rw [hq₀len]
    exact HoleMinusVertexPath.length_tail hd hlen
  have hintB₁ : ∀ u ∈ SPGT.interior q₀, u ∈ B₁ := by
    intro u hu
    have hmapu : (Sum.inl u : V ⊕ Unit) ∈ SPGT.interior d.tail := by
      rw [hq₀, interior_map]
      exact List.mem_map_of_mem hu
    rw [HoleMinusVertexPath.mem_interior_tail_iff hd hlen _] at hmapu
    obtain ⟨humem, hune0, hune1, hune2⟩ := hmapu
    obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem humem
    obtain ⟨w, hw, hwB₁⟩ := hother j hj
      (fun h => hune1 (hjeq.symm.trans (getElem_congr_idx d hj (by omega) h)))
      (fun h => hune2 (hjeq.symm.trans (getElem_congr_idx d hj (by omega) h)))
      (fun h => hune0 (hjeq.symm.trans (h.trans (hd0 (by omega)).symm)))
    have : (Sum.inl u : V ⊕ Unit) = Sum.inl w := hjeq.symm.trans hw
    exact (Sum.inl_injective this) ▸ hwB₁
  -- 4. the two ends are adjacent in `G`
  have hadjxy : G.Adj x₀ y₀ := by
    have hne := HoleMinusVertexPath.ends_ne hd hlen
    have hnadj := HoleMinusVertexPath.ends_not_adj hd hlen
    have hG' : (addPendantVertex G B₁).Adj (d[1]'(by omega)) (d[d.length - 1]'(by omega)) := by
      by_contra hcon
      exact hnadj ⟨hne, hcon⟩
    rw [hx0, hy0, adj_inl_inl] at hG'
    exact hG'
  -- 5. "since both `x` and `y` have nonneighbours in the interior of `Q` it follows that
  --    `x, y ∉ B`; and so `x, y ∈ A`"  (this is what length `≥ 3` is for)
  have hq0 : (q₀[0]'(by omega)) = x₀ :=
    PathBasics.getElem_zero_of_head? hpath0.2.1 (by omega)
  have hqlast : (q₀[q₀.length - 1]'(by omega)) = y₀ :=
    PathBasics.getElem_last_of_getLast? hpath0.2.2 (by omega)
  have hadj1 : Gᶜ.Adj (q₀[0]'(by omega)) (q₀[1]'(by omega)) :=
    PathBasics.path_adj_succ hpath0.1 (show 0 + 1 < q₀.length by omega)
  have hint1 : (q₀[1]'(by omega)) ∈ SPGT.interior q₀ :=
    PathBasics.getElem_mem_interior hpath0.1 (by omega) (by omega) (by omega)
  have hadj2 : Gᶜ.Adj (q₀[q₀.length - 2]'(by omega)) (q₀[q₀.length - 1]'(by omega)) := by
    have h := PathBasics.path_adj_succ hpath0.1
      (show (q₀.length - 2) + 1 < q₀.length by omega)
    rwa [getElem_congr_idx q₀ (show (q₀.length - 2) + 1 < q₀.length by omega)
      (show q₀.length - 1 < q₀.length by omega) (by omega)] at h
  have hint2 : (q₀[q₀.length - 2]'(by omega)) ∈ SPGT.interior q₀ :=
    PathBasics.getElem_mem_interior hpath0.1 (by omega) (by omega) (by omega)
  have hx₀notB : x₀ ∉ B := by
    intro hxB
    have h1 := hintB₁ _ hint1
    have hadj := hcompl _ h1 x₀ ⟨hxB, hx0nB₁⟩
    rw [hq0] at hadj1
    exact hadj1.2 hadj.symm
  have hy₀notB : y₀ ∉ B := by
    intro hyB
    have h2 := hintB₁ _ hint2
    have hadj := hcompl _ h2 y₀ ⟨hyB, hy0nB₁⟩
    rw [hqlast] at hadj2
    exact hadj2.2 hadj
  have hx₀A : x₀ ∈ A := by
    rcases (hAB ▸ Set.mem_univ x₀ : x₀ ∈ A ∪ B) with h | h
    · exact h
    · exact absurd h hx₀notB
  have hy₀A : y₀ ∈ A := by
    rcases (hAB ▸ Set.mem_univ y₀ : y₀ ∈ A ∪ B) with h | h
    · exact h
    · exact absurd h hy₀notB
  have hodd : Odd (pathLength q₀) := by
    have hpl : pathLength (q₀.map (Sum.inl : V → V ⊕ Unit)) = pathLength q₀ :=
      pathLength_map Sum.inl q₀
    rw [← hpl, ← hq₀, HoleMinusVertexPath.pathLength_tail hd hlen, Nat.odd_iff]
    have : holeLength c = c.length := rfl
    omega
  -- 6. "again contradicting that `(A, B)` is balanced" — clause (S4b)
  exact hbal.2 x₀ y₀ q₀ hx₀A hy₀A hadjxy hpath0 (fun u hu => hB₁.1 (hintB₁ u hu)) hodd

end Workspace.ProofLemmas.NoOddAntiholeThroughAddedVertex
