import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.Thm183EdgeCount
import Workspace.ProofLemmas.Thm183LineCounting
import Workspace.ProofLemmas.Thm183LineEvenCase
import Workspace.ProofLemmas.Thm183LineOddCase

/-!
# 18.3: the lines of `P`, and the closing counting paragraph

Three things happen here, all of them still inside the printed proof of **18.3**
(`paper/proofs/18_3.md`, published page 110).

1. **The printed symmetry `p₁ ↔ pₙ` is discharged.**  `Thm183LineOddCase` proves *"Consequently
   `P'` is odd"* for the line whose non-`Y`-complete end is `pₙ`.  The paper says *"we may
   assume it is `pₙ` from the symmetry"*; `line_odd_of_first_end_not_YComplete` below is that
   symmetry, obtained by running `Thm183LineOddCase` on `P` reversed.

2. **The three facts about lines are collected in index form**, as the hypotheses `hEven`,
   `hOddL`, `hOddR` of the pure-arithmetic `Thm183LineCounting.yEdge_parity`.  Two of the three
   need the side condition *"since at least two vertices of `P` are `Y`-complete"*, which is
   used exactly as the paper uses it: to produce a second `Y`-complete vertex off the line.
   That is `second_witness`.

3. **The closing paragraph is applied**, giving 18.3's third conclusion:

   > *"the number of odd lines equals `y + z`, where `y` is the number of `Y`-complete edges in
   > `P`, and `z` is the number of ends of `P` that are not `Y`-complete.  But since every edge
   > of `P` belongs to a unique line and `P` has even length, it follows that the number of odd
   > lines is even, and so `y, z` have the same parity."*

`yEdges_parity` is stated in exactly the shape of the third conjunct of the frozen
`Workspace.Statements.S18.SPGT.thm_18_3`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm183Lines

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## `Y`-completeness as a predicate on indices -/

/-- *"`pₖ` is `Y`-complete"*, read off positionally.  Out of range it is false. -/
def YIdx (G : SimpleGraph V) (Y : Set V) (p : List V) (k : ℕ) : Prop :=
  ∃ h : k < p.length, VertexComplete G (p[k]'h) Y

theorem yIdx_iff {G : SimpleGraph V} {Y : Set V} {p : List V} {k : ℕ} (hk : k < p.length) :
    YIdx G Y p k ↔ VertexComplete G (p[k]'hk) Y :=
  ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩

/-! ## The printed symmetry between `p₁` and `pₙ` -/

private theorem getElem_rev (p : List V) (k : ℕ) (hk : k < p.reverse.length)
    (hk' : p.length - 1 - k < p.length) :
    (p.reverse[k]'hk) = p[p.length - 1 - k]'hk' := by
  simp only [List.getElem_reverse]

/-- **18.3, "Case B", mirrored.**  *"… and we may assume it is `pₙ` from the symmetry."*

This is `Thm183LineOddCase.line_odd_of_last_end_not_YComplete` run on `P` reversed: the line is
`p₁-⋯-pⱼ`, its end `p₁` is not `Y`-complete, its other end `pⱼ` is the first `Y`-complete
vertex of `P`, and the second `Y`-complete vertex of `P` sits beyond `pⱼ`. -/
theorem line_odd_of_first_end_not_YComplete
    (G : SimpleGraph V) (hG5 : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)))
    (j : ℕ) (hj2 : 2 ≤ j) (hjlt : j + 1 < p.length)
    (hint : ∀ (k : ℕ) (hk : k < p.length), 0 < k → k < j →
       ¬ VertexComplete G (p[k]'hk) Y)
    (hcj : VertexComplete G (p[j]'(by omega)) Y)
    (hc0 : ¬ VertexComplete G p₁ Y)
    (hwit : ∃ (h : ℕ) (hh : h < p.length), j < h ∧ VertexComplete G (p[h]'hh) Y) :
    Odd j := by
  have hrl : p.reverse.length = p.length := List.length_reverse
  have hFrom : IsPathFrom G p p₁ pₙ := ⟨hp, hhead, hlast⟩
  have hFromR : IsPathFrom G p.reverse pₙ p₁ := PathBasics.isPathFrom_reverse hFrom
  -- The reversed path satisfies every hypothesis of 18.3 with `p₁` and `pₙ` interchanged.
  have hpXY' : ∀ w ∈ p.reverse, w ∉ X ∪ Y := fun w hw => hpXY w (List.mem_reverse.mp hw)
  have hn' : 5 ≤ p.reverse.length := by omega
  have hXuniq' : ∀ w ∈ p.reverse, (VertexComplete G w X ↔ (w = pₙ ∨ w = p₁)) := by
    intro w hw
    rw [hXuniq w (List.mem_reverse.mp hw)]
    exact or_comm
  -- The line `p₁-⋯-pⱼ` of `P` is the line `pₙ₋₁₋ⱼ-⋯-pₙ` of `P` reversed.
  set a : ℕ := p.length - 1 - j with ha
  have halt : a < p.reverse.length := by omega
  have hodd := Thm183LineOddCase.line_odd_of_last_end_not_YComplete G hG5 X Y hXY hXne hYne
    hXa hYa hcompl p.reverse pₙ p₁ hFromR.1 hpXY' hn' hFromR.2.1 hFromR.2.2 hXuniq'
    a (by omega) (by omega)
    (by
      intro k hk hak hkl
      have hk' : p.length - 1 - k < p.length := by omega
      rw [getElem_rev p k hk hk']
      exact hint (p.length - 1 - k) hk' (by omega) (by omega))
    (by
      have hk' : p.length - 1 - a < p.length := by omega
      rw [getElem_rev p a _ hk']
      have : p.length - 1 - a = j := by omega
      simpa only [this] using hcj)
    hc0
    (by
      obtain ⟨m, hm, hjm, hmY⟩ := hwit
      refine ⟨p.length - 1 - m, by omega, by omega, ?_⟩
      have hk' : p.length - 1 - (p.length - 1 - m) < p.length := by omega
      rw [getElem_rev p (p.length - 1 - m) _ hk']
      have heq : p.length - 1 - (p.length - 1 - m) = m := by omega
      simpa only [heq] using hmY)
  have : p.reverse.length - 1 - a = j := by omega
  rwa [this] at hodd

/-! ## "since at least two vertices of `P` are `Y`-complete" -/

/-- If every index at which `c` holds equals a single index `m`, then `c` holds at most once —
contradicting *"at least two vertices of `P` are `Y`-complete"*. -/
private theorem second_witness {N : ℕ} {c : ℕ → Prop} [DecidablePred c]
    (h2 : 2 ≤ ((Finset.range N).filter c).card) {m : ℕ}
    (hall : ∀ k, k < N → c k → k = m) : False := by
  have hle : ((Finset.range N).filter c).card ≤ 1 := by
    refine Finset.card_le_one.mpr ?_
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_range] at hx hy
    rw [hall x hx.1 hx.2, hall y hy.1 hy.2]
  omega

/-! ## The closing paragraph -/

/-- **18.3, third conclusion.**  *"the number of `Y`-complete edges of `P` has the same parity
as the number of elements of `{p₁, pₙ}` that are `Y`-complete."*

Stated in exactly the shape of the third conjunct of the frozen
`Workspace.Statements.S18.SPGT.thm_18_3`.  `hev` is 18.3's first conclusion (proved in
`Thm183EvenLength`) and `h2` is *"Assume that at least two vertices of `P` are
`Y`-complete"*. -/
theorem yEdges_parity
    (G : SimpleGraph V) (hG5 : InF5 G) (X Y : Set V)
    (hXY : Disjoint X Y) (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hXa : AnticonnectedSet G X) (hYa : AnticonnectedSet G Y)
    (hcompl : Complete G X Y)
    (p : List V) (p₁ pₙ : V) (hp : IsPathList G p)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y) (hn : 5 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ (w = p₁ ∨ w = pₙ)))
    (hev : Even (pathLength p))
    (h2 : 2 ≤ {w : V | w ∈ p ∧ VertexComplete G w Y}.ncard) :
    {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard % 2 =
      {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y}.ncard % 2 := by
  classical
  have h0lt : 0 < p.length := by omega
  have hLlt : p.length - 1 < p.length := by omega
  have hp0 : p[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpL : p[p.length - 1]'hLlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  have hne : p₁ ≠ pₙ := by
    rw [← hp0, ← hpL]; exact PathBasics.path_ne_of_ne_index hp h0lt hLlt (by omega)
  -- ### `h2` in index form
  have h2' : 2 ≤ ((Finset.range p.length).filter (YIdx G Y p)).card := by
    have hfin : {w : V | w ∈ p ∧ VertexComplete G w Y}.Finite := Set.toFinite _
    have h1 : 1 < {w : V | w ∈ p ∧ VertexComplete G w Y}.ncard := by omega
    obtain ⟨u, hu, -⟩ := Set.exists_ne_of_one_lt_ncard h1 p₁
    obtain ⟨v, hv, hvu⟩ := Set.exists_ne_of_one_lt_ncard h1 u
    obtain ⟨ku, hku, hkueq⟩ := List.getElem_of_mem hu.1
    obtain ⟨kv, hkv, hkveq⟩ := List.getElem_of_mem hv.1
    refine Nat.lt_iff_add_one_le.mp (Finset.one_lt_card.mpr ⟨kv, ?_, ku, ?_, ?_⟩)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkv, ⟨hkv, by rw [hkveq]; exact hv.2⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hku, ⟨hku, by rw [hkueq]; exact hu.2⟩⟩
    · intro hcon
      subst hcon
      exact hvu (hkveq.symm.trans hkueq)
  -- ### the arithmetic engine, fed with the three facts about lines
  have key : ((Finset.range (p.length - 1)).filter
        (fun k => YIdx G Y p k ∧ YIdx G Y p (k + 1))).card % 2
      = ((if YIdx G Y p 0 then 1 else 0)
          + (if YIdx G Y p (p.length - 1) then 1 else 0)) % 2 := by
    refine Thm183LineCounting.yEdge_parity p.length hn (YIdx G Y p) ?_ h2' ?_ ?_ ?_
    · rw [PathBasics.pathLength_eq] at hev; exact hev
    · -- `hEven`: a line of length `≥ 2` both of whose ends are `Y`-complete is even (Case A)
      intro i j hij hjN hnone hci hcj
      have hjlt : j < p.length := by omega
      refine Thm183LineEvenCase.line_even_of_both_ends_YComplete G hG5 X Y hXY hXa hYa hcompl
        p p₁ pₙ hp hpXY hn hhead hlast hXuniq i j hij hjlt ?_ ?_ ?_
      · intro k hk hik hkj hck
        exact hnone k hik hkj ⟨hk, hck⟩
      · exact hci.2
      · exact hcj.2
    · -- `hOddL`: a line of length `≥ 2` starting at `p₁`, when `p₁` is not `Y`-complete (Case B
      -- mirrored)
      intro j hj2 hjN hnone hc0 hcj
      by_cases hjE : j = p.length - 1
      · -- then `pⱼ` is the only `Y`-complete vertex of `P`, contrary to `h2`
        exfalso
        refine second_witness h2' (m := j) ?_
        intro k hk hck
        by_contra hkj
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · exact hc0 hck
        · exact hnone k hkpos (by omega) hck
      refine line_odd_of_first_end_not_YComplete G hG5 X Y hXY hXne hYne hXa hYa hcompl
        p p₁ pₙ hp hpXY hn hhead hlast hXuniq j hj2 (by omega) ?_ hcj.2 ?_ ?_
      · intro k hk hk0 hkj hck
        exact hnone k hk0 hkj ⟨hk, hck⟩
      · rw [← hp0]
        intro hcon
        exact hc0 ⟨h0lt, hcon⟩
      · -- the second `Y`-complete vertex lies beyond `pⱼ`
        by_contra hcon
        push_neg at hcon
        refine second_witness h2' (m := j) ?_
        intro k hk hck
        by_contra hkj
        rcases Nat.lt_or_ge k j with hlt | hge
        · rcases Nat.eq_zero_or_pos k with rfl | hkpos
          · exact hc0 hck
          · exact hnone k hkpos hlt hck
        · exact hcon k hk (by omega) hck.2
    · -- `hOddR`: a line of length `≥ 2` ending at `pₙ`, when `pₙ` is not `Y`-complete (Case B)
      intro i hipos hiN hnone hci hcN
      refine Thm183LineOddCase.line_odd_of_last_end_not_YComplete G hG5 X Y hXY hXne hYne
        hXa hYa hcompl p p₁ pₙ hp hpXY hn hhead hlast hXuniq i hipos hiN ?_ hci.2 ?_ ?_
      · intro k hk hik hkL hck
        exact hnone k hik hkL ⟨hk, hck⟩
      · rw [← hpL]
        intro hcon
        exact hcN ⟨hLlt, hcon⟩
      · -- the second `Y`-complete vertex lies before `pᵢ`
        by_contra hcon
        push_neg at hcon
        refine second_witness h2' (m := i) ?_
        intro k hk hck
        by_contra hki
        rcases Nat.lt_or_ge k i with hlt | hge
        · exact hcon k hk hlt hck.2
        · rcases Nat.lt_or_ge k (p.length - 1) with hlt2 | hge2
          · exact hnone k (by omega) hlt2 hck
          · have : k = p.length - 1 := by omega
            exact hcN (this ▸ hck)
  -- ### transport the two sides into the shape of the frozen conclusion
  have hLHS : {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G Y u v}
      = HoleYEdgeParity.yEdges G Y p := rfl
  have hidx : Thm183EdgeCount.YEdgeIdx G Y p
      = ↑((Finset.range (p.length - 1)).filter
          (fun k => YIdx G Y p k ∧ YIdx G Y p (k + 1))) := by
    ext k
    simp only [Thm183EdgeCount.YEdgeIdx, Set.mem_setOf_eq, Finset.coe_filter,
      Finset.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hk, hk1, hk2⟩
      exact ⟨by omega, ⟨by omega, hk1⟩, ⟨hk, hk2⟩⟩
    · rintro ⟨hkr, ⟨hk0, hk1⟩, ⟨hk2, hk3⟩⟩
      exact ⟨hk2, hk1, hk3⟩
  rw [hLHS, Thm183EdgeCount.yEdges_ncard_eq_index_ncard hp, hidx, Set.ncard_coe_finset, key,
    Thm183EdgeCount.ends_YComplete_ncard hne]
  have e0 : YIdx G Y p 0 ↔ VertexComplete G p₁ Y := by rw [yIdx_iff h0lt, hp0]
  have eL : YIdx G Y p (p.length - 1) ↔ VertexComplete G pₙ Y := by rw [yIdx_iff hLlt, hpL]
  by_cases hA : VertexComplete G p₁ Y <;> by_cases hB : VertexComplete G pₙ Y <;>
    simp [e0, eL, hA, hB]

end Workspace.ProofLemmas.Thm183Lines
