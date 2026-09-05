import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.OptimalWheelChoice

/-!
# The converse of the wheel condition: three `Y`-complete rim edges suffice

`Workspace.Types.Wheels.IsWheel` asks for **two disjoint** `Y`-complete edges of the rim.
In §§16–23 the hypothesis one actually has in hand is almost always a *count* — "`C'`
contains fewer `Y`-complete edges than `C`", "exactly 4 edges of `C` are `Y`-complete" — and
the step the paper never writes down is the passage from a count back to two disjoint edges.

The combinatorial fact is:

> three distinct edges of a cycle of length `≥ 4` cannot pairwise meet.

Indeed if all three pairwise met, either all three would share a vertex — impossible, since
every vertex of a hole has exactly two neighbours — or they would form a triangle, which a
hole of length `≥ 4` does not contain.  So among any three `Y`-complete rim edges two are
disjoint, and the wheel condition is met.

This is used at least twice in the printed proof of **23.2**: in step (1), to conclude that
the hole `C'` (which carries two fewer `Y`-complete edges than `C`) *would* be a wheel if `C`
had `≥ 6` of them; and in the final paragraph, where *"since `(C', Y)` is not a wheel, it
follows that `x₀, z` are the only `Y`-complete vertices in `C'`"*.

Everything is done on the index side, through `WheelParity.CycEdge` / `cycCount` (the cyclic
edge `eₘ` of `C` joins `C[m % n]` to `C[(m+1) % n]`) and
`WheelParity.ncard_yEdges_eq_cycCount`, so no vertex-level case analysis is needed: the whole
argument reduces to "among three distinct residues mod `n ≥ 4`, two differ by more than 1
cyclically", which is `omega` once the `%` is eliminated.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.WheelConverse

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cyclic-successor arithmetic -/

/-- The cyclic successor of an index below `n`, with the `%` eliminated. -/
private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- "`y` is the cyclic successor of `x`", with the `%` eliminated — the form `omega` can use. -/
private theorem succ_iff {n x y : ℕ} (hx : x < n) (hy : y < n) :
    y = (x + 1) % n ↔ (y = x + 1 ∨ (x + 1 = n ∧ y = 0)) := by
  rw [succ_mod_eq hx]
  by_cases h : x + 1 = n
  · rw [if_pos h]
    constructor
    · intro hy0; exact Or.inr ⟨h, hy0⟩
    · rintro (rfl | ⟨-, hy0⟩)
      · omega
      · exact hy0
  · rw [if_neg h]
    constructor
    · intro he; exact Or.inl he
    · rintro (he | ⟨hcon, -⟩)
      · exact he
      · exact absurd hcon h

/-- The cyclic successor map is injective below `n`. -/
private theorem succ_mod_inj {n p q : ℕ} (hp : p < n) (hq : q < n)
    (h : (p + 1) % n = (q + 1) % n) : p = q := by
  rw [succ_mod_eq hp, succ_mod_eq hq] at h
  split_ifs at h <;> omega

/-- **The combinatorial core.**  Among three distinct indices of a cycle of length `≥ 4`, two
are not cyclically consecutive.  (Three pairwise cyclically-consecutive indices would be a
triangle in the cycle, which needs `n = 3`.) -/
private theorem exists_far_pair {n a b c : ℕ} (hn : 4 ≤ n)
    (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ p q : ℕ, p < n ∧ q < n ∧ p ≠ q ∧
      q ≠ (p + 1) % n ∧ p ≠ (q + 1) % n ∧
      (p = a ∨ p = b ∨ p = c) ∧ (q = a ∨ q = b ∨ q = c) := by
  by_cases hab' : b = (a + 1) % n ∨ a = (b + 1) % n
  · by_cases hac' : c = (a + 1) % n ∨ a = (c + 1) % n
    · -- `b` and `c` are the two cyclic neighbours of `a`; they are not neighbours of each other
      rw [succ_iff ha hb, succ_iff hb ha] at hab'
      rw [succ_iff ha hc, succ_iff hc ha] at hac'
      refine ⟨b, c, hb, hc, hbc, ?_, ?_, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
      · intro hcon; rw [succ_iff hb hc] at hcon; omega
      · intro hcon; rw [succ_iff hc hb] at hcon; omega
    · exact ⟨a, c, ha, hc, hac, fun h => hac' (Or.inl h), fun h => hac' (Or.inr h),
        Or.inl rfl, Or.inr (Or.inr rfl)⟩
  · exact ⟨a, b, ha, hb, hab, fun h => hab' (Or.inl h), fun h => hab' (Or.inr h),
      Or.inl rfl, Or.inr (Or.inl rfl)⟩

/-! ### From a cyclic edge to its two ends -/

/-- The cyclic edge `eₘ` of `C`, read as an `EdgeComplete` fact about the two vertices
`C[m % n]` and `C[(m+1) % n]`. -/
private theorem edgeComplete_of_cycEdge {G : SimpleGraph V} {Y : Set V} {C : List V}
    (hn : 0 < C.length) {m : ℕ} (h : WheelParity.CycEdge G Y C m) :
    EdgeComplete G Y (C[m % C.length]'(Nat.mod_lt _ hn))
      (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  obtain ⟨u, v, hu, hv, hec⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu hv
  rw [Option.some_inj.mp hu, Option.some_inj.mp hv]
  exact hec

/-! ### The main lemma -/

/-- **Three `Y`-complete rim edges make a wheel.**  If `C` is a hole of length `≥ 6`, `Y` is a
nonempty anticonnected set disjoint from `C`, and at least three edges of `C` are
`Y`-complete, then two of those edges are disjoint and `(C, Y)` is a wheel. -/
theorem isWheel_of_three_yEdges {G : SimpleGraph V} {C : List V} {Y : Set V}
    (hC : IsHoleList G C) (hlen : 6 ≤ holeLength C)
    (hY : Y.Nonempty) (hYanti : AnticonnectedSet G Y) (hCY : ∀ v ∈ C, v ∉ Y)
    (h3 : 3 ≤ OptimalWheelChoice.yEdgeCount G Y C) :
    IsWheel G C Y := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  -- pass from the `Sym2` count to the cyclic-edge count
  rw [OptimalWheelChoice.yEdgeCount, WheelParity.ncard_yEdges_eq_cycCount hC,
    WheelParity.cycCount] at h3
  -- three distinct cyclic edge-indices
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hTcard
  have hmem : ∀ x : ℕ, x ∈ ({a, b, c} : Finset ℕ) → x < C.length ∧ WheelParity.CycEdge G Y C x := by
    intro x hx
    have := Finset.mem_filter.mp (hTsub hx)
    exact ⟨Finset.mem_range.mp this.1, this.2⟩
  obtain ⟨ha, hcea⟩ := hmem a (by simp)
  obtain ⟨hb, hceb⟩ := hmem b (by simp)
  obtain ⟨hc, hcec⟩ := hmem c (by simp)
  -- two of them are not cyclically consecutive
  obtain ⟨p, q, hp, hq, hpq, hqp1, hpq1, hpin, hqin⟩ := exists_far_pair hn4 ha hb hc hab hac hbc
  have hcep : WheelParity.CycEdge G Y C p := by
    rcases hpin with rfl | rfl | rfl
    exacts [hcea, hceb, hcec]
  have hceq : WheelParity.CycEdge G Y C q := by
    rcases hqin with rfl | rfl | rfl
    exacts [hcea, hceb, hcec]
  -- the four ends, as indices
  have hpm : p % C.length = p := Nat.mod_eq_of_lt hp
  have hqm : q % C.length = q := Nat.mod_eq_of_lt hq
  have hep := edgeComplete_of_cycEdge hn hcep
  have heq := edgeComplete_of_cycEdge hn hceq
  refine ⟨⟨hC, hlen⟩, ⟨hY, hYanti, hCY⟩,
    C[p % C.length]'(Nat.mod_lt _ hn), C[(p + 1) % C.length]'(Nat.mod_lt _ hn),
    C[q % C.length]'(Nat.mod_lt _ hn), C[(q + 1) % C.length]'(Nat.mod_lt _ hn),
    List.getElem_mem _, List.getElem_mem _, List.getElem_mem _, List.getElem_mem _,
    hep, heq, ?_, ?_, ?_, ?_⟩
  · -- `C[p] ≠ C[q]`
    exact HoleBasics.hole_ne_of_ne_index hC _ _ (by rw [hpm, hqm]; exact hpq)
  · -- `C[p] ≠ C[q+1]`
    exact HoleBasics.hole_ne_of_ne_index hC _ _ (by rw [hpm]; exact hpq1)
  · -- `C[p+1] ≠ C[q]`
    exact HoleBasics.hole_ne_of_ne_index hC _ _ (by rw [hqm]; exact fun h => hqp1 h.symm)
  · -- `C[p+1] ≠ C[q+1]`
    exact HoleBasics.hole_ne_of_ne_index hC _ _ (fun h => hpq (succ_mod_inj hp hq h))

/-- Contrapositive form, as used in the final paragraph of 23.2: a hole of length `≥ 6` with a
nonempty anticonnected disjoint `Y` that is **not** a wheel carries at most two `Y`-complete
edges. -/
theorem yEdgeCount_le_two_of_not_isWheel {G : SimpleGraph V} {C : List V} {Y : Set V}
    (hC : IsHoleList G C) (hlen : 6 ≤ holeLength C)
    (hY : Y.Nonempty) (hYanti : AnticonnectedSet G Y) (hCY : ∀ v ∈ C, v ∉ Y)
    (hnw : ¬ IsWheel G C Y) :
    OptimalWheelChoice.yEdgeCount G Y C ≤ 2 := by
  by_contra h
  exact hnw (isWheel_of_three_yEdges hC hlen hY hYanti hCY (by omega))

end Workspace.ProofLemmas.WheelConverse
