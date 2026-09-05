import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.SegmentBasics

/-! The two ordered triples in the closing argument of 23.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingGeometry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} {G : SimpleGraph V} {C : List V}

/-- The two middle vertices are distinct because their offsets are `1` and `d+1`,
both strictly within the same turn of the rim. -/
theorem middles_ne (hC : IsHoleList G C) {x₀ z x₁ c₁ c₂ c₃ : V} {k d : ℕ}
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d)) : z ≠ c₂ := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hz : C[(k + 1) % C.length]? = some z := by
    simpa using SegmentBasics.prefix_pos hn hpre1 (s := 1) (by simp)
  have hc : C[(k + (d + 1)) % C.length]? = some c₂ := by
    simpa only [Nat.add_assoc] using SegmentBasics.prefix_pos hn hpre2 (s := 1) (by simp)
  intro he
  have hm := SegmentBasics.pos_unique hC (hz.trans (congrArg some he)) hc
  have heq : 1 % C.length = (d + 1) % C.length := Nat.ModEq.add_left_cancel' k hm
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  omega

/-- The two possible end coincidences cannot both hold, since the rim has at least
six vertices.  This is the paper's “and therefore `x₁ ≠ c₁`”. -/
theorem not_both_overlap (hC : IsHoleList G C) (hn6 : 6 ≤ C.length)
    {x₀ z x₁ c₁ c₂ c₃ : V} {k d : ℕ}
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d)) : ¬ (x₀ = c₃ ∧ x₁ = c₁) := by
  have hn : 0 < C.length := by omega
  have h0 : C[(k + 0) % C.length]? = some x₀ := by
    simpa using SegmentBasics.prefix_pos hn hpre1 (s := 0) (by simp)
  have h1 : C[(k + 2) % C.length]? = some x₁ := by
    simpa using SegmentBasics.prefix_pos hn hpre1 (s := 2) (by simp)
  have hc1 : C[(k + d) % C.length]? = some c₁ := by
    simpa using SegmentBasics.prefix_pos hn hpre2 (s := 0) (by simp)
  have hc3 : C[(k + (d + 2)) % C.length]? = some c₃ := by
    simpa only [Nat.add_assoc] using SegmentBasics.prefix_pos hn hpre2 (s := 2) (by simp)
  rintro ⟨he0, he1⟩
  have hm1 := SegmentBasics.pos_unique hC (h1.trans (congrArg some he1)) hc1
  have hd : 2 % C.length = d % C.length := Nat.ModEq.add_left_cancel' k hm1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hd
  have hm0 := SegmentBasics.pos_unique hC (h0.trans (congrArg some he0)) hc3
  have he : 0 % C.length = (d + 2) % C.length := Nat.ModEq.add_left_cancel' k hm0
  rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at he
  omega

/-- Different offsets in one turn give different vertices of a hole. -/
theorem offset_ne (hC : IsHoleList G C) {k a b : ℕ} {v w : V}
    (hv : C[(k + a) % C.length]? = some v)
    (hw : C[(k + b) % C.length]? = some w)
    (hne : a % C.length ≠ b % C.length) : v ≠ w := by
  intro he
  exact hne (Nat.ModEq.add_left_cancel' k
    (SegmentBasics.pos_unique hC (hv.trans (congrArg some he)) hw))

/-- Apart from the two permitted end coincidences, the ordered triples do not
overlap at an outer vertex. -/
theorem outer_ne (hC : IsHoleList G C) (hn6 : 6 ≤ C.length)
    {x₀ z x₁ c₁ c₂ c₃ : V} {k d : ℕ}
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d)) :
    x₀ ≠ c₁ ∧ x₀ ≠ c₂ ∧ x₁ ≠ c₂ ∧ x₁ ≠ c₃ := by
  have hn : 0 < C.length := by omega
  have h0 : C[(k + 0) % C.length]? = some x₀ := by
    simpa using SegmentBasics.prefix_pos hn hpre1 (s := 0) (by simp)
  have h1 : C[(k + 2) % C.length]? = some x₁ := by
    simpa using SegmentBasics.prefix_pos hn hpre1 (s := 2) (by simp)
  have hc1 : C[(k + d) % C.length]? = some c₁ := by
    simpa using SegmentBasics.prefix_pos hn hpre2 (s := 0) (by simp)
  have hc2 : C[(k + (d + 1)) % C.length]? = some c₂ := by
    simpa only [Nat.add_assoc] using SegmentBasics.prefix_pos hn hpre2 (s := 1) (by simp)
  have hc3 : C[(k + (d + 2)) % C.length]? = some c₃ := by
    simpa only [Nat.add_assoc] using SegmentBasics.prefix_pos hn hpre2 (s := 2) (by simp)
  refine ⟨offset_ne hC h0 hc1 ?_, offset_ne hC h0 hc2 ?_,
    offset_ne hC h1 hc2 ?_, offset_ne hC h1 hc3 ?_⟩
  · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Nat.mod_eq_of_lt (by omega)]
    rcases lt_or_eq_of_le hdn with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · rw [heq, Nat.mod_self]
      omega

end Workspace.ProofLemmas.Thm232ClosingGeometry
