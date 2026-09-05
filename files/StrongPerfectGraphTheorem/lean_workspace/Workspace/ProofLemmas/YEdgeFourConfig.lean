import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.YEdgeConfiguration

/-!
# Counting the `Y`-complete edges carried by a run

Groundwork for the classification step of 23.2:

> *"Since `(C,Y)` is not an odd wheel, there are vertices `x₀, z, x₁, c₁, c₂, c₃` of `C`, in
> order, and all distinct except possibly `x₁ = c₁` or `c₃ = x₀`, such that the `Y`-complete
> edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`."*

`YEdgeConfiguration.run_odd_of_not_isOddWheel` already says every maximal run of `Y`-complete
positions has **odd** length, so a run of length `L` carries `L − 1` — an *even* number of —
`Y`-complete edges.  What is still missing is the bookkeeping that turns *"there are exactly
four `Y`-complete edges"* into a bound on `L`, and that is what this module supplies:

* `cycEdge_mod` — `CycEdge` only depends on the position modulo `C.length`;
* `exists_cycEdge` / `exists_not_cycVert` — the rim of a wheel with exactly four `Y`-complete
  edges has at least one such edge and at least one position that is *not* `Y`-complete (the
  latter is what makes "maximal run" meaningful at all, and is exactly the side condition of
  `SegmentBasics.exists_run_of_cycVert`);
* `run_edges_le` — a run of length `L` forces `L − 1 ≤ yEdgeCount`, so four `Y`-complete edges
  cap every run at five vertices;
* `run_length_eq_three_or_five` — combining the cap with oddness: the run through a
  `Y`-complete edge has exactly three or five vertices, the paper's generic and degenerate
  cases respectively.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.YEdgeFourConfig

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.WheelParity
open Workspace.ProofLemmas.SegmentBasics
open Workspace.ProofLemmas.YEdgeConfiguration

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### `CycEdge` only sees the position modulo the length -/

/-- `CycEdge` depends only on the cyclic position. -/
theorem cycEdge_mod (hn : 0 < C.length) (m : ℕ) :
    CycEdge G Y C (m % C.length) ↔ CycEdge G Y C m := by
  have e1 : m % C.length % C.length = m % C.length := Nat.mod_mod_of_dvd _ dvd_rfl
  have e2 : (m % C.length + 1) % C.length = (m + 1) % C.length := Nat.mod_add_mod m C.length 1
  unfold CycEdge
  rw [e1, e2]

/-- Two positions congruent mod `C.length` carry the same `CycEdge` status. -/
theorem cycEdge_congr (hn : 0 < C.length) {a b : ℕ} (h : a % C.length = b % C.length) :
    CycEdge G Y C a ↔ CycEdge G Y C b := by
  rw [← cycEdge_mod hn a, ← cycEdge_mod hn b, h]

/-! ### Reading the count -/

/-- The `Y`-complete edge count of the rim, as the cardinality of a `Finset` of positions. -/
theorem yEdgeCount_eq_card (hC : IsHoleList G C) :
    OptimalWheelChoice.yEdgeCount G Y C = cycCount G Y C C.length := by
  rw [OptimalWheelChoice.yEdgeCount, WheelParity.ncard_yEdges_eq_cycCount hC]

/-- A rim carrying at least one `Y`-complete edge has one at an explicit position `< C.length`. -/
theorem exists_cycEdge (hC : IsHoleList G C)
    (hpos : 0 < OptimalWheelChoice.yEdgeCount G Y C) :
    ∃ m : ℕ, m < C.length ∧ CycEdge G Y C m := by
  classical
  rw [yEdgeCount_eq_card hC, cycCount] at hpos
  obtain ⟨m, hm⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_filter, Finset.mem_range] at hm
  exact ⟨m, hm.1, hm.2⟩

/-- If every position of the rim were `Y`-complete then every edge would be `Y`-complete, so
the count would be `C.length`.  Hence a rim of length `≥ 6` with exactly four `Y`-complete
edges has a position that is not `Y`-complete. -/
theorem exists_not_cycVert (hC : IsHoleList G C) (hlen : 6 ≤ C.length)
    (h4 : OptimalWheelChoice.yEdgeCount G Y C = 4) :
    ∃ j : ℕ, ¬ CycVert G Y C j := by
  classical
  by_contra hcon
  push Not at hcon
  rw [yEdgeCount_eq_card hC, cycCount] at h4
  have hfilter : (Finset.range C.length).filter (fun m => CycEdge G Y C m)
      = Finset.range C.length := by
    refine Finset.filter_true_of_mem ?_
    intro m _
    exact (cycEdge_iff hC).mpr ⟨hcon m, hcon (m + 1)⟩
  rw [hfilter, Finset.card_range] at h4
  omega

/-! ### A run caps the count -/

/-- **A run of `L` `Y`-complete positions carries `L − 1` distinct `Y`-complete edges.**  Hence
its length is bounded by the total count. -/
theorem run_edges_le (hC : IsHoleList G C) {k L : ℕ} (hL : L + 1 ≤ C.length)
    (hall : ∀ t < L, CycVert G Y C (k + t)) :
    L - 1 ≤ OptimalWheelChoice.yEdgeCount G Y C := by
  classical
  have hn : 0 < C.length := by have := hC.1; omega
  rw [yEdgeCount_eq_card hC, cycCount]
  -- the `L - 1` positions `k, …, k + L - 2`, reduced mod `C.length`, are distinct and all
  -- carry a `Y`-complete edge
  have hsub : ((Finset.range (L - 1)).image (fun t => (k + t) % C.length))
      ⊆ (Finset.range C.length).filter (fun m => CycEdge G Y C m) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    rw [Finset.mem_range] at ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn), ?_⟩
    refine (cycEdge_mod hn _).mpr ?_
    exact cycEdge_of_run hC hall (by omega)
  have hinj : Set.InjOn (fun t => (k + t) % C.length) (Finset.range (L - 1)) := by
    intro a ha b hb hab
    rw [Finset.coe_range, Set.mem_Iio] at ha hb
    have h1 : (k + a) ≡ (k + b) [MOD C.length] := hab
    have h2 : a ≡ b [MOD C.length] := Nat.ModEq.add_left_cancel' k h1
    have ha' : a < C.length := by omega
    have hb' : b < C.length := by omega
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
  calc L - 1 = ((Finset.range (L - 1)).image (fun t => (k + t) % C.length)).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ _ := Finset.card_le_card hsub

/-! ### The run through a `Y`-complete edge -/

/-- The maximal run through a `Y`-complete edge has at least two positions, hence — being of
odd length — at least three. -/
theorem run_length_ge_three (hC : IsHoleList G C) {k L : ℕ}
    (hL : L + 1 ≤ C.length) (hodd : L % 2 = 1)
    (hall : ∀ t < L, CycVert G Y C (k + t))
    (hnext : ¬ CycVert G Y C (k + L))
    {t₀ : ℕ} (ht₀ : t₀ < L) (hedge : CycEdge G Y C (k + t₀)) :
    3 ≤ L := by
  have hn : 0 < C.length := by have := hC.1; omega
  have hsucc : CycVert G Y C (k + t₀ + 1) := cycVert_succ_of_cycEdge hC hedge
  have ht₀L : t₀ + 1 < L := by
    rcases Nat.lt_or_ge (t₀ + 1) L with h | h
    · exact h
    · exfalso
      have heq : t₀ + 1 = L := by omega
      exact hnext ((cycVert_congr (by rw [show k + t₀ + 1 = k + L by omega])).mp hsucc)
  omega

/-- **The run through a `Y`-complete edge of a rim with exactly four of them has three or five
positions** — the paper's generic case (`x₀-z-x₁` and `c₁-c₂-c₃` separate) and its degenerate
case (`x₁ = c₁`, one run of five). -/
theorem run_length_eq_three_or_five (hC : IsHoleList G C)
    (h4 : OptimalWheelChoice.yEdgeCount G Y C = 4)
    {k L : ℕ} (hL : L + 1 ≤ C.length) (hodd : L % 2 = 1)
    (hall : ∀ t < L, CycVert G Y C (k + t))
    (hnext : ¬ CycVert G Y C (k + L))
    {t₀ : ℕ} (ht₀ : t₀ < L) (hedge : CycEdge G Y C (k + t₀)) :
    L = 3 ∨ L = 5 := by
  have h3 := run_length_ge_three hC hL hodd hall hnext ht₀ hedge
  have hle := run_edges_le (Y := Y) hC hL hall
  rw [h4] at hle
  omega

end Workspace.ProofLemmas.YEdgeFourConfig
